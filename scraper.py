#!/usr/bin/env python3
"""
SteamRip + FitGirl combined games scraper (incremental, GitHub Actions friendly).

Design goals
------------
- Store ONLY the stable short link (`bzzhr_url`) in games.json.
- NEVER resolve the real download URL during the scrape.
  Resolving happens later, on-demand, when the user clicks Download
  inside Playnite (avoids rate-limits and expired links).
- Robust extraction of the short link even if page markup shifts.
- Resume / only-new: skips SteamRip URLs already present in games.json.
- FitGirl enrichment (cover, tags, company, updates, screenshots, video)
  is optional and still works the same way.

SteamRip provides: titles, short download link, system requirements,
game info, featured image, screenshots, description, size.

FitGirl (fuzzy-matched): cover, tags, company, updates, screenshots,
video, description (preferred over SteamRip when available).

Languages always ENG; size always from SteamRip when available.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any
from urllib.parse import urljoin, urlparse

from bs4 import BeautifulSoup, Tag
from curl_cffi import requests as cffi_requests

try:
    from rapidfuzz import fuzz, process
except ImportError:
    fuzz = process = None  # type: ignore

STEAMRIP_BASE = "https://steamrip.com/"
STEAMRIP_LIST = "https://steamrip.com/games-list-page/"
FITGIRL_LIST = "https://fitgirl-repacks.site/all-my-repacks-a-z/"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)
FUZZY_THRESHOLD = 85

# Hosts that indicate a BZZHR / Buzzheavier short link
BZZHR_HOSTS = (
    "bzzhr.to",
    "buzzheavier.com",
    "www.buzzheavier.com",
)


def session() -> cffi_requests.Session:
    return cffi_requests.Session(impersonate="chrome")


def get_html(url: str, referer: str | None = None, timeout: int = 45) -> str:
    s = session()
    headers = {
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
    }
    if referer:
        headers["Referer"] = referer
    r = s.get(url, headers=headers, timeout=timeout)
    r.raise_for_status()
    return r.text


def clean(value: str) -> str:
    return re.sub(r"\s+", " ", value or "").strip()


def absolute_url(value: str, base: str) -> str:
    return urljoin(base, (value or "").strip())


def clean_game_title(value: str) -> str:
    """Normalize display / match titles from SteamRip or FitGirl."""
    value = value or ""
    value = re.split(r"\s+free download\b", value, maxsplit=1, flags=re.I)[0]
    value = re.sub(r"\s*[-–—]\s*FitGirl\s*Repack.*$", "", value, flags=re.I)
    # FitGirl: "Game – v1.1.0 (Denuvoless)", "Game + Windows 7 Fix", "Game Build xxx"
    value = re.sub(r"\s*\+.*$", "", value)
    value = re.sub(
        r"\s*[-–—]\s*v?\d+(?:[\.\d]+)?.*$",
        "",
        value,
        flags=re.I,
    )
    value = re.sub(r"\s*\([^)]*denuvo[^)]*\)\s*", " ", value, flags=re.I)
    value = re.sub(r"\s*\([^)]*\)\s*$", "", value)  # trailing (anything)
    value = re.sub(r"\s+v\d+(?:[\.\d]+)?\b.*$", "", value, flags=re.I)
    return value.strip(" -–—:|")


def normalize_for_match(title: str) -> str:
    t = clean_game_title(title).lower()
    t = re.sub(r"[^\w\s]", " ", t)
    t = re.sub(r"\b(repack|goty|edition|deluxe|ultimate|remastered|definitive)\b", " ", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t


def is_steamrip_game_link(a: Tag) -> bool:
    href = absolute_url(a.get("href", ""), STEAMRIP_BASE)
    text = clean(a.get_text(" ", strip=True))
    parsed = urlparse(href)
    return (
        parsed.netloc.endswith("steamrip.com")
        and bool(parsed.path.strip("/"))
        and re.search(r"free download", text, re.I) is not None
        and not any(x in href for x in ("/games-list-page/", "/category/", "/tag/"))
    )


def is_bzzhr_url(href: str) -> bool:
    """Return True if the URL points at a known BZZHR short-link host."""
    if not href:
        return False
    try:
        netloc = urlparse(href).netloc.lower()
    except Exception:
        return False
    return any(netloc == h or netloc.endswith("." + h) for h in BZZHR_HOSTS)


def section_between(content: Tag, heading_text: str, next_headings: set[str]) -> Tag | None:
    heading = next(
        (
            h
            for h in content.find_all(["h2", "h3", "h4", "h5"])
            if clean(h.get_text(" ", strip=True)).lower() == heading_text.lower()
        ),
        None,
    )
    if not heading:
        return None
    wrapper = BeautifulSoup("<div></div>", "html.parser").div
    assert wrapper is not None
    stop = {x.lower() for x in next_headings}
    for sibling in heading.find_next_siblings():
        if sibling.name in {"h2", "h3", "h4", "h5"} and clean(sibling.get_text(" ", strip=True)).lower() in stop:
            break
        wrapper.append(BeautifulSoup(str(sibling), "html.parser"))
    return wrapper


def parse_labelled_list(section: Tag | None) -> dict[str, str]:
    result: dict[str, str] = {}
    if not section:
        return result
    for li in section.select("li"):
        strong = li.find(["strong", "b"])
        text = clean(li.get_text(" ", strip=True))
        if strong:
            raw_label = clean(strong.get_text(" ", strip=True))
            label = raw_label.rstrip(":")
            value = clean(text[len(raw_label) :]).lstrip(": ")
            if label and value:
                result[label] = value
        elif text:
            result["notes"] = clean(f"{result.get('notes', '')} {text}")
    return result


def extract_bzzhr_url(soup: BeautifulSoup, page_url: str) -> str | None:
    """
    Robustly find the BZZHR short link on a SteamRip game page.

    Strategy (in order):
    1. Prefer links that appear inside a "DOWNLOAD" / "DIRECT DOWNLOAD" section.
    2. Fall back to any anchor whose href points at a known BZZHR host.
    3. Also check plain text / regex in case the link is obfuscated or in a script.
    """
    content = soup.select_one(".entry-content") or soup.select_one("article") or soup.body
    candidates: list[str] = []

    # --- 1. Prefer download sections -----------------------------------------
    download_headings = {
        "download links",
        "direct download",
        "download",
        "downloads",
        "mirror",
        "mirrors",
    }
    if content:
        for h in content.find_all(["h2", "h3", "h4", "h5"]):
            heading = clean(h.get_text(" ", strip=True)).lower()
            if any(dh in heading for dh in download_headings):
                for sib in h.find_next_siblings():
                    if sib.name in {"h2", "h3", "h4", "h5"}:
                        break
                    for a in sib.select("a[href]"):
                        href = absolute_url(a.get("href", ""), page_url)
                        if is_bzzhr_url(href):
                            candidates.append(href)

    # --- 2. Any anchor on the page -------------------------------------------
    for a in soup.select("a[href]"):
        href = absolute_url(a.get("href", ""), page_url)
        if is_bzzhr_url(href) and href not in candidates:
            candidates.append(href)

    # --- 3. data-* attributes / plain text fallback --------------------------
    if not candidates:
        html = str(soup)
        for m in re.finditer(
            r"https?://(?:www\.)?(?:bzzhr\.to|buzzheavier\.com)/[a-zA-Z0-9_-]+",
            html,
            re.I,
        ):
            url = m.group(0).rstrip(".,);\"'")
            if url not in candidates:
                candidates.append(url)

    if not candidates:
        return None

    # Prefer the shortest / cleanest short-link (usually the canonical one)
    candidates.sort(key=lambda u: (len(u), u))
    return candidates[0]


def parse_steamrip_game(html: str, url: str) -> dict[str, Any]:
    soup = BeautifulSoup(html, "html.parser")
    content = soup.select_one(".entry-content") or soup.select_one("article") or soup.body
    if content is None:
        raise ValueError("Could not find game content container")

    title_node = (
        soup.select_one("h1.entry-title")
        or soup.select_one(".entry-header h1")
        or soup.find("h1")
    )
    title = clean_game_title(clean(title_node.get_text(" ", strip=True))) if title_node else ""
    if not title and soup.title:
        title = clean_game_title(
            clean(soup.title.get_text(" ", strip=True)).replace(" » SteamRIP", "")
        )

    cover = None
    fig = soup.select_one(
        "figure.single-featured-image img, .single-featured-image img, img.wp-post-image"
    )
    if fig:
        cover = fig.get("src") or fig.get("data-src") or fig.get("data-lazy-src")
        if cover:
            cover = absolute_url(cover, url)

    screenshots_section = section_between(
        content, "SCREENSHOTS", {"SYSTEM REQUIREMENTS", "GAME INFO", "DOWNLOAD LINKS"}
    )
    requirements_section = section_between(
        content, "SYSTEM REQUIREMENTS", {"GAME INFO", "DOWNLOAD LINKS"}
    )
    info_section = section_between(content, "GAME INFO", {"DOWNLOAD LINKS"})

    description_parts: list[str] = []
    h2 = next(
        (
            h
            for h in content.find_all(["h2", "h3"])
            if "direct download" in clean(h.get_text(" ", strip=True)).lower()
        ),
        None,
    )
    if h2:
        for sibling in h2.find_next_siblings():
            if sibling.name in {"h2", "h3", "h4", "h5"}:
                break
            if sibling.name == "p":
                text = clean(sibling.get_text(" ", strip=True))
                if text:
                    description_parts.append(text)

    screenshots: list[str] = []
    if screenshots_section:
        for element in screenshots_section.select("a[href], img[src]"):
            value = element.get("href") or element.get("src")
            if value:
                href = absolute_url(value, url)
                if href not in screenshots and any(
                    ext in href.lower() for ext in (".jpg", ".jpeg", ".png", ".webp", ".gif")
                ):
                    screenshots.append(href)

    # Only the short link – never resolve the real download URL here
    bzzhr_url = extract_bzzhr_url(soup, url)

    game_info = parse_labelled_list(info_section)
    size = (
        game_info.get("Game Size")
        or game_info.get("Size")
        or game_info.get("Repack Size")
        or game_info.get("Download Size")
        or game_info.get("Original Size")
    )

    return {
        "title": title,
        "url": url,
        "description": "\n\n".join(description_parts),
        "cover_image": cover,
        "screenshots": screenshots,
        "system_requirements": parse_labelled_list(requirements_section),
        "game_info": game_info,
        "size": size,
        "languages": "ENG",
        "bzzhr_url": bzzhr_url,  # short link only – never the direct file URL
        "fitgirl_url": None,
        "fitgirl_matched": False,
        "genres": [],
        "company": None,
        "updates": [],
        "video": None,
        "source_cover": "steamrip",
        "source_screenshots": "steamrip",
        "source_description": "steamrip",
    }


def scrape_steamrip_list() -> list[tuple[str, str]]:
    html = get_html(STEAMRIP_LIST)
    soup = BeautifulSoup(html, "html.parser")
    links: list[tuple[str, str]] = []
    seen: set[str] = set()
    for a in soup.select("a[href]"):
        if is_steamrip_game_link(a):
            url = absolute_url(a["href"], STEAMRIP_LIST)
            if url not in seen:
                seen.add(url)
                links.append((clean(a.get_text(" ", strip=True)), url))
    return links


def scrape_steamrip_one(title: str, url: str) -> dict[str, Any]:
    html = get_html(url)
    record = parse_steamrip_game(html, url)
    record["title"] = clean_game_title(record["title"] or title)
    # Intentionally do NOT call resolve_bzzhr_http here.
    return record


def detect_fitgirl_pages() -> int:
    html = get_html(FITGIRL_LIST)
    nums = [int(n) for n in re.findall(r"lcp_page0=(\d+)", html)]
    if nums:
        return max(nums)
    soup = BeautifulSoup(html, "html.parser")
    for a in soup.select(".lcp_paginator a, a.page-numbers"):
        m = re.search(r"(\d+)", a.get_text(" ", strip=True) or "")
        if m:
            nums.append(int(m.group(1)))
        href = a.get("href") or ""
        m2 = re.search(r"lcp_page0=(\d+)", href)
        if m2:
            nums.append(int(m2.group(1)))
    return max(nums) if nums else 1


def scrape_fitgirl_list_page(page: int) -> list[tuple[str, str]]:
    if page <= 1:
        url = FITGIRL_LIST
    else:
        url = f"{FITGIRL_LIST}?lcp_page0={page}#lcp_instance_0"
    html = get_html(url)
    soup = BeautifulSoup(html, "html.parser")
    results: list[tuple[str, str]] = []
    container = soup.select_one("#lcp_instance_0")
    items = container.select("li a") if container else []
    for a in items:
        href = a.get("href") or ""
        text = clean(a.get_text(" ", strip=True))
        if not href or not text:
            continue
        if "fitgirl-repacks.site" not in href and not href.startswith("/"):
            continue
        if any(x in href for x in ("/tag/", "/category/", "/all-my-repacks", "/page/")):
            continue
        full = absolute_url(href, FITGIRL_LIST)
        results.append((text, full))
    return results


def scrape_fitgirl_catalog(max_pages: int | None = None, delay: float = 0.5) -> dict[str, str]:
    total = detect_fitgirl_pages()
    if max_pages:
        total = min(total, max_pages)
    print(f"[fitgirl] detected {total} list pages")
    catalog: dict[str, str] = {}
    for page in range(1, total + 1):
        try:
            pairs = scrape_fitgirl_list_page(page)
            for title, url in pairs:
                if title not in catalog:
                    catalog[title] = url
            print(f"[fitgirl] page {page}/{total}: +{len(pairs)} (total unique {len(catalog)})")
        except Exception as e:
            print(f"[fitgirl] page {page} failed: {e}", file=sys.stderr)
        if delay:
            time.sleep(delay)
    return catalog


def parse_fitgirl_game(html: str, url: str) -> dict[str, Any]:
    soup = BeautifulSoup(html, "html.parser")
    content = soup.select_one(".entry-content") or soup.select_one("article") or soup.body
    if content is None:
        raise ValueError("no content")

    out: dict[str, Any] = {
        "fitgirl_url": url,
        "cover_image": None,
        "genres": [],
        "company": None,
        "updates": [],
        "screenshots": [],
        "video": None,
        "description": None,
    }

    for img in content.select("img"):
        src = img.get("src") or img.get("data-src") or ""
        if not src:
            continue
        src = absolute_url(src, url)
        if any(x in src.lower() for x in ("emoji", "icon", "avatar", "logo")):
            continue
        out["cover_image"] = src
        break

    text_blob = content.get_text("\n", strip=True)
    genres: list[str] = []
    for a in content.select('a[href*="/tag/"]'):
        t = clean(a.get_text(" ", strip=True))
        if t and t not in genres:
            genres.append(t)
    out["genres"] = genres

    m = re.search(r"Compan(?:y|ies)\s*:\s*(.+)", text_blob, re.I)
    if m:
        company = clean(m.group(1).split("\n")[0])
        company = re.sub(r"\s*(Languages|Original Size|Repack Size).*$", "", company, flags=re.I)
        out["company"] = company or None

    updates: list[dict[str, str]] = []
    for h in content.find_all(["h2", "h3", "h4"]):
        if "game updates" in clean(h.get_text(" ", strip=True)).lower():
            for sib in h.find_next_siblings():
                if sib.name in {"h2", "h3", "h4"}:
                    break
                for a in sib.select("a[href]"):
                    href = a.get("href") or ""
                    name = clean(a.get_text(" ", strip=True))
                    if not href or not name:
                        continue
                    if re.match(r"^https?://", name, re.I):
                        continue
                    if name.lower() in {"elamigos", "source", "here", "cs.rin.ru"}:
                        continue
                    if "cs.rin.ru" in href.lower() or "discussion" in name.lower():
                        continue
                    if not any(
                        x in name.lower()
                        for x in (".rar", "update", "fix", "converter", "patch", "dlc")
                    ):
                        # keep only file-like update entries
                        if "http" in name.lower():
                            continue
                    updates.append({"name": name, "url": absolute_url(href, url)})
            break
    out["updates"] = updates

    for h in content.find_all(["h2", "h3", "h4"]):
        if "screenshot" in clean(h.get_text(" ", strip=True)).lower():
            block_nodes = []
            for sib in h.find_next_siblings():
                if sib.name in {"h2", "h3", "h4"}:
                    break
                block_nodes.append(sib)
            block = BeautifulSoup("".join(str(n) for n in block_nodes), "html.parser")
            shots: list[str] = []
            for a in block.select("a[href]"):
                href = absolute_url(a.get("href", ""), url)
                if any(ext in href.lower() for ext in (".jpg", ".jpeg", ".png", ".webp", ".gif")):
                    if href not in shots:
                        shots.append(href)
                elif "riotpixels" in href and "screenshot" in href and href not in shots:
                    shots.append(href)
            for img in block.select("img[src]"):
                src = absolute_url(img.get("src", ""), url)
                if src and src not in shots:
                    shots.append(src)
            out["screenshots"] = shots
            video = block.select_one("video source[src], video[src]")
            if video:
                out["video"] = absolute_url(video.get("src") or "", url)
            break

    def _is_junk_desc(t: str) -> bool:
        tl = t.lower()
        if tl.startswith(
            ("genres", "company", "companies", "languages", "original size", "repack size")
        ):
            return True
        # mirror / part lists
        if ".rar" in tl or "fitgirl-repacks.site" in tl or "_part" in tl:
            return True
        if tl.count(".part") >= 2 or t.count(".rar") >= 2:
            return True
        if "download mirrors" in tl or "filehoster" in tl:
            return True
        return False

    # Prefer collapsed spoiler / story text
    for sel in (".su-spoiler-content", ".su-u-trim", ".su-spoiler .su-spoiler-content"):
        for node in content.select(sel):
            desc = clean(node.get_text(" ", strip=True))
            if desc and len(desc) > 60 and not _is_junk_desc(desc):
                out["description"] = desc
                break
        if out["description"]:
            break

    if not out["description"]:
        paras = []
        for p in content.select("p"):
            t = clean(p.get_text(" ", strip=True))
            if len(t) > 80 and not _is_junk_desc(t):
                paras.append(t)
        if paras:
            out["description"] = "\n\n".join(paras[:4])

    return out


def fuzzy_match_title(
    steamrip_title: str,
    fitgirl_titles: list[str],
    threshold: int = FUZZY_THRESHOLD,
) -> str | None:
    if not fitgirl_titles:
        return None
    if process is None or fuzz is None:
        n = normalize_for_match(steamrip_title)
        for t in fitgirl_titles:
            if normalize_for_match(t) == n:
                return t
        return None

    choices = {t: normalize_for_match(t) for t in fitgirl_titles}
    query = normalize_for_match(steamrip_title)
    # Prefer exact normalized equality first
    for orig, norm in choices.items():
        if norm == query:
            return orig

    norm_list = list(dict.fromkeys(choices.values()))  # unique norms, stable order
    # token_set_ratio tolerates extra tokens (version, denuvoless, etc.)
    hit = process.extractOne(query, norm_list, scorer=fuzz.token_set_ratio)
    if hit and hit[1] >= threshold:
        matched_norm = hit[0]
        for orig, norm in choices.items():
            if norm == matched_norm:
                return orig
    hit2 = process.extractOne(query, norm_list, scorer=fuzz.token_sort_ratio)
    if hit2 and hit2[1] >= threshold:
        matched_norm = hit2[0]
        for orig, norm in choices.items():
            if norm == matched_norm:
                return orig
    return None


def apply_fitgirl(record: dict[str, Any], fg: dict[str, Any]) -> dict[str, Any]:
    record["fitgirl_url"] = fg.get("fitgirl_url")
    record["fitgirl_matched"] = True
    if fg.get("cover_image"):
        record["cover_image"] = fg["cover_image"]
        record["source_cover"] = "fitgirl"
    if fg.get("screenshots"):
        record["screenshots"] = fg["screenshots"]
        record["source_screenshots"] = "fitgirl"
    if fg.get("description"):
        record["description"] = fg["description"]
        record["source_description"] = "fitgirl"
    if fg.get("genres"):
        record["genres"] = fg["genres"]
    if fg.get("company"):
        record["company"] = fg["company"]
    if fg.get("updates"):
        record["updates"] = fg["updates"]
    if fg.get("video"):
        record["video"] = fg["video"]
    record["languages"] = "ENG"
    return record


def load_games(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else []
    except (OSError, json.JSONDecodeError):
        print("Warning: could not load existing games.json", file=sys.stderr)
        return []


def save_games(path: Path, records: list[dict[str, Any]]) -> None:
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(records, ensure_ascii=False, indent=2), encoding="utf-8")
    temp.replace(path)


def strip_resolved_fields(record: dict[str, Any]) -> dict[str, Any]:
    """
    Ensure we never keep any previously-resolved direct download fields.
    This keeps the JSON clean if an older games.json is being resumed.
    """
    for key in ("bzzhr_download_url", "bzzhr_filename", "bzzhr_page_url"):
        record.pop(key, None)
    return record


def run(args: argparse.Namespace) -> int:
    out = Path(args.output)
    records = load_games(out)

    # Clean any leftover resolved fields from older runs
    for r in records:
        strip_resolved_fields(r)

    by_url = {r.get("url"): i for i, r in enumerate(records) if r.get("url")}

    print("[steamrip] fetching game list…")
    links = scrape_steamrip_list()
    if args.limit:
        links = links[: args.limit]
    pending = [(t, u) for t, u in links if u not in by_url]
    print(f"[steamrip] {len(links)} listed, {len(by_url)} known, {len(pending)} new")

    lock = threading.Lock()

    def do_steamrip(title: str, url: str) -> dict[str, Any]:
        try:
            rec = scrape_steamrip_one(title, url)
            strip_resolved_fields(rec)
            return rec
        except Exception as e:
            return {
                "title": title,
                "url": url,
                "error": str(e),
                "languages": "ENG",
                "bzzhr_url": None,
            }

    if pending:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futs = {pool.submit(do_steamrip, t, u): (t, u) for t, u in pending}
            for fut in as_completed(futs):
                rec = fut.result()
                with lock:
                    if rec.get("url") in by_url:
                        records[by_url[rec["url"]]] = rec
                    else:
                        by_url[rec.get("url")] = len(records)
                        records.append(rec)
                    save_games(out, records)

                if "error" in rec:
                    print(f"[steamrip] FAIL {rec.get('url')}: {rec['error']}", file=sys.stderr)
                else:
                    short = rec.get("bzzhr_url") or "(no short link)"
                    print(f"[steamrip] {rec.get('title')} → {short}")

                if args.steamrip_delay > 0:
                    time.sleep(args.steamrip_delay)

    if not args.skip_fitgirl:
        print("[fitgirl] building catalog…")
        catalog = scrape_fitgirl_catalog(
            max_pages=args.fitgirl_pages or None, delay=args.delay
        )
        fg_titles = list(catalog.keys())
        print(f"[fitgirl] catalog size: {len(fg_titles)}")

        need_enrich = [
            r
            for r in records
            if r.get("url")
            and not r.get("error")
            and (args.refitgirl or not r.get("fitgirl_matched"))
        ]
        print(f"[fitgirl] {len(need_enrich)} games to match/enrich")

        for r in need_enrich:
            title = r.get("title") or ""
            matched = fuzzy_match_title(title, fg_titles, threshold=args.fuzzy)
            if not matched:
                continue
            fg_url = catalog[matched]
            try:
                html = get_html(fg_url)
                fg = parse_fitgirl_game(html, fg_url)
                apply_fitgirl(r, fg)
                print(f"[fitgirl] matched '{title}' ≈ '{matched}'")
            except Exception as e:
                print(f"[fitgirl] fail {fg_url}: {e}", file=sys.stderr)
            if args.delay:
                time.sleep(args.delay)
            save_games(out, records)

    # Final cleanup pass
    for r in records:
        strip_resolved_fields(r)
    save_games(out, records)

    has_link = sum(1 for r in records if r.get("bzzhr_url"))
    print(f"Done. {len(records)} games in {out} ({has_link} with bzzhr_url)")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", default="games.json")
    p.add_argument("--workers", type=int, default=4)
    p.add_argument("--limit", type=int, default=0, help="Limit new SteamRip games this run")
    p.add_argument(
        "--steamrip-delay",
        type=float,
        default=0.0,
        help="Optional delay (seconds) after each SteamRip game page (helps avoid blocks)",
    )
    p.add_argument("--delay", type=float, default=0.4, help="Delay between FitGirl requests")
    p.add_argument("--fitgirl-pages", type=int, default=0, help="Limit FitGirl list pages (0=all)")
    p.add_argument("--fuzzy", type=int, default=FUZZY_THRESHOLD, help="Fuzzy match threshold 0-100")
    p.add_argument("--skip-fitgirl", action="store_true")
    p.add_argument(
        "--refitgirl",
        action="store_true",
        help="Re-run FitGirl match even if already matched",
    )
    p.add_argument(
        "--resume",
        action="store_true",
        help="Skip SteamRip URLs already in output (always on)",
    )
    args = p.parse_args()
    if args.workers < 1:
        p.error("--workers must be >= 1")
    if process is None:
        print(
            "Warning: rapidfuzz not installed – using exact title match only. "
            "pip install rapidfuzz",
            file=sys.stderr,
        )
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
