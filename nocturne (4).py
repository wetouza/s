#!/usr/bin/env python3
"""
Nocturne 3.0 - a fast local gallery client for rule34.xxx
=========================================================
Single file, zero dependencies (Python 3.10+ standard library only).

Runs a private HTTP server on 127.0.0.1 and opens the UI in an app window.
The page talks ONLY to this local server; every upstream request (API,
autocomplete, images, video) is proxied here with proper headers, streaming
and HTTP Range support, so video seeking works and the browser never
contacts the site directly.

What is new in 3.0.0
--------------------
* Midnight UI. One indigo hue carries every surface, depth comes from
  lightness. Six accent presets, three contrast levels, three corner radii.
* Reworked cards: known aspect ratios (no layout jump), blur-up loading,
  progressive fallback ladder, hover video previews, quick actions.
* Rebuilt viewer: crossfaded transitions, zoom + pan for stills, a custom
  video player (buffered bar, scrub, volume, speed, loop, PiP) and true
  fullscreen for both images and video.
* Query engine: chips, upstream operators (rating:, score:>, sort:, id:,
  wildcards), saved searches, recent searches, URL hash restore.
* Settings: tabbed, persisted, live-applied. No reload needed.
* Server: single route table, one streaming path, strict Range handling,
  bounded caches, clean shutdown.

Usage
-----
    py nocturne.py                 start + open an app window
    py nocturne.py --tab           force a normal browser tab
    py nocturne.py --no-open       just start the server
    py nocturne.py --port N        preferred port (default 8451)
    py nocturne.py --verbose       log every request

Config and favorites live in %APPDATA%\Nocturne (Windows) or
~/.config/Nocturne (Linux/macOS). Settings from older versions, including
the "Image Shelf" era, are migrated automatically.
"""
from __future__ import annotations

import argparse
import contextlib
import json
import math
import os
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from collections import OrderedDict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

# ═══════════════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════════════
APP_NAME = "Nocturne"
VERSION = "3.0.0"
DEFAULT_PORT = 8451

API_ORIGIN = os.environ.get("NOCTURNE_API", "https://api.rule34.xxx").rstrip("/")
AC_ORIGIN = os.environ.get("NOCTURNE_AC", "https://ac.rule34.xxx").rstrip("/")
SITE_POST_URL = "https://rule34.xxx/index.php?page=post&s=view&id={id}"

BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
API_HEADERS = {
    "User-Agent": BROWSER_UA,
    "Accept": "application/json, text/xml, */*;q=0.8",
    "Referer": "https://rule34.xxx/",
    "Origin": "https://rule34.xxx",
}
MEDIA_HEADERS = {
    "User-Agent": BROWSER_UA,
    "Accept": "image/avif,image/webp,image/apng,image/*,video/*,*/*;q=0.8",
    "Referer": "https://rule34.xxx/",
}

VIDEO_EXTS = frozenset({"mp4", "webm", "mov", "m4v"})
UPSTREAM_TIMEOUT = 25
MEDIA_CHUNK = 128 * 1024
MAX_BODY = 1024 * 1024
MAX_PAGE_WALK = 6
SIMILAR_POOL_PAGES = 3
SIMILAR_POOL_MAX = 120

DEFAULT_CONFIG: dict = {
    # account
    "api_key": "",
    "user_id": "",
    # feed
    "per_page": 42,
    "sort": "newest",           # newest | score | random
    "rating": "all",            # all | safe | questionable | explicit
    "min_score": 0,
    "infinite_scroll": True,
    # appearance
    "accent": "moon",           # moon | frost | sage | amber | rose | violet
    "contrast": "normal",       # soft | normal | high
    "corners": "soft",          # sharp | soft | round
    "density": "cozy",          # compact | cozy | large
    "grain": True,
    "motion": "full",           # full | reduced | off
    "meta_mode": "hover",       # hover | always | off
    # media
    "hq_previews": True,
    "full_quality": False,
    "hover_preview": True,
    "preload_next": True,
    # playback
    "autoplay": True,
    "muted": True,
    "loop": True,
    "volume": 80,
    "speed": 1.0,
    # viewer
    "sidebar": True,
    # content
    "blacklist": ["loli", "shota", "toddlercon", "cub", "ai_generated"],
    "blacklist_mode": "hide",   # hide | blur | mark
    # search
    "saved_searches": [],
    "recent_searches": [],
}

ALLOWED_ENUMS = {
    "sort": {"newest", "score", "random"},
    "rating": {"all", "safe", "questionable", "explicit"},
    "accent": {"moon", "frost", "sage", "amber", "rose", "violet"},
    "contrast": {"soft", "normal", "high"},
    "corners": {"sharp", "soft", "round"},
    "density": {"compact", "cozy", "large"},
    "motion": {"full", "reduced", "off"},
    "meta_mode": {"hover", "always", "off"},
    "blacklist_mode": {"hide", "blur", "mark"},
}
BOOL_KEYS = ("infinite_scroll", "grain", "hq_previews", "full_quality", "hover_preview",
             "preload_next", "autoplay", "muted", "loop", "sidebar")
INT_RANGES = {"per_page": (10, 100, 42), "min_score": (0, 100000, 0), "volume": (0, 100, 80)}

# Tags that say nothing about *what* a post is. Excluded from the similarity
# fingerprint so "1girl" does not make everything look related.
GENERIC_TAGS = frozenset("""
1girl 1girls 1boy 1boys 2girls 2boys 3girls 3boys multiple_girls multiple_boys
solo solo_focus duo group female female_only male male_only female_focus male_focus
looking_at_viewer smile blush open_mouth closed_eyes closed_mouth teeth tongue tongue_out
simple_background white_background transparent_background detailed_background gradient_background
highres absurdres hi_res widescreen 4k tagme animated video gif sound has_audio
breasts large_breasts medium_breasts small_breasts huge_breasts gigantic_breasts big_breasts
nipples areolae cleavage nude nudity completely_nude clothed partially_clothed topless bottomless
naked bottomwear topwear long_hair short_hair medium_hair very_long_hair hair_between_eyes
bangs ponytail twintails braid bare_shoulders collarbone
blue_eyes green_eyes red_eyes brown_eyes purple_eyes yellow_eyes pink_eyes grey_eyes
blonde_hair brown_hair black_hair white_hair blue_hair pink_hair red_hair purple_hair
green_hair silver_hair grey_hair orange_hair
thighs thighhighs thick_thighs wide_hips curvy hourglass_figure big_ass ass butt navel
penis pussy vagina anus testicles erection balls
sex vaginal penetration anal oral fellatio cum cumshot cum_inside creampie masturbation
standing sitting lying kneeling on_back on_side all_fours spread_legs legs_up
indoors outdoors bed bedroom day night sky nature
uncensored censored mosaic_censoring bar_censor
light-skinned_female light-skinned_male dark-skinned_female dark-skinned_male
""".split())


# ═══════════════════════════════════════════════════════════════════════
# Errors + small helpers
# ═══════════════════════════════════════════════════════════════════════
class ApiError(Exception):
    """Structured failure surfaced to the UI as {"error": {code, status}}."""

    def __init__(self, code: str, http_status: int = 502, upstream_status: int = 0):
        super().__init__(code)
        self.code = code            # nokey|auth|rate|network|upstream|parse|notfound|badreq
        self.http_status = http_status
        self.upstream_status = upstream_status


def to_int(value, default: int = 0) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return default


def clamp(value: int, low: int, high: int) -> int:
    return max(low, min(high, value))


# ═══════════════════════════════════════════════════════════════════════
# Persistence
# ═══════════════════════════════════════════════════════════════════════
def config_dir() -> Path:
    override = os.environ.get("NOCTURNE_CONFIG_DIR")
    if override:
        return Path(override)
    if os.name == "nt":
        base = Path(os.environ.get("APPDATA", str(Path.home())))
    elif sys.platform == "darwin":
        base = Path.home() / "Library" / "Application Support"
    else:
        base = Path(os.environ.get("XDG_CONFIG_HOME", str(Path.home() / ".config")))
    return base / APP_NAME


def migrate_legacy(target: Path) -> None:
    """Copy settings and favorites from an older install, once."""
    if target.exists():
        return
    for name in ("ImageShelf", "Nocturne2"):
        legacy = target.parent / name
        if not legacy.is_dir():
            continue
        try:
            target.mkdir(parents=True, exist_ok=True)
            for fname in ("config.json", "favorites.json"):
                src = legacy / fname
                if src.is_file():
                    shutil.copy2(src, target / fname)
            print(f"  migrated settings from {legacy}")
        except OSError:
            pass
        return


class JsonFile:
    """Thread-safe JSON document with atomic writes."""

    def __init__(self, path: Path, default):
        self.path = path
        self.default = default
        self.lock = threading.RLock()
        self._data = None

    def load(self):
        with self.lock:
            if self._data is None:
                try:
                    self._data = json.loads(self.path.read_text(encoding="utf-8"))
                except (OSError, ValueError):
                    self._data = json.loads(json.dumps(self.default))
            return self._data

    def save(self, data) -> None:
        with self.lock:
            self._data = data
            try:
                self.path.parent.mkdir(parents=True, exist_ok=True)
                tmp = self.path.with_suffix(".tmp")
                tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
                os.replace(tmp, self.path)
            except OSError as exc:
                print(f"[warn] could not write {self.path.name}: {exc}", file=sys.stderr)


def _clean_tag_list(raw, limit: int, maxlen: int = 80) -> list[str]:
    if isinstance(raw, str):
        raw = raw.replace(",", "\n").split("\n")
    if not isinstance(raw, list):
        return []
    out, seen = [], set()
    for entry in raw:
        tag = str(entry).strip().lower().replace(" ", "_")
        if tag and tag not in seen and len(tag) <= maxlen:
            seen.add(tag)
            out.append(tag)
        if len(out) >= limit:
            break
    return out


class ConfigStore:
    def __init__(self, path: Path):
        self.file = JsonFile(path, DEFAULT_CONFIG)
        self.revision = 0

    def get(self) -> dict:
        merged = dict(DEFAULT_CONFIG)
        data = self.file.load()
        if isinstance(data, dict):
            merged.update({k: data[k] for k in DEFAULT_CONFIG if k in data})
        return self._sanitize(merged)

    def update(self, patch: dict) -> dict:
        if not isinstance(patch, dict):
            raise ApiError("parse", 400)
        with self.file.lock:
            cfg = self.get()
            for key in DEFAULT_CONFIG:
                if key in patch:
                    cfg[key] = patch[key]
            cfg = self._sanitize(cfg)
            self.file.save(cfg)
            self.revision += 1
            return cfg

    def reset(self) -> dict:
        with self.file.lock:
            cfg = self._sanitize(dict(DEFAULT_CONFIG))
            # keep credentials, nobody wants to paste those twice
            current = self.get()
            cfg["api_key"] = current["api_key"]
            cfg["user_id"] = current["user_id"]
            cfg["saved_searches"] = current["saved_searches"]
            self.file.save(cfg)
            self.revision += 1
            return cfg

    @staticmethod
    def _sanitize(cfg: dict) -> dict:
        out = dict(cfg)
        out["api_key"] = str(out.get("api_key") or "").strip()[:512]
        out["user_id"] = str(out.get("user_id") or "").strip()[:64]

        for key, (low, high, fallback) in INT_RANGES.items():
            out[key] = clamp(to_int(out.get(key), fallback), low, high)

        try:
            speed = float(out.get("speed", 1.0))
        except (TypeError, ValueError):
            speed = 1.0
        out["speed"] = min(4.0, max(0.25, round(speed, 2)))

        for key, allowed in ALLOWED_ENUMS.items():
            if out.get(key) not in allowed:
                out[key] = DEFAULT_CONFIG[key]

        for key in BOOL_KEYS:
            out[key] = bool(out.get(key))

        out["blacklist"] = _clean_tag_list(out.get("blacklist"), 400)

        saved = out.get("saved_searches")
        clean_saved = []
        if isinstance(saved, list):
            for item in saved[:60]:
                if not isinstance(item, dict):
                    continue
                query = str(item.get("query") or "").strip()[:400]
                if not query:
                    continue
                clean_saved.append({
                    "name": str(item.get("name") or query).strip()[:60],
                    "query": query,
                })
        out["saved_searches"] = clean_saved

        recent = out.get("recent_searches")
        clean_recent, seen = [], set()
        if isinstance(recent, list):
            for item in recent[:40]:
                query = str(item or "").strip()[:400]
                if query and query not in seen:
                    seen.add(query)
                    clean_recent.append(query)
        out["recent_searches"] = clean_recent[:12]
        return out


FAVORITE_FIELDS = ("id", "file", "sample", "preview", "w", "h", "sw", "sh", "tags",
                   "score", "rating", "video", "ext", "source", "change", "page_url")


class FavoritesStore:
    def __init__(self, path: Path):
        self.file = JsonFile(path, {"posts": []})

    def all(self) -> list[dict]:
        data = self.file.load()
        posts = data.get("posts") if isinstance(data, dict) else None
        if not isinstance(posts, list):
            return []
        return [p for p in posts if isinstance(p, dict) and p.get("id")]

    def ids(self) -> list[int]:
        return [to_int(p.get("id")) for p in self.all()]

    def toggle(self, post: dict) -> bool:
        clean = _clean_favorite(post)
        with self.file.lock:
            posts = self.all()
            kept = [p for p in posts if p.get("id") != clean["id"]]
            added = len(kept) == len(posts)
            if added:
                kept.insert(0, clean)
            self.file.save({"posts": kept})
            return added

    def clear(self) -> None:
        with self.file.lock:
            self.file.save({"posts": []})


def _clean_favorite(post: dict) -> dict:
    if not isinstance(post, dict):
        raise ApiError("parse", 400)
    try:
        pid = int(post.get("id"))
    except (TypeError, ValueError):
        raise ApiError("parse", 400) from None
    clean: dict = {"id": pid}
    for key in FAVORITE_FIELDS:
        if key == "id" or key not in post:
            continue
        val = post[key]
        if key == "tags":
            if isinstance(val, list):
                clean["tags"] = [str(t)[:120] for t in val[:400]]
        elif key in ("w", "h", "sw", "sh", "score", "change"):
            clean[key] = to_int(val)
        elif key == "video":
            clean[key] = bool(val)
        elif val is None:
            clean[key] = None
        else:
            clean[key] = str(val)[:1000]
    return clean


# ═══════════════════════════════════════════════════════════════════════
# Cache
# ═══════════════════════════════════════════════════════════════════════
class TtlCache:
    """Bounded thread-safe LRU with per-entry TTL."""

    def __init__(self, max_items: int, ttl: float):
        self.max_items = max_items
        self.ttl = ttl
        self.lock = threading.Lock()
        self.data: OrderedDict = OrderedDict()

    def get(self, key):
        with self.lock:
            item = self.data.get(key)
            if not item:
                return None
            stamp, value = item
            if time.monotonic() - stamp > self.ttl:
                del self.data[key]
                return None
            self.data.move_to_end(key)
            return value

    def put(self, key, value) -> None:
        with self.lock:
            self.data[key] = (time.monotonic(), value)
            self.data.move_to_end(key)
            while len(self.data) > self.max_items:
                self.data.popitem(last=False)

    def clear(self) -> None:
        with self.lock:
            self.data.clear()

    def __len__(self) -> int:
        with self.lock:
            return len(self.data)


# ═══════════════════════════════════════════════════════════════════════
# Upstream access
# ═══════════════════════════════════════════════════════════════════════
def fetch_bytes(url: str, headers: dict, retries: int = 1) -> bytes:
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=UPSTREAM_TIMEOUT) as resp:
                return resp.read()
        except urllib.error.HTTPError as exc:
            if exc.code in (401, 403):
                raise ApiError("auth", 502, exc.code) from None
            if exc.code == 429:
                raise ApiError("rate", 502, 429) from None
            raise ApiError("upstream", 502, exc.code) from None
        except (urllib.error.URLError, TimeoutError, OSError):
            if attempt >= retries:
                raise ApiError("network", 502) from None
            time.sleep(0.5 * (attempt + 1))
    raise ApiError("network", 502)


def parse_posts(body: bytes) -> tuple[list[dict], int | None]:
    """Handles XML (with total count), JSON, and an empty body for zero hits."""
    text = body.decode("utf-8-sig", "replace").strip()
    if not text:
        return [], 0
    if text.startswith("<"):
        try:
            root = ET.fromstring(text)
        except ET.ParseError:
            raise ApiError("parse") from None
        if root.tag != "posts":
            raise ApiError("parse")
        return [dict(node.attrib) for node in root.iter("post")], to_int(root.get("count"), 0)
    try:
        data = json.loads(text)
    except ValueError:
        low = text.lower()
        if "missing authentication" in low or ("api" in low and "key" in low):
            raise ApiError("auth", 502) from None
        raise ApiError("parse") from None
    if isinstance(data, dict):
        if isinstance(data.get("post"), list):
            data = data["post"]
        elif data.get("message"):
            raise ApiError("upstream", 502)
        else:
            data = []
    if not isinstance(data, list):
        raise ApiError("parse")
    return [row for row in data if isinstance(row, dict)], None


def normalize_post(raw: dict) -> dict | None:
    file_url = str(raw.get("file_url") or "").strip()
    pid = to_int(raw.get("id"))
    if not file_url or not pid:
        return None
    tail = file_url.rsplit("/", 1)[-1].split("?", 1)[0]
    ext = tail.rsplit(".", 1)[-1].lower() if "." in tail else ""
    sample = str(raw.get("sample_url") or "").strip() or None
    if sample == file_url:
        sample = None
    preview = str(raw.get("preview_url") or "").strip() or None
    rating = str(raw.get("rating") or "").strip().lower()[:1]
    width, height = to_int(raw.get("width")), to_int(raw.get("height"))
    return {
        "id": pid,
        "file": file_url,
        "sample": sample,
        "preview": preview,
        "w": width,
        "h": height,
        "sw": to_int(raw.get("sample_width")),
        "sh": to_int(raw.get("sample_height")),
        "ratio": round(width / height, 5) if width and height else 1.0,
        "tags": str(raw.get("tags") or "").split(),
        "score": to_int(raw.get("score")),
        "rating": rating if rating in ("s", "q", "e") else "",
        "video": ext in VIDEO_EXTS,
        "ext": ext,
        "source": str(raw.get("source") or "").strip(),
        "change": to_int(raw.get("change")),
        "page_url": SITE_POST_URL.format(id=pid),
        "blocked": False,
    }


def fetch_posts(cfg: dict, tags: str, pid: int, limit: int) -> tuple[list[dict], int | None]:
    params = {
        "page": "dapi", "s": "post", "q": "index",
        "limit": clamp(limit, 1, 100), "pid": max(0, pid), "tags": tags,
        "api_key": cfg["api_key"], "user_id": cfg["user_id"],
    }
    body = fetch_bytes(f"{API_ORIGIN}/index.php?{urllib.parse.urlencode(params)}", API_HEADERS)
    return parse_posts(body)


def fetch_post_by_id(cfg: dict, post_id: int) -> dict | None:
    params = {
        "page": "dapi", "s": "post", "q": "index", "id": post_id,
        "api_key": cfg["api_key"], "user_id": cfg["user_id"],
    }
    body = fetch_bytes(f"{API_ORIGIN}/index.php?{urllib.parse.urlencode(params)}", API_HEADERS)
    rows, _ = parse_posts(body)
    return normalize_post(rows[0]) if rows else None


def fetch_autocomplete(term: str) -> list[dict]:
    url = f"{AC_ORIGIN}/autocomplete.php?{urllib.parse.urlencode({'q': term})}"
    body = fetch_bytes(url, API_HEADERS)
    try:
        rows = json.loads(body.decode("utf-8-sig", "replace") or "[]")
    except ValueError:
        return []
    out = []
    for row in rows if isinstance(rows, list) else []:
        if not isinstance(row, dict):
            continue
        value = str(row.get("value") or "").strip()
        if not value:
            continue
        label = str(row.get("label") or value)
        match = re.search(r"\((\d[\d,\s]*)\)\s*$", label)
        count = to_int((match.group(1).replace(",", "").replace(" ", "")) if match else 0)
        out.append({"value": value, "count": count, "type": str(row.get("type") or "tag")})
    return out[:20]


def build_blacklist_matcher(entries: list[str]):
    exact: set[str] = set()
    prefixes: list[str] = []
    for entry in entries:
        entry = entry.strip().lower()
        if not entry:
            continue
        if entry.endswith("*"):
            if entry[:-1]:
                prefixes.append(entry[:-1])
        else:
            exact.add(entry)

    def matches(tags: list[str]) -> bool:
        for tag in tags:
            low = tag.lower()
            if low in exact:
                return True
            for prefix in prefixes:
                if low.startswith(prefix):
                    return True
        return False

    return matches


# ── similarity ─────────────────────────────────────────────────────────
def tag_weight(tag: str) -> float:
    low = tag.lower()
    weight = 1.0
    if "_(" in low:
        weight += 2.2
    weight += min(len(low), 42) / 22.0
    weight += low.count("_") * 0.25
    return weight


def signature_tags(tags: list[str], limit: int = 6) -> list[str]:
    scored = []
    for tag in tags:
        low = tag.lower()
        if len(low) < 3 or low in GENERIC_TAGS:
            continue
        scored.append((tag_weight(low), tag))
    scored.sort(key=lambda item: (-item[0], item[1]))
    return [tag for _, tag in scored[:limit]]


def similarity(src_tags: set[str], other_tags: list[str]) -> float:
    other = set(other_tags)
    shared = src_tags & other
    if not shared:
        return 0.0
    weight = sum(tag_weight(t) for t in shared if t.lower() not in GENERIC_TAGS)
    weight += 0.15 * len(shared)
    return round(weight / math.sqrt(len(other) + 8), 4)


def allowed_media_url(url: str) -> bool:
    try:
        parts = urllib.parse.urlsplit(url)
    except ValueError:
        return False
    host = (parts.hostname or "").lower()
    if not host:
        return False
    extra = {h.strip().lower()
             for h in os.environ.get("NOCTURNE_MEDIA_ALLOW", "").split(",") if h.strip()}
    if host in extra:
        return parts.scheme in ("http", "https")
    if parts.scheme != "https":
        return False
    return host == "rule34.xxx" or host.endswith(".rule34.xxx")


# ═══════════════════════════════════════════════════════════════════════
# Application state
# ═══════════════════════════════════════════════════════════════════════
class App:
    def __init__(self, verbose: bool = False):
        base = config_dir()
        migrate_legacy(base)
        self.dir = base
        self.config = ConfigStore(base / "config.json")
        self.favorites = FavoritesStore(base / "favorites.json")
        self.posts_cache = TtlCache(max_items=64, ttl=90)
        self.ac_cache = TtlCache(max_items=512, ttl=600)
        self.similar_cache = TtlCache(max_items=24, ttl=300)
        self.verbose = verbose
        self.started = time.time()

    # ── feed ───────────────────────────────────────────────────────────
    def posts(self, tags: str, pid: int, limit: int) -> dict:
        cfg = self.config.get()
        key = (tags, pid, limit, self.config.revision)
        cached = self.posts_cache.get(key)
        if cached is not None:
            return cached

        matcher = build_blacklist_matcher(cfg["blacklist"])
        mode = cfg["blacklist_mode"]
        out: list[dict] = []
        hidden = 0
        walked = 0
        count: int | None = None
        cursor = max(0, pid)
        end = False

        while True:
            rows, total = fetch_posts(cfg, tags, cursor, limit)
            if total is not None:
                count = total
            walked += 1
            cursor += 1
            if not rows:
                end = True
                break
            for raw in rows:
                post = normalize_post(raw)
                if not post:
                    continue
                if matcher(post["tags"]):
                    hidden += 1
                    if mode == "hide":
                        continue
                    post["blocked"] = True
                out.append(post)
            if out or walked >= MAX_PAGE_WALK:
                break

        payload = {"posts": out, "next_pid": cursor, "count": count,
                   "hidden": hidden, "walked": walked, "end": end}
        self.posts_cache.put(key, payload)
        return payload

    # ── similar ────────────────────────────────────────────────────────
    def similar(self, post_id: int) -> dict:
        key = (post_id, self.config.revision)
        cached = self.similar_cache.get(key)
        if cached is not None:
            return cached

        cfg = self.config.get()
        source = fetch_post_by_id(cfg, post_id)
        if not source:
            raise ApiError("notfound", 404)

        signature = signature_tags(source["tags"])
        if not signature:
            payload = {"posts": [], "source": source, "signature": []}
            self.similar_cache.put(key, payload)
            return payload

        query = " ~ ".join(signature[:4])
        matcher = build_blacklist_matcher(cfg["blacklist"])
        src_tags = {t for t in source["tags"] if t.lower() not in GENERIC_TAGS}
        pool: dict[int, tuple[float, dict]] = {}

        for page in range(SIMILAR_POOL_PAGES):
            try:
                rows, _ = fetch_posts(cfg, query, page, 100)
            except ApiError:
                break
            if not rows:
                break
            for raw in rows:
                post = normalize_post(raw)
                if not post or post["id"] == post_id or post["id"] in pool:
                    continue
                if matcher(post["tags"]):
                    continue
                score = similarity(src_tags, post["tags"])
                if score > 0:
                    pool[post["id"]] = (score, post)

        ranked = sorted(pool.values(), key=lambda item: -item[0])[:SIMILAR_POOL_MAX]
        payload = {
            "posts": [dict(post, similarity=score) for score, post in ranked],
            "source": source,
            "signature": signature,
        }
        self.similar_cache.put(key, payload)
        return payload

    # ── autocomplete ───────────────────────────────────────────────────
    def autocomplete(self, term: str) -> list[dict]:
        term = term.strip().lower()[:60]
        if len(term) < 2:
            return []
        cached = self.ac_cache.get(term)
        if cached is not None:
            return cached
        try:
            rows = fetch_autocomplete(term)
        except ApiError:
            rows = []
        self.ac_cache.put(term, rows)
        return rows

    def drop_caches(self) -> None:
        self.posts_cache.clear()
        self.similar_cache.clear()


# ═══════════════════════════════════════════════════════════════════════
# UI: stylesheet
# ═══════════════════════════════════════════════════════════════════════
PAGE_CSS = r"""
/* ═══════ tokens ═══════ */
:root{
  --acc-l:0.862; --acc-c:0.048; --acc-h:252;
  --acc:      oklch(var(--acc-l) var(--acc-c) var(--acc-h));
  --acc-mid:  oklch(0.700 calc(var(--acc-c) * 1.45) var(--acc-h));
  --acc-deep: oklch(0.320 calc(var(--acc-c) * 0.95) var(--acc-h));
  --acc-ink:  oklch(0.160 0.024 var(--acc-h));

  --void:0.112; --l1:0.148; --l2:0.184; --l3:0.228; --l4:0.282;
  --bg:  oklch(var(--void) 0.013 268);
  --s1:  oklch(var(--l1) 0.013 268);
  --s2:  oklch(var(--l2) 0.013 268);
  --s3:  oklch(var(--l3) 0.013 268);
  --s4:  oklch(var(--l4) 0.014 268);
  --line:      oklch(0.248 0.012 268);
  --line-soft: oklch(0.196 0.011 268);

  --tx:  oklch(0.958 0.004 268);
  --tx2: oklch(0.752 0.010 268);
  --tx3: oklch(0.578 0.013 268);
  --tx4: oklch(0.462 0.014 268);

  --rose: oklch(0.745 0.098 16);
  --rose-ink: oklch(0.235 0.040 16);
  --sage: oklch(0.768 0.052 158);
  --amber: oklch(0.815 0.068 80);

  --r-xs:5px; --r-sm:8px; --r-md:11px; --r-lg:15px; --r-xl:20px;
  --sp-1:4px; --sp-2:8px; --sp-3:12px; --sp-4:16px; --sp-5:24px; --sp-6:32px; --sp-7:48px; --sp-8:80px;

  --e-quart:cubic-bezier(0.25,1,0.5,1);
  --e-expo:cubic-bezier(0.16,1,0.3,1);
  --e-both:cubic-bezier(0.65,0,0.35,1);

  --head-h:58px; --rail-h:44px; --status-h:30px;
  --tile-min:240px; --gap:14px; --unit:8px;
  --z-rail:40; --z-drawer:60; --z-modal:70; --z-pop:80; --z-toast:90;
}
html[data-contrast="soft"]{ --void:0.132; --l1:0.168; --l2:0.202; --l3:0.244; --l4:0.296; }
html[data-contrast="high"]{ --void:0.086; --l1:0.126; --l2:0.166; --l3:0.214; --l4:0.272; }
html[data-corners="sharp"]{ --r-xs:2px; --r-sm:3px; --r-md:4px; --r-lg:5px; --r-xl:7px; }
html[data-corners="round"]{ --r-xs:8px; --r-sm:12px; --r-md:16px; --r-lg:22px; --r-xl:28px; }
html[data-density="compact"]{ --tile-min:172px; --gap:9px; }
html[data-density="large"]{ --tile-min:340px; --gap:18px; }

*{box-sizing:border-box;min-width:0}
html{scrollbar-color:var(--s3) var(--bg);background:var(--bg)}
body{
  margin:0;background:var(--bg);color:var(--tx);
  font-family:"Hanken Grotesk",-apple-system,BlinkMacSystemFont,"Segoe UI",system-ui,sans-serif;
  font-size:16px;font-weight:350;line-height:1.6;letter-spacing:0.012em;
  -webkit-font-smoothing:antialiased;font-optical-sizing:auto;
  padding-bottom:var(--status-h);overflow-y:scroll;
}
html[data-grain="on"] body::after{
  content:"";position:fixed;inset:0;pointer-events:none;z-index:120;opacity:.028;mix-blend-mode:soft-light;
  background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='140' height='140'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='0.85' numOctaves='4'/%3E%3C/filter%3E%3Crect width='140' height='140' filter='url(%23n)'/%3E%3C/svg%3E");
}
html[data-motion="off"] *,html[data-motion="off"] *::before,html[data-motion="off"] *::after{
  animation-duration:1ms !important;animation-delay:0ms !important;transition-duration:1ms !important;
}
html[data-motion="reduced"] .tile{animation:none;opacity:1}
h1,h2,h3{margin:0;font-weight:inherit;text-wrap:balance}
p{text-wrap:pretty}
button,input,textarea,select{font:inherit;color:inherit}
button{background:none;border:none;cursor:pointer;padding:0;text-align:inherit}
a{color:inherit}
img,video{display:block;max-width:100%}
:focus-visible{outline:2px solid var(--acc-mid);outline-offset:2px;border-radius:5px}
::selection{background:var(--acc-deep);color:var(--tx)}
.num{font-variant-numeric:tabular-nums}
.eyebrow{font-size:0.6875rem;font-weight:600;letter-spacing:0.13em;text-transform:uppercase;color:var(--tx4)}
.serif{font-family:"Newsreader",Georgia,serif;font-weight:300}
.sr{position:absolute;width:1px;height:1px;overflow:hidden;clip:rect(0 0 0 0);white-space:nowrap}
.spacer{flex:1 1 auto}

/* ═══════ header ═══════ */
.topbar{
  position:sticky;top:0;z-index:var(--z-rail);height:var(--head-h);
  display:flex;align-items:center;gap:var(--sp-5);padding:0 var(--sp-5);
  background:var(--s1);border-bottom:1px solid var(--line-soft);
  transition:border-color .35s var(--e-quart),box-shadow .35s var(--e-quart);
}
.topbar.lifted{border-bottom-color:var(--line);box-shadow:0 18px 40px -30px oklch(0 0 0/1)}
.brand{display:flex;align-items:baseline;gap:10px;flex:0 0 auto;user-select:none}
.brand .mark{font-family:"Newsreader",Georgia,serif;font-weight:300;font-size:1.7rem;line-height:1;letter-spacing:.01em}
.brand .mark em{font-style:italic;color:var(--acc)}
.brand .ver{font-size:.6875rem;font-weight:500;color:var(--tx4);letter-spacing:.07em}

.search{position:relative;flex:1 1 auto;max-width:820px;margin-inline:auto}
.shell{
  display:flex;align-items:center;gap:8px;min-height:36px;padding:3px 6px 3px 12px;
  background:var(--bg);border:1px solid var(--line);border-radius:var(--r-sm);
  transition:border-color .2s var(--e-quart),background .2s var(--e-quart);
}
.shell:hover{border-color:var(--s4)}
.shell:focus-within{border-color:var(--acc-mid);background:oklch(calc(var(--void) + 0.016) 0.014 268)}
.shell > .ico{flex:0 0 auto;color:var(--tx4);display:grid;place-items:center}
.chips{display:flex;gap:5px;align-items:center;flex:0 1 auto;overflow:hidden}
.chip{
  display:inline-flex;align-items:center;gap:5px;height:23px;padding:0 3px 0 9px;
  background:var(--s2);border:1px solid var(--line-soft);border-radius:var(--r-xs);
  font-size:.8125rem;white-space:nowrap;animation:chipin .24s var(--e-expo);
}
@keyframes chipin{from{opacity:0;transform:translateX(-4px) scale(.95)}}
.chip.neg{background:var(--rose-ink);border-color:oklch(0.315 0.055 16);color:oklch(0.875 0.055 16)}
.chip.op{background:var(--acc-deep);border-color:var(--acc-mid);color:var(--acc)}
.chip button{display:grid;place-items:center;width:16px;height:16px;border-radius:3px;color:inherit;opacity:.6;transition:opacity .15s,background .15s}
.chip button:hover{opacity:1;background:oklch(1 0 0/.08)}
#q{flex:1 1 110px;min-width:80px;background:none;border:none;outline:none;font-size:.9375rem;font-weight:350;height:28px}
#q::placeholder{color:var(--tx4)}
.kbd{flex:0 0 auto;font-size:.6875rem;font-weight:600;color:var(--tx4);border:1px solid var(--line);border-radius:4px;padding:1px 6px;line-height:1.5}

.panel-pop{
  position:absolute;top:calc(100% + 9px);left:0;right:0;z-index:var(--z-pop);
  background:var(--s2);border:1px solid var(--line);border-radius:var(--r-md);
  box-shadow:0 30px 70px -30px oklch(0 0 0/1);padding:5px;max-height:min(60vh,460px);overflow:auto;
  opacity:0;transform:translateY(-6px) scale(.99);pointer-events:none;
  transition:opacity .2s var(--e-quart),transform .2s var(--e-quart);
}
.panel-pop.open{opacity:1;transform:none;pointer-events:auto}
.pop-head{display:flex;justify-content:space-between;align-items:center;padding:9px 11px 6px}
.pop-head button{font-size:.6875rem;color:var(--tx4);letter-spacing:.06em;text-transform:uppercase;font-weight:600}
.pop-head button:hover{color:var(--tx2)}
.ac-row{display:flex;align-items:center;gap:12px;width:100%;padding:7px 11px;border-radius:var(--r-xs);transition:background .12s}
.ac-row[aria-selected="true"]{background:var(--s3)}
.ac-row .t{flex:1;font-size:.9375rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.ac-row .t mark{background:none;color:var(--acc);font-weight:600}
.ac-row .k{font-size:.6875rem;letter-spacing:.09em;text-transform:uppercase;color:var(--tx4)}
.ac-row .c{font-size:.8125rem;color:var(--tx4);min-width:58px;text-align:right}
.ac-row .x{width:20px;height:20px;display:grid;place-items:center;border-radius:4px;color:var(--tx4);opacity:0}
.ac-row:hover .x{opacity:1}
.ac-row .x:hover{background:var(--s4);color:var(--tx)}
.pop-sep{height:1px;background:var(--line-soft);margin:5px 8px}
.opgrid{display:flex;flex-wrap:wrap;gap:5px;padding:4px 10px 9px}
.opgrid button{
  font-size:.75rem;padding:3px 9px;border-radius:var(--r-xs);background:var(--s3);color:var(--tx2);
  font-family:ui-monospace,SFMono-Regular,Menlo,monospace;transition:background .15s,color .15s;
}
.opgrid button:hover{background:var(--s4);color:var(--tx)}

.tools{display:flex;align-items:center;gap:4px;flex:0 0 auto}
.tbtn{
  display:inline-flex;align-items:center;gap:7px;height:32px;padding:0 11px;border-radius:var(--r-xs);
  color:var(--tx2);font-size:.875rem;font-weight:450;transition:background .18s var(--e-quart),color .18s var(--e-quart);
}
.tbtn:hover{background:var(--s2);color:var(--tx)}
.tbtn[aria-pressed="true"]{background:var(--acc-deep);color:var(--acc)}
.tbtn .count{font-size:.75rem;color:var(--tx4);font-variant-numeric:tabular-nums}
.tbtn[aria-pressed="true"] .count{color:var(--acc)}
.rule{width:1px;height:20px;background:var(--line);margin:0 5px}

/* ═══════ rail ═══════ */
.rail{
  position:sticky;top:var(--head-h);z-index:calc(var(--z-rail) - 1);
  display:flex;align-items:center;gap:var(--sp-4);height:var(--rail-h);padding:0 var(--sp-5);
  background:var(--bg);border-bottom:1px solid var(--line-soft);font-size:.8125rem;
  overflow-x:auto;scrollbar-width:none;
}
.rail::-webkit-scrollbar{display:none}
.rail > *{flex:0 0 auto}
.seg{display:flex;gap:2px;background:var(--s1);border:1px solid var(--line-soft);border-radius:var(--r-sm);padding:2px}
.seg button{padding:3px 11px;border-radius:calc(var(--r-sm) - 3px);color:var(--tx3);font-size:.8125rem;font-weight:450;white-space:nowrap;transition:color .18s,background .18s}
.seg button:hover{color:var(--tx2)}
.seg button[aria-pressed="true"]{background:var(--s3);color:var(--tx);font-weight:500}
.stepper{display:flex;align-items:center;gap:6px;background:var(--s1);border:1px solid var(--line-soft);border-radius:var(--r-sm);padding:2px 4px 2px 10px}
.stepper span{color:var(--tx3);font-size:.8125rem}
.stepper input{width:52px;background:none;border:none;outline:none;font-size:.8125rem;color:var(--tx);font-variant-numeric:tabular-nums}
.rail .meta{color:var(--tx4);white-space:nowrap}
.rail .meta b{color:var(--tx2);font-weight:500}
.veil{
  display:inline-flex;align-items:center;gap:6px;height:24px;padding:0 10px;border:1px solid var(--line-soft);
  border-radius:99px;color:var(--tx4);font-size:.75rem;white-space:nowrap;transition:border-color .18s,color .18s;
}
.veil:hover{border-color:var(--line);color:var(--tx3)}

/* ═══════ grid ═══════ */
main{padding:var(--sp-5) var(--sp-5) 0;max-width:2400px;margin:0 auto}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(var(--tile-min),1fr));grid-auto-rows:var(--unit);gap:var(--gap)}
.tile{
  position:relative;height:100%;border-radius:var(--r-lg);overflow:hidden;background:var(--s1);
  cursor:zoom-in;isolation:isolate;opacity:0;animation:rise .6s var(--e-expo) forwards;
  animation-delay:calc(var(--i,0) * 22ms);
  transition:transform .4s var(--e-quart),box-shadow .4s var(--e-quart);
}
@keyframes rise{from{opacity:0;transform:translateY(12px)}to{opacity:1;transform:none}}
.tile::before{
  content:"";position:absolute;inset:0;z-index:3;pointer-events:none;border-radius:inherit;
  background:linear-gradient(oklch(1 0 0/.055),transparent 42%);opacity:.9;
}
.tile::after{
  content:"";position:absolute;inset:0;z-index:4;pointer-events:none;border-radius:inherit;
  box-shadow:inset 0 0 0 1px oklch(0.95 0.01 268/.065);transition:box-shadow .3s var(--e-quart);
}
.tile:hover{transform:translateY(-3px);box-shadow:0 26px 50px -32px oklch(0 0 0/.95)}
.tile:hover::after,.tile:focus-visible::after{box-shadow:inset 0 0 0 1px oklch(0.95 0.01 268/.18)}
.tile .media{
  position:absolute;inset:0;width:100%;height:100%;object-fit:cover;z-index:0;
  opacity:0;transform:scale(1.02);filter:saturate(.94);
  transition:opacity .55s var(--e-quart),transform .85s var(--e-expo),filter .5s var(--e-quart);
}
.tile .media.ready{opacity:1;transform:none}
.tile:hover .media{transform:scale(1.045);filter:saturate(1)}
.tile video.media{z-index:1;opacity:0}
.tile video.media.ready{opacity:1}
.tile .shimmer{position:absolute;inset:0;z-index:0;background:var(--s1);overflow:hidden}
.tile .shimmer::after{
  content:"";position:absolute;inset:0;
  background:linear-gradient(100deg,transparent 22%,oklch(0.23 0.013 268/.85) 50%,transparent 78%);
  transform:translateX(-100%);animation:sweep 1.6s var(--e-both) infinite;
}
@keyframes sweep{to{transform:translateX(100%)}}
.tile.loaded .shimmer{opacity:0;transition:opacity .4s var(--e-quart);pointer-events:none}
.tile .scrim{
  position:absolute;inset:0;z-index:2;opacity:0;transition:opacity .3s var(--e-quart);
  background:linear-gradient(to top,oklch(0.08 0.012 268/.93) 0%,oklch(0.08 0.012 268/.52) 26%,oklch(0.08 0.012 268/.05) 56%,transparent 76%);
}
.tile:hover .scrim,.tile:focus-visible .scrim{opacity:1}
.tile .info{
  position:absolute;left:0;right:0;bottom:0;z-index:5;padding:13px 14px;display:flex;align-items:flex-end;
  justify-content:space-between;gap:12px;opacity:0;transform:translateY(8px);
  transition:opacity .26s var(--e-quart),transform .34s var(--e-quart);
}
.tile:hover .info,.tile:focus-visible .info{opacity:1;transform:none}
html[data-meta="always"] .tile .info{opacity:1;transform:none}
html[data-meta="always"] .tile .scrim{opacity:.85}
html[data-meta="off"] .tile .info{display:none}
.tile .id{font-size:.8125rem;font-weight:550;letter-spacing:.02em;font-variant-numeric:tabular-nums;display:block}
.tile .sub{font-size:.6875rem;color:oklch(0.80 0.008 268);letter-spacing:.045em}
.tile .score{display:inline-flex;align-items:center;gap:4px;white-space:nowrap}
.badges{position:absolute;top:11px;left:11px;z-index:5;display:flex;gap:5px}
.badge{
  display:inline-flex;align-items:center;gap:5px;height:21px;padding:0 8px;border-radius:var(--r-xs);
  font-size:.6875rem;font-weight:550;letter-spacing:.05em;background:oklch(0.11 0.012 268/.72);
  color:oklch(0.90 0.005 268);backdrop-filter:blur(8px);opacity:0;transition:opacity .26s var(--e-quart);
}
.tile:hover .badge,.tile:focus-visible .badge,.badge.pin{opacity:1}
.dot{width:6px;height:6px;border-radius:99px;display:inline-block;flex:0 0 auto}
.dot.s{background:var(--sage)} .dot.q{background:var(--amber)} .dot.e{background:var(--rose)}
.acts{position:absolute;top:10px;right:10px;z-index:6;display:flex;gap:5px}
.act{
  width:30px;height:30px;display:grid;place-items:center;border-radius:var(--r-sm);
  background:oklch(0.11 0.012 268/.68);color:oklch(0.88 0.005 268);backdrop-filter:blur(8px);
  opacity:0;transform:scale(.92);
  transition:opacity .22s var(--e-quart),transform .22s var(--e-quart),color .18s,background .18s;
}
.tile:hover .act,.tile:focus-within .act{opacity:1;transform:none}
.act:hover{background:oklch(0.20 0.02 268/.85);color:var(--tx)}
.act.fav:hover{color:var(--rose)}
.tile.faved .act.fav{opacity:1;transform:none;color:var(--rose)}
.tile.faved .act.fav svg{fill:var(--rose)}
@keyframes thump{40%{transform:scale(1.24)}}
.act.beat{animation:thump .34s var(--e-quart)}
.tile.blocked .media{filter:blur(26px) saturate(.5);transform:scale(1.1)}
.tile.blocked:hover .media{transform:scale(1.1)}
.tile.revealed .media{filter:saturate(.94);transform:none}
.veto{
  position:absolute;inset:0;z-index:6;display:grid;place-content:center;justify-items:center;gap:10px;
  background:oklch(0.11 0.012 268/.55);text-align:center;padding:16px;
}
.tile.revealed .veto{display:none}
.veto .t{font-size:.75rem;color:var(--tx2);letter-spacing:.04em}
.veto .t b{color:var(--tx);font-weight:550}

/* ═══════ feed footer + states ═══════ */
.more{display:flex;flex-direction:column;align-items:center;gap:12px;padding:var(--sp-7) 0}
.more p{margin:0;color:var(--tx4);font-size:.8125rem}
.btn{
  display:inline-flex;align-items:center;justify-content:center;gap:8px;height:36px;padding:0 17px;
  border-radius:var(--r-sm);font-size:.875rem;font-weight:500;letter-spacing:.01em;
  background:var(--s2);border:1px solid var(--line);color:var(--tx);
  transition:background .18s var(--e-quart),border-color .18s var(--e-quart),transform .14s var(--e-quart),opacity .18s;
}
.btn:hover{background:var(--s3);border-color:var(--s4)}
.btn:active{transform:translateY(1px)}
.btn:disabled{opacity:.5;cursor:default;transform:none}
.btn.primary{background:var(--acc);border-color:var(--acc);color:var(--acc-ink);font-weight:600}
.btn.primary:hover{filter:brightness(1.06)}
.btn.quiet{background:transparent;border-color:transparent;color:var(--tx3)}
.btn.quiet:hover{background:var(--s2);color:var(--tx)}
.btn.sm{height:30px;padding:0 12px;font-size:.8125rem}
.btn.danger:hover{background:var(--rose-ink);border-color:oklch(0.315 .055 16);color:oklch(0.86 .07 16)}
.spin{width:14px;height:14px;border-radius:99px;border:2px solid oklch(1 0 0/.18);border-top-color:var(--tx2);animation:sp .7s linear infinite}
@keyframes sp{to{transform:rotate(360deg)}}

.state{display:none;max-width:62ch;margin:var(--sp-8) auto}
.state.on{display:block;animation:rise .5s var(--e-expo)}
.glyph{width:64px;height:64px;border-radius:var(--r-lg);display:grid;place-items:center;background:var(--s1);border:1px solid var(--line-soft);color:var(--tx4);margin-bottom:var(--sp-5)}
.state h2{font-family:"Newsreader",Georgia,serif;font-weight:300;font-size:2.25rem;line-height:1.15;letter-spacing:-.01em;margin-bottom:var(--sp-3)}
.state h2 em{font-style:italic;color:var(--acc)}
.state p{color:var(--tx2);margin:0 0 var(--sp-5);font-size:.9375rem}
.state .row{display:flex;gap:8px;flex-wrap:wrap}
.flag{
  display:inline-flex;align-items:center;gap:7px;margin-bottom:var(--sp-4);font-size:.75rem;font-weight:600;
  letter-spacing:.09em;text-transform:uppercase;color:oklch(0.82 .085 16);background:var(--rose-ink);
  border:1px solid oklch(0.315 .055 16);border-radius:99px;padding:4px 13px;
}
code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.8125rem;font-variant-ligatures:none;
  background:var(--s1);border:1px solid var(--line-soft);border-radius:5px;padding:2px 6px;color:var(--tx2)}

/* ═══════ status ═══════ */
.status{
  position:fixed;left:0;right:0;bottom:0;z-index:var(--z-rail);display:flex;align-items:center;gap:var(--sp-4);
  height:var(--status-h);padding:0 var(--sp-5);background:var(--s1);border-top:1px solid var(--line-soft);
  font-size:.6875rem;color:var(--tx4);letter-spacing:.04em;
}
.status b{color:var(--tx2);font-weight:550}
.live{width:6px;height:6px;border-radius:99px;background:var(--sage);flex:0 0 auto;animation:pulse 3.4s var(--e-both) infinite}
.live.busy{background:var(--amber)}
.live.bad{background:var(--rose);animation:none}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.45}}

/* ═══════ viewer ═══════ */
dialog.viewer{
  width:min(1480px,96vw);height:min(940px,94vh);padding:0;border:none;background:var(--s1);
  border-radius:var(--r-xl);color:var(--tx);overflow:hidden;box-shadow:0 70px 160px -60px oklch(0 0 0/1);
}
dialog.viewer::backdrop{background:oklch(0.07 0.01 268/.88);backdrop-filter:blur(3px)}
dialog.viewer[open]{animation:vin .38s var(--e-expo)}
dialog.viewer.closing{animation:vout .2s var(--e-both) forwards}
@keyframes vin{from{opacity:0;transform:translateY(16px) scale(.985)}}
@keyframes vout{to{opacity:0;transform:translateY(8px) scale(.99)}}
.vwrap{display:grid;grid-template-columns:1fr 348px;height:100%;transition:grid-template-columns .42s var(--e-expo)}
.vwrap.solo{grid-template-columns:1fr 0}
.vwrap.solo .side{opacity:0;pointer-events:none}
.stage{position:relative;background:var(--bg);display:flex;align-items:center;justify-content:center;overflow:hidden}
.stage::before{content:"";position:absolute;inset:0;pointer-events:none;z-index:1;
  background:radial-gradient(120% 100% at 50% 50%,transparent 42%,oklch(0.07 0.01 268/.6) 100%)}
.frame{
  position:relative;display:grid;place-items:center;width:100%;height:100%;padding:var(--sp-6);
  touch-action:none;
}
.frame.zoomed{cursor:grab}
.frame.zoomed.dragging{cursor:grabbing}
.media-el{
  max-width:100%;max-height:100%;border-radius:var(--r-md);background:var(--s1);
  box-shadow:0 40px 90px -50px oklch(0 0 0/1);
  opacity:0;transform:scale(.985);
  transition:opacity .34s var(--e-quart),transform .44s var(--e-expo);
  transform-origin:center center;will-change:transform;
}
.media-el.in{opacity:1;transform:none}
.media-el.out{opacity:0;transform:scale(.99);transition-duration:.18s}
.frame.zoomed .media-el{transition:none;max-width:none;max-height:none;border-radius:var(--r-sm)}
.stage-load{position:absolute;inset:0;display:grid;place-items:center;z-index:3;opacity:0;pointer-events:none;transition:opacity .2s}
.stage-load.on{opacity:1}
.nav{
  position:absolute;top:50%;translate:0 -50%;width:42px;height:42px;border-radius:99px;z-index:6;
  display:grid;place-items:center;background:oklch(0.16 .013 268/.82);border:1px solid var(--line);
  color:var(--tx3);backdrop-filter:blur(8px);
  transition:background .18s,color .18s,transform .22s var(--e-quart),opacity .25s var(--e-quart);
}
.nav:hover{background:var(--s3);color:var(--tx)}
.nav.prev{left:16px} .nav.next{right:16px}
.nav.prev:hover{transform:translate(-3px,-50%)} .nav.next:hover{transform:translate(3px,-50%)}
.vclose{
  position:absolute;top:16px;right:16px;width:32px;height:32px;border-radius:var(--r-sm);z-index:6;
  display:grid;place-items:center;background:oklch(0.16 .013 268/.82);border:1px solid var(--line);
  color:var(--tx3);backdrop-filter:blur(8px);transition:background .18s,color .18s,opacity .25s;
}
.vclose:hover{background:var(--s3);color:var(--tx)}
.hud{
  position:absolute;left:16px;bottom:16px;right:16px;z-index:6;display:flex;align-items:flex-end;
  gap:8px;pointer-events:none;transition:opacity .25s var(--e-quart),transform .25s var(--e-quart);
}
.hud > *{pointer-events:auto}
.pill{
  display:inline-flex;align-items:center;gap:6px;height:28px;padding:0 11px;border-radius:var(--r-sm);
  background:oklch(0.16 .013 268/.82);border:1px solid var(--line);font-size:.75rem;color:var(--tx2);
  font-variant-numeric:tabular-nums;backdrop-filter:blur(10px);white-space:nowrap;
}
button.pill{transition:background .18s,color .18s}
button.pill:hover{background:var(--s3);color:var(--tx)}
button.pill[aria-pressed="true"]{color:var(--acc);border-color:var(--acc-deep)}
.stage.idle .hud,.stage.idle .nav,.stage.idle .vclose{opacity:0;pointer-events:none}
.stage.idle .hud{transform:translateY(6px)}

/* player */
.player{
  flex:1 1 auto;display:flex;flex-direction:column;gap:7px;padding:9px 12px 8px;border-radius:var(--r-md);
  background:oklch(0.16 .013 268/.86);border:1px solid var(--line);backdrop-filter:blur(14px);
  opacity:0;transform:translateY(8px);pointer-events:none;
  transition:opacity .26s var(--e-quart),transform .26s var(--e-quart);
}
.player.on{opacity:1;transform:none;pointer-events:auto}
.seek{position:relative;height:16px;display:flex;align-items:center;cursor:pointer;touch-action:none}
.seek .track{position:absolute;left:0;right:0;height:4px;border-radius:99px;background:oklch(1 0 0/.13);overflow:hidden}
.seek .buf{position:absolute;left:0;top:0;bottom:0;width:0;background:oklch(1 0 0/.16)}
.seek .prog{position:absolute;left:0;top:0;bottom:0;width:0;background:var(--acc)}
.seek .knob{
  position:absolute;left:0;width:11px;height:11px;border-radius:99px;background:var(--acc);
  translate:-50% 0;opacity:0;transform:scale(.6);transition:opacity .18s,transform .18s var(--e-quart);
}
.seek:hover .knob,.seek.scrub .knob{opacity:1;transform:none}
.seek .hover-t{
  position:absolute;bottom:20px;translate:-50% 0;padding:2px 7px;border-radius:5px;font-size:.6875rem;
  background:var(--s3);border:1px solid var(--line);color:var(--tx);opacity:0;transition:opacity .15s;pointer-events:none;
}
.seek:hover .hover-t{opacity:1}
.prow{display:flex;align-items:center;gap:4px}
.pbtn{width:30px;height:30px;display:grid;place-items:center;border-radius:var(--r-xs);color:var(--tx2);transition:background .16s,color .16s}
.pbtn:hover{background:var(--s3);color:var(--tx)}
.pbtn[aria-pressed="true"]{color:var(--acc)}
.ptime{font-size:.75rem;color:var(--tx3);font-variant-numeric:tabular-nums;padding:0 6px;white-space:nowrap}
.vol{display:flex;align-items:center;gap:6px;width:34px;overflow:hidden;transition:width .28s var(--e-quart)}
.prow:hover .vol,.vol:focus-within{width:112px}
.vol input{width:70px}
input[type=range]{-webkit-appearance:none;appearance:none;height:3px;background:var(--s4);border-radius:99px;outline:none}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:12px;height:12px;border-radius:99px;background:var(--acc);cursor:pointer}
input[type=range]::-moz-range-thumb{width:12px;height:12px;border:none;border-radius:99px;background:var(--acc);cursor:pointer}
.speed{font-size:.75rem;font-weight:600;color:var(--tx2);padding:0 8px;height:30px;border-radius:var(--r-xs);display:grid;place-items:center;transition:background .16s,color .16s}
.speed:hover{background:var(--s3);color:var(--tx)}

/* side panel */
.side{border-left:1px solid var(--line-soft);overflow-y:auto;overflow-x:hidden;padding:var(--sp-6) var(--sp-5) var(--sp-7);transition:opacity .3s var(--e-quart)}
.side h3{font-family:"Newsreader",Georgia,serif;font-weight:300;font-size:2rem;line-height:1.05;font-variant-numeric:tabular-nums}
.side .sub{color:var(--tx4);font-size:.8125rem;margin:6px 0 var(--sp-5)}
.qacts{display:grid;grid-template-columns:1fr 1fr;gap:7px;margin-bottom:var(--sp-6)}
.spec{display:grid;grid-template-columns:auto 1fr;gap:9px 20px;font-size:.8125rem;margin:0 0 var(--sp-6)}
.spec dt{color:var(--tx4)}
.spec dd{margin:0;color:var(--tx2);text-align:right;font-variant-numeric:tabular-nums;overflow:hidden;text-overflow:ellipsis}
.spec dd a{color:var(--acc);text-decoration:none;border-bottom:1px solid var(--acc-deep)}
.spec dd a:hover{border-bottom-color:var(--acc)}
.tgroup{margin-bottom:var(--sp-5)}
.tgroup .eyebrow{display:block;margin-bottom:10px}
.tags{display:flex;flex-wrap:wrap;gap:5px}
.tag{
  display:inline-flex;align-items:center;gap:7px;padding:3px 10px;border-radius:var(--r-xs);
  background:var(--s2);border:1px solid transparent;font-size:.8125rem;color:var(--tx2);max-width:100%;
  transition:border-color .16s,color .16s,background .16s;
}
.tag:hover{border-color:var(--s4);background:var(--s3);color:var(--tx)}
.tag .l{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.tag .n{font-size:.6875rem;color:var(--tx4);font-variant-numeric:tabular-nums;flex:0 0 auto}
.tag.hot{color:var(--acc)}
.simstrip{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin-top:10px}
.simstrip .s{aspect-ratio:1;border-radius:var(--r-sm);overflow:hidden;position:relative;cursor:pointer;background:var(--s2);transition:transform .28s var(--e-quart)}
.simstrip .s img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;opacity:0;transition:opacity .4s}
.simstrip .s img.ready{opacity:1}
.simstrip .s::after{content:"";position:absolute;inset:0;border-radius:inherit;box-shadow:inset 0 0 0 1px oklch(.95 .01 268/.08);transition:box-shadow .2s}
.simstrip .s:hover{transform:translateY(-3px)}
.simstrip .s:hover::after{box-shadow:inset 0 0 0 1px oklch(.95 .01 268/.24)}

/* fullscreen */
.stage:fullscreen{background:oklch(0.04 0.006 268);padding:0}
.stage:fullscreen .frame{padding:0}
.stage:fullscreen .media-el{border-radius:0;box-shadow:none;max-width:100vw;max-height:100vh}
.stage:fullscreen::before{opacity:0}

/* ═══════ drawer ═══════ */
.veil-full{position:fixed;inset:0;background:oklch(0.07 .01 268/.62);z-index:var(--z-drawer);opacity:0;pointer-events:none;transition:opacity .3s var(--e-quart)}
.veil-full.on{opacity:1;pointer-events:auto}
.drawer{
  position:fixed;top:0;right:0;bottom:0;width:min(460px,96vw);z-index:calc(var(--z-drawer) + 1);
  background:var(--s1);border-left:1px solid var(--line);display:flex;flex-direction:column;
  transform:translateX(102%);transition:transform .46s var(--e-expo);box-shadow:-50px 0 110px -60px oklch(0 0 0/1);
}
.drawer.on{transform:none}
.drawer header{display:flex;align-items:center;justify-content:space-between;padding:var(--sp-4) var(--sp-5) var(--sp-3);flex:0 0 auto}
.drawer header h2{font-family:"Newsreader",Georgia,serif;font-weight:300;font-size:1.55rem}
.tabs{display:flex;gap:2px;padding:0 var(--sp-4) var(--sp-3);border-bottom:1px solid var(--line-soft);flex:0 0 auto;overflow-x:auto;scrollbar-width:none}
.tabs::-webkit-scrollbar{display:none}
.tabs button{padding:5px 11px;border-radius:var(--r-xs);font-size:.8125rem;color:var(--tx3);white-space:nowrap;transition:background .16s,color .16s}
.tabs button:hover{color:var(--tx2);background:var(--s2)}
.tabs button[aria-selected="true"]{background:var(--s3);color:var(--tx);font-weight:500}
.drawer .body{flex:1 1 auto;overflow-y:auto;padding:var(--sp-5)}
.drawer footer{display:flex;gap:8px;align-items:center;padding:var(--sp-4) var(--sp-5);border-top:1px solid var(--line-soft);flex:0 0 auto}
.tabpane{display:none}
.tabpane.on{display:block;animation:fadeUp .3s var(--e-quart)}
@keyframes fadeUp{from{opacity:0;transform:translateY(6px)}}
.group{margin-bottom:var(--sp-6)}
.group > .eyebrow{display:block;margin-bottom:var(--sp-3)}
.field{display:flex;align-items:center;justify-content:space-between;gap:18px;padding:11px 0}
.field + .field{border-top:1px solid var(--line-soft)}
.field .t{font-size:.9375rem}
.field .d{font-size:.75rem;color:var(--tx4);margin-top:2px;line-height:1.5}
.field.stack{display:block}
.switch{position:relative;width:42px;height:24px;border-radius:99px;flex:0 0 auto;background:var(--s3);border:1px solid var(--line);transition:background .24s var(--e-quart),border-color .24s var(--e-quart)}
.switch::after{content:"";position:absolute;top:2px;left:2px;width:18px;height:18px;border-radius:99px;background:var(--tx4);transition:transform .28s var(--e-quart),background .24s var(--e-quart)}
.switch[aria-checked="true"]{background:var(--acc-deep);border-color:var(--acc-mid)}
.switch[aria-checked="true"]::after{transform:translateX(18px);background:var(--acc)}
.inp{width:100%;height:36px;padding:0 12px;background:var(--bg);border:1px solid var(--line);border-radius:var(--r-sm);font-size:.875rem;outline:none;transition:border-color .18s}
.inp:focus{border-color:var(--acc-mid)}
.rangeRow{display:flex;align-items:center;gap:12px;width:186px}
.rangeRow input[type=range]{flex:1}
.rangeRow .v{font-size:.8125rem;color:var(--tx2);width:34px;text-align:right;font-variant-numeric:tabular-nums}
.swatches{display:flex;gap:7px;flex-wrap:wrap}
.sw{width:30px;height:30px;border-radius:99px;border:2px solid transparent;display:grid;place-items:center;transition:border-color .18s,transform .18s var(--e-quart)}
.sw i{width:18px;height:18px;border-radius:99px;display:block}
.sw:hover{transform:scale(1.08)}
.sw[aria-pressed="true"]{border-color:var(--tx2)}
.chiplist{display:flex;flex-wrap:wrap;gap:5px;margin-top:10px}
.rowline{display:flex;gap:7px;align-items:center}
.keys{display:grid;grid-template-columns:auto 1fr;gap:8px 16px;font-size:.8125rem;align-items:center}
.keys kbd{
  font-family:ui-monospace,Menlo,monospace;font-size:.75rem;background:var(--s2);border:1px solid var(--line);
  border-bottom-width:2px;border-radius:5px;padding:2px 7px;color:var(--tx2);justify-self:start;white-space:nowrap;
}
.keys span{color:var(--tx3)}
.savedrow{display:flex;align-items:center;gap:8px;padding:8px 0}
.savedrow + .savedrow{border-top:1px solid var(--line-soft)}
.savedrow .nm{flex:1;font-size:.875rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.savedrow .qy{font-family:ui-monospace,Menlo,monospace;font-size:.6875rem;color:var(--tx4);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}

/* toast */
.toast{
  position:fixed;left:50%;bottom:48px;translate:-50% 0;z-index:var(--z-toast);display:flex;align-items:center;gap:9px;
  padding:9px 16px;border-radius:var(--r-sm);background:var(--s3);border:1px solid var(--line);font-size:.875rem;
  box-shadow:0 26px 54px -28px oklch(0 0 0/1);opacity:0;transform:translateY(10px);pointer-events:none;
  transition:opacity .24s var(--e-quart),transform .24s var(--e-quart);
}
.toast.on{opacity:1;transform:none}
.toast.bad{border-color:oklch(0.315 .055 16)}

/* ═══════ responsive ═══════ */
@media (max-width:1180px){ .vwrap{grid-template-columns:1fr 310px} }
@media (max-width:980px){
  html{--tile-min:190px;--gap:11px}
  .topbar{gap:var(--sp-3)}
  .search{max-width:none;margin-inline:0}
  .kbd{display:none}
  .tbtn .lbl{display:none}
  .tbtn{padding:0 9px}
  .rail .meta{display:none}
  .vwrap,.vwrap.solo{grid-template-columns:1fr;grid-template-rows:minmax(0,1fr) auto}
  .vwrap.solo .side{display:none}
  .side{border-left:none;border-top:1px solid var(--line-soft);max-height:44vh;padding:var(--sp-5) var(--sp-4) var(--sp-6);opacity:1}
  dialog.viewer{width:100vw;height:100dvh;max-width:none;max-height:none;border-radius:0}
  .frame{padding:var(--sp-4)}
}
@media (max-width:640px){
  html{--head-h:54px;--tile-min:150px;--gap:8px}
  .topbar{padding:0 var(--sp-3)}
  .brand .ver{display:none}
  .brand .mark{font-size:1.5rem}
  main{padding:var(--sp-3) var(--sp-3) 0}
  .rail{padding:0 var(--sp-3);gap:var(--sp-3)}
  .act,.badge{opacity:1}
  .state h2{font-size:1.75rem}
  .hide-sm{display:none}
  .vol{display:none}
}
@media (prefers-reduced-motion:reduce){
  *,*::before,*::after{animation-duration:1ms !important;animation-iteration-count:1 !important;transition-duration:1ms !important}
}
"""

# ═══════════════════════════════════════════════════════════════════════
# UI: client script
# ═══════════════════════════════════════════════════════════════════════
PAGE_JS = r"""
(() => {
"use strict";

/* ═══════════ helpers ═══════════ */
const $  = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const fmt = n => (n || 0).toLocaleString("en-US");
const escRx = s => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
const escHtml = s => String(s).replace(/[&<>"']/g, c => ({ "&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;" }[c]));
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const clock = s => {
  if (!isFinite(s) || s < 0) s = 0;
  const h = Math.floor(s / 3600), m = Math.floor(s / 60) % 60, x = Math.floor(s % 60);
  return (h ? h + ":" + String(m).padStart(2, "0") : String(m)) + ":" + String(x).padStart(2, "0");
};
const media = url => url ? "/media?u=" + encodeURIComponent(url) : "";
const ICON = {
  play:'<svg viewBox="0 0 24 24" fill="currentColor" width="16" height="16"><path d="M8 5v14l11-7z"/></svg>',
  pause:'<svg viewBox="0 0 24 24" fill="currentColor" width="16" height="16"><path d="M7 5h3.5v14H7zM13.5 5H17v14h-3.5z"/></svg>',
  vol:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="16" height="16"><path d="M4 9.5h3.5L12 5.5v13L7.5 14.5H4z"/><path d="M16 9.2a4 4 0 0 1 0 5.6"/><path d="M18.4 6.8a7.4 7.4 0 0 1 0 10.4"/></svg>',
  mute:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="16" height="16"><path d="M4 9.5h3.5L12 5.5v13L7.5 14.5H4z"/><path d="m16 10 4 4M20 10l-4 4"/></svg>',
  loop:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="16" height="16"><path d="M17 3.5 20 6.5l-3 3"/><path d="M4 12V9.5a3 3 0 0 1 3-3h13"/><path d="M7 20.5 4 17.5l3-3"/><path d="M20 12v2.5a3 3 0 0 1-3 3H4"/></svg>',
  pip:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="16" height="16"><rect x="3" y="5" width="18" height="14" rx="2.5"/><rect x="12" y="11" width="7" height="6" rx="1.5" fill="currentColor" stroke="none"/></svg>',
  fs:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="16" height="16"><path d="M4 9V5.5A1.5 1.5 0 0 1 5.5 4H9"/><path d="M15 4h3.5A1.5 1.5 0 0 1 20 5.5V9"/><path d="M20 15v3.5a1.5 1.5 0 0 1-1.5 1.5H15"/><path d="M9 20H5.5A1.5 1.5 0 0 1 4 18.5V15"/></svg>',
  fsx:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="16" height="16"><path d="M9 4v3.5A1.5 1.5 0 0 1 7.5 9H4"/><path d="M20 9h-3.5A1.5 1.5 0 0 1 15 7.5V4"/><path d="M15 20v-3.5a1.5 1.5 0 0 1 1.5-1.5H20"/><path d="M4 15h3.5A1.5 1.5 0 0 1 9 16.5V20"/></svg>',
  heart:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" width="15" height="15"><path d="M12 20.2S4.8 15.5 4.8 10.4A3.9 3.9 0 0 1 12 8.2a3.9 3.9 0 0 1 7.2 2.2c0 5.1-7.2 9.8-7.2 9.8Z"/></svg>',
  similar:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" width="15" height="15"><circle cx="10" cy="10" r="6"/><path d="m19 19-4.5-4.5"/><path d="M8 10h4M10 8v4"/></svg>',
  zin:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="15" height="15"><circle cx="11" cy="11" r="6.5"/><path d="m20 20-4.2-4.2M8.5 11h5M11 8.5v5"/></svg>',
  zout:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="15" height="15"><circle cx="11" cy="11" r="6.5"/><path d="m20 20-4.2-4.2M8.5 11h5"/></svg>',
  x:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linecap="round" width="15" height="15"><path d="m6 6 12 12M18 6 6 18"/></svg>',
};

/* ═══════════ api ═══════════ */
const ERRORS = {
  auth:  ["Credentials rejected", "The site refused the API key or user id. Check both under Settings, Account."],
  rate:  ["Upstream rate limit", "Nocturne backed off after three retries. An API key raises the ceiling considerably."],
  network:["Cannot reach the site", "No response from upstream. Check the connection, then retry."],
  upstream:["Upstream error", "The site returned an unexpected status. It is usually transient."],
  parse: ["Unreadable response", "The site answered with something that is not a valid post list."],
  notfound:["Post not found", "That id is gone, deleted or never existed."],
};
async function api(path, opts) {
  const res = await fetch(path, opts);
  let data = null;
  try { data = await res.json(); } catch { /* non-json body */ }
  if (!res.ok || (data && data.error)) {
    const code = (data && data.error && data.error.code) || "upstream";
    const err = new Error(code);
    err.code = code;
    throw err;
  }
  return data;
}

/* ═══════════ state ═══════════ */
const S = {
  cfg: null,
  chips: [],          // [{raw, kind:'tag'|'neg'|'op'}]
  posts: [],
  byId: new Map(),
  favIds: new Set(),
  pid: 0, count: null, end: false, loading: false,
  mode: "feed",       // feed | favorites | similar
  simFrom: null,
  view: "grid",       // grid | empty | error | loading
  lastError: null,
  cur: -1,
};

/* ═══════════ theme ═══════════ */
const ACCENTS = {
  moon:  [0.862, 0.048, 252], frost: [0.870, 0.052, 196], sage: [0.845, 0.050, 158],
  amber: [0.860, 0.058,  84], rose:  [0.845, 0.060,  16], violet:[0.855, 0.055, 300],
};
function applyTheme(cfg) {
  const root = document.documentElement;
  const [l, c, h] = ACCENTS[cfg.accent] || ACCENTS.moon;
  root.style.setProperty("--acc-l", l);
  root.style.setProperty("--acc-c", c);
  root.style.setProperty("--acc-h", h);
  root.dataset.contrast = cfg.contrast;
  root.dataset.corners  = cfg.corners;
  root.dataset.density  = cfg.density;
  root.dataset.motion   = cfg.motion;
  root.dataset.meta     = cfg.meta_mode;
  root.dataset.grain    = cfg.grain ? "on" : "off";
  requestAnimationFrame(layout);
}

/* ═══════════ query engine ═══════════ */
const OPERATORS = ["rating:", "score:>", "score:<", "sort:", "id:", "user:", "parent:", "width:>", "height:>", "md5:"];
const RATING_TAG = { all: "", safe: "rating:safe", questionable: "rating:questionable", explicit: "rating:explicit" };
const SORT_TAG   = { newest: "", score: "sort:score:desc", random: "sort:random" };

const isOp = t => /^-?[a-z_]+:/i.test(t);
function chipOf(raw) {
  const neg = raw.startsWith("-");
  return { raw, kind: isOp(raw) ? "op" : (neg ? "neg" : "tag") };
}
function queryString() {
  const parts = S.chips.map(c => c.raw);
  const rating = RATING_TAG[S.cfg.rating];
  const sort = SORT_TAG[S.cfg.sort];
  if (rating && !parts.some(p => p.startsWith("rating:"))) parts.push(rating);
  if (sort   && !parts.some(p => p.startsWith("sort:")))   parts.push(sort);
  if (S.cfg.min_score > 0 && !parts.some(p => p.startsWith("score:"))) parts.push("score:>" + (S.cfg.min_score - 1));
  return parts.join(" ");
}
const chipsText = () => S.chips.map(c => c.raw).join(" ");
function setChips(text, { silent } = {}) {
  S.chips = String(text || "").trim().split(/\s+/).filter(Boolean).slice(0, 40).map(chipOf);
  renderChips();
  if (!silent) reload();
}
function addChip(raw) {
  const t = String(raw || "").trim().toLowerCase().replace(/\s+/g, "_");
  if (!t || t === "-" || S.chips.some(c => c.raw === t)) return;
  S.chips.push(chipOf(t));
  renderChips();
  $("#q").value = "";
  closePop();
  reload();
}
function renderChips() {
  $("#chips").innerHTML = S.chips.map((c, i) => {
    const label = c.kind === "neg" ? "\u2212 " + c.raw.slice(1).replace(/_/g, " ")
                : c.kind === "op"  ? c.raw
                : c.raw.replace(/_/g, " ");
    return `<span class="chip ${c.kind === "neg" ? "neg" : c.kind === "op" ? "op" : ""}">${escHtml(label)}
      <button data-chip="${i}" aria-label="Remove ${escHtml(c.raw)}">${ICON.x}</button></span>`;
  }).join("");
  $("#q").placeholder = S.chips.length ? "Add tag" : "Search tags. \u2212 to exclude, rating: score: sort: for filters";
  syncHash();
}
function syncHash() {
  const q = chipsText();
  const want = q ? "#q=" + encodeURIComponent(q) : "";
  if (location.hash !== want) history.replaceState(null, "", location.pathname + want);
}
function readHash() {
  const m = /^#q=(.*)$/.exec(location.hash || "");
  return m ? decodeURIComponent(m[1]) : "";
}

/* ═══════════ suggestion popover ═══════════ */
let acIdx = -1, acRows = [], acToken = 0;
const pop = $("#pop");
function closePop() { pop.classList.remove("open"); $("#q").setAttribute("aria-expanded", "false"); acIdx = -1; acRows = []; }
function openPop() { pop.classList.add("open"); $("#q").setAttribute("aria-expanded", "true"); }

function renderIdle() {
  const cfg = S.cfg;
  const saved = cfg.saved_searches, recent = cfg.recent_searches;
  let html = `<div class="pop-head"><span class="eyebrow">Filters</span></div>
    <div class="opgrid">${OPERATORS.map(o => `<button data-op="${o}">${o}</button>`).join("")}</div>`;
  if (saved.length) {
    html += `<div class="pop-sep"></div><div class="pop-head"><span class="eyebrow">Saved</span></div>` +
      saved.map((s, i) => `<button class="ac-row" data-run="${escHtml(s.query)}">
        <span class="t">${escHtml(s.name)}</span><span class="c">${escHtml(s.query).slice(0, 26)}</span>
        <span class="x" data-unsave="${i}">${ICON.x}</span></button>`).join("");
  }
  if (recent.length) {
    html += `<div class="pop-sep"></div><div class="pop-head"><span class="eyebrow">Recent</span>
      <button data-clear-recent>clear</button></div>` +
      recent.map(r => `<button class="ac-row" data-run="${escHtml(r)}"><span class="t">${escHtml(r)}</span></button>`).join("");
  }
  acRows = [];
  pop.innerHTML = html;
  openPop();
}
async function suggest(term) {
  const raw = term.trim();
  if (!raw) return renderIdle();
  const neg = raw.startsWith("-");
  const bare = (neg ? raw.slice(1) : raw).toLowerCase();
  if (bare.includes(":")) {
    acRows = [];
    pop.innerHTML = `<div class="pop-head"><span class="eyebrow">Filter</span><span class="eyebrow">enter to add</span></div>
      <button class="ac-row" aria-selected="true" data-add="${escHtml(raw)}"><span class="t">${escHtml(raw)}</span><span class="k">operator</span></button>`;
    acRows = [{ value: raw }]; acIdx = 0;
    return openPop();
  }
  if (bare.length < 2) return renderIdle();
  const token = ++acToken;
  let rows = [];
  try { rows = await api("/api/ac?q=" + encodeURIComponent(bare)); } catch { rows = []; }
  if (token !== acToken) return;
  if (!rows.length) {
    acRows = [{ value: bare }]; acIdx = 0;
    pop.innerHTML = `<div class="pop-head"><span class="eyebrow">No suggestions</span></div>
      <button class="ac-row" aria-selected="true" data-add="${escHtml((neg ? "-" : "") + bare)}">
        <span class="t">Search <b>${escHtml(bare)}</b> anyway</span></button>`;
    return openPop();
  }
  acRows = rows.map(r => ({ value: (neg ? "-" : "") + r.value }));
  acIdx = 0;
  const rx = new RegExp("(" + escRx(bare) + ")", "i");
  pop.innerHTML = `<div class="pop-head"><span class="eyebrow">Tags</span><span class="eyebrow">\u2191\u2193 \u00b7 enter</span></div>` +
    rows.map((r, i) => `<button class="ac-row" role="option" aria-selected="${i === 0}" data-i="${i}">
      <span class="t">${(neg ? "\u2212 " : "") + escHtml(r.value.replace(/_/g, " ")).replace(rx, "<mark>$1</mark>")}</span>
      <span class="k">${escHtml(r.type || "tag")}</span>
      <span class="c num">${r.count ? fmt(r.count) : ""}</span></button>`).join("");
  openPop();
}
function moveAc(d) {
  if (!acRows.length) return;
  acIdx = (acIdx + d + acRows.length) % acRows.length;
  const rows = $$(".ac-row[data-i]", pop);
  rows.forEach((r, i) => r.setAttribute("aria-selected", i === acIdx));
  if (rows[acIdx]) rows[acIdx].scrollIntoView({ block: "nearest" });
}

/* ═══════════ grid ═══════════ */
const grid = $("#grid");
const sentinel = $("#more");
let ioLazy = null;

function candidates(p) {
  const hq = S.cfg.hq_previews;
  const list = [];
  if (p.video) {
    if (p.preview) list.push(p.preview);
    if (hq && p.sample) list.push(p.sample);
  } else {
    if (hq && p.sample) list.push(p.sample);
    if (p.preview) list.push(p.preview);
    list.push(p.file);
  }
  return [...new Set(list.filter(Boolean))];
}
function tileHTML(p, i) {
  const src = candidates(p);
  const blocked = p.blocked && S.cfg.blacklist_mode !== "mark";
  return `<article class="tile${S.favIds.has(p.id) ? " faved" : ""}${p.blocked ? " blocked" : ""}"
      data-id="${p.id}" data-ratio="${p.ratio || 1}" style="--i:${Math.min(i, 20)}" tabindex="0" role="button"
      aria-label="Post ${p.id}, score ${p.score}">
    <div class="shimmer"></div>
    <img class="media" alt="" decoding="async" data-src="${escHtml(src[0] || "")}"
         data-alt='${escHtml(JSON.stringify(src.slice(1)))}'>
    <div class="scrim"></div>
    <div class="badges">
      ${p.video ? `<span class="badge pin">${ICON.play}${escHtml(p.ext.toUpperCase())}</span>` : ""}
      ${p.blocked && S.cfg.blacklist_mode === "mark" ? `<span class="badge pin">filtered</span>` : ""}
      <span class="badge"><span class="dot ${p.rating}"></span>${escHtml(p.ext.toUpperCase())}</span>
    </div>
    <div class="acts">
      <button class="act sim" data-sim="${p.id}" title="Find similar" aria-label="Find similar to ${p.id}">${ICON.similar}</button>
      <button class="act fav" data-fav="${p.id}" title="Favorite" aria-pressed="${S.favIds.has(p.id)}" aria-label="Favorite ${p.id}">${ICON.heart}</button>
    </div>
    <div class="info">
      <div><span class="id num">#${p.id}</span><span class="sub">${p.w}\u00d7${p.h}</span></div>
      <span class="sub score"><svg viewBox="0 0 24 24" fill="currentColor" width="11" height="11"><path d="m12 3.2 2.6 5.7 6.3.7-4.7 4.2 1.3 6.1-5.5-3.1-5.5 3.1L8 13.8 3.2 9.6l6.3-.7z"/></svg>${fmt(p.score)}</span>
    </div>
    ${blocked ? `<div class="veto"><span class="t">Hidden by <b>blacklist</b></span>
      <button class="btn sm" data-reveal="${p.id}">Reveal</button></div>` : ""}
  </article>`;
}
function layout() {
  const kids = grid.children;
  if (!kids.length) return;
  const cs = getComputedStyle(grid);
  const gap = parseFloat(cs.rowGap) || 0;
  const unit = parseFloat(cs.gridAutoRows) || 8;
  const cols = cs.gridTemplateColumns.split(" ").filter(Boolean).length || 1;
  const colW = (grid.clientWidth - gap * (cols - 1)) / cols;
  if (colW <= 0) return;
  for (const el of kids) {
    const ratio = parseFloat(el.dataset.ratio) || 1;
    el.style.gridRowEnd = "span " + Math.max(2, Math.round((colW / ratio + gap) / (unit + gap)));
  }
}
let layoutQueued = false;
function queueLayout() {
  if (layoutQueued) return;
  layoutQueued = true;
  requestAnimationFrame(() => { layoutQueued = false; layout(); });
}
function mountLazy() {
  if (ioLazy) ioLazy.disconnect();
  ioLazy = new IntersectionObserver(entries => {
    for (const e of entries) {
      if (!e.isIntersecting) continue;
      const img = $(".media", e.target);
      if (img && img.dataset.src && !img.src) img.src = media(img.dataset.src);
      ioLazy.unobserve(e.target);
    }
  }, { rootMargin: "700px 0px" });
  for (const t of grid.children) ioLazy.observe(t);
}
function renderPosts(list, append) {
  const start = append ? grid.children.length : 0;
  const html = list.map((p, i) => tileHTML(p, append ? Math.min(i, 12) : i)).join("");
  if (append) grid.insertAdjacentHTML("beforeend", html);
  else grid.innerHTML = html;
  queueLayout();
  mountLazy();
  void start;
}
grid.addEventListener("load", e => {
  const img = e.target;
  if (!img.classList || !img.classList.contains("media")) return;
  img.classList.add("ready");
  const tile = img.closest(".tile");
  if (tile) tile.classList.add("loaded");
}, true);
grid.addEventListener("error", e => {
  const img = e.target;
  if (!img.classList || !img.classList.contains("media")) return;
  let alt = [];
  try { alt = JSON.parse(img.dataset.alt || "[]"); } catch { alt = []; }
  if (alt.length) {
    const next = alt.shift();
    img.dataset.alt = JSON.stringify(alt);
    img.src = media(next);
  } else {
    const tile = img.closest(".tile");
    if (tile) tile.classList.add("loaded");
  }
}, true);

/* hover video previews */
let hoverTimer = null, hoverEl = null;
function stopHover() {
  clearTimeout(hoverTimer);
  if (hoverEl) {
    hoverEl.pause();
    hoverEl.removeAttribute("src");
    hoverEl.load();
    hoverEl.remove();
    hoverEl = null;
  }
}
grid.addEventListener("pointerover", e => {
  if (!S.cfg.hover_preview) return;
  const tile = e.target.closest(".tile");
  if (!tile || tile.classList.contains("blocked")) return;
  const post = S.byId.get(+tile.dataset.id);
  if (!post || !post.video) return;
  if (hoverEl && hoverEl.closest(".tile") === tile) return;
  stopHover();
  hoverTimer = setTimeout(() => {
    const v = document.createElement("video");
    v.className = "media";
    v.muted = true; v.loop = true; v.playsInline = true; v.preload = "auto";
    v.src = media(post.sample && !S.cfg.full_quality ? post.sample : post.file);
    v.addEventListener("canplay", () => v.classList.add("ready"), { once: true });
    tile.appendChild(v);
    hoverEl = v;
    v.play().catch(() => {});
  }, 220);
});
grid.addEventListener("pointerout", e => {
  const tile = e.target.closest(".tile");
  if (!tile || (e.relatedTarget && tile.contains(e.relatedTarget))) return;
  stopHover();
});

/* grid interaction */
grid.addEventListener("click", e => {
  const rev = e.target.closest("[data-reveal]");
  if (rev) { rev.closest(".tile").classList.add("revealed"); return; }
  const fav = e.target.closest("[data-fav]");
  if (fav) { e.stopPropagation(); toggleFav(+fav.dataset.fav, fav); return; }
  const sim = e.target.closest("[data-sim]");
  if (sim) { e.stopPropagation(); loadSimilar(+sim.dataset.sim); return; }
  const tile = e.target.closest(".tile");
  if (tile) openViewer(+tile.dataset.id);
});
grid.addEventListener("keydown", e => {
  const tile = e.target.closest(".tile");
  if (!tile) return;
  if (e.key === "Enter" || e.key === " ") { e.preventDefault(); openViewer(+tile.dataset.id); }
  else if (e.key.toLowerCase() === "s") { e.preventDefault(); toggleFav(+tile.dataset.id, $(".act.fav", tile)); }
});

/* ═══════════ views ═══════════ */
function setView(v) {
  S.view = v;
  grid.style.display = (v === "grid" || v === "loading") ? "" : "none";
  sentinel.style.display = v === "grid" ? "" : "none";
  $("#emptyState").classList.toggle("on", v === "empty");
  $("#errState").classList.toggle("on", v === "error");
  if (v === "loading") {
    grid.innerHTML = Array.from({ length: 18 }, (_, i) => {
      const r = [0.66, 0.75, 1, 1.33, 1.5, 0.56][i % 6];
      return `<article class="tile loaded" data-ratio="${r}" style="--i:${i}"><div class="shimmer"></div></article>`;
    }).join("");
    queueLayout();
  }
}
function paintCounters() {
  $("#shown").textContent = fmt(S.posts.length);
  $("#total").textContent = S.count == null ? "\u2014" : fmt(S.count);
  $("#favCount").textContent = S.favIds.size;
  const walked = S.hidden || 0;
  $("#blNote").style.display = walked ? "" : "none";
  $("#blCount").textContent = walked;
}
function showError(code) {
  S.lastError = code;
  const [title, body] = ERRORS[code] || ERRORS.upstream;
  $("#errTitle").textContent = title;
  $("#errBody").textContent = body;
  $("#errFlag").textContent = "upstream \u00b7 " + code;
  setView("error");
}

/* ═══════════ loading ═══════════ */
async function reload() {
  S.pid = 0; S.end = false; S.posts = []; S.byId.clear(); S.mode = S.mode === "favorites" ? "favorites" : "feed";
  if (S.mode === "favorites") return loadFavorites();
  setView("loading");
  await loadPage(true);
  const q = chipsText();
  if (q) rememberSearch(q);
}
async function loadPage(fresh) {
  if (S.loading || (!fresh && S.end)) return;
  S.loading = true;
  busy(true);
  const btn = $("#loadMore");
  if (!fresh) { btn.disabled = true; btn.innerHTML = `<span class="spin"></span><span>Loading</span>`; }
  try {
    const params = new URLSearchParams({ tags: queryString(), pid: fresh ? 0 : S.pid, limit: S.cfg.per_page });
    const data = await api("/api/posts?" + params);
    S.pid = data.next_pid;
    S.count = data.count;
    S.hidden = (fresh ? 0 : (S.hidden || 0)) + (data.hidden || 0);
    S.end = data.end || !data.posts.length;
    const fresh_list = data.posts.filter(p => !S.byId.has(p.id));
    for (const p of fresh_list) S.byId.set(p.id, p);
    S.posts = S.posts.concat(fresh_list);
    if (!S.posts.length) { setView("empty"); }
    else {
      if (fresh) { setView("grid"); renderPosts(S.posts, false); }
      else renderPosts(fresh_list, true);
    }
    $("#moreNote").textContent = S.end
      ? "End of the feed."
      : (S.cfg.infinite_scroll ? "Infinite scroll is on. Blacklisted pages are walked server side."
                               : "Infinite scroll is off. Load pages manually.");
    $("#loadMore").style.display = S.end ? "none" : "";
  } catch (err) {
    if (fresh) showError(err.code);
    else toast("Could not load more: " + err.code, true);
  } finally {
    btn.disabled = false;
    btn.innerHTML = `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" width="15" height="15"><path d="M12 5v14"/><path d="m6 13 6 6 6-6"/></svg><span>Load more</span>`;
    S.loading = false;
    busy(false);
    paintCounters();
  }
}
async function loadFavorites() {
  setView("loading");
  busy(true);
  try {
    const data = await api("/api/favorites");
    const q = S.chips.filter(c => c.kind === "tag").map(c => c.raw);
    let list = data.posts;
    if (q.length) list = list.filter(p => q.every(t => (p.tags || []).some(x => x.includes(t))));
    S.posts = list;
    S.byId = new Map(list.map(p => [p.id, p]));
    S.count = data.posts.length;
    S.end = true;
    S.hidden = 0;
    if (!list.length) setView("empty");
    else { setView("grid"); renderPosts(list, false); }
    $("#loadMore").style.display = "none";
    $("#moreNote").textContent = `${list.length} saved ${list.length === 1 ? "post" : "posts"}.`;
  } catch (err) {
    showError(err.code);
  } finally { busy(false); paintCounters(); }
}
async function loadSimilar(id) {
  if (viewer.open) closeViewer();
  S.mode = "similar"; S.simFrom = id;
  $("#favBtn").setAttribute("aria-pressed", "false");
  setView("loading");
  busy(true);
  try {
    const data = await api("/api/similar?id=" + id);
    S.posts = data.posts;
    S.byId = new Map(data.posts.map(p => [p.id, p]));
    S.count = data.posts.length;
    S.end = true; S.hidden = 0;
    if (!data.posts.length) setView("empty");
    else { setView("grid"); renderPosts(data.posts, false); }
    $("#loadMore").style.display = "none";
    $("#moreNote").textContent = `Ranked by tag overlap with #${id}.`;
    toast(`${data.posts.length} similar to #${id}`);
  } catch (err) {
    showError(err.code);
  } finally { busy(false); paintCounters(); }
}

/* ═══════════ favorites ═══════════ */
async function toggleFav(id, btn) {
  const post = S.byId.get(id);
  if (!post) return;
  const wasFav = S.favIds.has(id);
  // optimistic
  if (wasFav) S.favIds.delete(id); else S.favIds.add(id);
  paintFavUI(id);
  if (btn) { btn.classList.remove("beat"); void btn.offsetWidth; if (!wasFav) btn.classList.add("beat"); }
  try {
    const res = await api("/api/favorites/toggle", {
      method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ post }),
    });
    if (res.favorite !== !wasFav) { // server disagreed, reconcile
      if (res.favorite) S.favIds.add(id); else S.favIds.delete(id);
      paintFavUI(id);
    }
    toast(res.favorite ? `Saved #${id}` : `Removed #${id}`);
    if (S.mode === "favorites" && !res.favorite) {
      S.posts = S.posts.filter(p => p.id !== id);
      const el = grid.querySelector(`.tile[data-id="${id}"]`);
      if (el) { el.style.opacity = "0"; setTimeout(() => { el.remove(); queueLayout(); }, 180); }
    }
  } catch {
    if (wasFav) S.favIds.add(id); else S.favIds.delete(id);
    paintFavUI(id);
    toast("Could not save that one", true);
  }
  paintCounters();
}
function paintFavUI(id) {
  const on = S.favIds.has(id);
  const tile = grid.querySelector(`.tile[data-id="${id}"]`);
  if (tile) {
    tile.classList.toggle("faved", on);
    const b = $(".act.fav", tile);
    if (b) b.setAttribute("aria-pressed", String(on));
  }
  if (viewer.open && S.posts[S.cur] && S.posts[S.cur].id === id) {
    $("#vFavLbl").textContent = on ? "Favorited" : "Favorite";
    $("#vFav").classList.toggle("primary", !on);
  }
}

/* ═══════════ viewer ═══════════ */
const viewer = $("#viewer");
const stage = $("#stage");
const frame = $("#frame");
const player = $("#player");
let mediaEl = null;          // current <img> or <video>
let zoom = 1, panX = 0, panY = 0, dragging = false, dragFrom = null;
let idleTimer = null;
let rafTick = 0;

function openViewer(id) {
  const i = S.posts.findIndex(p => p.id === id);
  if (i < 0) return;
  S.cur = i;
  paintViewer();
  if (!viewer.open) viewer.showModal();
  wakeStage();
}
function closeViewer() {
  if (!viewer.open) return;
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  teardownMedia();
  viewer.classList.add("closing");
  setTimeout(() => { viewer.classList.remove("closing"); viewer.close(); }, 170);
}
function teardownMedia() {
  cancelAnimationFrame(rafTick);
  if (mediaEl && mediaEl.tagName === "VIDEO") {
    mediaEl.pause();
    mediaEl.removeAttribute("src");
    mediaEl.load();
  }
  if (mediaEl) mediaEl.remove();
  mediaEl = null;
  player.classList.remove("on");
  resetZoom();
}
function resetZoom() {
  zoom = 1; panX = 0; panY = 0;
  frame.classList.remove("zoomed");
  if (mediaEl) mediaEl.style.transform = "";
  $("#zoomPill").textContent = "Fit";
}
function applyZoom() {
  if (!mediaEl) return;
  frame.classList.toggle("zoomed", zoom !== 1);
  mediaEl.style.transform = zoom === 1 ? "" : `translate(${panX}px, ${panY}px) scale(${zoom})`;
  $("#zoomPill").textContent = zoom === 1 ? "Fit" : Math.round(zoom * 100) + "%";
}
function setZoom(next, originX, originY) {
  const prev = zoom;
  zoom = clamp(next, 1, 8);
  if (zoom === 1) { panX = 0; panY = 0; }
  else if (originX != null) {
    const k = zoom / prev;
    panX = originX - (originX - panX) * k;
    panY = originY - (originY - panY) * k;
  }
  applyZoom();
}

function paintViewer() {
  const p = S.posts[S.cur];
  if (!p) return;
  const old = mediaEl;
  if (old) { old.classList.add("out"); setTimeout(() => old.remove(), 190); }
  if (old && old.tagName === "VIDEO") { old.pause(); old.removeAttribute("src"); old.load(); }
  cancelAnimationFrame(rafTick);
  resetZoom();
  player.classList.remove("on");
  $("#stageLoad").classList.add("on");

  const full = S.cfg.full_quality;
  const url = p.video ? (full || !p.sample ? p.file : p.sample) : (full || !p.sample ? p.file : p.sample);
  const el = p.video ? document.createElement("video") : document.createElement("img");
  el.className = "media-el";
  if (p.video) {
    el.playsInline = true;
    el.preload = "auto";
    el.loop = S.cfg.loop;
    el.muted = S.cfg.muted;
    el.volume = S.cfg.volume / 100;
    el.playbackRate = S.cfg.speed;
    el.src = media(url);
    bindPlayer(el);
  } else {
    el.alt = "Post " + p.id;
    el.decoding = "async";
    el.src = media(url);
    el.addEventListener("error", () => {
      if (el.dataset.retried) return;
      el.dataset.retried = "1";
      el.src = media(p.file);
    });
  }
  const reveal = () => { $("#stageLoad").classList.remove("on"); el.classList.add("in"); };
  el.addEventListener(p.video ? "loadeddata" : "load", reveal, { once: true });
  setTimeout(reveal, 2500); // never leave the spinner stuck

  frame.appendChild(el);
  mediaEl = el;

  if (p.video && S.cfg.autoplay) el.play().catch(() => {});

  // meta
  $("#vId").textContent = "#" + p.id;
  const rate = { s: "safe", q: "questionable", e: "explicit" }[p.rating] || "unrated";
  $("#vSub").textContent = `score ${fmt(p.score)} \u00b7 ${rate} \u00b7 ${p.ext.toUpperCase()}`;
  $("#vPos").textContent = `${S.cur + 1} / ${S.posts.length}`;
  $("#vDims").textContent = `${p.w} \u00d7 ${p.h}`;
  $("#sDim").textContent = `${p.w} \u00d7 ${p.h}`;
  $("#sFile").textContent = p.ext.toUpperCase() + (p.video ? " \u00b7 video" : "");
  $("#sScore").textContent = fmt(p.score);
  $("#sRate").textContent = rate;
  const src = $("#sSrc");
  if (p.source) { src.textContent = p.source.replace(/^https?:\/\//, "").slice(0, 34); src.href = p.source; src.style.display = ""; }
  else { src.textContent = "none"; src.removeAttribute("href"); }
  $("#sPage").href = p.page_url;

  const groups = { char: [], series: [], general: [] };
  for (const t of p.tags) {
    if (/_\(.+\)$/.test(t)) groups.char.push(t);
    else if (/(_series|^series_)/.test(t)) groups.series.push(t);
    else groups.general.push(t);
  }
  const chipTag = (t, cls) => `<button class="tag ${cls}" data-tag="${escHtml(t)}"><span class="l">${escHtml(t.replace(/_/g, " "))}</span></button>`;
  $("#tgChar").innerHTML = groups.char.map(t => chipTag(t, "hot")).join("") || `<span class="sub" style="color:var(--tx4)">none</span>`;
  $("#tgGen").innerHTML = groups.general.map(t => chipTag(t, "")).join("");
  $("#tgCharWrap").style.display = groups.char.length ? "" : "none";

  paintFavUI(p.id);
  $("#side").scrollTop = 0;
  $("#vidOnly").style.display = p.video ? "" : "none";
  $("#imgOnly").style.display = p.video ? "none" : "";

  if (S.cfg.preload_next) {
    for (const d of [1, -1]) {
      const n = S.posts[(S.cur + d + S.posts.length) % S.posts.length];
      if (n && !n.video) { const im = new Image(); im.src = media(n.sample || n.file); }
    }
  }
}
function step(d) {
  if (!S.posts.length) return;
  S.cur = (S.cur + d + S.posts.length) % S.posts.length;
  paintViewer();
  wakeStage();
  if (S.cur > S.posts.length - 4 && !S.end && S.cfg.infinite_scroll) loadPage(false);
}

/* ── player ── */
function bindPlayer(v) {
  player.classList.add("on");
  const seek = $("#seek"), prog = $("#seekProg"), buf = $("#seekBuf"), knob = $("#seekKnob");
  const time = $("#pTime");
  let scrubbing = false;

  const paint = () => {
    if (!v.duration || !isFinite(v.duration)) return;
    if (!scrubbing) {
      const pct = (v.currentTime / v.duration) * 100;
      prog.style.width = pct + "%";
      knob.style.left = pct + "%";
    }
    if (v.buffered.length) {
      buf.style.width = (v.buffered.end(v.buffered.length - 1) / v.duration) * 100 + "%";
    }
    time.textContent = clock(v.currentTime) + " / " + clock(v.duration);
  };
  const loop = () => { paint(); rafTick = requestAnimationFrame(loop); };
  cancelAnimationFrame(rafTick);
  rafTick = requestAnimationFrame(loop);

  const syncPlay = () => { $("#pPlay").innerHTML = v.paused ? ICON.play : ICON.pause; };
  v.addEventListener("play", syncPlay);
  v.addEventListener("pause", syncPlay);
  v.addEventListener("waiting", () => $("#stageLoad").classList.add("on"));
  v.addEventListener("playing", () => $("#stageLoad").classList.remove("on"));
  v.addEventListener("canplay", () => $("#stageLoad").classList.remove("on"));
  v.addEventListener("error", () => {
    $("#stageLoad").classList.remove("on");
    toast("This file will not play. Try full quality in settings.", true);
  });
  v.addEventListener("volumechange", () => {
    $("#pMute").innerHTML = v.muted || !v.volume ? ICON.mute : ICON.vol;
    $("#pVol").value = v.muted ? 0 : Math.round(v.volume * 100);
  });
  syncPlay();
  $("#pMute").innerHTML = v.muted ? ICON.mute : ICON.vol;
  $("#pVol").value = v.muted ? 0 : Math.round(v.volume * 100);
  $("#pLoop").setAttribute("aria-pressed", String(v.loop));
  $("#pSpeed").textContent = v.playbackRate + "\u00d7";

  const posOf = e => clamp((e.clientX - seek.getBoundingClientRect().left) / seek.clientWidth, 0, 1);
  seek.onpointerdown = e => {
    if (!v.duration) return;
    scrubbing = true; seek.classList.add("scrub");
    seek.setPointerCapture(e.pointerId);
    const f = posOf(e);
    prog.style.width = knob.style.left = f * 100 + "%";
  };
  seek.onpointermove = e => {
    const f = posOf(e);
    const tip = $("#seekTip");
    tip.style.left = f * 100 + "%";
    tip.textContent = clock(f * (v.duration || 0));
    if (!scrubbing) return;
    prog.style.width = knob.style.left = f * 100 + "%";
  };
  const endScrub = e => {
    if (!scrubbing) return;
    scrubbing = false; seek.classList.remove("scrub");
    try { seek.releasePointerCapture(e.pointerId); } catch {}
    if (v.duration) v.currentTime = posOf(e) * v.duration;
  };
  seek.onpointerup = endScrub;
  seek.onpointercancel = endScrub;
}
function togglePlay() {
  if (!mediaEl || mediaEl.tagName !== "VIDEO") return;
  if (mediaEl.paused) mediaEl.play().catch(() => {});
  else mediaEl.pause();
}
function nudge(sec) {
  if (!mediaEl || mediaEl.tagName !== "VIDEO" || !mediaEl.duration) return;
  mediaEl.currentTime = clamp(mediaEl.currentTime + sec, 0, mediaEl.duration);
}
$("#pPlay").onclick = togglePlay;
$("#pMute").onclick = () => { if (mediaEl && mediaEl.tagName === "VIDEO") { mediaEl.muted = !mediaEl.muted; saveCfg({ muted: mediaEl.muted }, true); } };
$("#pVol").oninput = e => {
  if (!mediaEl || mediaEl.tagName !== "VIDEO") return;
  const v = +e.target.value;
  mediaEl.volume = v / 100;
  mediaEl.muted = v === 0;
  saveCfg({ volume: v, muted: mediaEl.muted }, true);
};
$("#pLoop").onclick = e => {
  if (!mediaEl || mediaEl.tagName !== "VIDEO") return;
  mediaEl.loop = !mediaEl.loop;
  e.currentTarget.setAttribute("aria-pressed", String(mediaEl.loop));
  saveCfg({ loop: mediaEl.loop }, true);
};
const SPEEDS = [0.5, 0.75, 1, 1.25, 1.5, 2];
$("#pSpeed").onclick = () => {
  if (!mediaEl || mediaEl.tagName !== "VIDEO") return;
  const next = SPEEDS[(SPEEDS.indexOf(mediaEl.playbackRate) + 1) % SPEEDS.length] || 1;
  mediaEl.playbackRate = next;
  $("#pSpeed").textContent = next + "\u00d7";
  saveCfg({ speed: next }, true);
};
$("#pPip").onclick = async () => {
  if (!mediaEl || mediaEl.tagName !== "VIDEO" || !document.pictureInPictureEnabled) return toast("Picture in picture is unavailable", true);
  try {
    if (document.pictureInPictureElement) await document.exitPictureInPicture();
    else await mediaEl.requestPictureInPicture();
  } catch { toast("Picture in picture refused", true); }
};

/* ── fullscreen ── */
function toggleFullscreen() {
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  else stage.requestFullscreen({ navigationUI: "hide" }).catch(() => toast("Fullscreen refused by the browser", true));
}
document.addEventListener("fullscreenchange", () => {
  const on = !!document.fullscreenElement;
  $("#fsBtn").innerHTML = on ? ICON.fsx : ICON.fs;
  $("#pFs").innerHTML = on ? ICON.fsx : ICON.fs;
  wakeStage();
});
$("#fsBtn").onclick = toggleFullscreen;
$("#pFs").onclick = toggleFullscreen;

/* ── idle chrome ── */
function wakeStage() {
  stage.classList.remove("idle");
  clearTimeout(idleTimer);
  idleTimer = setTimeout(() => {
    if (mediaEl && mediaEl.tagName === "VIDEO" && !mediaEl.paused) stage.classList.add("idle");
    else if (document.fullscreenElement) stage.classList.add("idle");
  }, 2200);
}
stage.addEventListener("pointermove", wakeStage);
stage.addEventListener("pointerleave", () => clearTimeout(idleTimer));

/* ── zoom + pan ── */
frame.addEventListener("wheel", e => {
  if (!mediaEl || mediaEl.tagName === "VIDEO") return;
  e.preventDefault();
  const r = frame.getBoundingClientRect();
  setZoom(zoom * (e.deltaY < 0 ? 1.18 : 1 / 1.18), e.clientX - r.left - r.width / 2, e.clientY - r.top - r.height / 2);
}, { passive: false });
frame.addEventListener("dblclick", e => {
  if (!mediaEl || mediaEl.tagName === "VIDEO") { togglePlay(); return; }
  const r = frame.getBoundingClientRect();
  setZoom(zoom === 1 ? 2.4 : 1, e.clientX - r.left - r.width / 2, e.clientY - r.top - r.height / 2);
});
frame.addEventListener("pointerdown", e => {
  if (zoom === 1 || !mediaEl) return;
  dragging = true; dragFrom = { x: e.clientX - panX, y: e.clientY - panY };
  frame.classList.add("dragging");
  frame.setPointerCapture(e.pointerId);
});
frame.addEventListener("pointermove", e => {
  if (!dragging) return;
  panX = e.clientX - dragFrom.x;
  panY = e.clientY - dragFrom.y;
  applyZoom();
});
const endDrag = e => {
  if (!dragging) return;
  dragging = false;
  frame.classList.remove("dragging");
  try { frame.releasePointerCapture(e.pointerId); } catch {}
};
frame.addEventListener("pointerup", endDrag);
frame.addEventListener("pointercancel", endDrag);
$("#zoomIn").onclick = () => setZoom(zoom * 1.4, 0, 0);
$("#zoomOut").onclick = () => setZoom(zoom / 1.4, 0, 0);
$("#zoomPill").onclick = () => setZoom(zoom === 1 ? 2 : 1, 0, 0);

/* ── viewer chrome ── */
$("#vNext").onclick = () => step(1);
$("#vPrev").onclick = () => step(-1);
$("#vClose").onclick = closeViewer;
$("#vFav").onclick = () => { const p = S.posts[S.cur]; if (p) toggleFav(p.id, null); };
$("#vSimilar").onclick = () => { const p = S.posts[S.cur]; if (p) loadSimilar(p.id); };
$("#vCopy").onclick = async () => {
  const p = S.posts[S.cur]; if (!p) return;
  try { await navigator.clipboard.writeText(p.page_url); toast("Link copied"); }
  catch { toast("Clipboard refused", true); }
};
$("#vOpen").onclick = () => { const p = S.posts[S.cur]; if (p) window.open(p.page_url, "_blank", "noopener"); };
$("#sideToggle").onclick = e => {
  const solo = $("#vwrap").classList.toggle("solo");
  e.currentTarget.textContent = solo ? "Show info" : "Hide info";
  saveCfg({ sidebar: !solo }, true);
};
$("#side").addEventListener("click", e => {
  const t = e.target.closest("[data-tag]");
  if (!t) return;
  closeViewer();
  S.mode = "feed";
  addChip(t.dataset.tag);
});
viewer.addEventListener("cancel", e => {
  e.preventDefault();
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  else closeViewer();
});
viewer.addEventListener("click", e => { if (e.target === viewer) closeViewer(); });
viewer.addEventListener("keydown", e => {
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  const k = e.key.toLowerCase();
  const isVideo = mediaEl && mediaEl.tagName === "VIDEO";
  if (e.key === "ArrowRight") { e.preventDefault(); isVideo && e.shiftKey ? nudge(5) : step(1); }
  else if (e.key === "ArrowLeft") { e.preventDefault(); isVideo && e.shiftKey ? nudge(-5) : step(-1); }
  else if (k === " " || k === "k") { e.preventDefault(); isVideo ? togglePlay() : step(1); }
  else if (k === "j") { e.preventDefault(); nudge(-5); }
  else if (k === "l") { e.preventDefault(); nudge(5); }
  else if (k === "m") { e.preventDefault(); $("#pMute").click(); }
  else if (k === "f") { e.preventDefault(); toggleFullscreen(); }
  else if (k === "s") { e.preventDefault(); $("#vFav").click(); }
  else if (k === "i") { e.preventDefault(); $("#sideToggle").click(); }
  else if (k === "0") { e.preventDefault(); resetZoom(); }
});

/* ═══════════ settings ═══════════ */
const drawer = $("#drawer");
let lastFocus = null;
function openDrawer(tab) {
  lastFocus = document.activeElement;
  drawer.classList.add("on");
  drawer.setAttribute("aria-hidden", "false");
  $("#scrim").classList.add("on");
  if (tab) selectTab(tab);
}
function closeDrawer() {
  if (!drawer.classList.contains("on")) return;
  drawer.classList.remove("on");
  drawer.setAttribute("aria-hidden", "true");
  $("#scrim").classList.remove("on");
  if (lastFocus && lastFocus.focus) lastFocus.focus();
}
function selectTab(name) {
  $$("#tabs button").forEach(b => b.setAttribute("aria-selected", String(b.dataset.tab === name)));
  $$(".tabpane").forEach(p => p.classList.toggle("on", p.dataset.pane === name));
  $(".body", drawer).scrollTop = 0;
}
$("#tabs").addEventListener("click", e => {
  const b = e.target.closest("button[data-tab]");
  if (b) selectTab(b.dataset.tab);
});
$("#setBtn").onclick = () => openDrawer("appearance");
$("#dClose").onclick = closeDrawer;
$("#scrim").onclick = closeDrawer;

let saveTimer = null;
async function saveCfg(patch, quiet) {
  Object.assign(S.cfg, patch);
  applyTheme(S.cfg);
  clearTimeout(saveTimer);
  saveTimer = setTimeout(async () => {
    try {
      S.cfg = await api("/api/config", {
        method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(patch),
      });
      applyTheme(S.cfg);
      syncSettingsUI();
      if (!quiet) toast("Saved");
    } catch { toast("Could not write config.json", true); }
  }, 220);
}
function bindSettings() {
  // switches
  $$("[data-bool]").forEach(el => {
    el.onclick = () => {
      const key = el.dataset.bool;
      const next = el.getAttribute("aria-checked") !== "true";
      el.setAttribute("aria-checked", String(next));
      saveCfg({ [key]: next }, true);
      if (["hq_previews", "blacklist_mode"].includes(key)) reload();
    };
  });
  // enums
  $$("[data-enum]").forEach(box => {
    box.onclick = e => {
      const b = e.target.closest("button[data-val]");
      if (!b) return;
      const key = box.dataset.enum;
      $$("button[data-val]", box).forEach(x => x.setAttribute("aria-pressed", String(x === b)));
      saveCfg({ [key]: b.dataset.val }, true);
      if (["rating", "sort", "blacklist_mode"].includes(key)) reload();
    };
  });
  // numbers
  $$("[data-num]").forEach(inp => {
    inp.oninput = () => {
      const key = inp.dataset.num;
      const out = $(`[data-num-out="${key}"]`);
      if (out) out.textContent = inp.value;
      saveCfg({ [key]: +inp.value }, true);
    };
  });
  $("#perPage").addEventListener("change", () => reload());
  $("#minScore").addEventListener("change", () => reload());
  // credentials
  for (const id of ["apiKey", "userId"]) {
    $("#" + id).addEventListener("change", e => {
      saveCfg({ [id === "apiKey" ? "api_key" : "user_id"]: e.target.value.trim() });
      reload();
    });
  }
  $("#dReset").onclick = async () => {
    if (!confirm("Reset appearance and playback settings? Credentials and saved searches stay.")) return;
    S.cfg = await api("/api/config/reset", { method: "POST" });
    applyTheme(S.cfg);
    syncSettingsUI();
    toast("Settings reset");
    reload();
  };
  $("#dClear").onclick = async () => {
    await api("/api/cache/clear", { method: "POST" });
    toast("Caches dropped");
    reload();
  };
  // blacklist
  $("#blInput").addEventListener("keydown", e => {
    if (e.key !== "Enter") return;
    const v = e.target.value.trim().toLowerCase().replace(/\s+/g, "_");
    if (!v || S.cfg.blacklist.includes(v)) return;
    e.target.value = "";
    saveCfg({ blacklist: [...S.cfg.blacklist, v] });
    renderBlacklist();
    reload();
  });
  $("#blList").addEventListener("click", e => {
    const b = e.target.closest("[data-bl]");
    if (!b) return;
    const next = S.cfg.blacklist.filter((_, i) => i !== +b.dataset.bl);
    saveCfg({ blacklist: next });
    renderBlacklist();
    reload();
  });
  // saved searches
  $("#saveSearch").onclick = () => {
    const query = chipsText();
    if (!query) return toast("Nothing to save", true);
    const name = (prompt("Name this search", query.slice(0, 40)) || "").trim();
    if (!name) return;
    saveCfg({ saved_searches: [...S.cfg.saved_searches, { name, query }] });
    renderSaved();
    toast("Search saved");
  };
  $("#savedList").addEventListener("click", e => {
    const del = e.target.closest("[data-unsave]");
    if (del) {
      saveCfg({ saved_searches: S.cfg.saved_searches.filter((_, i) => i !== +del.dataset.unsave) });
      renderSaved();
      return;
    }
    const run = e.target.closest("[data-run]");
    if (run) { closeDrawer(); S.mode = "feed"; setChips(run.dataset.run); }
  });
}
function renderBlacklist() {
  $("#blList").innerHTML = S.cfg.blacklist.map((t, i) =>
    `<span class="chip">${escHtml(t)}<button data-bl="${i}" aria-label="Remove ${escHtml(t)}">${ICON.x}</button></span>`).join("")
    || `<span class="sub" style="color:var(--tx4);font-size:.8125rem">Empty. Everything is shown.</span>`;
}
function renderSaved() {
  $("#savedList").innerHTML = S.cfg.saved_searches.map((s, i) => `
    <div class="savedrow">
      <button class="nm" data-run="${escHtml(s.query)}">${escHtml(s.name)}<div class="qy">${escHtml(s.query)}</div></button>
      <button class="btn sm quiet" data-unsave="${i}">Remove</button>
    </div>`).join("") || `<p class="sub" style="color:var(--tx4);font-size:.8125rem;margin:0">No saved searches yet. Build a query, then hit Save current.</p>`;
}
function syncSettingsUI() {
  const cfg = S.cfg;
  $$("[data-bool]").forEach(el => el.setAttribute("aria-checked", String(!!cfg[el.dataset.bool])));
  $$("[data-enum]").forEach(box => {
    const val = cfg[box.dataset.enum];
    $$("button[data-val]", box).forEach(b => b.setAttribute("aria-pressed", String(b.dataset.val === String(val))));
  });
  $$("[data-num]").forEach(inp => {
    inp.value = cfg[inp.dataset.num];
    const out = $(`[data-num-out="${inp.dataset.num}"]`);
    if (out) out.textContent = cfg[inp.dataset.num];
  });
  $("#apiKey").value = cfg.api_key;
  $("#userId").value = cfg.user_id;
  // rail mirrors
  $$("#sortSeg button").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.val === cfg.sort)));
  $$("#rateSeg button").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.val === cfg.rating)));
  $$("#densSeg button").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.val === cfg.density)));
  $("#minScoreRail").value = cfg.min_score;
  renderBlacklist();
  renderSaved();
}

/* ═══════════ rail ═══════════ */
function railSeg(sel, key, reloads) {
  $(sel).addEventListener("click", e => {
    const b = e.target.closest("button[data-val]");
    if (!b) return;
    $$(sel + " button").forEach(x => x.setAttribute("aria-pressed", String(x === b)));
    saveCfg({ [key]: b.dataset.val }, true);
    syncSettingsUI();
    if (reloads) reload();
  });
}
railSeg("#sortSeg", "sort", true);
railSeg("#rateSeg", "rating", true);
railSeg("#densSeg", "density", false);
$("#minScoreRail").addEventListener("change", e => {
  const v = clamp(parseInt(e.target.value, 10) || 0, 0, 100000);
  e.target.value = v;
  saveCfg({ min_score: v }, true);
  syncSettingsUI();
  reload();
});
$("#favBtn").onclick = () => {
  const on = $("#favBtn").getAttribute("aria-pressed") !== "true";
  $("#favBtn").setAttribute("aria-pressed", String(on));
  S.mode = on ? "favorites" : "feed";
  on ? loadFavorites() : reload();
};
$("#blNote").onclick = () => openDrawer("content");

/* ═══════════ empty / error actions ═══════════ */
$("#dropLast").onclick = () => { S.chips.pop(); renderChips(); reload(); };
$("#clearAll").onclick = () => {
  S.chips = [];
  S.mode = "feed";
  $("#favBtn").setAttribute("aria-pressed", "false");
  saveCfg({ rating: "all", min_score: 0 }, true);
  renderChips();
  syncSettingsUI();
  reload();
};
$("#openBl").onclick = () => openDrawer("content");
$("#retryBtn").onclick = () => reload();
$("#openKey").onclick = () => openDrawer("account");

/* ═══════════ search input ═══════════ */
const q = $("#q");
let acDebounce = null;
q.addEventListener("input", () => {
  clearTimeout(acDebounce);
  const v = q.value;
  acDebounce = setTimeout(() => suggest(v), 130);
});
q.addEventListener("focus", () => { if (!q.value.trim()) renderIdle(); });
q.addEventListener("keydown", e => {
  if (e.key === "ArrowDown") { e.preventDefault(); moveAc(1); }
  else if (e.key === "ArrowUp") { e.preventDefault(); moveAc(-1); }
  else if (e.key === "Enter") {
    e.preventDefault();
    const typed = q.value.trim();
    if (acIdx >= 0 && acRows[acIdx]) addChip(acRows[acIdx].value);
    else if (typed) addChip(typed);
    else { closePop(); reload(); }
  } else if (e.key === "Escape") { e.stopPropagation(); closePop(); q.blur(); }
  else if (e.key === "Backspace" && !q.value && S.chips.length) { S.chips.pop(); renderChips(); reload(); }
});
$("#chips").addEventListener("click", e => {
  const b = e.target.closest("[data-chip]");
  if (!b) return;
  S.chips.splice(+b.dataset.chip, 1);
  renderChips();
  reload();
});
pop.addEventListener("mousedown", e => {
  const op = e.target.closest("[data-op]");
  if (op) { e.preventDefault(); q.value = op.dataset.op; q.focus(); suggest(q.value); return; }
  const unsave = e.target.closest("[data-unsave]");
  if (unsave) {
    e.preventDefault(); e.stopPropagation();
    saveCfg({ saved_searches: S.cfg.saved_searches.filter((_, i) => i !== +unsave.dataset.unsave) });
    renderSaved(); renderIdle();
    return;
  }
  const clearR = e.target.closest("[data-clear-recent]");
  if (clearR) { e.preventDefault(); saveCfg({ recent_searches: [] }); renderIdle(); return; }
  const run = e.target.closest("[data-run]");
  if (run) { e.preventDefault(); closePop(); S.mode = "feed"; setChips(run.dataset.run); return; }
  const add = e.target.closest("[data-add]");
  if (add) { e.preventDefault(); addChip(add.dataset.add); return; }
  const row = e.target.closest("[data-i]");
  if (row) { e.preventDefault(); addChip(acRows[+row.dataset.i].value); }
});
document.addEventListener("click", e => { if (!e.target.closest(".search")) closePop(); });
function rememberSearch(query) {
  const next = [query, ...S.cfg.recent_searches.filter(r => r !== query)].slice(0, 12);
  saveCfg({ recent_searches: next }, true);
}

/* ═══════════ chrome ═══════════ */
let toastTimer = null;
function toast(msg, bad) {
  const el = $("#toast");
  $("#toastMsg").textContent = msg;
  el.classList.toggle("bad", !!bad);
  el.classList.add("on");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => el.classList.remove("on"), 2400);
}
let busyCount = 0;
function busy(on) {
  busyCount = Math.max(0, busyCount + (on ? 1 : -1));
  $("#live").classList.toggle("busy", busyCount > 0);
}
addEventListener("scroll", () => $("#topbar").classList.toggle("lifted", scrollY > 4), { passive: true });
new ResizeObserver(queueLayout).observe(grid);
if (document.fonts) document.fonts.ready.then(queueLayout);
new IntersectionObserver(entries => {
  if (entries[0].isIntersecting && S.cfg && S.cfg.infinite_scroll && S.view === "grid") loadPage(false);
}, { rootMargin: "900px" }).observe(sentinel);
$("#loadMore").onclick = () => loadPage(false);

const typing = () => {
  const el = document.activeElement;
  return el && (el.tagName === "INPUT" || el.tagName === "TEXTAREA" || el.isContentEditable);
};
addEventListener("keydown", e => {
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  if (viewer.open) return;
  if (e.key === "/" && !typing()) { e.preventDefault(); q.focus(); }
  else if (e.key === "," && !typing()) { e.preventDefault(); openDrawer("appearance"); }
  else if (e.key === "Escape") { closePop(); closeDrawer(); }
  else if (e.key.toLowerCase() === "f" && !typing()) { e.preventDefault(); $("#favBtn").click(); }
  else if (e.key === "?" && !typing()) { e.preventDefault(); openDrawer("keys"); }
});
addEventListener("hashchange", () => {
  const q2 = readHash();
  if (q2 !== chipsText()) setChips(q2);
});
addEventListener("pagehide", () => { stopHover(); teardownMedia(); });

/* ═══════════ boot ═══════════ */
(async function boot() {
  try {
    const [cfg, favs] = await Promise.all([api("/api/config"), api("/api/favorites/ids")]);
    S.cfg = cfg;
    S.favIds = new Set(favs.ids);
    applyTheme(cfg);
    bindSettings();
    syncSettingsUI();
    if (!cfg.sidebar) $("#vwrap").classList.add("solo");
    const initial = readHash();
    if (initial) setChips(initial, { silent: true });
    renderChips();
    paintCounters();
    await loadPage(true);
  } catch (err) {
    showError(err.code || "network");
  }
})();
})();
"""

# ═══════════════════════════════════════════════════════════════════════
# UI: document
# ═══════════════════════════════════════════════════════════════════════
PAGE_HTML = r"""<!DOCTYPE html>
<html lang="en" data-contrast="normal" data-corners="soft" data-density="cozy" data-motion="full" data-meta="hover" data-grain="on">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="dark">
<title>Nocturne</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Hanken+Grotesk:ital,wght@0,300..700;1,300..600&family=Newsreader:ital,opsz,wght@0,6..72,300..500&display=swap" rel="stylesheet">
<style>__CSS__</style>
</head>
<body>

<header class="topbar" id="topbar">
  <div class="brand">
    <span class="mark">N<em>o</em>cturne</span>
    <span class="ver num">__VERSION__</span>
  </div>

  <div class="search">
    <div class="shell">
      <span class="ico"><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="11" cy="11" r="7"/><path d="m20 20-3.4-3.4"/></svg></span>
      <div class="chips" id="chips"></div>
      <input id="q" type="text" autocomplete="off" spellcheck="false" role="combobox"
             aria-expanded="false" aria-controls="pop" aria-label="Search tags"
             placeholder="Search tags. − to exclude, rating: score: sort: for filters">
      <span class="kbd">/</span>
    </div>
    <div class="panel-pop" id="pop" role="listbox" aria-label="Suggestions"></div>
  </div>

  <div class="tools">
    <button class="tbtn" id="favBtn" aria-pressed="false" title="Favorites (F)">
      <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7"><path d="M12 20.2S4.8 15.5 4.8 10.4A3.9 3.9 0 0 1 12 8.2a3.9 3.9 0 0 1 7.2 2.2c0 5.1-7.2 9.8-7.2 9.8Z"/></svg>
      <span class="lbl">Favorites</span><span class="count num" id="favCount">0</span>
    </button>
    <span class="rule"></span>
    <button class="tbtn" id="setBtn" title="Settings (,)">
      <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7"><circle cx="12" cy="12" r="3.2"/><path d="M19.6 14.4a1.5 1.5 0 0 0 .3 1.7l.1.1a1.9 1.9 0 1 1-2.7 2.7l-.1-.1a1.5 1.5 0 0 0-2.6 1.1v.2a1.9 1.9 0 1 1-3.8 0V20a1.5 1.5 0 0 0-2.6-1l-.1.1a1.9 1.9 0 1 1-2.7-2.7l.1-.1a1.5 1.5 0 0 0-1-2.6H4a1.9 1.9 0 1 1 0-3.8h.2a1.5 1.5 0 0 0 1-2.6l-.1-.1a1.9 1.9 0 1 1 2.7-2.7l.1.1a1.5 1.5 0 0 0 2.6-1V4a1.9 1.9 0 1 1 3.8 0v.2a1.5 1.5 0 0 0 2.6 1l.1-.1a1.9 1.9 0 1 1 2.7 2.7l-.1.1a1.5 1.5 0 0 0 1 2.6h.2a1.9 1.9 0 1 1 0 3.8H20a1.5 1.5 0 0 0-1.4.9Z"/></svg>
      <span class="lbl">Settings</span>
    </button>
  </div>
</header>

<div class="rail">
  <span class="eyebrow">Sort</span>
  <div class="seg" id="sortSeg">
    <button data-val="newest" aria-pressed="true">Newest</button>
    <button data-val="score">Score</button>
    <button data-val="random">Random</button>
  </div>
  <span class="eyebrow">Rating</span>
  <div class="seg" id="rateSeg">
    <button data-val="all" aria-pressed="true">All</button>
    <button data-val="safe">Safe</button>
    <button data-val="questionable">Questionable</button>
    <button data-val="explicit">Explicit</button>
  </div>
  <span class="eyebrow">Density</span>
  <div class="seg" id="densSeg">
    <button data-val="compact">Compact</button>
    <button data-val="cozy" aria-pressed="true">Cozy</button>
    <button data-val="large">Large</button>
  </div>
  <label class="stepper"><span>Score &gt;</span><input id="minScoreRail" class="num" type="number" min="0" max="100000" step="10" value="0"></label>
  <button class="veil" id="saveSearch" title="Save this query">
    <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9"><path d="M6 4h9l3 3v13l-6-3-6 3z"/></svg>
    Save current
  </button>
  <span class="spacer"></span>
  <button class="veil" id="blNote" title="Blacklist settings">
    <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9"><path d="M2 12s3.7-6.8 10-6.8S22 12 22 12s-3.7 6.8-10 6.8S2 12 2 12Z"/><path d="m4 20 16-16"/></svg>
    <span class="num" id="blCount">0</span> filtered
  </button>
  <span class="meta"><b class="num" id="shown">0</b> loaded · <span class="num" id="total">—</span> total</span>
</div>

<main>
  <div class="grid" id="grid"></div>

  <div class="more" id="more">
    <button class="btn" id="loadMore">
      <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round"><path d="M12 5v14"/><path d="m6 13 6 6 6-6"/></svg>
      <span>Load more</span>
    </button>
    <p id="moreNote">Infinite scroll is on. Blacklisted pages are walked server side.</p>
  </div>

  <section class="state" id="emptyState">
    <div class="glyph"><svg width="28" height="28" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.3"><circle cx="11" cy="11" r="7"/><path d="m20 20-3.4-3.4"/><path d="M8.4 11h5.2"/></svg></div>
    <h2>Nothing matches <em>this combination</em></h2>
    <p>Zero results after walking six upstream pages. Usually one tag is too narrow, or the blacklist is eating everything the query returns.</p>
    <div class="row">
      <button class="btn primary" id="dropLast">Drop the last tag</button>
      <button class="btn quiet" id="clearAll">Reset filters</button>
      <button class="btn quiet" id="openBl">Review blacklist</button>
    </div>
  </section>

  <section class="state" id="errState">
    <span class="flag" id="errFlag">upstream</span>
    <h2 id="errTitle">Something broke</h2>
    <p id="errBody"></p>
    <div class="row">
      <button class="btn primary" id="retryBtn">Retry</button>
      <button class="btn quiet" id="openKey">Account settings</button>
    </div>
  </section>
</main>

<div class="status">
  <span class="live" id="live"></span>
  <span>127.0.0.1<b>:__PORT__</b></span>
  <span class="hide-sm">proxy streaming · range on</span>
  <span class="spacer"></span>
  <span class="hide-sm">Nocturne __VERSION__</span>
</div>

<dialog class="viewer" id="viewer" aria-label="Post viewer">
  <div class="vwrap" id="vwrap">
    <div class="stage" id="stage">
      <div class="frame" id="frame"></div>
      <div class="stage-load" id="stageLoad"><span class="spin" style="width:24px;height:24px"></span></div>

      <button class="nav prev" id="vPrev" aria-label="Previous"><svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round"><path d="m14 6-6 6 6 6"/></svg></button>
      <button class="nav next" id="vNext" aria-label="Next"><svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round"><path d="m10 6 6 6-6 6"/></svg></button>
      <button class="vclose" id="vClose" aria-label="Close"><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linecap="round"><path d="m6 6 12 12M18 6 6 18"/></svg></button>

      <div class="hud">
        <span class="pill" id="vPos">0 / 0</span>
        <span class="pill hide-sm" id="vDims">—</span>
        <span id="imgOnly" style="display:flex;gap:6px">
          <button class="pill" id="zoomOut" aria-label="Zoom out"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="14" height="14"><circle cx="11" cy="11" r="6.5"/><path d="m20 20-4.2-4.2M8.5 11h5"/></svg></button>
          <button class="pill" id="zoomPill">Fit</button>
          <button class="pill" id="zoomIn" aria-label="Zoom in"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" width="14" height="14"><circle cx="11" cy="11" r="6.5"/><path d="m20 20-4.2-4.2M8.5 11h5M11 8.5v5"/></svg></button>
        </span>
        <span id="vidOnly" style="display:none;flex:1 1 auto">
          <div class="player" id="player">
            <div class="seek" id="seek">
              <div class="track"><div class="buf" id="seekBuf"></div><div class="prog" id="seekProg"></div></div>
              <div class="knob" id="seekKnob"></div>
              <div class="hover-t" id="seekTip">0:00</div>
            </div>
            <div class="prow">
              <button class="pbtn" id="pPlay" aria-label="Play or pause"></button>
              <span class="ptime" id="pTime">0:00 / 0:00</span>
              <div class="vol"><button class="pbtn" id="pMute" aria-label="Mute"></button><input type="range" id="pVol" min="0" max="100" value="80" aria-label="Volume"></div>
              <span class="spacer"></span>
              <button class="pbtn" id="pLoop" aria-label="Loop" aria-pressed="false"></button>
              <button class="speed" id="pSpeed">1×</button>
              <button class="pbtn" id="pPip" aria-label="Picture in picture"></button>
              <button class="pbtn" id="pFs" aria-label="Fullscreen"></button>
            </div>
          </div>
        </span>
        <span class="spacer"></span>
        <button class="pill" id="fsBtn" aria-label="Fullscreen"></button>
        <button class="pill hide-sm" id="sideToggle">Hide info</button>
      </div>
    </div>

    <aside class="side" id="side">
      <h3 id="vId">#0</h3>
      <p class="sub" id="vSub"></p>
      <div class="qacts">
        <button class="btn primary" id="vFav">
          <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7"><path d="M12 20.2S4.8 15.5 4.8 10.4A3.9 3.9 0 0 1 12 8.2a3.9 3.9 0 0 1 7.2 2.2c0 5.1-7.2 9.8-7.2 9.8Z"/></svg>
          <span id="vFavLbl">Favorite</span>
        </button>
        <button class="btn" id="vSimilar">Find similar</button>
        <button class="btn" id="vCopy">Copy link</button>
        <button class="btn" id="vOpen">Open on site</button>
      </div>
      <dl class="spec">
        <dt>Dimensions</dt><dd id="sDim">—</dd>
        <dt>File</dt><dd id="sFile">—</dd>
        <dt>Score</dt><dd id="sScore">—</dd>
        <dt>Rating</dt><dd id="sRate">—</dd>
        <dt>Source</dt><dd><a id="sSrc" target="_blank" rel="noopener">none</a></dd>
        <dt>Post</dt><dd><a id="sPage" target="_blank" rel="noopener">on rule34</a></dd>
      </dl>
      <div class="tgroup" id="tgCharWrap"><span class="eyebrow">Character &amp; series</span><div class="tags" id="tgChar"></div></div>
      <div class="tgroup"><span class="eyebrow">Tags</span><div class="tags" id="tgGen"></div></div>
    </aside>
  </div>
</dialog>

<div class="veil-full" id="scrim"></div>
<aside class="drawer" id="drawer" aria-label="Settings" aria-hidden="true">
  <header>
    <h2>Settings</h2>
    <button class="vclose" id="dClose" style="position:static;background:transparent;border-color:transparent" aria-label="Close settings">
      <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linecap="round"><path d="m6 6 12 12M18 6 6 18"/></svg>
    </button>
  </header>
  <div class="tabs" id="tabs" role="tablist">
    <button data-tab="appearance" aria-selected="true">Appearance</button>
    <button data-tab="feed">Feed</button>
    <button data-tab="playback">Playback</button>
    <button data-tab="content">Content</button>
    <button data-tab="searches">Searches</button>
    <button data-tab="account">Account</button>
    <button data-tab="keys">Keys</button>
  </div>

  <div class="body">
    <!-- appearance -->
    <section class="tabpane on" data-pane="appearance">
      <div class="group">
        <span class="eyebrow">Accent</span>
        <div class="swatches" data-enum="accent">
          <button class="sw" data-val="moon"   aria-pressed="true"  title="Moon"><i style="background:oklch(0.862 0.048 252)"></i></button>
          <button class="sw" data-val="frost"  title="Frost"><i style="background:oklch(0.870 0.052 196)"></i></button>
          <button class="sw" data-val="sage"   title="Sage"><i style="background:oklch(0.845 0.050 158)"></i></button>
          <button class="sw" data-val="amber"  title="Amber"><i style="background:oklch(0.860 0.058 84)"></i></button>
          <button class="sw" data-val="rose"   title="Rose"><i style="background:oklch(0.845 0.060 16)"></i></button>
          <button class="sw" data-val="violet" title="Violet"><i style="background:oklch(0.855 0.055 300)"></i></button>
        </div>
      </div>
      <div class="group">
        <span class="eyebrow">Surface</span>
        <div class="field"><div><div class="t">Contrast</div><div class="d">How deep the background sits</div></div>
          <div class="seg" data-enum="contrast"><button data-val="soft">Soft</button><button data-val="normal" aria-pressed="true">Normal</button><button data-val="high">Deep</button></div></div>
        <div class="field"><div><div class="t">Corners</div></div>
          <div class="seg" data-enum="corners"><button data-val="sharp">Sharp</button><button data-val="soft" aria-pressed="true">Soft</button><button data-val="round">Round</button></div></div>
        <div class="field"><div><div class="t">Film grain</div><div class="d">Stops large flat darks from banding</div></div>
          <button class="switch" role="switch" data-bool="grain" aria-checked="true" aria-label="Film grain"></button></div>
        <div class="field"><div><div class="t">Motion</div><div class="d">Reduced keeps transitions, drops entrances</div></div>
          <div class="seg" data-enum="motion"><button data-val="full" aria-pressed="true">Full</button><button data-val="reduced">Reduced</button><button data-val="off">Off</button></div></div>
      </div>
      <div class="group">
        <span class="eyebrow">Grid</span>
        <div class="field"><div><div class="t">Density</div></div>
          <div class="seg" data-enum="density"><button data-val="compact">Compact</button><button data-val="cozy" aria-pressed="true">Cozy</button><button data-val="large">Large</button></div></div>
        <div class="field"><div><div class="t">Card meta</div><div class="d">Id, size and score overlay</div></div>
          <div class="seg" data-enum="meta_mode"><button data-val="hover" aria-pressed="true">On hover</button><button data-val="always">Always</button><button data-val="off">Off</button></div></div>
      </div>
    </section>

    <!-- feed -->
    <section class="tabpane" data-pane="feed">
      <div class="group">
        <span class="eyebrow">Loading</span>
        <div class="field"><div><div class="t">Posts per page</div><div class="d">Upstream caps this at 100</div></div>
          <div class="rangeRow"><input type="range" id="perPage" data-num="per_page" min="10" max="100" step="2"><span class="v" data-num-out="per_page">42</span></div></div>
        <div class="field"><div><div class="t">Infinite scroll</div><div class="d">Off means the Load more button only</div></div>
          <button class="switch" role="switch" data-bool="infinite_scroll" aria-checked="true" aria-label="Infinite scroll"></button></div>
        <div class="field"><div><div class="t">Preload neighbours</div><div class="d">Fetches the next and previous still while you look</div></div>
          <button class="switch" role="switch" data-bool="preload_next" aria-checked="true" aria-label="Preload neighbours"></button></div>
      </div>
      <div class="group">
        <span class="eyebrow">Defaults</span>
        <div class="field"><div><div class="t">Sort</div></div>
          <div class="seg" data-enum="sort"><button data-val="newest" aria-pressed="true">Newest</button><button data-val="score">Score</button><button data-val="random">Random</button></div></div>
        <div class="field"><div><div class="t">Rating</div></div>
          <div class="seg" data-enum="rating"><button data-val="all" aria-pressed="true">All</button><button data-val="safe">Safe</button><button data-val="questionable">Q</button><button data-val="explicit">E</button></div></div>
        <div class="field"><div><div class="t">Minimum score</div><div class="d">Applied as score:&gt; on every query</div></div>
          <div class="rangeRow"><input type="range" id="minScore" data-num="min_score" min="0" max="1000" step="10"><span class="v" data-num-out="min_score">0</span></div></div>
      </div>
      <div class="group">
        <span class="eyebrow">Quality</span>
        <div class="field"><div><div class="t">High quality previews</div><div class="d">Sample files in the grid instead of 150px thumbs</div></div>
          <button class="switch" role="switch" data-bool="hq_previews" aria-checked="true" aria-label="High quality previews"></button></div>
        <div class="field"><div><div class="t">Always full quality</div><div class="d">Viewer skips samples. Slower on very large files</div></div>
          <button class="switch" role="switch" data-bool="full_quality" aria-checked="false" aria-label="Always full quality"></button></div>
      </div>
    </section>

    <!-- playback -->
    <section class="tabpane" data-pane="playback">
      <div class="group">
        <span class="eyebrow">Viewer</span>
        <div class="field"><div><div class="t">Autoplay</div></div>
          <button class="switch" role="switch" data-bool="autoplay" aria-checked="true" aria-label="Autoplay"></button></div>
        <div class="field"><div><div class="t">Start muted</div></div>
          <button class="switch" role="switch" data-bool="muted" aria-checked="true" aria-label="Start muted"></button></div>
        <div class="field"><div><div class="t">Loop</div></div>
          <button class="switch" role="switch" data-bool="loop" aria-checked="true" aria-label="Loop"></button></div>
        <div class="field"><div><div class="t">Volume</div></div>
          <div class="rangeRow"><input type="range" data-num="volume" min="0" max="100" step="5"><span class="v" data-num-out="volume">80</span></div></div>
      </div>
      <div class="group">
        <span class="eyebrow">Grid</span>
        <div class="field"><div><div class="t">Hover previews</div><div class="d">Plays a muted loop when you hover a video card</div></div>
          <button class="switch" role="switch" data-bool="hover_preview" aria-checked="true" aria-label="Hover previews"></button></div>
        <div class="field"><div><div class="t">Info panel open</div><div class="d">Default state of the viewer sidebar</div></div>
          <button class="switch" role="switch" data-bool="sidebar" aria-checked="true" aria-label="Info panel"></button></div>
      </div>
    </section>

    <!-- content -->
    <section class="tabpane" data-pane="content">
      <div class="group">
        <span class="eyebrow">Blacklist</span>
        <input class="inp" id="blInput" placeholder="Add a tag, wildcards allowed (cub*)" aria-label="Add blacklist tag">
        <div class="chiplist" id="blList"></div>
      </div>
      <div class="group">
        <span class="eyebrow">When something matches</span>
        <div class="field"><div><div class="t">Action</div><div class="d">Hide removes it, blur keeps a reveal button</div></div>
          <div class="seg" data-enum="blacklist_mode"><button data-val="hide" aria-pressed="true">Hide</button><button data-val="blur">Blur</button><button data-val="mark">Mark</button></div></div>
      </div>
      <div class="group">
        <span class="eyebrow">Storage</span>
        <div class="rowline">
          <button class="btn sm" id="dClear">Drop caches</button>
          <button class="btn sm danger" id="dReset">Reset settings</button>
        </div>
      </div>
    </section>

    <!-- searches -->
    <section class="tabpane" data-pane="searches">
      <div class="group">
        <span class="eyebrow">Saved searches</span>
        <div id="savedList"></div>
      </div>
      <div class="group">
        <span class="eyebrow">Operators</span>
        <div class="keys">
          <kbd>-tag</kbd><span>exclude a tag</span>
          <kbd>rating:safe</kbd><span>safe, questionable or explicit</span>
          <kbd>score:&gt;500</kbd><span>minimum score</span>
          <kbd>sort:score:desc</kbd><span>order the feed</span>
          <kbd>id:12345</kbd><span>one exact post</span>
          <kbd>tag*</kbd><span>wildcard prefix</span>
          <kbd>a ~ b</kbd><span>either tag</span>
        </div>
      </div>
    </section>

    <!-- account -->
    <section class="tabpane" data-pane="account">
      <div class="group">
        <span class="eyebrow">Credentials</span>
        <div class="field stack">
          <div class="t" style="margin-bottom:8px">API key</div>
          <input class="inp" id="apiKey" type="password" placeholder="Paste from your account page">
          <div class="d" style="margin-top:7px">Stored in <code>config.json</code> next to this app and sent only to the site.</div>
        </div>
        <div class="field stack">
          <div class="t" style="margin:10px 0 8px">User id</div>
          <input class="inp" id="userId" placeholder="Numeric id from the same page">
        </div>
      </div>
    </section>

    <!-- keys -->
    <section class="tabpane" data-pane="keys">
      <div class="group">
        <span class="eyebrow">Everywhere</span>
        <div class="keys">
          <kbd>/</kbd><span>focus search</span>
          <kbd>F</kbd><span>toggle favorites</span>
          <kbd>,</kbd><span>settings</span>
          <kbd>?</kbd><span>this list</span>
        </div>
      </div>
      <div class="group">
        <span class="eyebrow">Grid</span>
        <div class="keys">
          <kbd>Enter</kbd><span>open the focused card</span>
          <kbd>S</kbd><span>favorite the focused card</span>
        </div>
      </div>
      <div class="group">
        <span class="eyebrow">Viewer</span>
        <div class="keys">
          <kbd>← →</kbd><span>previous, next post</span>
          <kbd>Shift ← →</kbd><span>seek 5 seconds</span>
          <kbd>Space / K</kbd><span>play or pause</span>
          <kbd>J / L</kbd><span>seek 5 seconds</span>
          <kbd>M</kbd><span>mute</span>
          <kbd>F</kbd><span>fullscreen</span>
          <kbd>S</kbd><span>favorite</span>
          <kbd>I</kbd><span>info panel</span>
          <kbd>0</kbd><span>reset zoom</span>
          <kbd>Esc</kbd><span>close</span>
        </div>
      </div>
    </section>
  </div>

  <footer>
    <span class="eyebrow">Changes save instantly</span>
    <span class="spacer"></span>
    <button class="btn primary" onclick="document.getElementById('dClose').click()">Done</button>
  </footer>
</aside>

<div class="toast" id="toast"><span id="toastMsg"></span></div>

<script>__JS__</script>
</body>
</html>
"""


def render_page(port: int) -> bytes:
    html = (PAGE_HTML
            .replace("__CSS__", PAGE_CSS)
            .replace("__JS__", PAGE_JS)
            .replace("__VERSION__", VERSION)
            .replace("__PORT__", str(port)))
    return html.encode("utf-8")


# ═══════════════════════════════════════════════════════════════════════
# HTTP handler
# ═══════════════════════════════════════════════════════════════════════
class Handler(BaseHTTPRequestHandler):
    app: App
    page: bytes = b""
    protocol_version = "HTTP/1.1"
    server_version = f"Nocturne/{VERSION}"

    # ── plumbing ───────────────────────────────────────────────────────
    def log_message(self, fmt, *args):
        if self.app.verbose:
            sys.stderr.write("[http] %s\n" % (fmt % args))

    def _local_only(self) -> bool:
        host = (self.headers.get("Host") or "").split(":")[0].strip("[]").lower()
        if host in ("127.0.0.1", "localhost", "::1", ""):
            return True
        self._json({"error": {"code": "forbidden"}}, 403)
        return False

    def _bytes(self, payload: bytes, status: int = 200,
               ctype: str = "text/plain; charset=utf-8",
               extra: dict | None = None, head_only: bool = False) -> None:
        try:
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(payload)))
            self.send_header("X-Content-Type-Options", "nosniff")
            for key, val in (extra or {}).items():
                self.send_header(key, val)
            self.end_headers()
            if not head_only:
                self.wfile.write(payload)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            self.close_connection = True

    def _json(self, obj, status: int = 200, head_only: bool = False) -> None:
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self._bytes(body, status, "application/json; charset=utf-8",
                    {"Cache-Control": "no-store"}, head_only)

    def _body(self) -> dict:
        length = to_int(self.headers.get("Content-Length"), 0)
        if length <= 0:
            return {}
        if length > MAX_BODY:
            raise ApiError("parse", 413)
        try:
            return json.loads(self.rfile.read(length).decode("utf-8", "replace"))
        except ValueError:
            raise ApiError("parse", 400) from None

    # ── verbs ──────────────────────────────────────────────────────────
    def do_GET(self):
        self._dispatch(head_only=False)

    def do_HEAD(self):
        self._dispatch(head_only=True)

    def do_POST(self):
        self._dispatch(head_only=False)

    def _dispatch(self, head_only: bool) -> None:
        if not self._local_only():
            return
        parts = urllib.parse.urlsplit(self.path)
        path = parts.path.rstrip("/") or "/"
        query = urllib.parse.parse_qs(parts.query)
        try:
            handler = ROUTES.get((self.command, path))
            if handler is None:
                # HEAD falls back to the GET handler
                handler = ROUTES.get(("GET", path)) if head_only else None
            if handler is None:
                self._json({"error": {"code": "notfound"}}, 404, head_only)
                return
            handler(self, query, head_only)
        except ApiError as exc:
            self._json({"error": {"code": exc.code, "status": exc.upstream_status}},
                       exc.http_status, head_only)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            self.close_connection = True
        except Exception as exc:  # never take the server down for one bad request
            if self.app.verbose:
                import traceback
                traceback.print_exc()
            self._json({"error": {"code": "upstream", "detail": str(exc)[:200]}}, 500, head_only)

    # ── routes ─────────────────────────────────────────────────────────
    def r_index(self, query, head_only):
        self._bytes(self.page, 200, "text/html; charset=utf-8",
                    {"Cache-Control": "no-store"}, head_only)

    def r_health(self, query, head_only):
        self._json({
            "app": APP_NAME, "version": VERSION,
            "uptime": round(time.time() - self.app.started, 1),
            "cache": {"posts": len(self.app.posts_cache),
                      "ac": len(self.app.ac_cache),
                      "similar": len(self.app.similar_cache)},
        }, 200, head_only)

    def r_config_get(self, query, head_only):
        self._json(self.app.config.get(), 200, head_only)

    def r_config_set(self, query, head_only):
        cfg = self.app.config.update(self._body())
        self.app.drop_caches()
        self._json(cfg)

    def r_config_reset(self, query, head_only):
        cfg = self.app.config.reset()
        self.app.drop_caches()
        self._json(cfg)

    def r_cache_clear(self, query, head_only):
        self.app.drop_caches()
        self._json({"ok": True})

    def r_posts(self, query, head_only):
        tags = (query.get("tags", [""])[0] or "").strip()[:600]
        pid = to_int(query.get("pid", ["0"])[0], 0)
        limit = clamp(to_int(query.get("limit", ["42"])[0], 42), 10, 100)
        self._json(self.app.posts(tags, pid, limit), 200, head_only)

    def r_post(self, query, head_only):
        post_id = to_int(query.get("id", ["0"])[0])
        if post_id <= 0:
            raise ApiError("parse", 400)
        post = fetch_post_by_id(self.app.config.get(), post_id)
        if not post:
            raise ApiError("notfound", 404)
        self._json(post, 200, head_only)

    def r_similar(self, query, head_only):
        post_id = to_int(query.get("id", ["0"])[0])
        if post_id <= 0:
            raise ApiError("parse", 400)
        self._json(self.app.similar(post_id), 200, head_only)

    def r_ac(self, query, head_only):
        term = query.get("q", [""])[0]
        self._json(self.app.autocomplete(term), 200, head_only)

    def r_favorites(self, query, head_only):
        self._json({"posts": self.app.favorites.all()}, 200, head_only)

    def r_favorite_ids(self, query, head_only):
        self._json({"ids": self.app.favorites.ids()}, 200, head_only)

    def r_favorite_toggle(self, query, head_only):
        body = self._body()
        post = body.get("post")
        if not isinstance(post, dict):
            raise ApiError("parse", 400)
        added = self.app.favorites.toggle(post)
        self._json({"favorite": added, "count": len(self.app.favorites.all())})

    def r_favorites_clear(self, query, head_only):
        self.app.favorites.clear()
        self._json({"ok": True})

    # ── media proxy ────────────────────────────────────────────────────
    def r_media(self, query, head_only):
        url = query.get("u", [""])[0]
        if not url or not allowed_media_url(url):
            self._bytes(b"forbidden", 403, "text/plain; charset=utf-8", None, head_only)
            return

        headers = dict(MEDIA_HEADERS)
        rng = self.headers.get("Range")
        if rng:
            headers["Range"] = rng

        try:
            req = urllib.request.Request(url, headers=headers, method="GET")
            resp = urllib.request.urlopen(req, timeout=UPSTREAM_TIMEOUT)
        except urllib.error.HTTPError as exc:
            self._bytes(b"upstream", exc.code if exc.code >= 400 else 502,
                        "text/plain; charset=utf-8", None, head_only)
            return
        except (urllib.error.URLError, TimeoutError, OSError):
            self._bytes(b"unreachable", 504, "text/plain; charset=utf-8", None, head_only)
            return

        with contextlib.closing(resp):
            status = getattr(resp, "status", 200) or 200
            length = resp.headers.get("Content-Length")
            try:
                self.send_response(status)
                self.send_header("Content-Type", resp.headers.get("Content-Type") or "application/octet-stream")
                for name in ("Content-Range", "Last-Modified", "ETag"):
                    value = resp.headers.get(name)
                    if value:
                        self.send_header(name, value)
                self.send_header("Accept-Ranges", "bytes")
                self.send_header("Cache-Control", "private, max-age=86400")
                self.send_header("X-Content-Type-Options", "nosniff")
                if length:
                    self.send_header("Content-Length", length)
                else:
                    # unknown size: cannot keep the connection alive safely
                    self.close_connection = True
                self.end_headers()
                if head_only:
                    return
                shutil.copyfileobj(resp, self.wfile, MEDIA_CHUNK)
            except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
                self.close_connection = True   # the player seeked away, this is normal


ROUTES = {
    ("GET", "/"): Handler.r_index,
    ("GET", "/index.html"): Handler.r_index,
    ("GET", "/api/health"): Handler.r_health,
    ("GET", "/api/config"): Handler.r_config_get,
    ("POST", "/api/config"): Handler.r_config_set,
    ("POST", "/api/config/reset"): Handler.r_config_reset,
    ("POST", "/api/cache/clear"): Handler.r_cache_clear,
    ("GET", "/api/posts"): Handler.r_posts,
    ("GET", "/api/post"): Handler.r_post,
    ("GET", "/api/similar"): Handler.r_similar,
    ("GET", "/api/ac"): Handler.r_ac,
    ("GET", "/api/favorites"): Handler.r_favorites,
    ("GET", "/api/favorites/ids"): Handler.r_favorite_ids,
    ("POST", "/api/favorites/toggle"): Handler.r_favorite_toggle,
    ("POST", "/api/favorites/clear"): Handler.r_favorites_clear,
    ("GET", "/media"): Handler.r_media,
}


# ═══════════════════════════════════════════════════════════════════════
# Server bootstrap
# ═══════════════════════════════════════════════════════════════════════
class Server(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True

    def handle_error(self, request, client_address):
        exc = sys.exc_info()[1]
        if isinstance(exc, (BrokenPipeError, ConnectionResetError, ConnectionAbortedError)):
            return
        super().handle_error(request, client_address)


def pick_port(preferred: int) -> int:
    for candidate in [preferred] + [preferred + i for i in range(1, 20)]:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                sock.bind(("127.0.0.1", candidate))
                return candidate
            except OSError:
                continue
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


APP_BROWSERS = [
    r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
    r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
    r"C:\Program Files\Google\Chrome\Application\chrome.exe",
    r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge",
]


def open_ui(url: str, force_tab: bool) -> None:
    if force_tab:
        webbrowser.open(url)
        return
    exe = next((p for p in APP_BROWSERS if Path(p).exists()), None)
    if exe is None:
        exe = shutil.which("google-chrome") or shutil.which("chromium") or shutil.which("microsoft-edge")
    if exe:
        profile = config_dir() / "browser"
        try:
            subprocess.Popen(
                [exe, f"--app={url}", f"--user-data-dir={profile}",
                 "--window-size=1500,960", "--no-first-run", "--no-default-browser-check"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            return
        except OSError:
            pass
    webbrowser.open(url)


def main() -> int:
    parser = argparse.ArgumentParser(prog="nocturne", description=f"{APP_NAME} {VERSION}")
    parser.add_argument("--port", type=int, default=DEFAULT_PORT, help="preferred port")
    parser.add_argument("--tab", action="store_true", help="open a normal browser tab")
    parser.add_argument("--no-open", action="store_true", help="do not open a window")
    parser.add_argument("--verbose", action="store_true", help="log every request")
    args = parser.parse_args()

    app = App(verbose=args.verbose)
    port = pick_port(args.port)
    url = f"http://127.0.0.1:{port}/"

    Handler.app = app
    Handler.page = render_page(port)

    server = Server(("127.0.0.1", port), Handler)
    thread = threading.Thread(target=server.serve_forever, name="nocturne-http", daemon=True)
    thread.start()

    print(f"{APP_NAME} {VERSION}")
    print(f"  serving  {url}")
    print(f"  config   {app.dir}")
    if port != args.port:
        print(f"  note     port {args.port} was busy")
    print("  ctrl+c to stop")

    if not args.no_open:
        threading.Timer(0.35, open_ui, args=(url, args.tab)).start()

    try:
        while thread.is_alive():
            thread.join(0.5)
    except KeyboardInterrupt:
        print("\n  stopping")
    finally:
        server.shutdown()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
