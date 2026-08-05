#!/usr/bin/env python3
"""
Nocturne — a fast local gallery client for rule34.xxx
═════════════════════════════════════════════════════
• Single file, zero dependencies (Python 3.10+ standard library only).
• Runs a private server on 127.0.0.1 and opens the UI in an app window.
• The browser page talks ONLY to this local server; every request to the
  site (API, autocomplete, images, video) is proxied here with proper
  headers, streaming and HTTP Range support — so video seeking works and
  the browser never contacts the site directly.

What changed in 2.2.0
---------------------
• Infinite scroll no longer dies at the bottom of the feed. The server now
  walks past pages that are fully hidden by the blacklist and tells the
  browser the exact next page to ask for; the browser has three independent
  triggers (observer, scroll, manual button) so it can never get stuck.
• High-quality thumbnails and video previews (samples instead of 150px
  thumbnails, with an automatic fallback ladder when a size is missing).
• "Always full quality" option for the viewer.
• Similar-post search (/api/similar): ranks posts by weighted tag overlap
  against a source post, ignoring generic booru tags.

Usage:
  py nocturne.py               # start + open app window (Edge/Chrome) or tab
  py nocturne.py --tab         # force a normal browser tab
  py nocturne.py --no-open     # just start the server
  py nocturne.py --port N      # preferred port (default 8451)

Config & favorites live in %APPDATA%\\Nocturne (Windows)
or ~/.config/Nocturne (Linux/macOS).
Settings from the previous "Image Shelf" version are migrated automatically.
"""
from __future__ import annotations

import argparse
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

APP_NAME = "Nocturne"
VERSION = "2.2.0"
DEFAULT_PORT = 8451

# ── Upstream endpoints (env-overridable, used by the test harness) ──────────
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

VIDEO_EXTS = {"mp4", "webm", "mov", "m4v"}
UPSTREAM_TIMEOUT = 25
MEDIA_CHUNK = 64 * 1024
MAX_BODY = 1024 * 1024        # request body cap for POST endpoints
MAX_PAGE_WALK = 6             # pages the server may skip when all posts are hidden
SIMILAR_POOL_PAGES = 3        # upstream pages scanned when building a similar list
SIMILAR_POOL_MAX = 300        # ranked results kept per source post

DEFAULT_CONFIG: dict = {
    "api_key": "",
    "user_id": "",
    "per_page": 42,
    "lang": "auto",            # auto | ru | en
    "theme": "dark",           # dark | light
    "density": "cozy",         # compact | cozy | large
    "rating": "all",           # all | safe | questionable | explicit
    "sort": "newest",          # newest | score | random
    "autoplay": True,          # autoplay videos in the viewer
    "muted": True,             # start videos muted
    "hover_preview": True,     # play videos on card hover
    "sidebar": True,           # viewer info panel open by default
    "full_quality": False,     # viewer always loads the original file
    "hq_previews": True,       # grid uses sample-sized thumbs + video frames
    "blacklist": ["loli", "shota", "toddlercon", "cub", "ai_generated"],
}

ALLOWED_ENUMS = {
    "lang": {"auto", "ru", "en"},
    "theme": {"dark", "light"},
    "density": {"compact", "cozy", "large"},
    "rating": {"all", "safe", "questionable", "explicit"},
    "sort": {"newest", "score", "random"},
}

BOOL_KEYS = ("autoplay", "muted", "hover_preview", "sidebar", "full_quality", "hq_previews")

# Tags that say nothing about *what* a post is — excluded when picking the
# fingerprint used for similar-post search.
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


# ═══════════════════════════════════════════════════════════════════════════
# Errors
# ═══════════════════════════════════════════════════════════════════════════
class ApiError(Exception):
    """A structured error surfaced to the UI as {"error": {code, status}}."""

    def __init__(self, code: str, http_status: int = 502, upstream_status: int = 0):
        super().__init__(code)
        self.code = code                    # nokey | auth | rate | network | upstream | parse | notfound
        self.http_status = http_status      # status returned to the browser
        self.upstream_status = upstream_status


# ═══════════════════════════════════════════════════════════════════════════
# Persistence (config + favorites) — atomic writes, thread-safe
# ═══════════════════════════════════════════════════════════════════════════
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
    return base / "Nocturne"


def migrate_legacy_config(target: Path) -> None:
    """Copy settings/favorites from the old 'ImageShelf' folder, once."""
    if target.exists():
        return
    legacy = target.parent / "ImageShelf"
    if not legacy.is_dir():
        return
    try:
        target.mkdir(parents=True, exist_ok=True)
        for name in ("config.json", "favorites.json"):
            src = legacy / name
            if src.is_file():
                shutil.copy2(src, target / name)
        print(f"  ↳ migrated settings from {legacy}")
    except OSError:
        pass


class JsonFile:
    """Small thread-safe JSON document store with atomic writes."""

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


class ConfigStore:
    def __init__(self, path: Path):
        self.file = JsonFile(path, DEFAULT_CONFIG)
        self.revision = 0                   # bumped on save → invalidates caches

    def get(self) -> dict:
        merged = dict(DEFAULT_CONFIG)
        data = self.file.load()
        if isinstance(data, dict):
            merged.update({k: data[k] for k in DEFAULT_CONFIG if k in data})
        return self._sanitize(merged)

    def update(self, patch: dict) -> dict:
        with self.file.lock:
            cfg = self.get()
            for key in DEFAULT_CONFIG:
                if key in patch:
                    cfg[key] = patch[key]
            cfg = self._sanitize(cfg)
            self.file.save(cfg)
            self.revision += 1
        return cfg

    @staticmethod
    def _sanitize(cfg: dict) -> dict:
        out = dict(cfg)
        out["api_key"] = str(out.get("api_key") or "").strip()[:512]
        out["user_id"] = str(out.get("user_id") or "").strip()[:64]
        try:
            out["per_page"] = max(10, min(100, int(out.get("per_page") or 42)))
        except (TypeError, ValueError):
            out["per_page"] = 42
        for key, allowed in ALLOWED_ENUMS.items():
            if out.get(key) not in allowed:
                out[key] = DEFAULT_CONFIG[key]
        for key in BOOL_KEYS:
            out[key] = bool(out.get(key))
        raw_bl = out.get("blacklist")
        if isinstance(raw_bl, str):
            raw_bl = raw_bl.replace(",", "\n").split("\n")
        if not isinstance(raw_bl, list):
            raw_bl = []
        cleaned, seen = [], set()
        for entry in raw_bl:
            tag = str(entry).strip().lower().replace(" ", "_")
            if tag and tag not in seen and len(tag) <= 80:
                seen.add(tag)
                cleaned.append(tag)
            if len(cleaned) >= 400:
                break
        out["blacklist"] = cleaned
        return out


FAVORITE_FIELDS = ("id", "file", "sample", "preview", "w", "h", "sw", "sh", "tags",
                   "score", "rating", "video", "ext", "source", "change", "page_url")


class FavoritesStore:
    def __init__(self, path: Path):
        self.file = JsonFile(path, {"posts": []})

    def all(self) -> list[dict]:
        data = self.file.load()
        posts = data.get("posts") if isinstance(data, dict) else None
        return [p for p in posts if isinstance(p, dict) and p.get("id")] if isinstance(posts, list) else []

    def toggle(self, post: dict) -> bool:
        """Add or remove a post; returns True if it is now a favorite."""
        clean = _clean_favorite(post)
        with self.file.lock:
            posts = self.all()
            kept = [p for p in posts if p.get("id") != clean["id"]]
            added = len(kept) == len(posts)
            if added:
                kept.insert(0, clean)
            self.file.save({"posts": kept})
        return added


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
            clean[key] = _to_int(val)
        elif key == "video":
            clean[key] = bool(val)
        elif val is None:
            clean[key] = None
        else:
            clean[key] = str(val)[:1000]
    return clean


# ═══════════════════════════════════════════════════════════════════════════
# Upstream access
# ═══════════════════════════════════════════════════════════════════════════
def _to_int(value, default: int = 0) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return default


def fetch_bytes(url: str, headers: dict, retries: int = 1) -> bytes:
    """GET a small upstream document with one retry on network failure."""
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
    """Parse a dapi response. Handles XML (with total count), JSON, and the
    site's habit of returning an empty body when there are zero results."""
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
        count = _to_int(root.get("count"), 0)
        return [dict(node.attrib) for node in root.iter("post")], count
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
    pid = _to_int(raw.get("id"))
    if not file_url or not pid:
        return None
    tail = file_url.rsplit("/", 1)[-1].split("?", 1)[0]
    ext = tail.rsplit(".", 1)[-1].lower() if "." in tail else ""
    sample = str(raw.get("sample_url") or "").strip() or None
    if sample == file_url:
        sample = None
    preview = str(raw.get("preview_url") or "").strip() or None
    rating = str(raw.get("rating") or "").strip().lower()[:1]
    return {
        "id": pid,
        "file": file_url,
        "sample": sample,
        "preview": preview,
        "w": _to_int(raw.get("width")),
        "h": _to_int(raw.get("height")),
        "sw": _to_int(raw.get("sample_width")),
        "sh": _to_int(raw.get("sample_height")),
        "tags": str(raw.get("tags") or "").split(),
        "score": _to_int(raw.get("score")),
        "rating": rating if rating in ("s", "q", "e") else "",
        "video": ext in VIDEO_EXTS,
        "ext": ext,
        "source": str(raw.get("source") or "").strip(),
        "change": _to_int(raw.get("change")),
        "page_url": SITE_POST_URL.format(id=pid),
    }


def fetch_posts(cfg: dict, tags: str, pid: int, limit: int) -> tuple[list[dict], int | None]:
    """One dapi page. `pid` is zero-based, exactly like the upstream API."""
    params = {
        "page": "dapi", "s": "post", "q": "index",
        "limit": limit, "pid": max(0, pid), "tags": tags,
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


# ── Similar posts ───────────────────────────────────────────────────────────
def tag_weight(tag: str) -> float:
    """Rough rarity guess. Character/series tags carry the most signal."""
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
    # posts with hundreds of tags match everything; normalise them down
    return round(weight / math.sqrt(len(other) + 8), 4)


class TtlCache:
    """Tiny thread-safe LRU cache with per-entry TTL."""

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


def allowed_media_url(url: str) -> bool:
    try:
        parts = urllib.parse.urlsplit(url)
    except ValueError:
        return False
    host = (parts.hostname or "").lower()
    if not host:
        return False
    extra = {h.strip().lower() for h in os.environ.get("NOCTURNE_MEDIA_ALLOW", "").split(",") if h.strip()}
    if host in extra:
        return parts.scheme in ("http", "https")
    if parts.scheme != "https":
        return False
    return host == "rule34.xxx" or host.endswith(".rule34.xxx")


# ═══════════════════════════════════════════════════════════════════════════
# Application state shared across request threads
# ═══════════════════════════════════════════════════════════════════════════
class App:
    def __init__(self):
        base = config_dir()
        migrate_legacy_config(base)
        self.config = ConfigStore(base / "config.json")
        self.favorites = FavoritesStore(base / "favorites.json")
        self.posts_cache = TtlCache(max_items=64, ttl=90)
        self.ac_cache = TtlCache(max_items=512, ttl=600)
        self.similar_cache = TtlCache(max_items=24, ttl=300)
        self.verbose = False


# ═══════════════════════════════════════════════════════════════════════════
# HTTP handler
# ═══════════════════════════════════════════════════════════════════════════
class Handler(BaseHTTPRequestHandler):
    app: App                                # injected at startup
    protocol_version = "HTTP/1.1"
    server_version = f"Nocturne/{VERSION}"

    # ── Plumbing ────────────────────────────────────────────────────────────
    def log_message(self, fmt, *args):      # keep the console clean
        if self.app.verbose:
            sys.stderr.write("[http] %s\n" % (fmt % args))

    def _guard_host(self) -> bool:
        """Reject non-local Host headers (DNS-rebinding protection)."""
        host = (self.headers.get("Host") or "").split(":")[0].strip("[]").lower()
        if host in ("127.0.0.1", "localhost", "::1", ""):
            return True
        self._send_json({"error": {"code": "forbidden"}}, 403)
        return False

    def _send_bytes(self, payload: bytes, status: int = 200, ctype: str = "text/plain; charset=utf-8",
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
            pass

    def _send_json(self, obj, status: int = 200) -> None:
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self._send_bytes(body, status, "application/json; charset=utf-8",
                         {"Cache-Control": "no-store"})

    def _read_json_body(self) -> dict:
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            length = 0
        if length <= 0 or length > MAX_BODY:
            raise ApiError("parse", 400)
        try:
            data = json.loads(self.rfile.read(length).decode("utf-8"))
        except (ValueError, UnicodeDecodeError):
            raise ApiError("parse", 400) from None
        if not isinstance(data, dict):
            raise ApiError("parse", 400)
        return data

    # ── Routing ─────────────────────────────────────────────────────────────
    def do_GET(self):
        self._route("GET")

    def do_HEAD(self):
        self._route("HEAD")

    def do_POST(self):
        self._route("POST")

    def _route(self, method: str) -> None:
        if not self._guard_host():
            return
        parsed = urllib.parse.urlsplit(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
        try:
            if path == "/" and method in ("GET", "HEAD"):
                self._serve_page(head_only=method == "HEAD")
            elif path == "/media" and method in ("GET", "HEAD"):
                self._serve_media(query, head_only=method == "HEAD")
            elif path == "/api/posts" and method == "GET":
                self._serve_posts(query)
            elif path == "/api/similar" and method == "GET":
                self._serve_similar(query)
            elif path == "/api/autocomplete" and method == "GET":
                self._serve_autocomplete(query)
            elif path == "/api/config" and method == "GET":
                self._send_json({"config": self.app.config.get(), "version": VERSION})
            elif path == "/api/config" and method == "POST":
                cfg = self.app.config.update(self._read_json_body())
                self._send_json({"config": cfg})
            elif path == "/api/favorites" and method == "GET":
                self._send_json({"posts": self.app.favorites.all()})
            elif path == "/api/favorites" and method == "POST":
                body = self._read_json_body()
                fav = self.app.favorites.toggle(body.get("post") or {})
                self._send_json({"favorited": fav})
            else:
                self._send_json({"error": {"code": "notfound"}}, 404)
        except ApiError as exc:
            self._send_json({"error": {"code": exc.code, "status": exc.upstream_status}}, exc.http_status)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass
        except Exception as exc:            # never leak a traceback with secrets into the response
            print(f"[error] {type(exc).__name__}: {exc}", file=sys.stderr)
            self._send_json({"error": {"code": "internal"}}, 500)

    # ── Routes ──────────────────────────────────────────────────────────────
    def _serve_page(self, head_only: bool) -> None:
        html = get_page_html()
        self._send_bytes(
            html, 200, "text/html; charset=utf-8",
            {
                "Cache-Control": "no-store",
                # The page can only ever talk to this local server.
                "Content-Security-Policy": (
                    "default-src 'none'; img-src 'self' data:; media-src 'self'; "
                    "style-src 'unsafe-inline'; script-src 'unsafe-inline'; "
                    "connect-src 'self'; base-uri 'none'; form-action 'none'"
                ),
            },
            head_only=head_only,
        )

    def _require_keys(self) -> dict:
        cfg = self.app.config.get()
        if not cfg["api_key"] or not cfg["user_id"]:
            raise ApiError("nokey", 400)
        return cfg

    def _serve_posts(self, query: dict) -> None:
        cfg = self._require_keys()
        tags = (query.get("tags", [""])[0] or "").strip()
        page = max(1, _to_int(query.get("page", ["1"])[0], 1))
        limit = max(1, min(100, _to_int(query.get("limit", ["0"])[0], 0) or cfg["per_page"]))
        random_mode = "sort:random" in tags

        cache_key = (tags, page, limit, self.app.config.revision)
        if not random_mode:
            cached = self.app.posts_cache.get(cache_key)
            if cached is not None:
                self._send_json(cached)
                return

        matcher = build_blacklist_matcher(cfg["blacklist"])
        visible: list[dict] = []
        hidden = raw_total = 0
        count: int | None = None
        cursor = page
        exhausted = False

        # Walk forward over pages that the blacklist empties out completely.
        # Without this the browser receives an empty page, assumes the feed is
        # over and stops loading — the "scrolling dies at the bottom" bug.
        for _ in range(MAX_PAGE_WALK):
            rows, cnt = fetch_posts(cfg, tags, cursor - 1, limit)
            if cnt is not None:
                count = cnt
            if not rows:
                exhausted = True
                break
            raw_total += len(rows)
            posts = [p for p in (normalize_post(r) for r in rows) if p]
            keep = [p for p in posts if not matcher(p["tags"])]
            hidden += len(posts) - len(keep)
            visible.extend(keep)
            cursor += 1
            if visible or random_mode:
                break

        pages = None
        if count is not None:
            pages = max(1, math.ceil(count / limit)) if count else 0

        payload = {
            "posts": visible,
            "count": count,
            "pages": pages,
            "page": page,
            "next_page": None if exhausted else cursor,
            "limit": limit,
            "raw_count": raw_total,
            "hidden": hidden,
            "exhausted": exhausted,
        }
        if not random_mode:
            self.app.posts_cache.put(cache_key, payload)
        self._send_json(payload)

    def _serve_similar(self, query: dict) -> None:
        cfg = self._require_keys()
        post_id = _to_int(query.get("id", ["0"])[0])
        if post_id <= 0:
            raise ApiError("parse", 400)
        page = max(1, _to_int(query.get("page", ["1"])[0], 1))
        limit = max(1, min(100, _to_int(query.get("limit", ["0"])[0], 0) or cfg["per_page"]))
        hint = (query.get("tags", [""])[0] or "").split()

        key = (post_id, self.app.config.revision)
        bundle = self.app.similar_cache.get(key)
        if bundle is None:
            bundle = self._build_similar(cfg, post_id, hint)
            self.app.similar_cache.put(key, bundle)
        source, pool, basis = bundle

        start = (page - 1) * limit
        chunk = pool[start:start + limit]
        more = start + limit < len(pool)
        self._send_json({
            "posts": chunk,
            "source": source,
            "basis": basis,
            "count": len(pool),
            "pages": max(1, math.ceil(len(pool) / limit)) if pool else 0,
            "page": page,
            "limit": limit,
            "raw_count": len(chunk),
            "hidden": 0,
            "next_page": page + 1 if more else None,
            "exhausted": not more,
        })

    def _build_similar(self, cfg: dict, post_id: int, hint: list[str]):
        source = fetch_post_by_id(cfg, post_id)
        if source is None and hint:
            source = {"id": post_id, "tags": hint, "file": "", "preview": None,
                      "sample": None, "video": False, "ext": "", "rating": "",
                      "score": 0, "w": 0, "h": 0, "page_url": SITE_POST_URL.format(id=post_id)}
        if source is None:
            raise ApiError("notfound", 404)

        src_tags = [t for t in (source.get("tags") or hint) if t]
        basis = signature_tags(src_tags)
        if not basis:
            basis = [t for t in src_tags if t.lower() not in GENERIC_TAGS][:4] or src_tags[:4]
        if not basis:
            return source, [], []

        matcher = build_blacklist_matcher(cfg["blacklist"])
        src_set = set(src_tags)
        query = " ~ ".join(basis) + " sort:score:desc"
        seen = {post_id}
        pool: list[dict] = []
        for pid in range(SIMILAR_POOL_PAGES):
            try:
                rows, _ = fetch_posts(cfg, query, pid, 100)
            except ApiError:
                break
            if not rows:
                break
            for raw in rows:
                post = normalize_post(raw)
                if not post or post["id"] in seen:
                    continue
                seen.add(post["id"])
                if matcher(post["tags"]):
                    continue
                post["similarity"] = similarity(src_set, post["tags"])
                if post["similarity"] <= 0:
                    continue
                pool.append(post)
        pool.sort(key=lambda p: (-p["similarity"], -p["score"]))
        return source, pool[:SIMILAR_POOL_MAX], basis

    def _serve_autocomplete(self, query: dict) -> None:
        term = (query.get("q", [""])[0] or "").strip().lower().replace(" ", "_")
        if len(term) < 2:
            self._send_json({"tags": []})
            return
        cached = self.app.ac_cache.get(term)
        if cached is not None:
            self._send_json({"tags": cached})
            return
        tags: list[dict] = []
        try:
            body = fetch_bytes(f"{AC_ORIGIN}/autocomplete.php?q={urllib.parse.quote(term)}",
                               API_HEADERS, retries=0)
            data = json.loads(body.decode("utf-8-sig", "replace") or "[]")
            if isinstance(data, list):
                for row in data[:15]:
                    if not isinstance(row, dict):
                        continue
                    value = str(row.get("value") or "").strip()
                    if value:
                        tags.append({
                            "value": value,
                            "label": str(row.get("label") or value).strip(),
                            "type": str(row.get("type") or "tag"),
                        })
        except (ApiError, ValueError):
            pass                            # autocomplete is best-effort; never block typing
        self.app.ac_cache.put(term, tags)
        self._send_json({"tags": tags})

    def _serve_media(self, query: dict, head_only: bool) -> None:
        url = (query.get("u", [""])[0] or "").strip()
        if not allowed_media_url(url):
            self._send_json({"error": {"code": "forbidden"}}, 403)
            return
        headers = dict(MEDIA_HEADERS)
        client_range = self.headers.get("Range")
        if client_range and not head_only:
            headers["Range"] = client_range

        req = urllib.request.Request(url, headers=headers, method="HEAD" if head_only else "GET")
        try:
            upstream = urllib.request.urlopen(req, timeout=UPSTREAM_TIMEOUT)
        except urllib.error.HTTPError as exc:
            extra = {}
            if exc.code == 416 and exc.headers.get("Content-Range"):
                extra["Content-Range"] = exc.headers["Content-Range"]
            self._send_bytes(b"", exc.code, "text/plain", extra, head_only=head_only)
            return
        except (urllib.error.URLError, TimeoutError, OSError):
            self._send_bytes(b"", 502, head_only=head_only)
            return

        with upstream:
            status = getattr(upstream, "status", 200) or 200
            up_headers = upstream.headers
            try:
                self.send_response(206 if status == 206 else 200)
                self.send_header("Content-Type", up_headers.get("Content-Type") or "application/octet-stream")
                length = up_headers.get("Content-Length")
                if length:
                    self.send_header("Content-Length", length)
                else:
                    self.close_connection = True
                for name in ("Content-Range", "Accept-Ranges", "Last-Modified", "ETag"):
                    if up_headers.get(name):
                        self.send_header(name, up_headers[name])
                if status == 206 and not up_headers.get("Accept-Ranges"):
                    self.send_header("Accept-Ranges", "bytes")
                self.send_header("Cache-Control", "public, max-age=31536000, immutable")
                self.send_header("X-Content-Type-Options", "nosniff")
                if query.get("dl", ["0"])[0] == "1":
                    name = re.sub(r"[^\w.\-]+", "_", query.get("name", ["media"])[0])[:120]
                    name = name.encode("ascii", "ignore").decode() or "media"   # headers must be latin-1 safe
                    self.send_header("Content-Disposition", f'attachment; filename="{name}"')
                self.end_headers()
                if head_only:
                    return
                while True:
                    chunk = upstream.read(MEDIA_CHUNK)
                    if not chunk:
                        break
                    self.wfile.write(chunk)
            except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
                self.close_connection = True


# ═══════════════════════════════════════════════════════════════════════════
# Page + startup
# ═══════════════════════════════════════════════════════════════════════════
def get_page_html() -> bytes:
    override = os.environ.get("NOCTURNE_HTML")
    if override:
        try:
            return Path(override).read_bytes()
        except OSError:
            pass
    return PAGE.encode("utf-8")


def pick_port(preferred: int) -> int:
    for candidate in range(preferred, preferred + 20):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as probe:
            probe.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                probe.bind(("127.0.0.1", candidate))
                return candidate
            except OSError:
                continue
    raise SystemExit(f"No free port found in {preferred}–{preferred + 19}")


def _app_mode_browser() -> str | None:
    """Find Edge/Chrome/Brave so the UI can open as its own window."""
    if os.name != "nt":
        return None
    roots = [os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"),
             os.environ.get("ProgramFiles", r"C:\Program Files"),
             os.environ.get("LocalAppData", "")]
    tails = [r"Microsoft\Edge\Application\msedge.exe",
             r"Google\Chrome\Application\chrome.exe",
             r"BraveSoftware\Brave-Browser\Application\brave.exe"]
    for tail in tails:
        for root in roots:
            if root:
                path = os.path.join(root, tail)
                if os.path.isfile(path):
                    return path
    return None


def open_ui(url: str, force_tab: bool) -> None:
    if not force_tab:
        exe = _app_mode_browser()
        if exe:
            try:
                subprocess.Popen([exe, f"--app={url}"], stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL)
                return
            except OSError:
                pass
    try:
        webbrowser.open(url)
    except Exception:
        pass


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="nocturne", description=f"{APP_NAME} {VERSION}")
    parser.add_argument("--port", type=int, default=DEFAULT_PORT, help="preferred port (default 8451)")
    parser.add_argument("--tab", action="store_true", help="open in a normal browser tab")
    parser.add_argument("--no-open", action="store_true", help="do not open a browser")
    parser.add_argument("--verbose", action="store_true", help="log every request")
    args = parser.parse_args(argv)

    for stream in (sys.stdout, sys.stderr):     # never crash on exotic console encodings
        try:
            stream.reconfigure(errors="replace")
        except Exception:
            pass

    app = App()
    app.verbose = args.verbose
    Handler.app = app

    port = pick_port(args.port)
    server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    server.daemon_threads = True
    url = f"http://127.0.0.1:{port}/"

    print(f"\n  ☾ {APP_NAME} {VERSION}")
    print(f"  → {url}")
    print(f"  ⚙ {config_dir()}")
    print("  Ctrl+C to stop\n")

    if not args.no_open:
        threading.Timer(0.35, open_ui, (url, args.tab)).start()

    try:
        server.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        print("\n  Bye!")
    finally:
        server.server_close()
    return 0


# ═══════════════════════════════════════════════════════════════════════════
# Embedded UI
# ═══════════════════════════════════════════════════════════════════════════
PAGE = r'''<!doctype html>
<html lang="en" data-theme="dark">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="dark light">
<meta name="referrer" content="no-referrer">
<title>Nocturne</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Cdefs%3E%3ClinearGradient id='g' x1='0' y1='0' x2='1' y2='1'%3E%3Cstop stop-color='%238b7cff'/%3E%3Cstop offset='1' stop-color='%235ea8ff'/%3E%3C/linearGradient%3E%3C/defs%3E%3Cpath d='M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z' fill='url(%23g)'/%3E%3C/svg%3E">
<style>
/* ═══════════════ Design tokens ═══════════════ */
:root{
  --bg:#0b0d12; --surface:#12151d; --surface-2:#171c27; --card:#141824;
  --border:rgba(148,163,199,.13); --border-2:rgba(148,163,199,.24);
  --text:#e9edf5; --dim:#8f98ab; --faint:#5e6678;
  --accent:#8b7cff; --accent-2:#5ea8ff;
  --grad:linear-gradient(135deg,#8b7cff 0%,#5ea8ff 100%);
  --pink:#ff5b87; --ok:#3fd68f; --warn:#ffb454; --bad:#ff5c74;
  --r-s:#3fd68f; --r-q:#ffb454; --r-e:#ff5c74;
  --shadow:0 10px 30px rgba(3,5,10,.45);
  --ease:cubic-bezier(.16,.84,.32,1);
  --rh:230px; --gap:10px;
  color-scheme:dark;
}
html[data-theme="light"]{
  --bg:#eef1f7; --surface:#ffffff; --surface-2:#f6f8fc; --card:#ffffff;
  --border:rgba(30,41,70,.12); --border-2:rgba(30,41,70,.22);
  --text:#1b2334; --dim:#5b6478; --faint:#98a0b3;
  --shadow:0 10px 30px rgba(23,32,58,.13);
  color-scheme:light;
}
*{box-sizing:border-box}
html,body{margin:0;padding:0}
body{
  background:var(--bg); color:var(--text);
  font:14px/1.45 "Segoe UI Variable Text","Segoe UI",system-ui,-apple-system,"Inter",Roboto,sans-serif;
  -webkit-font-smoothing:antialiased; overflow-y:scroll;
  overflow-anchor:none;                       /* stop the browser fighting the infinite feed */
}
body::before{content:""; position:fixed; inset:0; z-index:-1; pointer-events:none;
  background:radial-gradient(60rem 34rem at 12% -12%,rgba(139,124,255,.09),transparent 60%),
             radial-gradient(52rem 30rem at 100% -8%,rgba(94,168,255,.07),transparent 60%);}
body.noscroll{overflow:hidden}
button{font:inherit; color:inherit; background:none; border:0; cursor:pointer; padding:0}
input,select,textarea{font:inherit; color:inherit}
::selection{background:rgba(139,124,255,.35)}
:focus-visible{outline:2px solid var(--accent); outline-offset:2px; border-radius:6px}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-thumb{background:rgba(139,148,171,.25);border-radius:6px;border:2px solid transparent;background-clip:content-box}
::-webkit-scrollbar-thumb:hover{background:rgba(139,148,171,.45);border:2px solid transparent;background-clip:content-box}
::-webkit-scrollbar-track{background:transparent}
.icon{width:18px;height:18px;stroke:currentColor;stroke-width:2;fill:none;stroke-linecap:round;stroke-linejoin:round;flex:none;display:block}
.icon.fill{fill:currentColor;stroke:none}
[hidden]{display:none !important}

/* ═══════════════ Header ═══════════════ */
#progress{position:fixed;left:0;right:0;top:0;height:2px;z-index:100;overflow:hidden;pointer-events:none}
#progress::after{content:"";position:absolute;top:0;bottom:0;width:34%;border-radius:0 3px 3px 0;
  background:var(--grad);animation:sweep 1.15s var(--ease) infinite}
@keyframes sweep{0%{transform:translateX(-110%)}100%{transform:translateX(400%)}}

#topbar{position:sticky;top:0;z-index:40;
  background:color-mix(in srgb,var(--bg) 84%,transparent);
  -webkit-backdrop-filter:blur(16px) saturate(1.4); backdrop-filter:blur(16px) saturate(1.4);
  border-bottom:1px solid var(--border)}
.bar{display:flex;align-items:center;gap:12px;max-width:1900px;margin:0 auto;padding:0 18px}
.row1{height:62px}
.row2{height:48px;padding-bottom:6px}
.row2.off{opacity:.35;pointer-events:none}
.brand{display:flex;align-items:center;gap:10px;font-size:16px;font-weight:700;letter-spacing:.2px;white-space:nowrap;user-select:none}
.brand .mark{width:26px;height:26px;border-radius:8px;background:var(--grad);display:grid;place-items:center;box-shadow:0 4px 14px rgba(139,124,255,.4)}
.brand .mark svg{width:14px;height:14px;fill:none;stroke:#fff;stroke-width:2.4;stroke-linecap:round;stroke-linejoin:round}
.brand small{color:var(--faint);font-weight:500;font-size:11px;margin-top:3px}

#searchwrap{position:relative;flex:1;min-width:200px;max-width:860px;margin:0 auto}
.searchbox{display:flex;align-items:center;gap:6px;flex-wrap:wrap;
  background:var(--surface); border:1px solid var(--border-2); border-radius:14px;
  padding:5px 6px 5px 12px; min-height:42px; transition:border-color .15s, box-shadow .15s}
.searchbox:focus-within{border-color:var(--accent); box-shadow:0 0 0 3px rgba(139,124,255,.18)}
.searchbox>.icon{color:var(--faint)}
#chips{display:contents}
.chip{display:inline-flex;align-items:center;gap:6px;background:rgba(139,124,255,.16);
  border:1px solid rgba(139,124,255,.35); color:var(--text);
  border-radius:9px;padding:3px 6px 3px 9px;font-size:13px;font-weight:600;max-width:260px;animation:pop .16s ease}
.chip .t{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.chip.neg{background:rgba(255,92,116,.13);border-color:rgba(255,92,116,.4)}
.chip.sim{background:rgba(94,168,255,.15);border-color:rgba(94,168,255,.42)}
.chip button{display:grid;place-items:center;width:18px;height:18px;border-radius:6px;color:var(--dim)}
.chip button:hover{background:rgba(255,255,255,.14);color:var(--text)}
.chip button .icon{width:12px;height:12px}
#q{flex:1;min-width:130px;background:none;border:0;outline:0;padding:6px 2px;font-size:14px}
#q::placeholder{color:var(--faint)}
#go{display:flex;align-items:center;gap:7px;background:var(--grad);color:#fff;font-weight:600;
  border-radius:10px;padding:8px 16px;box-shadow:0 4px 14px rgba(110,140,255,.3);transition:filter .15s,transform .1s}
#go:hover{filter:brightness(1.1)} #go:active{transform:scale(.97)}
#go .icon{width:15px;height:15px}

#acbox{position:absolute;top:calc(100% + 6px);left:0;right:0;z-index:50;
  background:var(--surface); border:1px solid var(--border-2); border-radius:14px;
  box-shadow:var(--shadow); overflow:hidden; padding:5px; max-height:330px; overflow-y:auto}
.acrow{display:flex;align-items:center;gap:10px;width:100%;text-align:left;
  padding:8px 10px;border-radius:9px;font-size:13.5px}
.acrow .icon{width:15px;height:15px;color:var(--faint)}
.acrow .lbl{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.acrow .cnt{color:var(--faint);font-size:12px;font-variant-numeric:tabular-nums}
.acrow:hover,.acrow.on{background:rgba(139,124,255,.14)}
.achead{color:var(--faint);font-size:11.5px;text-transform:uppercase;letter-spacing:.8px;padding:7px 10px 3px}
.acclear{display:flex;align-items:center;gap:10px;width:100%;text-align:left;padding:8px 10px;border-radius:9px;
  color:var(--dim);font-size:12.5px}
.acclear:hover{background:var(--surface-2)}
.acclear .icon{width:13px;height:13px}

.hdr-actions{display:flex;align-items:center;gap:6px}
.iconbtn{position:relative;display:grid;place-items:center;width:38px;height:38px;border-radius:11px;
  color:var(--dim);border:1px solid transparent;transition:background .15s,color .15s}
.iconbtn:hover{background:var(--surface-2);color:var(--text);border-color:var(--border)}
.iconbtn.txt{font-weight:700;font-size:12.5px;letter-spacing:.5px}
.iconbtn.active{color:var(--accent);background:rgba(139,124,255,.13);border-color:rgba(139,124,255,.3)}
.iconbtn .pill{position:absolute;top:-4px;right:-5px;background:var(--pink);color:#fff;
  font-size:10px;font-weight:700;border-radius:999px;min-width:17px;height:17px;line-height:17px;
  text-align:center;padding:0 4px;box-shadow:0 2px 6px rgba(255,91,135,.5)}
#favbtn.active{color:var(--pink);background:rgba(255,91,135,.12);border-color:rgba(255,91,135,.3)}

.seg{display:flex;background:var(--surface);border:1px solid var(--border);border-radius:11px;padding:3px;gap:2px}
.seg button{padding:6px 12px;border-radius:8px;font-size:12.5px;font-weight:600;color:var(--dim);
  display:flex;align-items:center;gap:6px;transition:background .13s,color .13s;white-space:nowrap}
.seg button:hover{color:var(--text)}
.seg button.on{background:var(--surface-2);color:var(--text);box-shadow:inset 0 0 0 1px var(--border-2)}
.seg button.on[data-r="safe"]{color:var(--r-s)} .seg button.on[data-r="questionable"]{color:var(--r-q)} .seg button.on[data-r="explicit"]{color:var(--r-e)}
.seg .icon{width:14px;height:14px}
.selectwrap{position:relative}
.selectwrap select{appearance:none;background:var(--surface);border:1px solid var(--border);border-radius:11px;
  padding:8px 30px 8px 12px;font-size:12.5px;font-weight:600;color:var(--text);cursor:pointer;outline:none}
.selectwrap::after{content:"";position:absolute;right:11px;top:50%;width:7px;height:7px;pointer-events:none;
  border-right:2px solid var(--faint);border-bottom:2px solid var(--faint);transform:translateY(-70%) rotate(45deg)}
.spacer{flex:1}
.stats{color:var(--dim);font-size:12.5px;white-space:nowrap;display:flex;gap:14px;align-items:center;font-variant-numeric:tabular-nums}
.stats b{color:var(--text);font-weight:600}
.stats .hid{color:var(--warn)}

/* ═══════════════ Main / grid ═══════════════ */
main{max-width:1900px;margin:0 auto;padding:14px 18px 40px}
.grid{display:flex;flex-wrap:wrap;gap:var(--gap)}
.grid::after{content:"";flex-grow:1000000;flex-basis:0}
.card{position:relative;overflow:hidden;border-radius:14px;background:var(--card);
  flex-grow:calc(var(--ar,1)*100);flex-basis:calc(var(--ar,1)*var(--rh));
  max-width:calc(var(--ar,1)*var(--rh)*2.3);aspect-ratio:var(--ar,1);
  border:1px solid var(--border);cursor:pointer;
  animation:rise .3s var(--ease) both;
  transition:transform .18s var(--ease),box-shadow .18s ease,border-color .18s ease}
.card:hover,.card:focus-visible{transform:translateY(-3px);box-shadow:var(--shadow);border-color:var(--border-2)}
.card>img,.card video.hoverv{position:absolute;inset:0;width:100%;height:100%;object-fit:cover}
.card>img{transition:transform .45s var(--ease),opacity .3s;opacity:0}
.card>img.ld{opacity:1}
.card:hover>img{transform:scale(1.04)}
.card video.hoverv{opacity:0;transition:opacity .25s}
.card video.hoverv.on{opacity:1}
.card:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
.c-top{position:absolute;top:8px;right:8px;display:flex;gap:5px;z-index:2}
.badge{font-size:10.5px;font-weight:800;letter-spacing:.4px;border-radius:7px;padding:3px 6px;
  background:rgba(8,10,16,.72);color:#fff;-webkit-backdrop-filter:blur(4px);backdrop-filter:blur(4px);
  display:flex;align-items:center;gap:4px}
.badge .icon{width:11px;height:11px}
.badge.r-s{color:var(--r-s)} .badge.r-q{color:var(--r-q)} .badge.r-e{color:var(--r-e)}
.badge.match{color:var(--accent-2)}
.c-acts{position:absolute;top:8px;left:8px;z-index:3;display:flex;flex-direction:column;gap:6px}
.cbtn{display:grid;place-items:center;width:32px;height:32px;border-radius:10px;
  background:rgba(8,10,16,.62);-webkit-backdrop-filter:blur(4px);backdrop-filter:blur(4px);
  color:#fff;opacity:0;transform:translateY(-4px);transition:opacity .18s,transform .18s,color .15s,background .15s}
.card:hover .cbtn,.card:focus-within .cbtn,.cbtn.active{opacity:1;transform:none}
.cbtn:hover{background:rgba(8,10,16,.85)}
.cbtn.fv:hover{color:var(--pink)}
.cbtn.fv.active{color:var(--pink)} .cbtn.fv.active .icon{fill:var(--pink);stroke:var(--pink)}
.cbtn.dlb:hover{color:var(--accent-2)}
.cbtn.smb:hover{color:var(--accent)}
.cbtn .icon{width:16px;height:16px}
.c-meta{position:absolute;left:0;right:0;bottom:0;z-index:2;display:flex;flex-direction:column;gap:3px;
  padding:22px 11px 9px;color:#fff;pointer-events:none;
  background:linear-gradient(to top,rgba(4,6,10,.82),rgba(4,6,10,.32) 62%,transparent);
  opacity:0;transform:translateY(6px);transition:opacity .18s,transform .18s}
.card:hover .c-meta,.card:focus-visible .c-meta{opacity:1;transform:none}
.c-meta .row{display:flex;justify-content:space-between;align-items:center;font-size:11.5px;font-weight:650;
  text-shadow:0 1px 4px rgba(0,0,0,.8)}
.c-meta .sc{display:flex;align-items:center;gap:4px}
.c-meta .row .icon{width:12px;height:12px;fill:currentColor;stroke:none}
.c-meta .tgs{font-size:10.5px;font-weight:500;color:rgba(255,255,255,.72);white-space:nowrap;
  overflow:hidden;text-overflow:ellipsis;text-shadow:0 1px 3px rgba(0,0,0,.8)}
.c-play{position:absolute;inset:0;display:grid;place-items:center;z-index:1;pointer-events:none}
.c-play span{display:grid;place-items:center;width:46px;height:46px;border-radius:50%;
  background:rgba(8,10,16,.55);-webkit-backdrop-filter:blur(3px);backdrop-filter:blur(3px);
  box-shadow:0 4px 16px rgba(0,0,0,.4);transition:transform .2s,opacity .2s}
.card:hover .c-play span{transform:scale(1.1)}
.card.playing .c-play span{opacity:0}
.c-play .icon{width:19px;height:19px;fill:#fff;stroke:none;margin-left:2px}
.card.broken{display:grid;place-items:center;color:var(--faint)}
.card.broken>img{display:none}
.skel{position:relative;overflow:hidden;border-radius:14px;background:var(--card);border:1px solid var(--border);
  flex-grow:calc(var(--ar,1)*100);flex-basis:calc(var(--ar,1)*var(--rh));aspect-ratio:var(--ar,1);
  max-width:calc(var(--ar,1)*var(--rh)*2.3)}
.skel::after{content:"";position:absolute;inset:0;
  background:linear-gradient(100deg,transparent 30%,rgba(148,163,199,.09) 50%,transparent 70%);
  animation:shimmer 1.4s infinite}
@keyframes shimmer{from{transform:translateX(-100%)}to{transform:translateX(100%)}}
@keyframes rise{from{opacity:0;transform:translateY(10px) scale(.985)}to{opacity:1;transform:none}}
@keyframes pop{from{opacity:0;transform:scale(.9)}to{opacity:1;transform:none}}

#sentinel{display:flex;flex-direction:column;align-items:center;gap:12px;padding:26px 0 6px;min-height:78px}
.spinner{width:26px;height:26px;border-radius:50%;border:3px solid var(--border-2);
  border-top-color:var(--accent);animation:spin .8s linear infinite}
@keyframes spin{to{transform:rotate(1turn)}}
#loadmore{display:flex;align-items:center;gap:8px;background:var(--surface);border:1px solid var(--border-2);
  border-radius:12px;padding:10px 20px;font-weight:600;font-size:13px;color:var(--dim);transition:color .15s,border-color .15s}
#loadmore:hover{color:var(--text);border-color:var(--accent)}
#loadmore .icon{width:14px;height:14px}
#endnote{text-align:center;color:var(--faint);font-size:12.5px;padding:18px 0 6px;letter-spacing:.3px}
#endnote b{color:var(--dim)}

#notice{display:flex;align-items:center;gap:12px;background:rgba(255,92,116,.09);
  border:1px solid rgba(255,92,116,.3);border-radius:14px;padding:12px 16px;margin-bottom:14px;font-size:13.5px}
#notice .icon{color:var(--bad)}
#notice .msg{flex:1}
#notice button.retry{background:var(--surface-2);border:1px solid var(--border-2);border-radius:9px;
  padding:7px 14px;font-weight:600;font-size:12.5px}
#notice button.retry:hover{border-color:var(--accent);color:var(--accent)}

#simbar{display:flex;align-items:center;gap:14px;margin-bottom:16px;padding:10px 14px;
  border:1px solid rgba(94,168,255,.28);border-radius:16px;
  background:linear-gradient(100deg,rgba(94,168,255,.13),rgba(139,124,255,.06) 55%,transparent)}
#simbar img{width:52px;height:52px;border-radius:11px;object-fit:cover;border:1px solid var(--border-2);flex:none}
#simbar .who{min-width:0;flex:1}
#simbar .who .h{font-size:13.5px;font-weight:650}
#simbar .who .basis{margin-top:3px;color:var(--dim);font-size:11.5px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#simbar .who .basis span{color:var(--accent-2)}
#simbar .exit{display:flex;align-items:center;gap:7px;border:1px solid var(--border-2);border-radius:10px;
  padding:8px 13px;font-size:12.5px;font-weight:600;color:var(--dim)}
#simbar .exit:hover{color:var(--text);border-color:var(--accent)}
#simbar .exit .icon{width:14px;height:14px}

#hero{display:flex;flex-direction:column;align-items:center;justify-content:center;
  text-align:center;padding:80px 20px;color:var(--dim)}
#hero .big{width:74px;height:74px;border-radius:22px;background:var(--surface);border:1px solid var(--border);
  display:grid;place-items:center;margin-bottom:22px;box-shadow:var(--shadow)}
#hero .big .icon{width:32px;height:32px;color:var(--accent);stroke-width:1.6}
#hero h2{margin:0 0 8px;font-size:21px;color:var(--text);font-weight:700}
#hero p{margin:0 0 6px;max-width:440px;font-size:14px}
#hero .path{font-size:12.5px;color:var(--faint);background:var(--surface);border:1px solid var(--border);
  border-radius:9px;padding:6px 12px;margin-top:10px;font-family:Consolas,monospace}
#hero .cta{margin-top:22px;background:var(--grad);color:#fff;font-weight:600;border-radius:12px;
  padding:11px 22px;box-shadow:0 6px 20px rgba(110,140,255,.35)}
#hero .cta:hover{filter:brightness(1.08)}

#totop{position:fixed;right:22px;bottom:22px;z-index:35;display:grid;place-items:center;width:44px;height:44px;
  border-radius:14px;background:var(--surface);border:1px solid var(--border-2);color:var(--dim);
  box-shadow:var(--shadow);transition:transform .15s,color .15s}
#totop:hover{color:var(--text);transform:translateY(-2px)}

/* ═══════════════ Viewer ═══════════════ */
#viewer{position:fixed;inset:0;z-index:60;display:flex;flex-direction:column;
  background:rgba(5,7,11,.9);-webkit-backdrop-filter:blur(18px);backdrop-filter:blur(18px);
  animation:fade .16s ease}
@keyframes fade{from{opacity:0}}
.v-top{display:flex;align-items:center;gap:10px;height:58px;padding:0 14px;flex:none}
.v-title{display:flex;align-items:center;gap:12px;color:#cfd6e4;font-size:13px;min-width:0;font-variant-numeric:tabular-nums}
.v-title .vid{font-weight:700;color:#fff;white-space:nowrap}
.v-title .badge{position:static}
.v-title .dims,.v-title .cnt{color:#8f98ab;white-space:nowrap}
.v-title .sc{display:flex;align-items:center;gap:4px;color:#ffb0c6}
.v-title .sc .icon{width:12px;height:12px;fill:currentColor;stroke:none}
.v-actions{margin-left:auto;display:flex;gap:5px;align-items:center}
.vbtn{display:grid;place-items:center;width:40px;height:40px;border-radius:12px;color:#aab3c5;
  transition:background .15s,color .15s}
.vbtn:hover{background:rgba(255,255,255,.09);color:#fff}
.vbtn.active{color:var(--accent);background:rgba(139,124,255,.16)}
.vbtn.fav.active{color:var(--pink);background:rgba(255,91,135,.14)}
.vbtn.fav.active .icon{fill:var(--pink);stroke:var(--pink)}
.vbtn.txt{font-size:11.5px;font-weight:800;letter-spacing:.5px;width:auto;padding:0 12px}
.v-body{flex:1;display:flex;min-height:0}
.v-stage{flex:1;position:relative;display:flex;align-items:center;justify-content:center;overflow:hidden;min-width:0}
.v-stage.zoomed{cursor:grab}
.v-stage.zoomed.panning{cursor:grabbing}
.v-holder{max-width:calc(100% - 36px);max-height:calc(100% - 16px);display:flex;align-items:center;justify-content:center;will-change:transform}
.v-holder img,.v-holder video{max-width:100%;max-height:calc(100vh - 90px);object-fit:contain;border-radius:6px;
  box-shadow:0 20px 60px rgba(0,0,0,.5);user-select:none;-webkit-user-drag:none}
.v-holder img{cursor:zoom-in}
.v-stage.zoomed .v-holder img{cursor:inherit}
.v-load{position:absolute;inset:0;display:grid;place-items:center;pointer-events:none}
.v-err{color:var(--bad);display:flex;flex-direction:column;align-items:center;gap:10px;font-size:13.5px}
.v-err .icon{width:30px;height:30px}
.v-nav{position:absolute;top:0;bottom:0;width:84px;z-index:5;display:grid;place-items:center;color:rgba(255,255,255,.22);
  transition:color .15s;border-radius:0}
.v-nav:hover{color:#fff;background:linear-gradient(to right,rgba(5,7,11,.35),transparent)}
.v-nav.next:hover{background:linear-gradient(to left,rgba(5,7,11,.35),transparent)}
.v-nav.prev{left:0}.v-nav.next{right:0}
.v-nav .icon{width:34px;height:34px;stroke-width:2.4;filter:drop-shadow(0 2px 8px rgba(0,0,0,.6))}
.v-nav[disabled]{pointer-events:none;opacity:0}
#viewer:not(.hasinfo) .v-info{display:none}
.v-info{width:342px;flex:none;background:color-mix(in srgb,var(--surface) 88%,transparent);
  border-left:1px solid var(--border);overflow-y:auto;padding:16px 18px;animation:slidein .18s ease}
@keyframes slidein{from{transform:translateX(30px);opacity:0}}
.v-info h4{margin:14px 0 8px;font-size:11px;font-weight:700;letter-spacing:1.1px;text-transform:uppercase;color:var(--faint)}
.v-info h4:first-child{margin-top:0}
.tagrow{display:flex;align-items:center;gap:4px;border-radius:9px;padding:3px 4px 3px 2px}
.tagrow:hover{background:rgba(139,124,255,.09)}
.tagrow .tg{flex:1;text-align:left;font-size:13px;color:var(--text);padding:4px 6px;border-radius:7px;
  overflow-wrap:anywhere}
.tagrow .tg:hover{color:var(--accent)}
.tagrow .mini{display:none;place-items:center;width:24px;height:24px;border-radius:7px;color:var(--faint)}
.tagrow:hover .mini{display:grid}
.tagrow .mini:hover{background:var(--surface-2);color:var(--text)}
.tagrow .mini .icon{width:13px;height:13px}
.meta-t{width:100%;border-collapse:collapse;font-size:13px}
.meta-t td{padding:5px 0;vertical-align:top}
.meta-t td:first-child{color:var(--faint);width:88px}
.meta-t a{color:var(--accent-2);text-decoration:none;overflow-wrap:anywhere}
.meta-t a:hover{text-decoration:underline}
.v-info .rowbtns{display:flex;gap:8px;margin-top:14px;flex-wrap:wrap}
.sbtn{display:flex;align-items:center;gap:7px;background:var(--surface-2);border:1px solid var(--border-2);
  border-radius:10px;padding:8px 12px;font-size:12.5px;font-weight:600;color:var(--text)}
.sbtn:hover{border-color:var(--accent);color:var(--accent)}
.sbtn.wide{width:100%;justify-content:center;margin-top:12px;padding:10px 12px}
.sbtn .icon{width:14px;height:14px}

/* ═══════════════ Modal / settings ═══════════════ */
.modal{position:fixed;inset:0;z-index:70;display:grid;place-items:center;padding:20px;
  background:rgba(5,7,11,.6);-webkit-backdrop-filter:blur(8px);backdrop-filter:blur(8px);animation:fade .15s ease}
.sheet{width:min(600px,100%);max-height:calc(100vh - 60px);overflow-y:auto;background:var(--surface);
  border:1px solid var(--border-2);border-radius:20px;box-shadow:var(--shadow);padding:24px 26px;
  animation:sheetin .2s var(--ease)}
@keyframes sheetin{from{opacity:0;transform:translateY(14px) scale(.98)}}
.sheet h2{margin:0 0 4px;font-size:19px;display:flex;align-items:center;gap:10px}
.sheet h2 .icon{color:var(--accent)}
.sheet .sub{color:var(--faint);font-size:12.5px;margin:0 0 18px}
.sheet h3{margin:20px 0 10px;font-size:11px;font-weight:700;letter-spacing:1.1px;text-transform:uppercase;color:var(--faint);
  border-top:1px solid var(--border);padding-top:16px}
.sheet h3:first-of-type{border-top:0;padding-top:0;margin-top:8px}
.frow{display:flex;gap:10px;align-items:center;margin-bottom:10px}
.frow label.fl{width:130px;flex:none;color:var(--dim);font-size:13px}
.fin{flex:1;display:flex;align-items:center;gap:6px;background:var(--surface-2);border:1px solid var(--border-2);
  border-radius:10px;padding:0 6px 0 12px;min-height:38px;transition:border-color .15s}
.fin:focus-within{border-color:var(--accent)}
.fin input{flex:1;background:none;border:0;outline:0;min-width:0;font-size:13.5px}
.fin .peek{display:grid;place-items:center;width:28px;height:28px;border-radius:8px;color:var(--faint)}
.fin .peek:hover{color:var(--text);background:var(--surface)}
.fin .peek .icon{width:15px;height:15px}
.hint{color:var(--faint);font-size:12px;margin:2px 0 12px;line-height:1.5}
.hint code{background:var(--surface-2);border:1px solid var(--border);border-radius:6px;padding:1px 6px;font-size:11px}
.checkrow{display:flex;align-items:flex-start;gap:10px;padding:7px 0;font-size:13.5px;cursor:pointer;user-select:none}
.checkrow input{width:17px;height:17px;accent-color:var(--accent);cursor:pointer;margin:1px 0 0}
.checkrow em{display:block;font-style:normal;color:var(--faint);font-size:11.5px;margin-top:2px}
.selrow select{background:var(--surface-2);border:1px solid var(--border-2);border-radius:10px;
  padding:8px 12px;font-size:13px;outline:none;cursor:pointer;min-width:150px}
textarea#blacklist{width:100%;min-height:110px;background:var(--surface-2);border:1px solid var(--border-2);
  border-radius:10px;padding:10px 12px;font:12.5px/1.6 Consolas,monospace;outline:none;resize:vertical}
textarea#blacklist:focus{border-color:var(--accent)}
.sheet .foot{display:flex;gap:10px;align-items:center;margin-top:20px;padding-top:16px;border-top:1px solid var(--border)}
.sheet .foot .status{flex:1;font-size:12.5px;color:var(--dim);min-height:18px}
.sheet .foot .status.ok{color:var(--ok)} .sheet .foot .status.bad{color:var(--bad)}
.btn{display:inline-flex;align-items:center;gap:8px;border-radius:11px;padding:9px 16px;font-weight:600;font-size:13px;
  background:var(--surface-2);border:1px solid var(--border-2);transition:filter .15s,border-color .15s}
.btn:hover{border-color:var(--accent)}
.btn.primary{background:var(--grad);border:0;color:#fff;box-shadow:0 4px 14px rgba(110,140,255,.3)}
.btn.primary:hover{filter:brightness(1.1)}
.btn .icon{width:15px;height:15px}
.kbdhint{margin-top:14px;color:var(--faint);font-size:11.5px;line-height:1.7}
kbd{background:var(--surface-2);border:1px solid var(--border-2);border-bottom-width:2px;border-radius:5px;
  padding:0 5px;font:11px Consolas,monospace;color:var(--dim)}

/* ═══════════════ Toasts ═══════════════ */
#toasts{position:fixed;right:18px;bottom:18px;z-index:90;display:flex;flex-direction:column;gap:8px;align-items:flex-end}
.toast{display:flex;align-items:center;gap:10px;background:var(--surface);border:1px solid var(--border-2);
  border-radius:12px;padding:11px 15px;font-size:13px;box-shadow:var(--shadow);max-width:360px;cursor:pointer;
  animation:toastin .22s var(--ease)}
.toast.err{border-color:rgba(255,92,116,.5)} .toast.err .icon{color:var(--bad)}
.toast.ok .icon{color:var(--ok)}
.toast .icon{width:16px;height:16px;flex:none}
@keyframes toastin{from{opacity:0;transform:translateY(10px) scale(.96)}}
.toast.out{transition:opacity .25s,transform .25s;opacity:0;transform:translateY(6px)}

/* ═══════════════ Responsive ═══════════════ */
@media (max-width:900px){
  .row1{flex-wrap:wrap;height:auto;padding-top:10px;padding-bottom:4px}
  #searchwrap{order:3;flex-basis:100%;margin:6px 0 8px}
  .row2{overflow-x:auto;scrollbar-width:none}
  .row2::-webkit-scrollbar{display:none}
  .stats{display:none}
  .v-info{position:absolute;right:0;top:58px;bottom:0;z-index:8;box-shadow:var(--shadow)}
  .brand small{display:none}
  #simbar{flex-wrap:wrap}
  #simbar .exit{flex:1}
}
@media (prefers-reduced-motion:reduce){
  *,*::before,*::after{animation-duration:.01ms !important;transition-duration:.01ms !important}
}
</style>
</head>
<body>

<svg width="0" height="0" style="position:absolute" aria-hidden="true"><defs>
<symbol id="i-search" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><path d="M21 21l-4.3-4.3"/></symbol>
<symbol id="i-heart" viewBox="0 0 24 24"><path d="M20.8 4.6a5.5 5.5 0 0 0-7.8 0L12 5.7l-1-1.1a5.5 5.5 0 0 0-7.8 7.8l1.1 1L12 21.2l7.7-7.8 1.1-1a5.5 5.5 0 0 0 0-7.8z"/></symbol>
<symbol id="i-dl" viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><path d="M7 10l5 5 5-5"/><path d="M12 15V3"/></symbol>
<symbol id="i-x" viewBox="0 0 24 24"><path d="M18 6L6 18M6 6l12 12"/></symbol>
<symbol id="i-chevl" viewBox="0 0 24 24"><path d="M15 18l-6-6 6-6"/></symbol>
<symbol id="i-chevr" viewBox="0 0 24 24"><path d="M9 18l6-6-6-6"/></symbol>
<symbol id="i-info" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M12 16v-4M12 8h.01"/></symbol>
<symbol id="i-ext" viewBox="0 0 24 24"><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/><path d="M15 3h6v6"/><path d="M10 14L21 3"/></symbol>
<symbol id="i-play" viewBox="0 0 24 24"><path d="M6 3.5l14 8.5-14 8.5z"/></symbol>
<symbol id="i-sun" viewBox="0 0 24 24"><circle cx="12" cy="12" r="4.5"/><path d="M12 1.5v3M12 19.5v3M4.6 4.6l2.1 2.1M17.3 17.3l2.1 2.1M1.5 12h3M19.5 12h3M4.6 19.4l2.1-2.1M17.3 6.7l2.1-2.1"/></symbol>
<symbol id="i-moon" viewBox="0 0 24 24"><path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z"/></symbol>
<symbol id="i-sliders" viewBox="0 0 24 24"><path d="M4 21v-7M4 10V3M12 21v-9M12 8V3M20 21v-5M20 12V3M1 14h6M9 8h6M17 16h6"/></symbol>
<symbol id="i-copy" viewBox="0 0 24 24"><rect x="9" y="9" width="13" height="13" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/></symbol>
<symbol id="i-check" viewBox="0 0 24 24"><path d="M20 6L9 17l-5-5"/></symbol>
<symbol id="i-clock" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M12 6v6l4 2"/></symbol>
<symbol id="i-img" viewBox="0 0 24 24"><rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="M21 15l-5-5L5 21"/></symbol>
<symbol id="i-max" viewBox="0 0 24 24"><path d="M8 3H5a2 2 0 0 0-2 2v3M16 3h3a2 2 0 0 1 2 2v3M8 21H5a2 2 0 0 1-2-2v-3M16 21h3a2 2 0 0 0 2-2v-3"/></symbol>
<symbol id="i-loop" viewBox="0 0 24 24"><path d="M17 1l4 4-4 4"/><path d="M3 11V9a4 4 0 0 1 4-4h14"/><path d="M7 23l-4-4 4-4"/><path d="M21 13v2a4 4 0 0 1-4 4H3"/></symbol>
<symbol id="i-plus" viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></symbol>
<symbol id="i-minus" viewBox="0 0 24 24"><path d="M5 12h14"/></symbol>
<symbol id="i-up" viewBox="0 0 24 24"><path d="M12 19V5M5 12l7-7 7 7"/></symbol>
<symbol id="i-key" viewBox="0 0 24 24"><circle cx="7.5" cy="15.5" r="4.5"/><path d="M11 12l10-10M16 7l3 3"/></symbol>
<symbol id="i-eye" viewBox="0 0 24 24"><path d="M1 12s4-7.5 11-7.5S23 12 23 12s-4 7.5-11 7.5S1 12 1 12z"/><circle cx="12" cy="12" r="3"/></symbol>
<symbol id="i-alert" viewBox="0 0 24 24"><path d="M10.3 3.9L1.8 18a2 2 0 0 0 1.7 3h17a2 2 0 0 0 1.7-3L13.7 3.9a2 2 0 0 0-3.4 0z"/><path d="M12 9v4M12 17h.01"/></symbol>
<symbol id="i-tag" viewBox="0 0 24 24"><path d="M20.6 13.4L12 22 2 12V2h10l8.6 8.6a2 2 0 0 1 0 2.8z"/><circle cx="7.5" cy="7.5" r="1.2"/></symbol>
<symbol id="i-similar" viewBox="0 0 24 24"><rect x="3" y="3" width="9" height="9" rx="2"/><rect x="12" y="12" width="9" height="9" rx="2"/><path d="M15.5 7.5h3M17 6v3M6 15.5h3M7.5 14v3"/></symbol>
<symbol id="i-back" viewBox="0 0 24 24"><path d="M19 12H5M11 18l-6-6 6-6"/></symbol>
<symbol id="i-d1" viewBox="0 0 24 24"><rect x="3" y="3" width="18" height="18" rx="3"/></symbol>
<symbol id="i-d2" viewBox="0 0 24 24"><rect x="3" y="3" width="8" height="8" rx="2"/><rect x="13" y="3" width="8" height="8" rx="2"/><rect x="3" y="13" width="8" height="8" rx="2"/><rect x="13" y="13" width="8" height="8" rx="2"/></symbol>
<symbol id="i-d3" viewBox="0 0 24 24"><rect x="3" y="3" width="5" height="5" rx="1.4"/><rect x="9.5" y="3" width="5" height="5" rx="1.4"/><rect x="16" y="3" width="5" height="5" rx="1.4"/><rect x="3" y="9.5" width="5" height="5" rx="1.4"/><rect x="9.5" y="9.5" width="5" height="5" rx="1.4"/><rect x="16" y="9.5" width="5" height="5" rx="1.4"/><rect x="3" y="16" width="5" height="5" rx="1.4"/><rect x="9.5" y="16" width="5" height="5" rx="1.4"/><rect x="16" y="16" width="5" height="5" rx="1.4"/></symbol>
</defs></svg>

<div id="progress" hidden></div>

<header id="topbar">
  <div class="bar row1">
    <div class="brand"><span class="mark"><svg><use href="#i-moon"/></svg></span><span data-i18n="app">Nocturne</span><small>2.2</small></div>
    <div id="searchwrap">
      <div id="searchbox" class="searchbox">
        <svg class="icon"><use href="#i-search"/></svg>
        <div id="chips"></div>
        <input id="q" autocomplete="off" spellcheck="false" enterkeyhint="search">
        <button id="go"><svg class="icon"><use href="#i-search"/></svg><span data-i18n="go">Search</span></button>
      </div>
      <div id="acbox" hidden></div>
    </div>
    <div class="hdr-actions">
      <button id="favbtn" class="iconbtn" data-i18n-title="favorites"><svg class="icon"><use href="#i-heart"/></svg><span id="favcount" class="pill" hidden>0</span></button>
      <button id="themebtn" class="iconbtn" data-i18n-title="theme"><svg class="icon"><use href="#i-moon"/></svg></button>
      <button id="langbtn" class="iconbtn txt" data-i18n-title="language">RU</button>
      <button id="setbtn" class="iconbtn" data-i18n-title="settings"><svg class="icon"><use href="#i-sliders"/></svg></button>
    </div>
  </div>
  <div class="bar row2" id="toolbar">
    <div class="seg" id="ratingseg">
      <button data-r="all" data-i18n="r_all">All</button>
      <button data-r="safe" data-i18n="r_safe">Safe</button>
      <button data-r="questionable" data-i18n="r_quest">Questionable</button>
      <button data-r="explicit" data-i18n="r_expl">Explicit</button>
    </div>
    <div class="selectwrap"><select id="sortsel">
      <option value="newest" data-i18n="s_new">Newest</option>
      <option value="score" data-i18n="s_top">Top rated</option>
      <option value="random" data-i18n="s_rand">Random</option>
    </select></div>
    <div class="seg" id="densityseg">
      <button data-d="compact" data-i18n-title="d_compact"><svg class="icon"><use href="#i-d3"/></svg></button>
      <button data-d="cozy" data-i18n-title="d_cozy"><svg class="icon"><use href="#i-d2"/></svg></button>
      <button data-d="large" data-i18n-title="d_large"><svg class="icon"><use href="#i-d1"/></svg></button>
    </div>
    <div class="spacer"></div>
    <div id="stats" class="stats"></div>
  </div>
</header>

<main>
  <div id="simbar" hidden></div>
  <div id="notice" hidden>
    <svg class="icon"><use href="#i-alert"/></svg>
    <span class="msg"></span>
    <button class="retry" data-i18n="retry">Try again</button>
  </div>
  <div id="hero" hidden></div>
  <div id="grid" class="grid"></div>
  <div id="sentinel">
    <div class="spinner" hidden></div>
    <button id="loadmore" class="btn" hidden><svg class="icon"><use href="#i-plus"/></svg><span data-i18n="load_more">Load more</span></button>
  </div>
  <div id="endnote" hidden></div>
</main>

<button id="totop" hidden data-i18n-title="to_top"><svg class="icon"><use href="#i-up"/></svg></button>

<div id="viewer" hidden tabindex="-1">
  <div class="v-top">
    <div class="v-title">
      <span class="vid"></span>
      <span class="sc"><svg class="icon"><use href="#i-heart"/></svg><span class="scn"></span></span>
      <span class="vrating badge"></span>
      <span class="dims"></span>
      <span class="cnt"></span>
    </div>
    <div class="v-actions">
      <button class="vbtn txt" id="vhd" data-i18n-title="hd" hidden>HD</button>
      <button class="vbtn" id="vloop" data-i18n-title="loop" hidden><svg class="icon"><use href="#i-loop"/></svg></button>
      <button class="vbtn" id="vsim" data-i18n-title="similar"><svg class="icon"><use href="#i-similar"/></svg></button>
      <button class="vbtn" id="vslide" data-i18n-title="slideshow"><svg class="icon"><use href="#i-play"/></svg></button>
      <button class="vbtn" id="vfull" data-i18n-title="fullscreen"><svg class="icon"><use href="#i-max"/></svg></button>
      <button class="vbtn fav" id="vfav" data-i18n-title="fav_add"><svg class="icon"><use href="#i-heart"/></svg></button>
      <button class="vbtn" id="vdl" data-i18n-title="download"><svg class="icon"><use href="#i-dl"/></svg></button>
      <button class="vbtn" id="vext" data-i18n-title="open_site"><svg class="icon"><use href="#i-ext"/></svg></button>
      <button class="vbtn" id="vinfo" data-i18n-title="details"><svg class="icon"><use href="#i-info"/></svg></button>
      <button class="vbtn" id="vclose" data-i18n-title="close"><svg class="icon"><use href="#i-x"/></svg></button>
    </div>
  </div>
  <div class="v-body">
    <div class="v-stage" id="vstage">
      <button class="v-nav prev" id="vprev"><svg class="icon"><use href="#i-chevl"/></svg></button>
      <div class="v-holder" id="vholder"></div>
      <div class="v-load" id="vload" hidden><div class="spinner"></div></div>
      <button class="v-nav next" id="vnext"><svg class="icon"><use href="#i-chevr"/></svg></button>
    </div>
    <aside class="v-info" id="vpanel"></aside>
  </div>
</div>

<div id="settings" class="modal" hidden>
  <div class="sheet" role="dialog" aria-modal="true">
    <h2><svg class="icon"><use href="#i-sliders"/></svg><span data-i18n="st_title">Settings</span></h2>
    <p class="sub" data-i18n="st_sub">Everything is stored locally on this computer.</p>

    <h3 data-i18n="st_access">Access</h3>
    <div class="frow"><label class="fl" for="f_key" data-i18n="st_key">API key</label>
      <div class="fin"><svg class="icon" style="width:14px;color:var(--faint)"><use href="#i-key"/></svg>
        <input id="f_key" type="password" autocomplete="off" spellcheck="false">
        <button class="peek" id="peekkey" tabindex="-1"><svg class="icon"><use href="#i-eye"/></svg></button>
      </div></div>
    <div class="frow"><label class="fl" for="f_uid" data-i18n="st_uid">User ID</label>
      <div class="fin"><input id="f_uid" inputmode="numeric" autocomplete="off" spellcheck="false"></div></div>
    <p class="hint"><span data-i18n="st_keyhint">Paste the whole “api_key=…&user_id=…” line into the key field, both fields fill in automatically.</span><br>
      <span data-i18n="st_keywhere">Get it at</span> <code>rule34.xxx → My Account → Options → API Access Credentials</code></p>

    <h3 data-i18n="st_browse">Browsing</h3>
    <div class="frow"><label class="fl" for="f_pp" data-i18n="st_pp">Posts per page</label>
      <div class="selrow"><select id="f_pp"><option>20</option><option>42</option><option>60</option><option>80</option></select></div></div>
    <div class="frow"><label class="fl" for="f_lang" data-i18n="st_lang">Language</label>
      <div class="selrow"><select id="f_lang">
        <option value="auto" data-i18n="st_lang_auto">Auto</option>
        <option value="en">English</option>
        <option value="ru">Русский</option>
      </select></div></div>

    <h3 data-i18n="st_quality">Quality</h3>
    <label class="checkrow"><input type="checkbox" id="f_full"><span><span data-i18n="st_full">Always load full-quality images</span><em data-i18n="st_full_note">Skips the sample copy in the viewer. Slower on big files.</em></span></label>
    <label class="checkrow"><input type="checkbox" id="f_hq"><span><span data-i18n="st_hq">Sharp thumbnails and video frames</span><em data-i18n="st_hq_note">Uses sample-size previews instead of 150px thumbnails.</em></span></label>
    <label class="checkrow"><input type="checkbox" id="f_autoplay"><span data-i18n="st_autoplay">Autoplay videos in the viewer</span></label>
    <label class="checkrow"><input type="checkbox" id="f_muted"><span data-i18n="st_muted">Open videos muted</span></label>
    <label class="checkrow"><input type="checkbox" id="f_hover"><span data-i18n="st_hover">Play video previews on hover</span></label>

    <h3 data-i18n="st_bl">Blacklist</h3>
    <textarea id="blacklist" spellcheck="false"></textarea>
    <p class="hint" data-i18n="st_blhint">One tag per line. A “*” at the end matches any ending, e.g. ai_*</p>

    <div class="kbdhint" id="kbdhint"></div>

    <div class="foot">
      <div class="status" id="st_status"></div>
      <button class="btn" id="st_check" data-i18n="st_check">Check connection</button>
      <button class="btn primary" id="st_save"><svg class="icon"><use href="#i-check"/></svg><span data-i18n="st_save">Save</span></button>
    </div>
  </div>
</div>

<div id="toasts"></div>

<script>
"use strict";
/* ═══════════════ i18n ═══════════════ */
const I18N = {
  en: {
    app:"Nocturne", go:"Search", search_ph:"Search tags — Space adds a tag, Enter searches",
    filter_ph:"Filter favorites…", favorites:"Favorites", theme:"Theme", language:"Language", settings:"Settings",
    r_all:"All", r_safe:"Safe", r_quest:"Questionable", r_expl:"Explicit",
    s_new:"Newest", s_top:"Top rated", s_rand:"Random",
    d_compact:"Compact grid", d_cozy:"Cozy grid", d_large:"Large grid",
    results_label:"results", page_of:"page {p} / {t}", hidden_n:"{n} hidden",
    hidden_tip:"Hidden by your blacklist",
    end_all:"That's everything — {n} posts", end_favs:"{n} in favorites", end_sim:"{n} similar posts",
    retry:"Try again", loading:"Loading…", to_top:"Back to top", load_more:"Load more",
    hero_key_title:"Connect your account", hero_key_text:"Add your rule34.xxx API key and User ID to start browsing.",
    hero_key_btn:"Open settings",
    hero_none_title:"Nothing found", hero_none_text:"Try fewer tags, a different spelling, or another rating filter.",
    hero_fav_title:"No favorites yet", hero_fav_text:"Press the heart on any post to keep it here.",
    hero_sim_title:"No close matches", hero_sim_text:"This post's tags are either too rare or too generic to match anything.",
    err_nokey:"Add your API key and User ID in settings.", err_auth:"Access denied — check your API key and User ID.",
    err_network:"Can't reach the site. Check your connection and try again.",
    err_rate:"Too many requests — give it a moment.", err_upstream:"The site returned an error (HTTP {s}).",
    err_parse:"Unexpected response from the site.", err_internal:"Local server error.",
    err_notfound:"That post is gone or unavailable.",
    fav_add:"Add to favorites", fav_del:"Remove from favorites",
    download:"Download", open_site:"Open on rule34.xxx", copy_link:"Copy file link", copied:"Copied",
    details:"Details (I)", close:"Close (Esc)", hd:"Load full quality", loop:"Loop video",
    slideshow:"Slideshow", fullscreen:"Fullscreen",
    similar:"Find similar (S)", similar_to:"Similar to #{id}", similar_by:"Matched by",
    exit_similar:"Back to search", similar_count:"similar", match:"match",
    t_tags:"Tags", t_copy_tags:"Copy tags", t_meta:"Post", t_score:"Score", t_rating:"Rating", t_size:"Size",
    t_date:"Updated", t_source:"Source", t_id:"ID", t_search_tag:"Search this tag",
    t_add_tag:"Add to search", t_excl_tag:"Exclude from search",
    rating_s:"Safe", rating_q:"Questionable", rating_e:"Explicit",
    video_err:"Could not play this video.", img_err:"Could not load this image.",
    st_title:"Settings", st_sub:"Everything is stored locally on this computer.",
    st_access:"Access", st_key:"API key", st_uid:"User ID",
    st_keyhint:"Paste the whole “api_key=…&user_id=…” line into the key field, both fields fill in automatically.",
    st_keywhere:"Get it at", st_browse:"Browsing", st_pp:"Posts per page", st_lang:"Language", st_lang_auto:"Auto",
    st_quality:"Quality", st_full:"Always load full-quality images",
    st_full_note:"Skips the sample copy in the viewer. Slower on big files.",
    st_hq:"Sharp thumbnails and video frames", st_hq_note:"Uses sample-size previews instead of 150px thumbnails.",
    st_autoplay:"Autoplay videos in the viewer", st_muted:"Open videos muted", st_hover:"Play video previews on hover",
    st_bl:"Blacklist", st_blhint:"One tag per line. A “*” at the end matches any ending, e.g. ai_*",
    st_check:"Check connection", st_save:"Save", st_saved:"Saved",
    st_ok:"Connection OK — {n} posts available", st_checking:"Checking…",
    kbd:"Shortcuts: <kbd>/</kbd> search · <kbd>←</kbd><kbd>→</kbd> navigate · <kbd>F</kbd> favorite · <kbd>S</kbd> similar · <kbd>D</kbd> download · <kbd>I</kbd> details · <kbd>M</kbd> mute · <kbd>Esc</kbd> close",
    recent:"Recent searches", clear:"Clear",
  },
  ru: {
    app:"Nocturne", go:"Найти", search_ph:"Поиск по тегам — пробел добавляет тег, Enter ищет",
    filter_ph:"Фильтр по избранному…", favorites:"Избранное", theme:"Тема", language:"Язык", settings:"Настройки",
    r_all:"Все", r_safe:"Safe", r_quest:"Questionable", r_expl:"Explicit",
    s_new:"Сначала новые", s_top:"По рейтингу", s_rand:"Случайно",
    d_compact:"Компактная сетка", d_cozy:"Средняя сетка", d_large:"Крупная сетка",
    results_label:"результатов", page_of:"стр. {p} / {t}", hidden_n:"{n} скрыто",
    hidden_tip:"Скрыто вашим чёрным списком",
    end_all:"Это всё — {n} постов", end_favs:"В избранном: {n}", end_sim:"Похожих постов: {n}",
    retry:"Повторить", loading:"Загрузка…", to_top:"Наверх", load_more:"Показать ещё",
    hero_key_title:"Подключите аккаунт", hero_key_text:"Укажите API-ключ и User ID с rule34.xxx, чтобы начать просмотр.",
    hero_key_btn:"Открыть настройки",
    hero_none_title:"Ничего не найдено", hero_none_text:"Попробуйте меньше тегов, другое написание или другой рейтинг.",
    hero_fav_title:"В избранном пока пусто", hero_fav_text:"Нажмите на сердечко на любом посте, чтобы сохранить его здесь.",
    hero_sim_title:"Похожего ничего нет", hero_sim_text:"Теги этого поста слишком редкие или слишком общие.",
    err_nokey:"Укажите API-ключ и User ID в настройках.", err_auth:"Доступ отклонён — проверьте API-ключ и User ID.",
    err_network:"Нет соединения с сайтом. Проверьте интернет и попробуйте ещё раз.",
    err_rate:"Слишком много запросов — подождите немного.", err_upstream:"Сайт вернул ошибку (HTTP {s}).",
    err_parse:"Неожиданный ответ сайта.", err_internal:"Ошибка локального сервера.",
    err_notfound:"Пост недоступен или удалён.",
    fav_add:"В избранное", fav_del:"Убрать из избранного",
    download:"Скачать", open_site:"Открыть на rule34.xxx", copy_link:"Скопировать ссылку на файл", copied:"Скопировано",
    details:"Подробности (I)", close:"Закрыть (Esc)", hd:"Полное качество", loop:"Зациклить видео",
    slideshow:"Слайд-шоу", fullscreen:"Во весь экран",
    similar:"Похожие (S)", similar_to:"Похожие на #{id}", similar_by:"Совпадения по",
    exit_similar:"Вернуться к поиску", similar_count:"похожих", match:"совпадение",
    t_tags:"Теги", t_copy_tags:"Копировать теги", t_meta:"Пост", t_score:"Оценка", t_rating:"Рейтинг", t_size:"Размер",
    t_date:"Обновлено", t_source:"Источник", t_id:"ID", t_search_tag:"Искать этот тег",
    t_add_tag:"Добавить к поиску", t_excl_tag:"Исключить из поиска",
    rating_s:"Safe", rating_q:"Questionable", rating_e:"Explicit",
    video_err:"Не удалось воспроизвести видео.", img_err:"Не удалось загрузить изображение.",
    st_title:"Настройки", st_sub:"Все данные хранятся только на этом компьютере.",
    st_access:"Доступ", st_key:"API-ключ", st_uid:"User ID",
    st_keyhint:"Вставьте в поле ключа целиком строку «api_key=…&user_id=…», оба поля заполнятся сами.",
    st_keywhere:"Где взять:", st_browse:"Просмотр", st_pp:"Постов на страницу", st_lang:"Язык", st_lang_auto:"Авто",
    st_quality:"Качество", st_full:"Всегда загружать полное качество",
    st_full_note:"В просмотрщике сразу открывается оригинал. Медленнее на больших файлах.",
    st_hq:"Чёткие превью и кадры видео", st_hq_note:"Вместо миниатюр 150px используются превью размера sample.",
    st_autoplay:"Автовоспроизведение видео", st_muted:"Открывать видео без звука", st_hover:"Проигрывать видео при наведении",
    st_bl:"Чёрный список", st_blhint:"Один тег на строку. «*» в конце — любое окончание, например ai_*",
    st_check:"Проверить соединение", st_save:"Сохранить", st_saved:"Сохранено",
    st_ok:"Соединение в порядке — доступно {n} постов", st_checking:"Проверяю…",
    kbd:"Клавиши: <kbd>/</kbd> поиск · <kbd>←</kbd><kbd>→</kbd> листать · <kbd>F</kbd> избранное · <kbd>S</kbd> похожие · <kbd>D</kbd> скачать · <kbd>I</kbd> детали · <kbd>M</kbd> звук · <kbd>Esc</kbd> закрыть",
    recent:"Недавние запросы", clear:"Очистить",
  }
};
let LANG = "en";
const t = (k, vars) => {
  let s = (I18N[LANG] && I18N[LANG][k]) || I18N.en[k] || k;
  if (vars) for (const [key, val] of Object.entries(vars)) s = s.replaceAll("{" + key + "}", String(val));
  return s;
};
const fmtN = n => new Intl.NumberFormat(LANG === "ru" ? "ru" : "en").format(n);
const fmtC = n => new Intl.NumberFormat(LANG === "ru" ? "ru" : "en", {notation:"compact",maximumFractionDigits:1}).format(n);

/* ═══════════════ Utils / state ═══════════════ */
const $ = s => document.querySelector(s);
const $$ = s => [...document.querySelectorAll(s)];
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const el = (tag, cls, html) => { const e = document.createElement(tag); if (cls) e.className = cls; if (html != null) e.innerHTML = html; return e; };
const svgIcon = (name, extra) => `<svg class="icon ${extra||""}"><use href="#i-${name}"/></svg>`;
const ESCAPES = {"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"};
const esc = s => String(s).replace(/[&<>"']/g, c => ESCAPES[c]);
const prox = u => "/media?u=" + encodeURIComponent(u);
const IMG_EXT = /\.(jpe?g|png|webp|gif|avif)(\?|$)/i;
const LS = {
  get(k, d) { try { const v = JSON.parse(localStorage.getItem("noct_" + k)); return v == null ? d : v; } catch { return d; } },
  set(k, v) { try { localStorage.setItem("noct_" + k, JSON.stringify(v)); } catch {} }
};

const S = {
  cfg: null, mode: "browse",
  tags: [], posts: [], ids: new Set(),
  page: 0, next: 1, pages: null, count: null, hidden: 0,
  loading: false, ended: false, stall: 0, epoch: 0, abort: null, lastFailed: false,
  favs: new Map(), favOrder: [], favFilter: "",
  sim: null, simBasis: [],
};
const V = { open:false, list:null, i:0, z:1, tx:0, ty:0, hd:false, slide:false, slideTimer:0, sbOpen:true };

async function api(url, opts) {
  let r;
  try { r = await fetch(url, opts); }
  catch (e) { if (e && e.name === "AbortError") throw e; throw { api: { code: "network" } }; }
  let d = null;
  try { d = await r.json(); } catch {}
  if (!r.ok || (d && d.error)) throw { api: (d && d.error) || { code: "internal" }, http: r.status };
  return d;
}
const errMsg = e => {
  const a = (e && e.api) || {};
  const code = a.code || "network";
  const map = { nokey:"err_nokey", auth:"err_auth", network:"err_network", rate:"err_rate",
                upstream:"err_upstream", parse:"err_parse", internal:"err_internal",
                forbidden:"err_internal", notfound:"err_notfound" };
  return t(map[code] || "err_network", { s: a.status || "" });
};

function fileName(p) {
  const base = (p.tags || []).slice(0, 3).join("_").replace(/[^\w.-]+/g, "_").slice(0, 48) || "post";
  return `${base}_${p.id}.${p.ext || "jpg"}`;
}
/* rule34 stores a sample-sized still next to every 150px thumbnail:
   /thumbnails/aa/bb/thumbnail_HASH.jpg → /samples/aa/bb/sample_HASH.jpg
   That single swap is what makes video cards stop looking like mush. */
function bigThumb(u) {
  if (!u) return u;
  return u.replace("/thumbnails/", "/samples/").replace("/thumbnail_", "/sample_").replace(/\.\w+($|\?)/, ".jpg$1");
}
function gridSources(p) {
  const hq = !S.cfg || S.cfg.hq_previews !== false;
  const out = [];
  if (p.video) {
    if (hq && p.preview) out.push(bigThumb(p.preview));
    if (p.sample && IMG_EXT.test(p.sample)) out.push(p.sample);
    if (p.preview) out.push(p.preview);
  } else if (p.ext === "gif") {
    if (p.sample) out.push(p.sample);
    if (hq && p.preview) out.push(bigThumb(p.preview));
    if (p.preview) out.push(p.preview);
    out.push(p.file);
  } else {
    if (p.sample) out.push(p.sample);
    if (hq && !p.sample && p.preview) out.push(bigThumb(p.preview));
    out.push(p.file);
    if (p.preview) out.push(p.preview);
  }
  return [...new Set(out.filter(Boolean))].map(prox);
}
function viewSrc(p, hd) {
  const full = hd || (S.cfg && S.cfg.full_quality);
  if (p.video || p.ext === "gif" || !p.sample) return prox(p.file);
  return full ? prox(p.file) : prox(p.sample);
}

/* ═══════════════ Prefs / theming ═══════════════ */
function resolveLang() {
  const pref = S.cfg.lang || "auto";
  if (pref === "auto") return (navigator.language || "en").toLowerCase().startsWith("ru") ? "ru" : "en";
  return pref;
}
function applyI18n() {
  document.documentElement.lang = LANG;
  $$("[data-i18n]").forEach(n => { n.textContent = t(n.dataset.i18n); });
  $$("[data-i18n-title]").forEach(n => { n.title = t(n.dataset.i18nTitle); n.setAttribute("aria-label", n.title); });
  $("#q").placeholder = S.mode === "favorites" ? t("filter_ph") : t("search_ph");
  $("#langbtn").textContent = LANG === "ru" ? "EN" : "RU";
  $("#kbdhint").innerHTML = t("kbd");
  const note = $("#endnote");
  if (!note.hidden) note.textContent = endText();
  if (S.mode === "similar") renderSimBar();
}
function applyPrefs() {
  LANG = resolveLang();
  document.documentElement.dataset.theme = S.cfg.theme;
  $("#themebtn").innerHTML = svgIcon(S.cfg.theme === "dark" ? "moon" : "sun");
  const RH = { compact: 148, cozy: 200, large: 266 };
  document.documentElement.style.setProperty("--rh", (RH[S.cfg.density] || 200) + "px");
  $$("#densityseg button").forEach(b => b.classList.toggle("on", b.dataset.d === S.cfg.density));
  $$("#ratingseg button").forEach(b => b.classList.toggle("on", b.dataset.r === S.cfg.rating));
  $("#sortsel").value = S.cfg.sort;
  applyI18n();
  updateStats();
}
let cfgSeq = 0;
function persistCfg(patch) {
  Object.assign(S.cfg, patch);
  const seq = ++cfgSeq;
  api("/api/config", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(patch) })
    .then(d => { if (seq === cfgSeq) S.cfg = d.config; })   // ignore out-of-order responses
    .catch(e => toast(errMsg(e), "err"));
}

/* ═══════════════ Toasts ═══════════════ */
function toast(msg, kind = "info", icon) {
  const box = el("div", "toast " + (kind === "err" ? "err" : kind === "ok" ? "ok" : ""),
    svgIcon(icon || (kind === "err" ? "alert" : kind === "ok" ? "check" : "info")) + `<span>${esc(msg)}</span>`);
  $("#toasts").appendChild(box);
  const bye = () => { box.classList.add("out"); setTimeout(() => box.remove(), 260); };
  box.addEventListener("click", bye);
  setTimeout(bye, 4200);
}

/* ═══════════════ Search: chips + autocomplete + history ═══════════════ */
const qInput = $("#q"), acBox = $("#acbox");
let acItems = [], acSel = -1, acTimer = 0, acCache = new Map(), acAbort = null;

function normTag(s) { return s.trim().toLowerCase().replace(/\s+/g, "_"); }
function renderChips() {
  const wrap = $("#chips");
  wrap.innerHTML = "";
  if (S.mode !== "browse") return;
  for (const tag of S.tags) {
    const neg = tag.startsWith("-");
    const chip = el("span", "chip" + (neg ? " neg" : ""));
    chip.appendChild(el("span", "t", esc(neg ? tag.slice(1) : tag)));
    const rm = el("button", "", svgIcon("x"));
    rm.title = t("close");
    rm.addEventListener("click", () => { S.tags = S.tags.filter(x => x !== tag); renderChips(); runSearch(); });
    chip.appendChild(rm);
    wrap.appendChild(chip);
  }
}
function addTag(raw, silent) {
  let tag = normTag(raw);
  if (!tag || tag === "-") return false;
  if (/^-?rating:/.test(tag)) {                     // typed rating → drive the segmented control
    const val = tag.replace(/^-?rating:/, "");
    const map = { s:"safe", safe:"safe", q:"questionable", questionable:"questionable", e:"explicit", explicit:"explicit" };
    if (!tag.startsWith("-") && map[val]) { setRating(map[val], true); return true; }
  }
  if (S.tags.includes(tag)) return false;
  S.tags.push(tag);
  renderChips();
  if (!silent) runSearch();
  return true;
}
function commitInput(silent) {
  const val = qInput.value.trim();
  qInput.value = "";
  hideAc();
  if (val) return addTag(val, silent);
  return false;
}
function saveHistory() {
  if (!S.tags.length) return;
  const key = S.tags.join(" ");
  const h = LS.get("history", []).filter(x => x !== key);
  h.unshift(key);
  LS.set("history", h.slice(0, 12));
}

function hideAc() { acBox.hidden = true; acBox.innerHTML = ""; acItems = []; acSel = -1; }
function renderAcRows(rows) {
  acBox.innerHTML = "";
  acItems = rows;
  acSel = -1;
  if (!rows.length) { acBox.hidden = true; return; }
  rows.forEach((row, i) => {
    const btn = el("button", "acrow");
    if (row.kind === "history") {
      btn.innerHTML = svgIcon("clock") + `<span class="lbl">${esc(row.value)}</span>`;
    } else {
      const m = /^(.*)\((\d[\d,. ]*)\)\s*$/.exec(row.label || "");
      const name = m ? m[1].trim() : (row.label || row.value);
      const cnt = m ? m[2].trim() : "";
      btn.innerHTML = svgIcon("tag") + `<span class="lbl">${esc(name)}</span>` + (cnt ? `<span class="cnt">${esc(cnt)}</span>` : "");
    }
    btn.addEventListener("mousedown", e => e.preventDefault());
    btn.addEventListener("click", () => chooseAc(i));
    acBox.appendChild(btn);
  });
  acBox.hidden = false;
}
function markAc() { $$("#acbox .acrow").forEach((r, i) => r.classList.toggle("on", i === acSel)); }
function chooseAc(i) {
  const row = acItems[i];
  if (!row) return;
  const neg = qInput.value.trim().startsWith("-");
  qInput.value = "";
  hideAc();
  if (row.kind === "history") { exitSimilar(true); S.tags = row.value.split(" "); renderChips(); runSearch(); }
  else { exitSimilar(true); addTag((neg ? "-" : "") + row.value); }
  qInput.focus();
}
function showHistory() {
  const h = LS.get("history", []);
  if (!h.length || S.mode === "favorites") return;
  renderAcRows(h.map(v => ({ kind: "history", value: v })));
  acBox.prepend(el("div", "achead", esc(t("recent"))));   // not .acrow → keeps ↑↓ highlight aligned
  const clr = el("button", "acclear", svgIcon("x") + `<span class="lbl">${esc(t("clear"))}</span>`);
  clr.addEventListener("mousedown", e => e.preventDefault());
  clr.addEventListener("click", () => { LS.set("history", []); hideAc(); });
  acBox.appendChild(clr);
}
async function fetchAc(text) {
  const term = normTag(text.replace(/^-/, ""));
  if (term.length < 2) { hideAc(); return; }
  if (acCache.has(term)) { renderAcRows(acCache.get(term)); return; }
  if (acAbort) acAbort.abort();
  const ctl = new AbortController();
  acAbort = ctl;
  try {
    const d = await api("/api/autocomplete?q=" + encodeURIComponent(term), { signal: ctl.signal });
    const rows = (d.tags || []).filter(r => !S.tags.includes(r.value));
    acCache.set(term, rows);
    if (acCache.size > 300) acCache.delete(acCache.keys().next().value);
    if (qInput.value.trim().replace(/^-/, "") && normTag(qInput.value.replace(/^-/, "")) === term) renderAcRows(rows);
  } catch (e) { if (!e || e.name !== "AbortError") hideAc(); }
}

qInput.addEventListener("input", () => {
  if (S.mode === "favorites") { S.favFilter = qInput.value.trim().toLowerCase(); renderFavGrid(); return; }
  clearTimeout(acTimer);
  const v = qInput.value;
  if (!v.trim()) { hideAc(); return; }
  acTimer = setTimeout(() => fetchAc(v), 170);
});
qInput.addEventListener("focus", () => { if (!qInput.value.trim() && S.mode !== "favorites") showHistory(); });
qInput.addEventListener("keydown", e => {
  if (S.mode === "favorites") { if (e.key === "Escape") { qInput.value = ""; S.favFilter = ""; renderFavGrid(); } return; }
  if (e.key === "ArrowDown" && !acBox.hidden) { e.preventDefault(); acSel = (acSel + 1) % acItems.length; markAc(); }
  else if (e.key === "ArrowUp" && !acBox.hidden) { e.preventDefault(); acSel = (acSel - 1 + acItems.length) % acItems.length; markAc(); }
  else if (e.key === "Tab" && !acBox.hidden && acItems.length) { e.preventDefault(); chooseAc(acSel < 0 ? 0 : acSel); }
  else if (e.key === "Enter") {
    e.preventDefault();
    if (!acBox.hidden && acSel >= 0) { chooseAc(acSel); return; }
    const had = commitInput(true);
    runSearch();
    if (!had) qInput.blur();
  }
  else if (e.key === " " && qInput.value.trim()) { e.preventDefault(); commitInput(false); }
  else if (e.key === "Backspace" && !qInput.value && S.tags.length) { S.tags.pop(); renderChips(); runSearch(); }
  else if (e.key === "Escape") { hideAc(); qInput.blur(); }
});
document.addEventListener("pointerdown", e => { if (!$("#searchwrap").contains(e.target)) hideAc(); });
$("#go").addEventListener("click", () => { commitInput(true); runSearch(); });
$("#searchbox").addEventListener("click", e => { if (e.target === $("#searchbox") || e.target.id === "chips") qInput.focus(); });

/* ═══════════════ Query / hash routing ═══════════════ */
function buildQuery() {
  const parts = [...S.tags];
  if (S.cfg.rating !== "all" && !parts.some(x => /^-?rating:/.test(x))) parts.push("rating:" + S.cfg.rating);
  if (!parts.some(x => x.startsWith("sort:"))) {          // typed sort: chips win
    if (S.cfg.sort === "score") parts.push("sort:score:desc");
    else if (S.cfg.sort === "random") parts.push("sort:random");
  }
  return parts.join(" ");
}
function hashFromState() {
  const p = new URLSearchParams();
  if (S.mode === "similar" && S.sim) { p.set("sim", String(S.sim.id)); return "#" + p.toString(); }
  if (S.tags.length) p.set("q", S.tags.join(" "));
  if (S.cfg.sort !== "newest") p.set("s", S.cfg.sort);
  if (p.toString() || S.cfg.rating !== "all") p.set("r", S.cfg.rating);   // explicit → exact restore
  const str = p.toString();
  return str ? "#" + str : "";
}
function stateFromHash(fromNav) {
  const h = location.hash.replace(/^#/, "");
  if (!h) {
    if (fromNav) { S.tags = []; S.mode = "browse"; S.sim = null; }
    return !!fromNav;
  }
  const p = new URLSearchParams(h);
  const sim = parseInt(p.get("sim") || "", 10);
  if (sim > 0) { S.mode = "similar"; S.sim = { id: sim, tags: [] }; return true; }
  S.mode = "browse"; S.sim = null;
  S.tags = (p.get("q") || "").split(" ").map(normTag).filter(Boolean);
  if (["all","safe","questionable","explicit"].includes(p.get("r"))) S.cfg.rating = p.get("r");
  if (["newest","score","random"].includes(p.get("s"))) S.cfg.sort = p.get("s");
  return true;
}
function pushHash() {
  const h = hashFromState();
  if (location.hash === h || (!h && !location.hash)) return;
  history.pushState(null, "", h || location.pathname);
}
window.addEventListener("popstate", () => {
  stateFromHash(true);
  renderChips();
  applyPrefs();
  syncModeChrome();
  if (S.mode === "similar") startSimilar(false);
  else if (S.mode === "browse") runSearch(false);
});

/* ═══════════════ Grid ═══════════════ */
const grid = $("#grid"), sentinel = $("#sentinel"), spinnerEl = $("#sentinel .spinner"), moreBtn = $("#loadmore");

function showSkeletons() {
  const ars = [1.42, .72, 1, 1.78, .8, 1.2, .65, 1.5, 1.05, .9, 1.33, 1.6, .75, 1.1];
  const frag = document.createDocumentFragment();
  for (let i = 0; i < 14; i++) {
    const sk = el("div", "skel");
    sk.style.setProperty("--ar", ars[i % ars.length]);
    frag.appendChild(sk);
  }
  grid.appendChild(frag);
}
function removeSkeletons() { $$(".skel").forEach(n => n.remove()); }
function clearGrid() {
  grid.querySelectorAll(".card").forEach(c => { if (c._stopHover) c._stopHover(); });
  grid.innerHTML = "";
}

function ratingBadge(r) {
  return r ? `<span class="badge r-${r}" title="${esc(t("rating_" + r))}">${r.toUpperCase()}</span>` : "";
}
function downloadPost(p) {
  const a = el("a");
  a.href = prox(p.file) + "&dl=1&name=" + encodeURIComponent(fileName(p));
  a.download = fileName(p);
  document.body.appendChild(a); a.click(); a.remove();
}
function makeCard(p, listGetter, n) {
  const card = el("figure", "card");
  card.dataset.id = p.id;
  card.tabIndex = 0;
  card.setAttribute("role", "button");
  card.setAttribute("aria-label", (p.tags || []).slice(0, 6).join(", "));
  const ar = clamp(p.w > 0 && p.h > 0 ? p.w / p.h : 1, .55, 2.6);
  card.style.setProperty("--ar", ar.toFixed(4));
  card.style.animationDelay = Math.min(n * 24, 320) + "ms";

  // thumbnail with a fallback ladder: sharp → smaller → original → broken
  const sources = gridSources(p);
  let step = 0;
  const img = new Image();
  img.loading = "lazy"; img.decoding = "async"; img.draggable = false; img.alt = "";
  img.src = sources[0];
  img.addEventListener("load", () => img.classList.add("ld"));
  img.addEventListener("error", () => {
    step++;
    if (step < sources.length) { img.src = sources[step]; return; }
    card.classList.add("broken");
    card.insertAdjacentHTML("beforeend", svgIcon("img"));
  });
  card.appendChild(img);

  const badges = [ratingBadge(p.rating)];
  if (p.similarity != null) badges.push(`<span class="badge match">${svgIcon("similar")}${Math.round(clamp(p.similarity / 6, 0, 1) * 100)}%</span>`);
  if (p.video) badges.push(`<span class="badge">${svgIcon("play","fill")}${esc((p.ext || "video").toUpperCase())}</span>`);
  else if (p.ext === "gif") badges.push(`<span class="badge">GIF</span>`);
  card.appendChild(el("div", "c-top", badges.join("")));
  if (p.video) card.appendChild(el("div", "c-play", `<span>${svgIcon("play")}</span>`));

  const acts = el("div", "c-acts");
  const fav = el("button", "cbtn fv" + (S.favs.has(p.id) ? " active" : ""), svgIcon("heart"));
  fav.title = t(S.favs.has(p.id) ? "fav_del" : "fav_add");
  fav.addEventListener("click", e => { e.stopPropagation(); toggleFav(p); });
  const smb = el("button", "cbtn smb", svgIcon("similar"));
  smb.title = t("similar");
  smb.addEventListener("click", e => { e.stopPropagation(); startSimilarFrom(p); });
  const dlb = el("button", "cbtn dlb", svgIcon("dl"));
  dlb.title = t("download");
  dlb.addEventListener("click", e => { e.stopPropagation(); downloadPost(p); });
  acts.append(fav, smb, dlb);
  card.appendChild(acts);

  const meta = el("figcaption", "c-meta");
  meta.appendChild(el("div", "row",
    `<span class="sc">${svgIcon("heart")}${fmtC(p.score || 0)}</span><span>${p.w && p.h ? p.w + "×" + p.h : ""}</span>`));
  const snippet = (p.tags || []).slice(0, 5).join(" · ").replaceAll("_", " ");
  if (snippet) meta.appendChild(el("div", "tgs", esc(snippet)));
  card.appendChild(meta);

  // hover previews: videos play, big GIFs animate
  let hoverV = null, hoverT = 0;
  const stopHover = () => {
    clearTimeout(hoverT);
    card.classList.remove("playing");
    if (hoverV) { try { hoverV.pause(); hoverV.removeAttribute("src"); hoverV.load(); } catch {} hoverV.remove(); hoverV = null; }
    if (img.dataset.gif) { delete img.dataset.gif; img.src = sources[step] || sources[0]; }
  };
  if (p.video) {
    card.addEventListener("pointerenter", e => {
      if (!S.cfg.hover_preview || e.pointerType === "touch") return;
      hoverT = setTimeout(() => {
        hoverV = document.createElement("video");
        hoverV.muted = true; hoverV.loop = true; hoverV.playsInline = true; hoverV.preload = "auto";
        hoverV.className = "hoverv";
        if (p.preview) hoverV.poster = prox(bigThumb(p.preview));
        hoverV.src = prox(p.file);
        hoverV.addEventListener("loadedmetadata", () => {
          // start a few seconds in: opening frames are usually black
          if (hoverV && hoverV.duration > 6) { try { hoverV.currentTime = Math.min(4, hoverV.duration * 0.12); } catch {} }
        });
        hoverV.addEventListener("canplay", () => { if (hoverV) { hoverV.classList.add("on"); card.classList.add("playing"); } });
        card.insertBefore(hoverV, card.querySelector(".c-top"));
        hoverV.play().catch(() => {});
      }, 230);
    });
    card.addEventListener("pointerleave", stopHover);
  } else if (p.ext === "gif" && sources[0] !== prox(p.file)) {
    card.addEventListener("pointerenter", e => {
      if (!S.cfg.hover_preview || e.pointerType === "touch") return;
      hoverT = setTimeout(() => { img.dataset.gif = "1"; img.src = prox(p.file); }, 200);
    });
    card.addEventListener("pointerleave", stopHover);
  }
  card._stopHover = stopHover;

  const open = () => { stopHover(); const list = listGetter(); const i = list.findIndex(x => x.id === p.id); if (i >= 0) openViewer(list, i); };
  card.addEventListener("click", open);
  card.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); open(); } });
  return card;
}
function appendCards(list, listGetter) {
  const frag = document.createDocumentFragment();
  list.forEach((p, i) => frag.appendChild(makeCard(p, listGetter, i)));
  grid.appendChild(frag);
}

/* ═══════════════ Stats / hero / notice ═══════════════ */
function endText() {
  if (S.mode === "favorites") return t("end_favs", { n: fmtN(favView().length) });
  if (S.mode === "similar") return t("end_sim", { n: fmtN(S.posts.length) });
  return t("end_all", { n: fmtN(S.posts.length) });
}
function updateStats() {
  const stats = $("#stats");
  if (!S.cfg) { stats.textContent = ""; return; }
  if (S.mode === "favorites") { stats.innerHTML = `<span><b>${fmtN(favView().length)}</b> · ${esc(t("favorites"))}</span>`; return; }
  const bits = [];
  if (S.mode === "similar") {
    bits.push(`<span><b>${fmtN(S.count != null ? S.count : S.posts.length)}</b>&nbsp;${esc(t("similar_count"))}</span>`);
  } else {
    if (S.count != null) bits.push(`<span><b>${fmtN(S.count)}</b>${S.pages == null ? "+" : ""}&nbsp;${esc(t("results_label"))}</span>`);
    if (S.page > 0 && S.pages) bits.push(`<span>${esc(t("page_of", {p: fmtN(S.page), t: fmtN(S.pages)}))}</span>`);
  }
  if (S.hidden > 0) bits.splice(1, 0, `<span class="hid" title="${esc(t("hidden_tip"))}">${esc(t("hidden_n", {n: fmtN(S.hidden)}))}</span>`);
  stats.innerHTML = bits.join("");
}
function showHero(kind) {
  const hero = $("#hero");
  hero.innerHTML = "";
  const conf = {
    nokey: { icon: "key", title: "hero_key_title", text: "hero_key_text", btn: "hero_key_btn",
             path: "rule34.xxx → My Account → Options → API Access Credentials" },
    none:  { icon: "search", title: "hero_none_title", text: "hero_none_text" },
    favs:  { icon: "heart", title: "hero_fav_title", text: "hero_fav_text" },
    sim:   { icon: "similar", title: "hero_sim_title", text: "hero_sim_text" },
  }[kind];
  if (!conf) { hero.hidden = true; return; }
  hero.appendChild(el("div", "big", svgIcon(conf.icon)));
  hero.appendChild(el("h2", "", esc(t(conf.title))));
  hero.appendChild(el("p", "", esc(t(conf.text))));
  if (conf.path) hero.appendChild(el("div", "path", esc(conf.path)));
  if (conf.btn) {
    const b = el("button", "cta", esc(t(conf.btn)));
    b.addEventListener("click", openSettings);
    hero.appendChild(b);
  }
  hero.hidden = false;
}
function hideHero() { $("#hero").hidden = true; }
function showNotice(msg, retryFn) {
  const box = $("#notice");
  box.querySelector(".msg").textContent = msg;
  const btn = box.querySelector(".retry");
  btn.textContent = t("retry");
  btn.onclick = () => { box.hidden = true; retryFn(); };
  box.hidden = false;
}
function setBusy(on) {
  $("#progress").hidden = !on;
  spinnerEl.hidden = !on;
  moreBtn.hidden = on || S.ended || !S.posts.length || S.mode === "favorites";
}

/* ═══════════════ Feed ═══════════════ */
function resetFeed() {
  S.epoch++;
  if (S.abort) { S.abort.abort(); S.abort = null; }
  S.posts = []; S.ids.clear();
  S.page = 0; S.next = 1; S.pages = null; S.count = null;
  S.hidden = 0; S.ended = false; S.stall = 0; S.loading = false; S.lastFailed = false;
  clearGrid();
  $("#endnote").hidden = true;
  $("#notice").hidden = true;
  hideHero();
  setBusy(false);
}

async function runSearch(push = true) {
  if (S.mode === "similar") { S.mode = "browse"; S.sim = null; syncModeChrome(); }
  if (S.mode === "favorites") { renderFavGrid(); return; }
  resetFeed();
  if (push) pushHash();
  if (S.tags.length) saveHistory();
  document.title = (S.tags.length ? S.tags.join(" ") + " — " : "") + t("app");
  if (!S.cfg.api_key || !S.cfg.user_id) { showHero("nokey"); updateStats(); return; }
  showSkeletons();
  updateStats();
  await loadMore();
  topUp();
}

function feedUrl() {
  if (S.mode === "similar") {
    const hint = (S.sim.tags || []).slice(0, 40).join(" ");
    return `/api/similar?id=${S.sim.id}&page=${S.next}&limit=${S.cfg.per_page}` +
           (hint ? `&tags=${encodeURIComponent(hint)}` : "");
  }
  return `/api/posts?tags=${encodeURIComponent(buildQuery())}&page=${S.next}&limit=${S.cfg.per_page}`;
}

async function loadMore() {
  if (S.loading || S.ended || S.mode === "favorites") return;
  if (!S.cfg || !S.cfg.api_key || !S.cfg.user_id) return;
  const ep = S.epoch;
  S.loading = true; S.lastFailed = false;
  setBusy(true);
  const ctl = new AbortController();
  S.abort = ctl;
  try {
    const d = await api(feedUrl(), { signal: ctl.signal });
    if (ep !== S.epoch) return;
    removeSkeletons();
    S.page = d.page || S.next;
    if (d.count != null) S.count = d.count;
    S.pages = d.pages != null ? d.pages : S.pages;
    S.hidden += d.hidden || 0;
    if (d.basis) S.simBasis = d.basis;
    if (d.source && S.mode === "similar" && (!S.sim.tags || !S.sim.tags.length)) S.sim = d.source;
    if (d.basis || d.source) renderSimBar();

    const fresh = (d.posts || []).filter(p => !S.ids.has(p.id));
    fresh.forEach(p => S.ids.add(p.id));
    S.posts.push(...fresh);
    appendCards(fresh, () => S.posts);

    // The server tells us exactly where to continue. Only a genuinely empty
    // upstream page ends the feed, so a blacklisted page can't stop scrolling.
    S.next = d.next_page || (S.page + 1);
    if (d.exhausted || d.next_page == null) S.ended = true;
    else if (!fresh.length) { if (++S.stall >= 3) S.ended = true; }
    else S.stall = 0;

    if (S.ended && !S.posts.length) showHero(S.mode === "similar" ? "sim" : "none");
    if (S.posts.length && S.ended) { $("#endnote").textContent = endText(); $("#endnote").hidden = false; }
    updateStats();
  } catch (e) {
    if ((e && e.name === "AbortError") || ep !== S.epoch) return;
    S.lastFailed = true;
    removeSkeletons();
    const msg = errMsg(e);
    if (e && e.api && e.api.code === "nokey") showHero("nokey");
    else if (!S.posts.length) showNotice(msg, () => { S.ended = false; loadMore().then(topUp); });
    else { toast(msg, "err"); showNotice(msg, () => { $("#notice").hidden = true; loadMore().then(topUp); }); }
  } finally {
    if (ep === S.epoch) { S.loading = false; setBusy(false); }
  }
}

function sentinelVisible() {
  const r = sentinel.getBoundingClientRect();
  return r.top < innerHeight + 900;
}
let topping = false;
async function topUp() {
  if (topping) return;
  topping = true;
  try {
    for (let i = 0; i < 20; i++) {
      if (S.ended || S.lastFailed || S.mode === "favorites") break;
      if (!sentinelVisible()) break;
      await loadMore();
      await new Promise(r => requestAnimationFrame(r));
    }
  } finally { topping = false; }
}
new IntersectionObserver(entries => {
  if (entries.some(x => x.isIntersecting)) topUp();
}, { rootMargin: "1200px 0px" }).observe(sentinel);
moreBtn.addEventListener("click", () => { S.lastFailed = false; topUp(); });

/* ═══════════════ Similar ═══════════════ */
function renderSimBar() {
  const bar = $("#simbar");
  if (S.mode !== "similar" || !S.sim) { bar.hidden = true; bar.innerHTML = ""; return; }
  bar.innerHTML = "";
  const src = S.sim;
  const thumbUrl = src.preview ? prox(bigThumb(src.preview)) : (src.sample ? prox(src.sample) : null);
  if (thumbUrl) {
    const im = new Image();
    im.src = thumbUrl; im.alt = "";
    im.addEventListener("error", () => im.remove());
    bar.appendChild(im);
  }
  const who = el("div", "who");
  who.appendChild(el("div", "h", esc(t("similar_to", { id: src.id }))));
  if (S.simBasis.length) {
    who.appendChild(el("div", "basis",
      esc(t("similar_by")) + " " + S.simBasis.map(x => `<span>${esc(x.replaceAll("_", " "))}</span>`).join(", ")));
  }
  bar.appendChild(who);
  const exit = el("button", "exit", svgIcon("back") + `<span>${esc(t("exit_similar"))}</span>`);
  exit.addEventListener("click", () => { exitSimilar(); runSearch(); });
  bar.appendChild(exit);
  bar.hidden = false;
}
function syncModeChrome() {
  $("#favbtn").classList.toggle("active", S.mode === "favorites");
  $("#toolbar").classList.toggle("off", S.mode !== "browse");
  renderSimBar();
  applyI18n();
}
function exitSimilar(silent) {
  if (S.mode !== "similar") return false;
  S.mode = "browse"; S.sim = null; S.simBasis = [];
  syncModeChrome();
  if (!silent) { renderChips(); }
  return true;
}
function startSimilarFrom(post) {
  if (!post) return;
  if (V.open) closeViewer();
  S.mode = "similar";
  S.sim = post;
  S.simBasis = [];
  syncModeChrome();
  startSimilar(true);
}
async function startSimilar(push) {
  resetFeed();
  renderChips();
  syncModeChrome();
  if (push) pushHash();
  document.title = t("similar_to", { id: S.sim.id }) + " — " + t("app");
  if (!S.cfg.api_key || !S.cfg.user_id) { showHero("nokey"); return; }
  showSkeletons();
  updateStats();
  await loadMore();
  topUp();
}

/* ═══════════════ Favorites ═══════════════ */
async function loadFavorites() {
  try {
    const d = await api("/api/favorites");
    S.favOrder = d.posts || [];
    S.favs = new Map(S.favOrder.map(p => [p.id, p]));
    updateFavBadge();
    refreshFavMarks();
  } catch { /* non-fatal */ }
}
function updateFavBadge() {
  const n = S.favs.size;
  const pill = $("#favcount");
  pill.hidden = n === 0;
  pill.textContent = n > 99 ? "99+" : n;
}
function refreshFavMarks() {
  $$(".card").forEach(card => {
    const b = card.querySelector(".cbtn.fv");
    if (!b) return;
    const on = S.favs.has(+card.dataset.id);
    b.classList.toggle("active", on);
    b.title = t(on ? "fav_del" : "fav_add");
  });
  if (V.open) syncViewerFav();
}
async function toggleFav(p) {
  const had = S.favs.has(p.id);
  if (had) { S.favs.delete(p.id); S.favOrder = S.favOrder.filter(x => x.id !== p.id); }
  else { S.favs.set(p.id, p); S.favOrder.unshift(p); }
  updateFavBadge(); refreshFavMarks();
  if (S.mode === "favorites" && had) renderFavGrid();
  try {
    const d = await api("/api/favorites", { method: "POST", headers: { "Content-Type": "application/json" },
                                            body: JSON.stringify({ post: p }) });
    if (d.favorited === had) loadFavorites();                 // out of sync → resync
  } catch (e) {
    toast(errMsg(e), "err");                                  // revert
    if (had) { S.favs.set(p.id, p); S.favOrder.unshift(p); } else { S.favs.delete(p.id); S.favOrder = S.favOrder.filter(x => x.id !== p.id); }
    updateFavBadge(); refreshFavMarks();
    if (S.mode === "favorites") renderFavGrid();
  }
}
function favView() {
  if (!S.favFilter) return S.favOrder.slice();
  const words = S.favFilter.split(/\s+/).filter(Boolean);
  return S.favOrder.filter(p => {
    const hay = (p.tags || []).join(" ").toLowerCase() + " " + p.id;
    return words.every(w => hay.includes(w));
  });
}
function renderFavGrid() {
  clearGrid();
  $("#notice").hidden = true; $("#endnote").hidden = true;
  const list = favView();
  hideHero();
  if (!list.length) showHero("favs");
  else {
    appendCards(list, favView);
    $("#endnote").textContent = endText();
    $("#endnote").hidden = false;
  }
  setBusy(false);
  updateStats();
}
function setMode(mode) {
  if (S.mode === mode) return;
  const wasSimilar = S.mode === "similar";
  S.mode = mode;
  if (mode !== "similar") { S.sim = null; S.simBasis = []; }
  qInput.value = ""; S.favFilter = "";
  hideAc();
  renderChips();
  syncModeChrome();
  if (mode === "favorites") {
    S.epoch++;
    if (S.abort) S.abort.abort();
    S.loading = false;
    setBusy(false);
    document.title = t("favorites") + " — " + t("app");
    renderFavGrid();
  } else if (wasSimilar || mode === "browse") {
    runSearch(false);
  }
}
$("#favbtn").addEventListener("click", () => setMode(S.mode === "favorites" ? "browse" : "favorites"));

/* ═══════════════ Viewer ═══════════════ */
const viewer = $("#viewer"), vstage = $("#vstage"), vholder = $("#vholder"), vpanel = $("#vpanel");

function openViewer(list, i) {
  V.open = true; V.list = list; V.sbOpen = !!S.cfg.sidebar;
  document.body.classList.add("noscroll");
  viewer.hidden = false;
  viewer.classList.toggle("hasinfo", V.sbOpen);
  renderViewer(i);
  viewer.focus({ preventScroll: true });
}
function closeViewer() {
  stopSlideshow();
  cleanupMedia();
  V.open = false;
  viewer.hidden = true;
  document.body.classList.remove("noscroll");
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  const cur = V.list && V.list[V.i];
  const card = cur ? grid.querySelector(`.card[data-id="${cur.id}"]`) : null;
  if (card) { card.scrollIntoView({ block: "nearest" }); card.focus({ preventScroll: true }); }
}
function cleanupMedia() {
  const vid = vholder.querySelector("video");
  if (vid) { try { vid.pause(); vid.removeAttribute("src"); vid.load(); } catch {} }
  vholder.innerHTML = "";
}
function resetZoom() { V.z = 1; V.tx = 0; V.ty = 0; applyZoom(); }
function applyZoom() {
  vholder.style.transform = V.z === 1 && !V.tx && !V.ty ? "" : `translate(${V.tx}px,${V.ty}px) scale(${V.z})`;
  vstage.classList.toggle("zoomed", V.z > 1);
}
function clampPan() {
  const sw = vstage.clientWidth, sh = vstage.clientHeight;
  const mw = vholder.offsetWidth * V.z, mh = vholder.offsetHeight * V.z;
  const mx = Math.max(0, (mw - sw) / 2) + 60, my = Math.max(0, (mh - sh) / 2) + 60;
  V.tx = clamp(V.tx, -mx, mx); V.ty = clamp(V.ty, -my, my);
}
function setZoom(nz, cx, cy) {
  const p = V.list[V.i];
  if (!p || p.video) return;
  nz = clamp(nz, 1, 8);
  if (cx != null) {
    const r = vstage.getBoundingClientRect();
    const px = cx - r.left - r.width / 2, py = cy - r.top - r.height / 2;
    const k = nz / V.z;
    V.tx = px - k * (px - V.tx);
    V.ty = py - k * (py - V.ty);
  }
  V.z = nz;
  if (V.z === 1) { V.tx = 0; V.ty = 0; } else clampPan();
  applyZoom();
  if (V.z > 1.4 && !V.hd && p.sample && !p.video && p.ext !== "gif") loadHd();
}
function loadHd() {
  const p = V.list[V.i];
  if (!p || V.hd) return;
  V.hd = true;
  $("#vhd").classList.add("active");
  const img = vholder.querySelector("img");
  if (img) {
    const pre = new Image();
    pre.onload = () => { const cur = vholder.querySelector("img"); if (cur && V.list[V.i] === p) cur.src = pre.src; };
    pre.src = viewSrc(p, true);
  }
}

function renderViewer(i) {
  const list = V.list;
  if (!list || !list[i]) return;
  stopSlideTimer();
  cleanupMedia();
  resetZoom();
  V.i = i;
  V.hd = !!(S.cfg && S.cfg.full_quality);
  const p = list[i];

  // top bar
  $(".v-title .vid").textContent = "#" + p.id;
  $(".v-title .scn").textContent = fmtC(p.score || 0);
  const rb = $(".v-title .vrating");
  rb.className = "vrating badge" + (p.rating ? " r-" + p.rating : "");
  rb.textContent = p.rating ? p.rating.toUpperCase() : "";
  rb.hidden = !p.rating;
  $(".v-title .dims").textContent = p.w && p.h ? `${p.w}×${p.h}` : "";
  const more = S.mode !== "favorites" && !S.ended && list === S.posts;
  $(".v-title .cnt").textContent = `${fmtN(i + 1)} / ${fmtN(list.length)}${more ? "+" : ""}`;
  $("#vhd").hidden = !(p.sample && !p.video && p.ext !== "gif");
  $("#vhd").classList.toggle("active", V.hd);
  $("#vloop").hidden = !p.video;
  syncViewerFav();
  $("#vprev").disabled = i <= 0;
  $("#vnext").disabled = i >= list.length - 1 && !more;

  // media
  $("#vload").hidden = false;
  if (p.video) {
    const vid = document.createElement("video");
    vid.controls = true; vid.playsInline = true;
    vid.autoplay = !!S.cfg.autoplay;
    vid.muted = !!S.cfg.muted;
    vid.loop = LS.get("loop", false) && !V.slide;
    $("#vloop").classList.toggle("active", LS.get("loop", false));
    if (p.preview) vid.poster = prox(bigThumb(p.preview));
    vid.src = prox(p.file);
    const vol = LS.get("vol", null);
    if (vol != null) vid.volume = clamp(vol, 0, 1);
    vid.addEventListener("volumechange", () => { LS.set("vol", vid.volume); });
    vid.addEventListener("loadedmetadata", sizeMedia);
    vid.addEventListener("canplay", () => { $("#vload").hidden = true; }, { once: true });
    vid.addEventListener("ended", () => { if (V.slide) nav(1); });
    vid.addEventListener("error", () => {
      $("#vload").hidden = true;
      vholder.innerHTML = "";
      vholder.appendChild(el("div", "v-err", svgIcon("alert") + `<span>${esc(t("video_err"))}</span>`));
    });
    vholder.appendChild(vid);
  } else {
    const img = new Image();
    img.decoding = "async"; img.draggable = false; img.alt = "";
    img.src = viewSrc(p, V.hd);
    img.addEventListener("load", () => { $("#vload").hidden = true; sizeMedia(); scheduleSlide(); }, { once: true });
    img.addEventListener("error", () => {
      if (!img.dataset.fb) { img.dataset.fb = "1"; img.src = p.sample && !V.hd ? prox(p.file) : prox(p.sample || p.file); return; }
      $("#vload").hidden = true;
      vholder.innerHTML = "";
      vholder.appendChild(el("div", "v-err", svgIcon("alert") + `<span>${esc(t("img_err"))}</span>`));
    });
    img.addEventListener("dblclick", e => { setZoom(V.z > 1 ? 1 : 2.4, e.clientX, e.clientY); });
    vholder.appendChild(img);
  }

  renderInfo(p);
  preload(i + 1); preload(i - 1);
  if (!p.video && V.slide) scheduleSlide();
}
function preload(j) {
  const p = V.list && V.list[j];
  if (p && !p.video && p.ext !== "gif") { const im = new Image(); im.src = viewSrc(p, false); }
}
function syncViewerFav() {
  const p = V.list && V.list[V.i];
  if (!p) return;
  const on = S.favs.has(p.id);
  $("#vfav").classList.toggle("active", on);
  $("#vfav").title = t(on ? "fav_del" : "fav_add");
}
function sizeMedia() {
  const m = vholder.querySelector("img,video");
  if (!m) return;
  const nw = m.tagName === "VIDEO" ? m.videoWidth : m.naturalWidth;
  const nh = m.tagName === "VIDEO" ? m.videoHeight : m.naturalHeight;
  if (!nw || !nh) return;
  const sw = vstage.clientWidth - 48, sh = vstage.clientHeight - 20;
  let fit = Math.min(sw / nw, sh / nh);
  if (m.tagName === "IMG" && fit > 2.4) fit = 2.4;      // don't blow tiny images into mush
  m.style.width = Math.round(nw * fit) + "px";
  m.style.height = Math.round(nh * fit) + "px";
}
window.addEventListener("resize", () => { if (V.open) sizeMedia(); });

function renderInfo(p) {
  vpanel.innerHTML = "";
  const tagsH = el("h4", "", esc(t("t_tags")) + ` <span style="color:var(--faint);font-weight:500">· ${p.tags.length}</span>`);
  vpanel.appendChild(tagsH);
  const list = el("div");
  for (const tag of p.tags) {
    const row = el("div", "tagrow");
    const b = el("button", "tg", esc(tag.replaceAll("_", " ")));
    b.title = t("t_search_tag");
    b.addEventListener("click", () => { closeViewer(); exitSimilar(true); setMode("browse"); S.tags = [tag]; renderChips(); runSearch(); });
    const add = el("button", "mini", svgIcon("plus"));
    add.title = t("t_add_tag");
    add.addEventListener("click", () => { addTag(tag, true); toast(tag, "ok", "plus"); });
    const not = el("button", "mini", svgIcon("minus"));
    not.title = t("t_excl_tag");
    not.addEventListener("click", () => { addTag("-" + tag, true); toast("−" + tag, "ok", "minus"); });
    row.append(b, add, not);
    list.appendChild(row);
  }
  vpanel.appendChild(list);
  const cpTags = el("button", "sbtn", svgIcon("copy") + `<span>${esc(t("t_copy_tags"))}</span>`);
  cpTags.style.marginTop = "10px";
  cpTags.addEventListener("click", () => copyText(p.tags.join(" ")));
  vpanel.appendChild(cpTags);

  vpanel.appendChild(el("h4", "", esc(t("t_meta"))));
  const rows = [];
  rows.push([t("t_id"), `<a href="${esc(p.page_url)}" target="_blank" rel="noopener noreferrer">#${p.id}</a>`]);
  rows.push([t("t_score"), fmtN(p.score || 0)]);
  if (p.rating) rows.push([t("t_rating"), `<span style="color:var(--r-${p.rating})">${esc(t("rating_" + p.rating))}</span>`]);
  if (p.w && p.h) rows.push([t("t_size"), `${p.w} × ${p.h}` + (p.ext ? ` · ${esc(p.ext.toUpperCase())}` : "")]);
  if (p.change) rows.push([t("t_date"), new Date(p.change * 1000).toLocaleDateString(LANG === "ru" ? "ru" : "en", { year: "numeric", month: "short", day: "numeric" })]);
  if (p.source) {
    const src = /^https?:\/\//i.test(p.source)
      ? `<a href="${esc(p.source)}" target="_blank" rel="noopener noreferrer">${esc(shortUrl(p.source))}</a>`
      : esc(p.source);
    rows.push([t("t_source"), src]);
  }
  const table = el("table", "meta-t", rows.map(r => `<tr><td>${esc(r[0])}</td><td>${r[1]}</td></tr>`).join(""));
  vpanel.appendChild(table);

  const simBtn = el("button", "sbtn wide", svgIcon("similar") + `<span>${esc(t("similar"))}</span>`);
  simBtn.addEventListener("click", () => startSimilarFrom(p));
  vpanel.appendChild(simBtn);

  const btns = el("div", "rowbtns");
  const cpl = el("button", "sbtn", svgIcon("copy") + `<span>${esc(t("copy_link"))}</span>`);
  cpl.addEventListener("click", () => copyText(p.file));
  btns.appendChild(cpl);
  vpanel.appendChild(btns);
}
function shortUrl(u) { try { const x = new URL(u); return x.hostname + (x.pathname.length > 22 ? x.pathname.slice(0, 22) + "…" : x.pathname); } catch { return u.slice(0, 40); } }
function copyText(text) {
  (navigator.clipboard ? navigator.clipboard.writeText(text) : Promise.reject())
    .then(() => toast(t("copied"), "ok", "check"))
    .catch(() => { const ta = el("textarea"); ta.value = text; document.body.appendChild(ta); ta.select(); document.execCommand("copy"); ta.remove(); toast(t("copied"), "ok", "check"); });
}

async function nav(dir) {
  if (!V.open || !V.list) return;
  const j = V.i + dir;
  if (j < 0) return;
  if (j >= V.list.length) {
    if (S.mode !== "favorites" && V.list === S.posts && !S.ended) {
      await loadMore();
      if (j >= V.list.length) { if (V.slide) stopSlideshow(); return; }
    } else { if (V.slide) stopSlideshow(); return; }
  }
  renderViewer(j);
}

/* zoom + pan */
vstage.addEventListener("wheel", e => {
  const p = V.list && V.list[V.i];
  if (!p || p.video) return;
  e.preventDefault();
  setZoom(V.z * Math.exp(-e.deltaY * 0.0016), e.clientX, e.clientY);
}, { passive: false });
let panPointer = null, panMoved = false;
vstage.addEventListener("pointerdown", e => {
  if (e.button !== 0) return;
  const p = V.list && V.list[V.i];
  if (!p || p.video || V.z <= 1) return;
  panPointer = { id: e.pointerId, x: e.clientX, y: e.clientY };
  panMoved = false;
  vstage.classList.add("panning");
  vstage.setPointerCapture(e.pointerId);
});
vstage.addEventListener("pointermove", e => {
  if (!panPointer || e.pointerId !== panPointer.id) return;
  const dx = e.clientX - panPointer.x, dy = e.clientY - panPointer.y;
  if (Math.abs(dx) + Math.abs(dy) > 3) panMoved = true;
  panPointer.x = e.clientX; panPointer.y = e.clientY;
  V.tx += dx; V.ty += dy;
  clampPan();
  applyZoom();
});
const endPan = e => {
  if (panPointer && e.pointerId === panPointer.id) { panPointer = null; vstage.classList.remove("panning"); }
};
vstage.addEventListener("pointerup", endPan);
vstage.addEventListener("pointercancel", endPan);
vstage.addEventListener("click", e => { if (e.target === vstage && !panMoved) closeViewer(); });

/* slideshow */
function scheduleSlide() {
  stopSlideTimer();
  if (!V.slide) return;
  const p = V.list && V.list[V.i];
  if (p && !p.video) V.slideTimer = setTimeout(() => nav(1), 5000);
}
function stopSlideTimer() { clearTimeout(V.slideTimer); V.slideTimer = 0; }
function stopSlideshow() {
  V.slide = false;
  stopSlideTimer();
  $("#vslide").classList.remove("active");
  const vid = vholder.querySelector("video");
  if (vid) vid.loop = LS.get("loop", false);
}
function toggleSlideshow() {
  if (V.slide) { stopSlideshow(); return; }
  V.slide = true;
  $("#vslide").classList.add("active");
  const vid = vholder.querySelector("video");
  if (vid) { vid.loop = false; if (vid.paused) vid.play().catch(() => {}); }
  else scheduleSlide();
}

/* viewer buttons */
$("#vclose").addEventListener("click", closeViewer);
$("#vprev").addEventListener("click", () => nav(-1));
$("#vnext").addEventListener("click", () => nav(1));
$("#vfav").addEventListener("click", () => { const p = V.list[V.i]; if (p) toggleFav(p); });
$("#vdl").addEventListener("click", () => { const p = V.list[V.i]; if (p) downloadPost(p); });
$("#vsim").addEventListener("click", () => { const p = V.list[V.i]; if (p) startSimilarFrom(p); });
$("#vext").addEventListener("click", () => { const p = V.list[V.i]; if (p) window.open(p.page_url, "_blank", "noopener"); });
$("#vinfo").addEventListener("click", () => {
  V.sbOpen = !V.sbOpen;
  viewer.classList.toggle("hasinfo", V.sbOpen);
  persistCfg({ sidebar: V.sbOpen });
  sizeMedia();
});
$("#vhd").addEventListener("click", loadHd);
$("#vloop").addEventListener("click", () => {
  const on = !LS.get("loop", false);
  LS.set("loop", on);
  $("#vloop").classList.toggle("active", on);
  const vid = vholder.querySelector("video");
  if (vid && !V.slide) vid.loop = on;
});
$("#vslide").addEventListener("click", toggleSlideshow);
$("#vfull").addEventListener("click", () => {
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  else viewer.requestFullscreen().catch(() => {});
});

/* ═══════════════ Toolbar ═══════════════ */
function setRating(r, silent) {
  S.cfg.rating = r;
  $$("#ratingseg button").forEach(b => b.classList.toggle("on", b.dataset.r === r));
  persistCfg({ rating: r });
  if (!silent) runSearch();
}
$$("#ratingseg button").forEach(b => b.addEventListener("click", () => {
  S.tags = S.tags.filter(x => !/^-?rating:/.test(x));
  renderChips();
  setRating(b.dataset.r);
}));
$("#sortsel").addEventListener("change", () => { persistCfg({ sort: $("#sortsel").value }); runSearch(); });
$$("#densityseg button").forEach(b => b.addEventListener("click", () => {
  persistCfg({ density: b.dataset.d });
  applyPrefs();
}));
$("#themebtn").addEventListener("click", () => { persistCfg({ theme: S.cfg.theme === "dark" ? "light" : "dark" }); applyPrefs(); });
$("#langbtn").addEventListener("click", () => {
  const next = LANG === "ru" ? "en" : "ru";
  persistCfg({ lang: next });
  applyPrefs();
  if (V.open) { renderInfo(V.list[V.i]); syncViewerFav(); }
  if (!$("#settings").hidden) fillSettings();
  updateStats();
});

/* ═══════════════ Settings ═══════════════ */
const settings = $("#settings");
function openSettings() {
  fillSettings();
  settings.hidden = false;
  setTimeout(() => $("#f_key").focus(), 60);
}
function closeSettings() { settings.hidden = true; $("#st_status").textContent = ""; $("#st_status").className = "status"; }
function fillSettings() {
  $("#f_key").value = S.cfg.api_key;
  $("#f_uid").value = S.cfg.user_id;
  $("#f_pp").value = String([20,42,60,80].includes(S.cfg.per_page) ? S.cfg.per_page : 42);
  $("#f_lang").value = S.cfg.lang;
  $("#f_full").checked = !!S.cfg.full_quality;
  $("#f_hq").checked = S.cfg.hq_previews !== false;
  $("#f_autoplay").checked = !!S.cfg.autoplay;
  $("#f_muted").checked = !!S.cfg.muted;
  $("#f_hover").checked = !!S.cfg.hover_preview;
  $("#blacklist").value = (S.cfg.blacklist || []).join("\n");
}
function parseKeyBlob() {
  const v = $("#f_key").value;
  const mk = v.match(/api_key=([A-Za-z0-9]+)/);
  if (mk) {
    $("#f_key").value = mk[1];
    const mu = v.match(/user_id=(\d+)/);
    if (mu) $("#f_uid").value = mu[1];
  }
}
$("#f_key").addEventListener("input", parseKeyBlob);
$("#peekkey").addEventListener("click", () => {
  const f = $("#f_key");
  f.type = f.type === "password" ? "text" : "password";
});
function collectSettings() {
  parseKeyBlob();
  return {
    api_key: $("#f_key").value.trim(),
    user_id: $("#f_uid").value.trim(),
    per_page: parseInt($("#f_pp").value, 10) || 42,
    lang: $("#f_lang").value,
    full_quality: $("#f_full").checked,
    hq_previews: $("#f_hq").checked,
    autoplay: $("#f_autoplay").checked,
    muted: $("#f_muted").checked,
    hover_preview: $("#f_hover").checked,
    blacklist: $("#blacklist").value.split("\n").map(x => x.trim()).filter(Boolean),
  };
}
async function saveSettings(thenCheck) {
  const patch = collectSettings();
  const refetch = ["api_key","user_id","per_page","blacklist","hq_previews"]
    .some(k => JSON.stringify(patch[k]) !== JSON.stringify(S.cfg[k]));
  const status = $("#st_status");
  try {
    const d = await api("/api/config", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(patch) });
    S.cfg = d.config;
    applyPrefs();
    if (thenCheck) {
      status.className = "status";
      status.textContent = t("st_checking");
      try {
        const test = await api("/api/posts?tags=&page=1&limit=1");
        status.className = "status ok";
        status.textContent = t("st_ok", { n: test.count == null ? "?" : fmtN(test.count) });
      } catch (e) {
        status.className = "status bad";
        status.textContent = errMsg(e);
      }
    } else {
      closeSettings();
      toast(t("st_saved"), "ok");
    }
    if (refetch) {
      if (S.mode === "similar") startSimilar(false);
      else if (S.mode === "browse") runSearch(false);
      else renderFavGrid();
    }
  } catch (e) {
    status.className = "status bad";
    status.textContent = errMsg(e);
  }
}
$("#st_save").addEventListener("click", () => saveSettings(false));
$("#st_check").addEventListener("click", () => saveSettings(true));
$("#setbtn").addEventListener("click", openSettings);
settings.addEventListener("pointerdown", e => { if (e.target === settings) closeSettings(); });

/* ═══════════════ Misc UI ═══════════════ */
const totop = $("#totop");
let scrollTick = 0;
addEventListener("scroll", () => {
  totop.hidden = scrollY < 1400;
  if (scrollTick) return;
  scrollTick = setTimeout(() => {          // belt-and-braces: the observer can miss
    scrollTick = 0;                        // fast flings and zero-height reflows
    if (!V.open && sentinelVisible()) topUp();
  }, 150);
}, { passive: true });
totop.addEventListener("click", () => scrollTo({ top: 0, behavior: "smooth" }));

/* ═══════════════ Keyboard ═══════════════ */
document.addEventListener("keydown", e => {
  const typing = /^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement && document.activeElement.tagName);
  if (!settings.hidden) {
    if (e.key === "Escape") closeSettings();
    return;
  }
  if (V.open) {
    if (typing) return;
    const vid = vholder.querySelector("video");
    const onVideo = vid && document.activeElement === vid;   // native controls own arrows/space there
    switch (e.key) {
      case "Escape": closeViewer(); break;
      case "ArrowLeft": if (onVideo) return; e.preventDefault(); nav(-1); break;
      case "ArrowRight": if (onVideo) return; e.preventDefault(); nav(1); break;
      case " ": if (onVideo) return; if (vid) { e.preventDefault(); vid.paused ? vid.play().catch(()=>{}) : vid.pause(); } break;
      case "f": case "F": case "а": case "А": { const p = V.list[V.i]; if (p) toggleFav(p); break; }
      case "s": case "S": case "ы": case "Ы": { const p = V.list[V.i]; if (p) startSimilarFrom(p); break; }
      case "d": case "D": case "в": case "В": $("#vdl").click(); break;
      case "i": case "I": case "ш": case "Ш": $("#vinfo").click(); break;
      case "m": case "M": case "ь": case "Ь": if (vid) vid.muted = !vid.muted; break;
    }
    return;
  }
  if (e.key === "/" && !typing) { e.preventDefault(); qInput.focus(); }
  else if (e.key === "Escape" && typing) document.activeElement.blur();
});

/* ═══════════════ Init ═══════════════ */
(async function init() {
  try {
    const d = await api("/api/config");
    S.cfg = d.config;
  } catch (e) {
    S.cfg = { api_key:"", user_id:"", per_page:42, lang:"auto", theme:"dark", density:"cozy",
              rating:"all", sort:"newest", autoplay:true, muted:true, hover_preview:true, sidebar:true,
              full_quality:false, hq_previews:true, blacklist:[] };
    toast(errMsg(e), "err");
  }
  stateFromHash();
  applyPrefs();
  renderChips();
  syncModeChrome();
  loadFavorites();
  if (!S.cfg.api_key || !S.cfg.user_id) {
    showHero("nokey");
    updateStats();
    openSettings();
  } else if (S.mode === "similar") {
    startSimilar(false);
  } else {
    runSearch(false);
  }
})();

</script>
</body>
</html>
'''

if __name__ == "__main__":
    sys.exit(main())
