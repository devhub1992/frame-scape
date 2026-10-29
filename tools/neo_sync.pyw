# -*- coding: utf-8 -*-
"""
NeoSync (lite) — pure-tkinter edition of neocities_sync, single file.
=====================================================================
Same app, same features, same ~/.neocities-sync/config.json — but built ONLY
on Python's stock tkinter (no customtkinter). Use this one if customtkinter
refuses to install, or when you want zero GUI dependencies beyond tkinter.

.deliver as  neocities_sync_tk.pyw  (double-click on Windows runs without a console)

  pip install requests          # the ONLY hard dependency
  pip install tkinterdnd2       # OPTIONAL — enables drag & drop

WHAT'S DIFFERENT vs the customtkinter edition (neocities_sync.pyw)
  * Identical core: Neocities client (upload/delete/download), Scan & Plan,
    mirror Sync, drop-guess engine, auto-sync timer, Verify, and the hidden
    Rebuild (Settings ▸ Maintenance — server→local pull, `neocities pull .`
    style).
  * UI redrawn with plain tk/ttk widgets in the same WWZ dark design
    (#1a1a1a surfaces / #f39a24 amber / #ececed text + slim dark scrollbars).
    Flat buttons, stat tiles, filter chips and plan rows are recreated 1:1.
  * theme/scrollbar overrides from config.json apply on next launch (no live
    re-style in the lite edition).
  * Mouse-wheel scrolling is routed app-wide (plain tk canvases don't scroll
    out of the box); with tkinterdnd2 present, drag & drop works as usual.

CONFIG      ~/.neocities-sync/config.json   (shared with the main edition)
"""
from __future__ import annotations

import os
import re
import sys
import json
import time
import random
import difflib
import fnmatch
import hashlib
import mimetypes
import posixpath
import threading
import queue
import traceback
import urllib.parse
import webbrowser
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests

import tkinter as tk
import tkinter.ttk as ttk
from tkinter import font as tkfont, filedialog, messagebox

try:  # drag & drop is optional; app degrades to "choose files" buttons
    from tkinterdnd2 import TkinterDnD, DND_FILES
    HAS_DND = True
except Exception:
    HAS_DND = False

APP_NAME = "NeoSync"
APP_VER = "1.2.0"   # 1.0.1 perf: chunked plain-tk plan rows, no CTk DPI
                    # rescale storm, gated re-scan, batch-level dir gather
                    # 1.1.0: auto-sync — Scan & Plan + Sync on an interval
                    # 1.2.0: rebuild — server→local pull, Settings ▸ Maintenance
API_BASE = "https://neocities.org"
CONFIG_DIR = os.path.join(os.path.expanduser("~"), ".neocities-sync")
CONFIG_PATH = os.path.join(CONFIG_DIR, "config.json")

# ── theme: WWZ unified profile §02 tokens-dark, "Dark · effects off" mode ──
THEME_DEFAULTS = {
    "bg": "#1a1a1a", "bg2": "#222222", "bg3": "#2a2a2a", "bg4": "#333333",
    "bg5": "#3a3a3a", "bg6": "#444444", "black_hl": "#000000",
    "fg1": "#ececed", "fg2": "#a4a4a8", "fg3": "#6f6f73",
    "accent": "#f39a24", "accent2": "#ffad3d", "accent_dark": "#a76a1c",
    "ok": "#5cb47e", "err": "#d96565", "info": "#7ba3d8",
    "border1": "#262626", "border2": "#313131", "comp": "#414141",
    "buy": "#2a2a2e",
    # §23 Ultra-Thin Minimal scrollbar standard
    "scrl_width": 6, "scrl_thumb": "#4b5563", "scrl_thumb_hover": "#6b7280",
    "scrl_track": "#000000", "scrl_radius": 3,
}
# font stacks — type.font.ui / type.font.mono with sane fallbacks
UI_FONTS = ["Space Grotesk", "Segoe UI Variable Text", "Segoe UI",
            "SF Pro Text", "Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"]
MONO_FONTS = ["JetBrains Mono", "Cascadia Mono", "Cascadia Code", "Consolas",
              "SF Mono", "Menlo", "DejaVu Sans Mono", "Courier New"]

DEFAULT_CONFIG = {
    "api_key": "",
    "site_name": "",
    "site_domain": "",
    "local_folder": "",
    "workers": 8,
    "mirror_deletes": True,
    "auto_verify": True,
    "auto_scan_on_open": True,
    "auto_sync_secs": 0,           # >0: run Scan&Plan + Sync every N seconds
    "auto_sync_deletes": False,    # allow the interval job to mirror-delete
    "excludes": ["*.psd", "*.ai", "*.log", "*.tmp", "*.bak", "node_modules/",
                 ".DS_Store", "Thumbs.db", "desktop.ini", "__MACOSX/"],
    "learned_routes": {},          # normalized source folder -> remote folder
    "theme": {},                   # user overrides of THEME_DEFAULTS
    "scrollbar": {},               # user overrides of §23 tokens
    "last_sync": None,             # unix epoch
}


# ── small utils ──────────────────────────────────────────────────────────────
def blend(fg: str, bg: str, alpha: float) -> str:
    """alpha-composite fg over bg, both '#rrggbb' -> '#rrggbb'."""
    f, b = fg.lstrip("#"), bg.lstrip("#")
    f = f * (6 // len(f)) if len(f) == 3 else f
    b = b * (6 // len(b)) if len(b) == 3 else b
    r = round(int(f[0:2], 16) * alpha + int(b[0:2], 16) * (1 - alpha))
    g = round(int(f[2:4], 16) * alpha + int(b[2:4], 16) * (1 - alpha))
    bl = round(int(f[4:6], 16) * alpha + int(b[4:6], 16) * (1 - alpha))
    return "#%02x%02x%02x" % (min(r, 255), min(g, 255), min(bl, 255))


def sha1_file(path: str, buf: int = 1 << 20) -> str:
    h = hashlib.sha1()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(buf)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def human_size(n) -> str:
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return ("%d %s" % (n, unit)) if unit == "B" else ("%.1f %s" % (n, unit))
        n /= 1024.0
    return "%d B" % n


def rel_ago(epoch) -> str:
    if not epoch:
        return "never"
    d = max(0, time.time() - float(epoch))
    if d < 60:
        return "just now"
    if d < 3600:
        return "%dm ago" % (d // 60)
    if d < 86400:
        return "%dh ago" % (d // 3600)
    return "%dd ago" % (d // 86400)


AUTO_CHOICES = [("Off", 0), ("Every 30 s", 30), ("Every 1 min", 60),
                ("Every 2 min", 120), ("Every 5 min", 300),
                ("Every 15 min", 900), ("Every 30 min", 1800),
                ("Every 1 h", 3600)]


def _secs_choice(secs: int) -> str:
    """full label from AUTO_CHOICES for a seconds value (fallback: Off)."""
    for label, s in AUTO_CHOICES:
        if s == secs:
            return label
    return "Off"


def norm_key(path: str) -> str:
    """stable normalized key for learned route mapping."""
    try:
        p = os.path.normpath(os.path.abspath(path))
    except Exception:
        p = str(path)
    return p.lower().replace("\\", "/")


def to_posix(p: str) -> str:
    return (p or "").replace("\\", "/").strip("/")


def in_root(root: str, path: str):
    """return (inside?, posix relpath) for path under root."""
    if not root or not os.path.isdir(root):
        return False, None
    ra, pa = os.path.abspath(root), os.path.abspath(path)
    try:
        rel = os.path.relpath(pa, ra)
    except ValueError:
        return False, None
    if rel == ".." or rel.startswith(".." + os.sep) or os.path.isabs(rel):
        return False, None
    return True, rel.replace(os.sep, "/")


def is_excluded(rel_posix: str, name: str, is_dir: bool, patterns) -> bool:
    rel = to_posix(rel_posix).lower()
    low_name = (name or "").lower()
    for pat in patterns or []:
        p = (pat or "").strip().strip("/").lower()
        if not p:
            continue
        if "/" in pat.strip("/"):
            if fnmatch.fnmatch(rel, p) or rel.startswith(p + "/"):
                return True
        elif fnmatch.fnmatch(low_name, p):
            return True
    return False


def count_files_fast(root: str, excludes) -> int:
    """cheap walk that only COUNTS non-excluded files (no stat / no sha1).
    Used to decide whether an automatic full re-scan is worth the disk hit."""
    n = 0
    root = os.path.abspath(root)
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames
                       if not is_excluded(os.path.relpath(
                           os.path.join(dirpath, d), root).replace(os.sep, "/"),
                           d, True, excludes)]
        for fn in filenames:
            try:
                rel = os.path.relpath(os.path.join(dirpath, fn),
                                      root).replace(os.sep, "/")
            except ValueError:
                continue
            if not is_excluded(rel, fn, False, excludes):
                n += 1
    return n


# ── config ─────────────────────────────────────────────────────────────────
def deep_merge(base: dict, over: dict) -> dict:
    out = dict(base)
    for k, v in (over or {}).items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = deep_merge(out[k], v)
        else:
            out[k] = v
    return out


def load_config() -> dict:
    os.makedirs(CONFIG_DIR, exist_ok=True)
    cfg = deep_merge(DEFAULT_CONFIG, {})
    if os.path.isfile(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                cfg = deep_merge(DEFAULT_CONFIG, json.load(f))
        except Exception:
            pass  # corrupt config -> fall back to defaults, keep file for inspection
    else:
        save_config(cfg)
    return cfg


def save_config(cfg: dict) -> None:
    os.makedirs(CONFIG_DIR, exist_ok=True)
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)
    os.replace(tmp, CONFIG_PATH)


def build_theme(cfg: dict) -> dict:
    """merge user overrides + compute alpha washes from §02 tokens."""
    t = deep_merge(THEME_DEFAULTS, (cfg.get("theme") or {}))
    sb = deep_merge({"width": t["scrl_width"], "thumb": t["scrl_thumb"],
                     "thumb_hover": t["scrl_thumb_hover"], "track": t["scrl_track"]},
                    (cfg.get("scrollbar") or {}))
    t["accent_dim"] = blend(t["accent"], t["bg"], 0.10)        # tok.accent.dim
    t["accent_border"] = blend(t["accent"], t["bg"], 0.35)     # tok.accent.active-border
    t["ok_dim"] = blend(t["ok"], t["bg"], 0.12)
    t["err_dim"] = blend(t["err"], t["bg"], 0.12)
    t["info_dim"] = blend(t["info"], t["bg"], 0.12)
    t["scrl_width"] = int(sb["width"]); t["scrl_thumb"] = sb["thumb"]
    t["scrl_thumb_hover"] = sb["thumb_hover"]; t["scrl_track"] = sb["track"]
    return t


# ── errors ───────────────────────────────────────────────────────────────────
_PLAIN_SESS = None


def _plain_session():
    """requests.Session WITHOUT the API key — used for rebuild downloads via
    custom domains, so the bearer token is never sent to a non-neocities
    host. Public site files need no auth anyway."""
    global _PLAIN_SESS
    if _PLAIN_SESS is None:
        _PLAIN_SESS = requests.Session()
        _PLAIN_SESS.headers.update(
            {"User-Agent": "%s/%s" % (APP_NAME, APP_VER)})
    return _PLAIN_SESS


class ApiError(Exception):
    def __init__(self, status: int, body: str = ""):
        self.status, self.body = status, (body or "")[:220]
        super().__init__("HTTP %s %s" % (status or "?", self.body))


class Cancelled(Exception):
    pass


class QuietExit(Exception):
    """user-fixable condition already reported to the UI."""


# ── Neocities REST client ────────────────────────────────────────────────────
class Neocities:
    """Bearer-auth client. Retries 429/5xx/conn-errors with backoff; honours cancel."""

    def __init__(self, api_key: str, cancel: threading.Event = None):
        self.cancel = cancel or threading.Event()
        self.sess = requests.Session()
        self.sess.headers.update({
            "Authorization": "Bearer %s" % api_key.strip(),
            "User-Agent": "%s/%s" % (APP_NAME, APP_VER),
        })

    # low-level ---------------------------------------------------------------
    def _backoff(self, attempt: int):
        time.sleep(min(8.0, 1.6 ** attempt) + random.uniform(0.0, 0.6))

    def _req(self, method: str, path: str, tries: int = 4, **kw):
        last = None
        for attempt in range(tries):
            if self.cancel.is_set():
                raise Cancelled()
            try:
                r = self.sess.request(method, API_BASE + path, timeout=(10, 90), **kw)
                if r.status_code == 429 or r.status_code >= 500:
                    last = ApiError(r.status_code, (r.text or "")[:160])
                    self._backoff(attempt)
                    continue
                if r.status_code >= 400:
                    raise ApiError(r.status_code, (r.text or "")[:220])
                try:
                    return r.json()
                except ValueError:
                    return {"result": "success", "message": (r.text or "")[:160]}
            except (requests.exceptions.ConnectionError,
                    requests.exceptions.Timeout) as e:
                last = e
                self._backoff(attempt)
        raise last if last is not None else RuntimeError("request failed")

    @staticmethod
    def _normalize(j: dict) -> dict:
        out = {}
        for e in (j.get("files") or []):
            p = (e.get("path") or "").lstrip("/")
            if not p:
                continue
            out[p] = {"path": p, "is_dir": bool(e.get("is_directory")),
                      "size": e.get("size") or 0,
                      "sha1": (e.get("sha1_hash") or "").lower() or None,
                      "updated_at": e.get("updated_at") or ""}
        return out

    # endpoints ---------------------------------------------------------------
    def list_all(self) -> dict:
        return self._normalize(self._req("GET", "/api/list"))

    def list_dir(self, path: str) -> dict:
        q = ("?path=" + urllib.parse.quote(path)) if path else ""
        return self._normalize(self._req("GET", "/api/list" + q))

    def info(self) -> dict:
        j = self._req("GET", "/api/info")
        return j.get("info") or {}

    def upload(self, remote_path: str, local_path: str) -> str:
        """multipart: field NAME == full destination path on the site.
        Missing destination directories are created automatically by the server."""
        remote_path = to_posix(remote_path)
        mime = mimetypes.guess_type(local_path)[0] or "application/octet-stream"
        with open(local_path, "rb") as fh:
            files = {remote_path: (posixpath.basename(remote_path), fh, mime)}
            j = self._req("POST", "/api/upload", files=files)
        if str(j.get("result")) != "success":
            raise ApiError(0, str(j.get("message") or j)[:220])
        return j.get("message") or "uploaded"

    def download(self, remote_path: str, local_path: str, base_url: str,
                 tries: int = 4) -> bool:
        """server→local pull (what the CLI's `neocities pull` does): GET the
        live file from the site's public URL and stream it to local_path.
        Bearer auth is only attached for *.neocities.org hosts — the key is
        never sent to custom domains. Retries 429/5xx/conn-errors with
        backoff, honours cancel, writes via a .part temp file. Returns True
        on success; raises ApiError for 4xx / exhausted retries."""
        remote_path = to_posix(remote_path)
        url = base_url + urllib.parse.quote(remote_path)
        host = (urllib.parse.urlsplit(url).hostname or "").lower()
        sess = self.sess if host.endswith("neocities.org") else _plain_session()
        last = None
        for attempt in range(tries):
            if self.cancel.is_set():
                raise Cancelled()
            r = None
            try:
                r = sess.get(url, timeout=(10, 120), stream=True)
                if r.status_code == 429 or r.status_code >= 500:
                    last = ApiError(r.status_code, (r.text or "")[:160])
                    r.close()
                    self._backoff(attempt)
                    continue
                if r.status_code >= 400:
                    body = ""
                    try:
                        body = (r.text or "")[:160]
                    except Exception:
                        pass
                    r.close()
                    raise ApiError(r.status_code, body)
                d = os.path.dirname(local_path)
                if d:
                    os.makedirs(d, exist_ok=True)
                tmp = local_path + ".part~"
                try:
                    with open(tmp, "wb") as f:
                        for chunk in r.iter_content(1 << 15):
                            if self.cancel.is_set():
                                raise Cancelled()
                            if chunk:
                                f.write(chunk)
                    os.replace(tmp, local_path)
                except Cancelled:
                    try:
                        os.remove(tmp)
                    except OSError:
                        pass
                    raise
                return True
            except (requests.exceptions.ConnectionError,
                    requests.exceptions.Timeout) as e:
                last = e
                self._backoff(attempt)
            finally:
                if r is not None:
                    try:
                        r.close()
                    except Exception:
                        pass
        if isinstance(last, ApiError):
            raise last
        raise ApiError(0, str(last or "download failed")[:220])

    def delete(self, paths) -> list:
        """batches of 25; a failing batch falls back to one-by-one so one bad
        path cannot cancel its neighbours. Returns the list of failures."""
        paths = list(paths)
        failed = []
        B = 25
        for i in range(0, len(paths), B):
            batch = paths[i:i + B]
            if self.cancel.is_set():
                raise Cancelled()
            data = [("filenames[]", p) for p in batch]
            try:
                j = self._req("POST", "/api/delete", data=data)
                if str(j.get("result")) != "success":
                    raise ApiError(0, str(j.get("message") or j)[:160])
            except ApiError:
                if len(batch) == 1:
                    failed.append(batch[0])
                else:
                    for p in batch:
                        if self.cancel.is_set():
                            raise Cancelled()
                        try:
                            j2 = self._req("POST", "/api/delete",
                                           data=[("filenames[]", p)])
                            if str(j2.get("result")) != "success":
                                failed.append(p)
                        except ApiError:
                            failed.append(p)
        return failed
# ═════════════════════════════════════════════════════════════════════════════
#  LOCAL SCANNER · MIRROR PLAN · DROP-GUESS ENGINE
# ═════════════════════════════════════════════════════════════════════════════

def scan_folder(root: str, excludes, cancel=None, progress=None,
                sha_cache=None) -> dict:
    """walk local site folder -> {posix relpath: {size, mtime, sha1}}.
    Excluded dirs are pruned (never descended). Unreadable files are skipped.
    sha_cache: optional {rel: (size, mtime, sha1)} — files whose size AND
    mtime are unchanged reuse the cached hash (rsync-style quick check), so
    interval auto-syncs don't re-hash the whole site every tick."""
    out = {}
    root = os.path.abspath(root)
    n = 0
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames
                       if not is_excluded(os.path.relpath(
                           os.path.join(dirpath, d), root).replace(os.sep, "/"),
                           d, True, excludes)]
        for fn in filenames:
            if cancel is not None and cancel.is_set():
                raise Cancelled()
            full = os.path.join(dirpath, fn)
            try:
                rel = os.path.relpath(full, root).replace(os.sep, "/")
            except ValueError:
                continue
            if rel == "." or rel.startswith("../"):
                continue
            if is_excluded(rel, fn, False, excludes):
                continue
            try:
                if not os.path.isfile(full):
                    continue
                st = os.stat(full)
                sha = None
                if sha_cache is not None:
                    c = sha_cache.get(rel)
                    if c and c[0] == st.st_size \
                            and abs(c[1] - st.st_mtime) < 0.001:
                        sha = c[2]
                if sha is None:
                    sha = sha1_file(full)
                out[rel] = {"size": st.st_size, "mtime": st.st_mtime,
                            "sha1": sha}
                if sha_cache is not None:
                    sha_cache[rel] = (st.st_size, st.st_mtime, sha)
                n += 1
                if progress:
                    progress(n)
            except OSError:
                continue
    return out


def build_plan(local: dict, remote: dict) -> list:
    """compare local SHA1 map against remote /api/list map.
    Matching is case-insensitive (Windows FS vs Neocities is case-sensitive);
    a remote file is never flagged DELETE if any local file matches its name
    case-insensitively. Plan order: NEW (newest first) -> CHG -> DEL -> SAME."""
    remote_files = {p: e for p, e in (remote or {}).items() if not e["is_dir"]}
    low_remote = {}
    for p in remote_files:
        low_remote.setdefault(p.lower(), p)
    low_local = {}
    for p in (local or {}):
        low_local.setdefault(p.lower(), p)

    entries = []
    for lp, le in (local or {}).items():
        rp = low_remote.get(lp.lower())
        re_ = remote_files.get(rp) if rp else None
        if re_ is None:
            entries.append({"path": lp, "action": "new", "size": le["size"],
                            "mtime": le["mtime"], "note": ""})
        elif re_.get("sha1") and le.get("sha1"):
            # sha1 is the authority — when both sides are hashed, size is ignored
            if re_["sha1"] != le["sha1"]:
                entries.append({"path": lp, "action": "chg", "size": le["size"],
                                "mtime": le["mtime"], "note": "content differs"})
            else:
                entries.append({"path": lp, "action": "same", "size": le["size"],
                                "mtime": le["mtime"], "note": ""})
        elif (re_.get("size") or 0) != le["size"]:
            entries.append({"path": lp, "action": "chg", "size": le["size"],
                            "mtime": le["mtime"], "note": "size differs (no remote sha1)"})
        else:
            entries.append({"path": lp, "action": "same", "size": le["size"],
                            "mtime": le["mtime"], "note": ""})
    for rp, re_ in remote_files.items():
        if rp.lower() in low_local:
            continue
        note = ""
        if rp.lower() == "index.html":
            note = "root index.html is server-protected — will be skipped"
        entries.append({"path": rp, "action": "del", "size": re_.get("size") or 0,
                        "mtime": None, "note": note})

    order = {"new": 0, "chg": 1, "del": 2, "same": 3}
    entries.sort(key=lambda e: (order[e["action"]],
                                -(e["mtime"] or 0.0),
                                e["path"].lower()))
    return entries


def _unsafe_remote_path(p: str) -> bool:
    """true for paths a local pull must never touch (traversal / weird)."""
    if not p or p.startswith("/") or "\\" in p:
        return True
    return any(seg in ("..", "") for seg in p.split("/"))


def collect_pull_files(remote: dict, excludes):
    """server→local rebuild list (like the CLI's `neocities pull .`).
    Returns (files, dirs, collisions):
      files      sorted [{path, size, sha1}] — non-dir, non-excluded, safe
      dirs       sorted dir paths to mkdir locally (gem does mkdir_p too)
      collisions remote paths dropped because another path differs only by
                 case (case-insensitive local filesystems can't hold both)
    Excluded patterns are skipped so pulls never resurrect excluded junk."""
    files, dirs, collisions = [], [], []
    seen_low = {}
    for p, e in (remote or {}).items():
        if _unsafe_remote_path(p):
            continue
        if e["is_dir"]:
            if not is_excluded(p, p.rsplit("/", 1)[-1], True, excludes):
                dirs.append(p)
            continue
        low = p.lower()
        if low in seen_low:
            collisions.append(p)
            continue
        seen_low[low] = p
        if is_excluded(p, p.rsplit("/", 1)[-1], False, excludes):
            continue
        files.append({"path": p, "size": e.get("size") or 0,
                      "sha1": e.get("sha1")})
    files.sort(key=lambda f: f["path"].lower())
    dirs.sort()
    return files, dirs, collisions


# ── HTML hint extraction (what is this page about?) ─────────────────────────
def _clean_hint(t: str) -> str:
    t = re.sub(r"<[^>]+>", " ", t or "")
    return re.sub(r"\s+", " ", t).strip()


def extract_html_hints(path: str) -> list:
    """[<title>, og:title, first <h1>] — first 64KB, tag-stripped, unique."""
    hints = []
    try:
        with open(path, "rb") as f:
            raw = f.read(65536)
        s = raw.decode("utf-8", "ignore")
        m = re.search(r"<title[^>]*>(.*?)</title", s, re.I | re.S)
        if m:
            hints.append(_clean_hint(m.group(1)))
        m = re.search(r"<meta[^>]+(?:property|name)=['\"]og:title['\"][^>]*"
                      r"content=['\"](.*?)['\"]", s, re.I)
        if m:
            hints.append(_clean_hint(m.group(1)))
        m = re.search(r"<h1[^>]*>(.*?)</h1", s, re.I | re.S)
        if m:
            hints.append(_clean_hint(m.group(1)))
    except OSError:
        pass
    out, seen = [], set()
    for h in hints:
        if h and len(h) >= 3 and h.lower() not in seen:
            seen.add(h.lower())
            out.append(h[:60])
    return out[:3]


def gather_dirs(local_root: str, remote_map: dict, excludes) -> list:
    """candidate destination folders = remote dirs ∪ local site dirs (pruned)."""
    dirs = set()
    for p, e in (remote_map or {}).items():
        if e["is_dir"]:
            dirs.add(p)
    if local_root and os.path.isdir(local_root):
        root = os.path.abspath(local_root)
        for dirpath, dirnames, _ in os.walk(root):
            keep = []
            for d in dirnames:
                rel = os.path.relpath(os.path.join(dirpath, d), root).replace(os.sep, "/")
                if is_excluded(rel, d, True, excludes):
                    continue
                keep.append(d)
                dirs.add(rel)
            dirnames[:] = keep
    dirs.discard("")
    return sorted(dirs)


def rank_candidates(file_path: str, dirs, learned=None, hints=None) -> list:
    """score every known folder against the dropped file's context.
    Signals (cumulative): remembered route ★ > exact parent-name match >
    partial name match > fuzzy name similarity > page-title similarity.
    Returns top 3: [{dir, preview, score, rel, why}]."""
    fp = os.path.abspath(file_path)
    parent_dir = os.path.dirname(fp)
    parent = os.path.basename(parent_dir)
    parent_low = parent.lower()
    key = norm_key(parent_dir)
    learned = learned or {}
    hints = hints or []
    filename = os.path.basename(fp)
    remembered = learned.get(key)
    scores = {}

    def add(d, pts, why):
        s, whys = scores.get(d, (0, []))
        if why and why not in whys:
            whys = whys + [why]
        scores[d] = (s + pts, whys)

    for d in dirs or []:
        seg = d.rsplit("/", 1)[-1]
        seg_low = seg.lower()
        if remembered and d == remembered:
            add(d, 95, "★ remembered for this source folder")
        if parent_low and seg_low:
            if parent_low == seg_low:
                add(d, 55, 'folder name matches "%s"' % seg)
            elif seg_low in parent_low or parent_low in seg_low:
                add(d, 32, 'folder name close to "%s"' % parent)
            else:
                r = difflib.SequenceMatcher(None, parent_low, seg_low).ratio()
                if r >= 0.72:
                    add(d, int((r - 0.6) * 75), '"%s" ~ "%s" %d%%' % (seg, parent, r * 100))
        for h in hints:
            hl = h.lower()
            if seg_low and seg_low in hl:
                add(d, 16, 'page mentions "%s"' % seg)
                continue
            if seg_low:
                r = difflib.SequenceMatcher(None, hl, seg_low).ratio()
                if r >= 0.60:
                    add(d, int(r * 22), 'title ≈ "%s"' % seg)

    ranked = []
    for d, (s, whys) in scores.items():
        if s <= 0:
            continue
        preview = (d + "/" + filename) if d else filename
        ranked.append({"dir": d, "preview": preview, "score": s,
                       "why": "  ·  ".join(whys[:2])})
    ranked.sort(key=lambda c: (-c["score"], c["dir"]))
    mx = ranked[0]["score"] if ranked else 1
    for c in ranked:
        c["rel"] = max(0.15, min(1.0, c["score"] / float(mx)))
    return ranked[:3]

# ═════════════════════════════════════════════════════════════════════════════
#  UI — PURE TKINTER EDITION (no customtkinter), same WWZ design tokens
# ═════════════════════════════════════════════════════════════════════════════
if HAS_DND:
    class RootBase(TkinterDnD.Tk):
        pass
else:
    class RootBase(tk.Tk):
        pass


def pick_font(root, candidates, fallback):
    try:
        fams = set(tkfont.families(root))
        for c in candidates:
            if c in fams:
                return c
    except Exception:
        pass
    return fallback


class Btn(tk.Button):
    """flat CTk-look button: no relief, steady 1px ring, hover tint.
    Stays visually calm while disabled (hover only when armed)."""

    def __init__(self, parent, text, command=None, font=None, bg="#333333",
                 fg="#ececed", hover=None, ring=None, ring_hover=None,
                 disabled_fg="#6f6f73", padx=14, ipady=4, **kw):
        self._bg, self._hv = bg, hover or bg
        self._ring, self._ring_hv = ring, ring_hover or ring or bg
        super().__init__(parent, text=text, command=command, font=font,
                         bg=bg, fg=fg, activebackground=self._hv,
                         activeforeground=fg, disabledforeground=disabled_fg,
                         relief="flat", bd=0,
                         highlightthickness=1 if ring else 0,
                         highlightbackground=ring or bg,
                         highlightcolor=ring or bg, cursor="hand2",
                         padx=padx, pady=ipady, takefocus=0, **kw)
        self.bind("<Enter>", self._on_enter, add="+")
        self.bind("<Leave>", self._on_leave, add="+")

    def _armed(self):
        try:
            return str(self["state"]) != "disabled"
        except Exception:
            return True

    def _on_enter(self, _e):
        if self._armed():
            self.configure(bg=self._hv, highlightbackground=self._ring_hv)

    def _on_leave(self, _e):
        self.configure(bg=self._bg, highlightbackground=self._ring)

    def configure(self, cnf=None, **kw):
        """track external restyles (render_plan / auto-btn) so hover and
        leave states keep using the CURRENT colors, not the init ones."""
        merged = dict(cnf or {})
        merged.update(kw)
        try:
            if merged.get("bg"):
                self._bg = merged["bg"]
            if merged.get("activebackground"):
                self._hv = merged["activebackground"]
            if merged.get("highlightbackground"):
                self._ring = merged["highlightbackground"]
        except Exception:
            pass
        return super().configure(cnf, **kw)

    def itemconfig(self, *a, **k):   # tk alias
        return self.configure(*a, **k)


class ScrollFrame(tk.Frame):
    """dark canvas scroll area — the lite stand-in for CTkScrollableFrame.
    wheel() is called by the app-wide wheel router."""

    def __init__(self, parent, bg):
        super().__init__(parent, bg=bg, highlightthickness=0, bd=0)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0,
                                yscrollincrement=26)
        self.vsb = ttk.Scrollbar(self, orient="vertical",
                                 command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner = tk.Frame(self.canvas, bg=bg)
        self._win = self.canvas.create_window((0, 0), window=self.inner,
                                              anchor="nw")
        self.inner.bind("<Configure>", self._on_inner_cfg)
        self.canvas.bind("<Configure>", self._on_canvas_cfg)
        self.inner.grid_columnconfigure(0, weight=1)

    def _on_inner_cfg(self, _e):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _on_canvas_cfg(self, e):
        self.canvas.itemconfigure(self._win, width=e.width)

    def wheel(self, e):
        d = getattr(e, "delta", 0) or 0
        if d:
            self.canvas.yview_scroll(-1 if d > 0 else 1, "units")
        elif getattr(e, "num", 0) == 4:
            self.canvas.yview_scroll(-1, "units")
        elif getattr(e, "num", 0) == 5:
            self.canvas.yview_scroll(1, "units")


class ProgressCanvas(tk.Canvas):
    """6px slim bar — the lite stand-in for CTkProgressBar."""

    def __init__(self, parent, T, width=250, height=6):
        self._w0, self._h0 = width, height
        super().__init__(parent, width=width, height=height, bg=T["bg3"],
                         highlightthickness=0, bd=0)
        self._T, self._v = T, 0.0
        self.bind("<Configure>", lambda e: self._draw(), add="+")

    def set(self, v):
        self._v = max(0.0, min(1.0, float(v or 0.0)))
        self._draw()

    def _draw(self):
        self.delete("all")
        try:
            w = self.winfo_width() or self._w0
        except Exception:
            w = self._w0
        if self._v > 0:
            self.create_rectangle(0, 0, max(2, int(w * self._v)), self._h0,
                                  fill=self._T["accent"], width=0)


class App(RootBase):
    def __init__(self):
        super().__init__()
        self.cfg = load_config()
        self.T = build_theme(self.cfg)

        self.title("%s (lite) — Neocities drop & sync" % APP_NAME)
        self.geometry("1140x730")
        self.minsize(960, 620)
        self.configure(bg=self.T["bg"])
        self._setup_ttk_style()

        # state
        self.client = None
        self.remote_map = None
        self.remote_ts = 0.0
        self.local_map = None
        self.plan = []
        self.busy = False
        self.cancel_event = threading.Event()
        self.ui_q = queue.Queue()
        self.filter = "all"
        self._toast_job = None
        self._row_cap = 400         # hard cap of rows kept in the list
        self._row_chunk = 40        # rows rendered per event-loop pass
        self._chunk_gap = 20        # ms between passes
        self._rows_shown = 0
        self._render_gen = 0
        self._entries_view = []
        self._last_counts = {"all": 0, "new": 0, "chg": 0,
                             "same": 0, "del": 0}
        self._last_prog = None
        self._sha_cache = {}
        self._auto_job = None
        self._auto_ticker_job = None
        self._auto_left = 0

        self._pick_fonts()
        self._build_header()
        self._build_toolbar()
        self._build_content()
        self._build_footer()
        self.render_plan()
        self._apply_style()
        self._apply_dnd()

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(80, self._poll)
        self._arm_auto()

        self._log("NeoSync (lite) %s ready — pure tkinter, config: %s"
                  % (APP_VER, CONFIG_PATH), "dim")
        if not self.cfg.get("api_key"):
            self._log("No API key yet — click ⚙ Settings to add it "
                      "(neocities.org/settings → Your API Key).", "warn")
        if self.cfg.get("auto_scan_on_open") and self.cfg.get("local_folder") \
                and self.cfg.get("api_key"):
            self.after(700, self.start_scan)

    # style -------------------------------------------------------------------
    def _setup_ttk_style(self):
        T = self.T
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Vertical.TScrollbar",
                        background=T["scrl_thumb"],
                        troughcolor=T["scrl_track"],
                        bordercolor=T["scrl_track"],
                        arrowcolor=T["scrl_thumb_hover"],
                        arrowsize=10, gripcount=0, relief="flat")
        style.map("Vertical.TScrollbar",
                  background=[("active", T["scrl_thumb_hover"]),
                              ("!active", T["scrl_thumb"])])

    def _pick_fonts(self):
        T = self.T
        ui = pick_font(self, UI_FONTS, "TkDefaultFont")
        mo = pick_font(self, MONO_FONTS, "TkFixedFont")
        self.f_h1 = tkfont.Font(family=ui, size=17, weight="bold")
        self.f_body = tkfont.Font(family=ui, size=13)
        self.f_small = tkfont.Font(family=ui, size=11)
        self.f_label = tkfont.Font(family=ui, size=10, weight="bold")
        self.f_btn = tkfont.Font(family=ui, size=11, weight="bold")
        self.f_num = tkfont.Font(family=ui, size=16, weight="bold")
        self.f_mono = tkfont.Font(family=mo, size=12)
        self.f_mono_sm = tkfont.Font(family=mo, size=11)
        self.tk_small = tkfont.Font(family=ui, size=11)
        self.tk_tiny_b = tkfont.Font(family=ui, size=10, weight="bold")
        self.tk_mono = tkfont.Font(family=mo, size=11)
        self.tk_strike = tkfont.Font(family=mo, size=11, overstrike=True)

    def _kcolor(self, kind):
        T = self.T
        return {"ok": T["ok"], "err": T["err"], "warn": T["accent"],
                "info": T["info"], "dim": T["fg3"]}.get(kind, T["fg2"])

    # global wheel router -------------------------------------------------------
    def _install_wheel_router(self):
        if getattr(self, "_wheel_installed", False):
            return
        self._wheel_installed = True

        def route(e):
            w = getattr(e, "widget", None)
            while w is not None:
                if isinstance(w, ScrollFrame):
                    w.wheel(e)
                    return "break"
                nxt = getattr(w, "master", None)
                if nxt is None and isinstance(w, tk.Widget):
                    try:
                        nxt = self.nametowidget(w.winfo_parent())
                    except Exception:
                        nxt = None
                w = nxt
            return None
        self.bind_all("<MouseWheel>", route, add="+")
        self.bind_all("<Button-4>", route, add="+")
        self.bind_all("<Button-5>", route, add="+")

    # header ------------------------------------------------------------------
    def _build_header(self):
        T = self.T
        hdr = tk.Frame(self, bg=T["bg2"], height=86)
        hdr.grid(row=0, column=0, sticky="ew")
        hdr.grid_propagate(False)
        hdr.grid_columnconfigure(2, weight=1)
        self.hdr = hdr

        brand = tk.Frame(hdr, bg=T["bg2"])
        brand.grid(row=0, column=0, sticky="w", padx=(18, 6), pady=12)
        tk.Label(brand, text="NeoSync", font=self.f_h1, bg=T["bg2"],
                 fg=T["accent"]).grid(row=0, column=0, sticky="w")
        tk.Label(brand, text="drop · guess · sync · lite", font=self.f_label,
                 bg=T["bg2"], fg=T["fg3"]).grid(row=1, column=0, sticky="w")

        site = tk.Frame(hdr, bg=T["bg2"])
        site.grid(row=0, column=1, sticky="w", padx=(10, 6))
        self.site_name_lbl = tk.Label(site, text="not connected",
                                      font=self.f_body, bg=T["bg2"],
                                      fg=T["fg1"])
        self.site_name_lbl.grid(row=0, column=0, sticky="w")
        self.site_url_lbl = tk.Label(site, text="—", font=self.f_small,
                                     bg=T["bg2"], fg=T["info"],
                                     cursor="hand2")
        self.site_url_lbl.grid(row=1, column=0, sticky="w")
        self.site_url_lbl.bind("<Button-1>", lambda e: self._open_site())

        tiles = tk.Frame(hdr, bg=T["bg2"])
        tiles.grid(row=0, column=3, sticky="e", padx=(6, 10))
        self.tile_vals = {}
        for i, (key, cap) in enumerate([("files", "FILES"), ("views", "VIEWS"),
                                        ("hits", "HITS"),
                                        ("sync", "LAST SYNC")]):
            tile = tk.Frame(tiles, bg=T["bg"], padx=10, pady=6,
                            highlightbackground=T["border1"],
                            highlightthickness=1)
            tile.grid(row=0, column=i, padx=4)
            v = tk.Label(tile, text="—", font=self.f_num, bg=T["bg"],
                         fg=T["fg1"])
            v.grid(row=0, column=0, sticky="e")
            tk.Label(tile, text=cap, font=self.f_label, bg=T["bg"],
                     fg=T["fg3"]).grid(row=1, column=0, sticky="e")
            self.tile_vals[key] = v
        self.tile_vals["sync"].configure(fg=T["fg2"], font=self.f_small)

        gear = Btn(hdr, text="⚙", font=self.f_h1, bg=T["bg4"],
                   hover=T["bg5"], fg=T["fg2"], ring=T["border2"],
                   disabled_fg=T["fg3"], padx=8, ipady=2,
                   command=self.open_settings)
        gear.grid(row=0, column=4, sticky="e", padx=(2, 16))
        self.gear_btn = gear

    def _open_site(self):
        url = self.cfg.get("site_domain") or ""
        if not url and self.cfg.get("site_name"):
            url = "%s.neocities.org" % self.cfg["site_name"]
        if url:
            webbrowser.open("https://" + url if "//" not in url else url)

    # toolbar -----------------------------------------------------------------
    def _build_toolbar(self):
        T = self.T
        tb = tk.Frame(self, bg=T["bg"], height=58)
        tb.grid(row=1, column=0, sticky="ew")
        tb.grid_propagate(False)
        tb.grid_columnconfigure(0, weight=1)
        self.toolbar = tb

        self.folder_var = tk.StringVar(value=self.cfg.get("local_folder") or "")
        self.folder_entry = tk.Entry(tb, textvariable=self.folder_var,
                                     font=self.f_mono_sm, bg=T["bg3"],
                                     fg=T["fg1"], insertbackground=T["fg1"],
                                     relief="flat", bd=0,
                                     highlightthickness=1,
                                     highlightbackground=T["border1"],
                                     highlightcolor=T["accent_border"],
                                     disabledbackground=T["bg2"],
                                     disabledforeground=T["fg3"])
        self.folder_entry.grid(row=0, column=0, sticky="ew",
                               padx=(14, 6), pady=11, ipady=6)
        self.folder_entry.bind("<Return>", lambda e: self.start_scan())

        self.browse_btn = Btn(tb, text="Browse…", font=self.f_btn,
                              bg=T["bg4"], hover=T["bg5"], fg=T["fg1"],
                              ring=T["comp"], command=self.pick_folder)
        self.browse_btn.grid(row=0, column=1, padx=(0, 10), pady=11)

        self.scan_btn = Btn(tb, text="Scan & Plan", font=self.f_btn,
                            bg=T["bg4"], hover=T["accent_dim"],
                            fg=T["accent"], ring=T["accent_border"],
                            ring_hover=T["accent_border"],
                            command=self.start_scan)
        self.scan_btn.grid(row=0, column=2, padx=(0, 6), pady=11)

        self.sync_btn = Btn(tb, text="Sync Now ⬆", font=self.f_btn,
                            bg=T["accent"], hover=T["accent2"],
                            fg="#1a1a1a", command=self.start_sync)
        self.sync_btn.grid(row=0, column=3, padx=(0, 6), pady=11)

        self.verify_btn = Btn(tb, text="Verify", font=self.f_btn,
                              bg=T["bg4"], hover=T["bg5"], fg=T["fg2"],
                              ring=T["border2"], command=self.start_verify)
        self.verify_btn.grid(row=0, column=4, padx=(0, 14), pady=11)

        self.auto_btn = Btn(tb, text="Auto ⏱ off", font=self.f_btn,
                            bg=T["bg4"], hover=T["bg5"], fg=T["fg2"],
                            ring=T["border2"], command=self._auto_menu)
        self.auto_btn.grid(row=0, column=5, padx=(0, 14), pady=11)

    def pick_folder(self):
        d = filedialog.askdirectory(parent=self,
                                    title="Choose local site folder")
        if d:
            self.folder_var.set(d)
            self.cfg["local_folder"] = d
            save_config(self.cfg)

    # content: tab strip + two pages --------------------------------------------
    def _build_content(self):
        T = self.T
        wrap = tk.Frame(self, bg=T["bg"])
        wrap.grid(row=2, column=0, sticky="nsew", padx=12, pady=(4, 4))
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_rowconfigure(1, weight=1)
        self.content_wrap = wrap

        # tab strip (CTk tabview look-alike)
        strip = tk.Frame(wrap, bg=T["bg2"])
        strip.grid(row=0, column=0, sticky="ew")
        self.tab_btns = {}
        for tid, label in (("plan", "Sync Plan"), ("activity", "Activity")):
            b = Btn(strip, text=label, font=self.f_btn, bg=T["bg2"],
                    hover=T["bg2"], fg=T["fg2"], padx=18, ipady=5,
                    command=lambda t=tid: self._show_tab(t))
            b.pack(side="left", padx=(2, 0), pady=3)
            self.tab_btns[tid] = b

        holder = tk.Frame(wrap, bg=T["bg"])
        holder.grid(row=1, column=0, sticky="nsew")
        holder.grid_columnconfigure(0, weight=1)
        holder.grid_rowconfigure(0, weight=1)
        self.tab_holder = holder
        self._tab_frames = {}
        self._build_plan_tab(holder)
        self._build_activity_tab(holder)
        self._show_tab("plan")

    def _show_tab(self, tid):
        T = self.T
        for t, f in self._tab_frames.items():
            if t == tid:
                f.grid()
            else:
                f.grid_remove()
        for t, b in self.tab_btns.items():
            on = (t == tid)
            b.configure(bg=T["accent_dim"] if on else T["bg2"],
                        fg=T["accent"] if on else T["fg2"])
        self._tab = tid

    def _build_plan_tab(self, holder):
        T = self.T
        tab = tk.Frame(holder, bg=T["bg"])
        tab.grid(row=0, column=0, sticky="nsew")
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(2, weight=1)
        self._tab_frames["plan"] = tab

        # slim drop strip (always visible on plan tab)
        strip = tk.Frame(tab, bg=T["accent_dim"], height=44,
                         highlightbackground=T["accent_border"],
                         highlightthickness=1)
        strip.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 6))
        strip.grid_columnconfigure(0, weight=1)
        tk.Label(strip, text="⬇  Drop files anywhere on this window — "
                             "I'll guess the folder, you confirm.",
                 font=self.f_small, bg=T["accent_dim"], fg=T["fg1"],
                 anchor="w").grid(row=0, column=0, sticky="w",
                                  padx=(14, 4), pady=9)
        self.choose_btn = Btn(strip, text="Choose files…", font=self.f_btn,
                              bg=T["bg4"], hover=T["bg5"], fg=T["accent"],
                              ring=T["accent_border"], ipady=2,
                              command=self.choose_files)
        self.choose_btn.grid(row=0, column=1, padx=(4, 10), pady=7)
        self.drop_strip = strip

        # filter chips row
        chips = tk.Frame(tab, bg=T["bg"])
        chips.grid(row=1, column=0, sticky="ew", padx=10, pady=(2, 4))
        self.chips_frame = chips
        self.chip_btns = {}
        for i, fid in enumerate(["all", "new", "chg", "same", "del"]):
            b = Btn(chips, text=fid.upper(), font=self.f_btn, bg=T["bg3"],
                    hover=T["bg4"], fg=T["fg2"], ring=T["border1"], ipady=2,
                    padx=12, command=lambda f=fid: self._on_filter(f))
            b.grid(row=0, column=i, padx=(0, 5), sticky="w")
            self.chip_btns[fid] = b

        # rows scroll area
        self.plan_scroll = ScrollFrame(tab, T["bg"])
        self.plan_scroll.grid(row=2, column=0, sticky="nsew", padx=6,
                              pady=(0, 8))

        # empty-state drop card (shown when no plan)
        self.empty_card = tk.Frame(tab, bg=T["accent_dim"],
                                   highlightbackground=T["accent_border"],
                                   highlightthickness=2)
        self.empty_card.grid(row=2, column=0, sticky="nsew", padx=10,
                             pady=(0, 10))
        self.empty_card.grid_columnconfigure(0, weight=1)
        tk.Label(self.empty_card, text="⬇", font=self.f_h1, bg=T["accent_dim"],
                 fg=T["accent"]).grid(row=0, column=0, pady=(70, 6))
        tk.Label(self.empty_card, text="Drop an HTML file here",
                 font=self.f_h1, bg=T["accent_dim"], fg=T["fg1"]
                 ).grid(row=1, column=0)
        tk.Label(self.empty_card,
                 text="I read its folder name + <title>, guess the "
                      "destination,\nand offer the top 3 matches. "
                      "Scan & Plan for a full site mirror sync.",
                 font=self.f_small, bg=T["accent_dim"], fg=T["fg2"],
                 justify="center").grid(row=2, column=0, pady=(6, 4))
        tk.Label(self.empty_card,
                 text="or press Scan & Plan to compare your local "
                      "folder with the live site",
                 font=self.f_label, bg=T["accent_dim"], fg=T["fg3"]
                 ).grid(row=3, column=0, pady=(2, 60))

    def _build_activity_tab(self, holder):
        T = self.T
        tab = tk.Frame(holder, bg=T["bg"])
        tab.grid(row=0, column=0, sticky="nsew")
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(1, weight=1)
        self._tab_frames["activity"] = tab

        top = tk.Frame(tab, bg=T["bg"])
        top.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 0))
        Btn(top, text="Clear log", font=self.f_small, bg=T["bg3"],
            hover=T["bg4"], fg=T["fg3"], ipady=2,
            command=self._clear_log).pack(side="right")

        wrap = tk.Frame(tab, bg=T["bg2"],
                        highlightbackground=T["border1"],
                        highlightthickness=1)
        wrap.grid(row=1, column=0, sticky="nsew", padx=10, pady=(6, 10))
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_rowconfigure(0, weight=1)
        self.log_box = tk.Text(wrap, font=self.f_mono_sm, wrap="word",
                               bg=T["bg2"], fg=T["fg2"],
                               insertbackground=T["fg1"], relief="flat",
                               bd=0, highlightthickness=0, padx=10, pady=8,
                               selectbackground=T["bg5"], state="disabled")
        self.log_box.grid(row=0, column=0, sticky="nsew")
        vsb = ttk.Scrollbar(wrap, orient="vertical",
                            command=self.log_box.yview)
        self.log_box.configure(yscrollcommand=vsb.set)
        vsb.grid(row=0, column=1, sticky="ns")
        for kind in ("ok", "err", "warn", "info", "dim"):
            self.log_box.tag_configure(kind, foreground=self._kcolor(kind))

    def _clear_log(self):
        try:
            self.log_box.configure(state="normal")
            self.log_box.delete("1.0", "end")
            self.log_box.configure(state="disabled")
        except Exception:
            pass

    # footer ------------------------------------------------------------------
    def _build_footer(self):
        T = self.T
        ft = tk.Frame(self, bg=T["bg2"], height=46)
        ft.grid(row=3, column=0, sticky="ew")
        ft.grid_propagate(False)
        ft.grid_columnconfigure(0, weight=1)
        self.footer = ft

        self.status_lbl = tk.Label(ft, text="Ready.", font=self.f_small,
                                   bg=T["bg2"], fg=T["fg2"], anchor="w")
        self.status_lbl.grid(row=0, column=0, sticky="ew", padx=(16, 8),
                             pady=10)

        self.prog = ProgressCanvas(ft, T, width=250, height=6)
        self.prog.grid(row=0, column=1, padx=8, pady=20)
        self.prog.set(0)
        self.prog_lbl = tk.Label(ft, text="", width=16, font=self.f_mono_sm,
                                 bg=T["bg2"], fg=T["fg3"], anchor="w")
        self.prog_lbl.grid(row=0, column=2, padx=(0, 6))

        self.cancel_btn = Btn(ft, text="✕ Cancel", font=self.f_btn,
                              bg=T["err_dim"],
                              hover=blend(T["err"], T["bg"], 0.22),
                              fg=T["err"], ring=T["err"], ipady=2,
                              command=self._do_cancel)
        # gridded only while busy

    # plan rendering -------------------------------------------------------------
    def _clear_frame(self, frame):
        for w in frame.winfo_children():
            try:
                w.destroy()
            except Exception:
                pass

    def _on_filter(self, fid):
        self.filter = fid
        self.render_plan()

    def render_plan(self):
        T = self.T
        counts = {"all": len(self.plan), "new": 0, "chg": 0, "same": 0,
                  "del": 0}
        for e in self.plan:
            counts[e["action"]] += 1
        labels = {"all": "ALL", "new": "NEW", "chg": "CHANGED",
                  "same": "SAME", "del": "DELETE"}
        for fid, b in self.chip_btns.items():
            on = (fid == self.filter)
            b.configure(text="%s %d" % (labels[fid], counts[fid]),
                        bg=T["accent_dim"] if on else T["bg3"],
                        highlightbackground=T["accent_border"] if on
                        else T["border1"],
                        fg=T["accent"] if on else T["fg2"])

        entries = [e for e in self.plan
                   if self.filter == "all" or e["action"] == self.filter]
        if not self.plan:
            self._render_gen += 1
            self._entries_view = []
            self.empty_card.grid()
            self.plan_scroll.grid_remove()
            self.chips_frame.grid_remove()
            self._set_status("Ready.", "plain")
            return
        self.empty_card.grid_remove()
        self.plan_scroll.grid()
        self.chips_frame.grid()

        self._clear_frame(self.plan_scroll.inner)
        self.plan_scroll.canvas.yview_moveto(0)
        self._render_gen += 1
        if not entries:
            self._entries_view = []
            tk.Label(self.plan_scroll.inner, text="nothing in this filter ✓",
                     font=self.f_small, bg=T["bg"], fg=T["fg3"]
                     ).grid(sticky="w", padx=12, pady=10)
            self._set_status("Plan: %d new · %d changed · %d identical · "
                             "%d to delete"
                             % (counts["new"], counts["chg"], counts["same"],
                                counts["del"]), "dim")
        else:
            # render in small passes so the event loop keeps breathing
            self._entries_view = entries
            self._rows_shown = 0
            self._last_counts = counts
            self._set_status("Plan: %d new · %d changed · %d identical · "
                             "%d to delete — rendering…"
                             % (counts["new"], counts["chg"], counts["same"],
                                counts["del"]), "dim")
            self.after(1, lambda g=self._render_gen: self._render_rows(g))
            return

    def _render_rows(self, gen):
        """append one chunk of plan rows per event-loop pass (UI stays alive)."""
        if gen != self._render_gen or not self._entries_view:
            return
        T = self.T
        entries = self._entries_view
        end = min(self._rows_shown + self._row_chunk,
                  len(entries), self._row_cap)
        badge = {"new": ("NEW", T["ok"], T["ok_dim"]),
                 "chg": ("CHG", T["accent"], T["accent_dim"]),
                 "del": ("DEL", T["err"], T["err_dim"]),
                 "same": ("SAME", T["fg3"], T["bg3"])}
        stat = {"new": ("→ upload", "ok"), "chg": ("↑ replace", "warn"),
                "del": ("✕ delete", "err"), "same": ("✓ identical", "dim")}
        for e in entries[self._rows_shown:end]:
            self._plan_row(e, badge, stat)
        self._rows_shown = end
        if end < len(entries):
            if end >= self._row_cap:
                tk.Label(self.plan_scroll.inner,
                         text="… and %d more — use the filter chips"
                              % (len(entries) - end),
                         font=self.f_small, bg=T["bg"], fg=T["fg3"]
                         ).grid(sticky="w", padx=12, pady=8)
            else:
                self.after(self._chunk_gap,
                           lambda g=gen: self._render_rows(g))
                return
        c = self._last_counts
        self._set_status("Plan: %d new · %d changed · %d identical · "
                         "%d to delete"
                         % (c["new"], c["chg"], c["same"], c["del"]), "dim")

    def _plan_row(self, e, badge, stat):
        """one plan row from plain tk widgets — same WWZ palette as the rest."""
        T = self.T
        act = e["action"]
        txt, kc, kb = badge[act]
        bg = T["err_dim"] if act == "del" else \
            (T["bg2"] if act != "same" else T["bg"])
        row = tk.Frame(self.plan_scroll.inner, bg=bg,
                       highlightbackground=T["border1"],
                       highlightthickness=1)
        row.grid(sticky="ew", padx=6, pady=2)
        row.grid_columnconfigure(1, weight=1)
        tk.Label(row, text=txt, bg=kb, fg=kc, font=self.tk_tiny_b,
                 padx=6, pady=2).grid(row=0, column=0, padx=(6, 6), pady=6)
        tk.Label(row, text=e["path"], bg=bg,
                 fg=T["fg2"] if act == "del" else T["fg1"],
                 font=self.tk_strike if act == "del" else self.tk_mono,
                 anchor="w").grid(row=0, column=1, sticky="ew")
        tk.Label(row, text=human_size(e["size"]), width=11, bg=bg,
                 fg=T["fg3"], font=self.tk_mono, anchor="e"
                 ).grid(row=0, column=2, padx=4)
        tk.Label(row, text=rel_ago(e["mtime"]) if e["mtime"] else "—",
                 width=10, bg=bg, fg=T["fg3"], font=self.tk_small, anchor="e"
                 ).grid(row=0, column=3, padx=4)
        so = e.get("status_override")
        s_txt, s_kind = so if so else stat[act]
        tk.Label(row, text=s_txt, width=15, bg=bg, fg=self._kcolor(s_kind),
                 font=self.tk_small, anchor="w"
                 ).grid(row=0, column=4, padx=(4, 10), sticky="w")

    # status / toast / log / progress --------------------------------------------
    def _set_status(self, text, kind="plain"):
        try:
            self.status_lbl.configure(text=text, fg=self._kcolor(kind))
        except Exception:
            pass

    def _log(self, text, kind="plain"):
        try:
            self.log_box.configure(state="normal")
            ts = datetime.now().strftime("%H:%M:%S")
            self.log_box.insert("end", "[%s] %s\n" % (ts, text), kind)
            self._log_n = getattr(self, "_log_n", 0) + 1
            if self._log_n % 400 == 0:
                n = int(self.log_box.index("end-1c").split(".")[0])
                if n > 2400:
                    self.log_box.delete("1.0", "%d.0" % (n - 2000))
            self.log_box.see("end")
            self.log_box.configure(state="disabled")
        except Exception:
            pass

    def _toast(self, text, kind="info"):
        T = self.T
        if self._toast_job:
            try:
                self.after_cancel(self._toast_job)
            except Exception:
                pass
        if not hasattr(self, "toast_lbl"):
            self.toast_lbl = tk.Label(self, font=self.f_small, bg=T["buy"],
                                      fg=T["fg1"], padx=14, pady=8,
                                      highlightthickness=1)
        kc = self._kcolor(kind)
        self.toast_lbl.configure(text="  %s  " % text, fg=kc,
                                 highlightbackground=kc, highlightcolor=kc)
        self.toast_lbl.place(relx=0.5, rely=0.90, anchor="center")
        self.toast_lbl.lift()
        self._toast_job = self.after(3600, self.toast_lbl.place_forget)

    def _prog(self, done, total, label=""):
        try:
            key = (done, total, label)
            if key == getattr(self, "_last_prog", None):
                return
            self._last_prog = key
            self.prog.set((done / float(total)) if total else 0.0)
            self.prog_lbl.configure(
                text=("%d/%d %s" % (done, total, label)) if total else "")
        except Exception:
            pass

    def busy_begin(self, label="working"):
        self.busy = True
        self.cancel_event.clear()
        for b in (self.scan_btn, self.sync_btn, self.verify_btn,
                  self.auto_btn, self.browse_btn, self.choose_btn,
                  self.gear_btn):
            try:
                b.configure(state="disabled")
            except Exception:
                pass
        self.cancel_btn.grid(row=0, column=3, padx=(2, 14))
        self._prog(0, 0, "")
        self._set_status(label + "…", "warn")

    def busy_end(self):
        self.busy = False
        for b in (self.scan_btn, self.sync_btn, self.verify_btn,
                  self.auto_btn, self.browse_btn, self.choose_btn,
                  self.gear_btn):
            try:
                b.configure(state="normal")
            except Exception:
                pass
        self.cancel_btn.grid_forget()

    def _do_cancel(self):
        self.cancel_event.set()
        self._set_status("cancelling — finishing in-flight requests…", "warn")

    # auto-sync timer (Scan & Plan + Sync on an interval) -----------------------
    def _update_auto_btn(self):
        T = self.T
        secs = int(self.cfg.get("auto_sync_secs") or 0)
        if secs > 0:
            self.auto_btn.configure(
                text="Auto ⏱ %s" % _secs_choice(secs).replace("Every ", ""),
                bg=T["accent_dim"], fg=T["accent"],
                highlightbackground=T["accent_border"])
        else:
            self.auto_btn.configure(
                text="Auto ⏱ off", bg=T["bg4"], fg=T["fg2"],
                highlightbackground=T["border2"])

    def _auto_menu(self):
        m = tk.Menu(self, tearoff=0, font=self.tk_small,
                    bg=self.T["bg3"], fg=self.T["fg1"], bd=0,
                    activebackground=self.T["bg5"],
                    activeforeground=self.T["accent"])
        cur = int(self.cfg.get("auto_sync_secs") or 0)
        for label, secs in AUTO_CHOICES:
            mark = "✓ " if secs == cur else "    "
            m.add_command(label="%s%s" % (mark, label),
                          command=lambda s=secs: self._auto_apply(s))
        try:
            m.tk_popup(self.auto_btn.winfo_rootx(),
                       self.auto_btn.winfo_rooty()
                       + self.auto_btn.winfo_height())
        finally:
            m.grab_release()

    def _auto_apply(self, secs):
        self.cfg["auto_sync_secs"] = int(secs)
        save_config(self.cfg)
        self._arm_auto(announce=True)

    def _arm_auto(self, announce=False):
        """(re)arm the interval timer from config; secs<=0 disarms."""
        if self._auto_job:
            try:
                self.after_cancel(self._auto_job)
            except Exception:
                pass
            self._auto_job = None
        secs = int(self.cfg.get("auto_sync_secs") or 0)
        self._auto_left = secs
        if secs > 0:
            self._auto_job = self.after(secs * 1000, self._auto_tick)
            if announce:
                self._log("auto-sync armed — full Scan & Plan + Sync every "
                          "%s (first run in %ss)"
                          % (_secs_choice(secs).replace("Every ", ""), secs),
                          "info")
            self._auto_ticker()
        elif self._auto_ticker_job:
            try:
                self.after_cancel(self._auto_ticker_job)
            except Exception:
                pass
            self._auto_ticker_job = None
        self._update_auto_btn()

    def _auto_ticker(self):
        """1 Hz countdown on the button while auto-sync is enabled."""
        self._auto_ticker_job = None
        if int(self.cfg.get("auto_sync_secs") or 0) <= 0:
            return
        if not self.busy and self._auto_left > 0:
            self._auto_left -= 1
        try:
            self.auto_btn.configure(text="Auto ⏱ %ds" % self._auto_left
                                    if self._auto_left > 0 else "Auto ⏱ …")
        except Exception:
            pass
        self._auto_ticker_job = self.after(1000, self._auto_ticker)

    def _auto_tick(self):
        self._auto_job = None
        if self.busy:
            self._log("auto-sync skipped this round — a job is still running",
                      "dim")
        elif not (self.cfg.get("api_key") or "").strip() \
                or not self.cfg.get("local_folder") \
                or not os.path.isdir(self.cfg["local_folder"]):
            self._log("auto-sync skipped — API key / local folder missing",
                      "warn")
        else:
            self.ui_q.put(("log", "auto-sync tick — scanning…", "dim"))
            threading.Thread(target=self._auto_worker, daemon=True).start()
        self._arm_auto()          # schedule the next round

    def _auto_worker(self):
        """one full automatic round: list site → hash local (cached) →
        build plan → sync uploads (+deletes only if explicitly allowed)."""
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            folder = self.cfg["local_folder"]
            self.ui_q.put(("status", "auto-sync — listing live site…", "dim"))
            remote = cli.list_all()
            self.remote_map, self.remote_ts = remote, time.time()
            try:
                total = count_files_fast(folder, self.cfg["excludes"])
            except Exception:
                total = 0

            def prog(k):
                if k == 1 or k % 5 == 0:
                    self.ui_q.put(("prog", k, total, "hashed"))
            local = scan_folder(folder, self.cfg["excludes"],
                                self.cancel_event, prog,
                                sha_cache=self._sha_cache)
            plan = build_plan(local, remote)
            self.ui_q.put(("plan", plan, local, remote))
            uploads = [e for e in plan if e["action"] in ("new", "chg")]
            dels = [e for e in plan if e["action"] == "del"
                    and e["path"].lower() != "index.html"]
            n_del = len(dels)
            if not (self.cfg.get("mirror_deletes", True)
                    and self.cfg.get("auto_sync_deletes", False)):
                dels = []          # auto mode never deletes unless opted in
            if not uploads and not dels:
                hint = (" · %d remote-only kept (auto-delete off)" % n_del)
                self.ui_q.put(("log", "auto-sync: %d files checked — "
                               "everything already matches ✓%s"
                               % (len(local), hint if n_del else ""), "dim"))
                self.ui_q.put(("status", "auto-sync: everything matches ✓",
                               "ok"))
                return
            if dels:
                self.ui_q.put(("log", "auto-sync: mirror-deleting %d "
                               "remote-only file(s) (auto-delete enabled)"
                               % len(dels), "warn"))
            self._sync_worker(uploads, dels)
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except ApiError as e:
            self.ui_q.put(("toast", "API error: %s" % e, "err"))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "auto-sync failed: %s" % e, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # header stats ------------------------------------------------------------
    def refresh_stats(self, info, nfiles):
        T = self.T
        if info:
            site = info.get("sitename") or self.cfg.get("site_name") or "site"
            self.cfg["site_name"] = site
            dom = info.get("domain") or ("%s.neocities.org" % site)
            self.cfg["site_domain"] = dom
            self.site_name_lbl.configure(text=site)
            self.site_url_lbl.configure(text=dom)
            self.tile_vals["views"].configure(
                text="{:,}".format(info.get("views") or 0))
            self.tile_vals["hits"].configure(
                text="{:,}".format(info.get("hits") or 0))
            save_config(self.cfg)
        if nfiles is not None:
            self.tile_vals["files"].configure(text=str(nfiles))
        self.tile_vals["sync"].configure(
            text=rel_ago(self.cfg.get("last_sync")),
            fg=T["accent"] if self.cfg.get("last_sync") else T["fg2"])

    # theme re-apply (lite: main surfaces only, full re-style on next launch) ---
    def _apply_style(self):
        T = self.T
        try:
            self.configure(bg=T["bg"])
            for f in (self.hdr, self.footer):
                f.configure(bg=T["bg2"])
            self.toolbar.configure(bg=T["bg"])
            self.content_wrap.configure(bg=T["bg"])
            self.status_lbl.configure(bg=T["bg2"], fg=T["fg2"])
            self.prog.configure(bg=T["bg3"])
        except Exception:
            pass

    # queue poll --------------------------------------------------------------
    def _poll(self):
        try:
            while True:
                msg = self.ui_q.get_nowait()
                self._dispatch(msg)
        except queue.Empty:
            pass
        except Exception:
            traceback.print_exc()
        self.after(80, self._poll)

    def _dispatch(self, msg):
        op = msg[0]
        if op == "status":
            self._set_status(msg[1], msg[2] if len(msg) > 2 else "plain")
        elif op == "log":
            self._log(msg[1], msg[2] if len(msg) > 2 else "plain")
        elif op == "toast":
            self._toast(msg[1], msg[2] if len(msg) > 2 else "info")
        elif op == "prog":
            self._prog(msg[1], msg[2], msg[3] if len(msg) > 3 else "")
        elif op == "busy":
            self.busy_begin(msg[1]) if msg[2] else self.busy_end()
        elif op == "plan":
            self.plan = msg[1]
            self.local_map = msg[2]
            self.remote_map = msg[3]
            self.remote_ts = time.time()
            self.render_plan()
        elif op == "stats":
            self.refresh_stats(msg[1], msg[2])
        elif op == "guess":
            self._open_guess(msg[1])
        elif op == "open_settings":
            self.open_settings()
        elif op == "test_result":
            d = getattr(self, "settings_dlg", None)
            if d is not None and d.winfo_exists():
                d.apply_test_result(msg[1], msg[2])
        elif op == "rebuild_confirm":
            self._rebuild_confirm(msg[1], msg[2], msg[3], msg[4])
        elif op == "sync_done":
            up, dele, ver, fail = msg[1], msg[2], msg[3], msg[4]
            self._toast("sync complete — %d uploaded, %d deleted%s" %
                        (up, dele, ", %d failed ✕" % fail if fail else " ✓"),
                        "ok" if not fail else "err")
            self._set_status("sync complete — %d uploaded · %d deleted · "
                             "%d verified ✓" % (up, dele, ver),
                             "ok" if not fail else "err")

    # drag & drop -------------------------------------------------------------
    def _apply_dnd(self):
        if not HAS_DND:
            self._log("drag & drop unavailable — run  pip install tkinterdnd2  "
                      "to enable it. 'Choose files…' works meanwhile.", "warn")
            return
        try:
            self.drop_target_register(DND_FILES)
            self.dnd_bind("<<Drop>>", self._on_drop)
            self._dnd_ok = True
        except Exception:
            return
        # register child surfaces too; the <<Drop>> event bubbles to the root
        # binding, so we deliberately bind ONLY the root (no double-fires)
        for w in (self.drop_strip, self.empty_card):
            try:
                w.drop_target_register(DND_FILES)
            except Exception:
                pass
        self._log("drag & drop active — drop an HTML file and I'll guess "
                  "its folder (top 3 matches).", "dim")

    def _on_drop(self, event):
        if self.busy:
            self._toast("busy — wait for the current job to finish", "warn")
            return
        try:
            paths = list(self.tk.splitlist(event.data))
        except Exception:
            paths = [a or b for a, b in
                     re.findall(r"\{([^}]+)\}|(\S+)", event.data or "")]
        files = [p for p in paths if os.path.isfile(p)]
        dirs = [p for p in paths if os.path.isdir(p)]
        if dirs:
            self._toast("drop files, not folders (for now)", "warn")
        if files:
            threading.Thread(target=self._drop_worker, args=(files,),
                             daemon=True).start()

    def choose_files(self):
        if self.busy:
            return
        fs = filedialog.askopenfilenames(parent=self,
                                         title="Choose files to upload")
        if fs:
            threading.Thread(target=self._drop_worker, args=(list(fs),),
                             daemon=True).start()

    def open_settings(self):
        d = getattr(self, "settings_dlg", None)
        if d is not None and d.winfo_exists():
            d.lift()
            d.focus_force()
            return                          # never stack modal dialogs
        self.settings_dlg = SettingsDialog(self)

    # shared client/remote helpers (worker-thread context) ----------------------
    def _ensure_client(self):
        key = (self.cfg.get("api_key") or "").strip()
        if not key:
            self.ui_q.put(("toast", "add your API key first — ⚙ Settings",
                           "warn"))
            self.ui_q.put(("open_settings",))  # via queue — never tk from a thread
            raise QuietExit()
        return Neocities(key, self.cancel_event)

    def _ensure_remote(self, cli, max_age=90.0):
        if self.remote_map is None or (time.time() - self.remote_ts) > max_age:
            self.ui_q.put(("status", "listing site…", "dim"))
            remote = cli.list_all()
            self.remote_map, self.remote_ts = remote, time.time()
            nfiles = sum(1 for e in remote.values() if not e["is_dir"])
            self.ui_q.put(("stats", None, nfiles))
            return remote
        return self.remote_map

    # scan / verify -------------------------------------------------------------
    def start_scan(self, *_):
        if self.busy:
            return
        folder = self.folder_var.get().strip()
        if folder and folder != self.cfg.get("local_folder"):
            self.cfg["local_folder"] = folder
            save_config(self.cfg)
        if not (self.cfg.get("api_key") or "").strip():
            self._toast("add your API key first — ⚙ Settings", "warn")
            self.open_settings()
            return
        if not self.cfg.get("local_folder") or \
                not os.path.isdir(self.cfg["local_folder"]):
            self._toast("choose the local site folder first", "warn")
            return
        threading.Thread(target=self._scan_worker, daemon=True).start()

    def _scan_worker(self):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            folder = self.cfg["local_folder"]
            self.ui_q.put(("status", "listing live site…", "dim"))
            remote = cli.list_all()
            self.remote_map, self.remote_ts = remote, time.time()
            nfiles = sum(1 for e in remote.values() if not e["is_dir"])
            self.ui_q.put(("log", "site listing: %d entries (%d files)"
                           % (len(remote), nfiles), "dim"))
            self.ui_q.put(("status", "hashing local files (sha1)…", "dim"))
            try:                    # fast count → real progress total
                total = count_files_fast(folder, self.cfg["excludes"])
            except Exception:
                total = 0
            state = {"n": 0}

            def prog(k):
                if k == 1 or k % 5 == 0:
                    self.ui_q.put(("prog", k, total, "hashed"))
                    state["n"] = k
            local = scan_folder(folder, self.cfg["excludes"],
                                self.cancel_event, prog,
                                sha_cache=self._sha_cache)
            plan = build_plan(local, remote)
            self.ui_q.put(("plan", plan, local, remote))
            try:
                self.ui_q.put(("stats", cli.info(), nfiles))
            except Exception:
                self.ui_q.put(("stats", None, nfiles))
            n_new = sum(1 for e in plan if e["action"] == "new")
            n_chg = sum(1 for e in plan if e["action"] == "chg")
            n_del = sum(1 for e in plan if e["action"] == "del")
            self.ui_q.put(("toast", "plan ready — %d new · %d changed"
                           % (n_new, n_chg), "ok"))
            self.ui_q.put(("log", "scan: %d local vs %d remote files — "
                           "%d new, %d changed, %d identical, %d remote-only"
                           % (len(local), nfiles, n_new, n_chg,
                              sum(1 for e in plan if e["action"] == "same"),
                              n_del), "ok"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except ApiError as e:
            self.ui_q.put(("toast", "API error: %s" % e, "err"))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "scan failed: %s" % e, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    def start_verify(self):
        if self.busy:
            return
        if not (self.cfg.get("api_key") or "").strip():
            self.open_settings()
            return
        if not self.cfg.get("local_folder") or \
                not os.path.isdir(self.cfg["local_folder"]):
            self._toast("choose the local site folder first", "warn")
            return
        threading.Thread(target=self._verify_worker, daemon=True).start()

    def _verify_worker(self):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            self.ui_q.put(("status",
                           "verify — listing site + hashing local…", "dim"))
            remote = cli.list_all()
            self.remote_map, self.remote_ts = remote, time.time()
            local = scan_folder(self.cfg["local_folder"], self.cfg["excludes"],
                                self.cancel_event,
                                sha_cache=self._sha_cache)
            plan = build_plan(local, remote)
            self.ui_q.put(("plan", plan, local, remote))
            c = {"new": 0, "chg": 0, "same": 0, "del": 0}
            for e in plan:
                c[e["action"]] += 1
            ok = (c["new"] == 0 and c["chg"] == 0)
            self.ui_q.put(("toast", "integrity: %d identical ✓ — %d differ, "
                           "%d missing remotely"
                           % (c["same"], c["chg"], c["new"]),
                           "ok" if ok else "warn"))
            self.ui_q.put(("log", "integrity check — %d identical, %d differ, "
                           "%d missing remotely, %d remote-only"
                           % (c["same"], c["chg"], c["new"], c["del"]),
                           "ok" if ok else "warn"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "verify failed: %s" % e, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # rebuild (server→local pull, Settings ▸ Maintenance) -----------------------
    def start_rebuild(self) -> bool:
        """pull every file from the live site into the local folder — the
        GUI twin of the CLI's `neocities pull .`. Deliberately reachable
        ONLY from Settings ▸ Maintenance so it can't be hit by mistake."""
        if self.busy:
            self._toast("busy — wait for the current job to finish", "warn")
            return False
        if not (self.cfg.get("api_key") or "").strip():
            self._toast("add your API key first — ⚙ Settings", "warn")
            self.open_settings()
            return False
        folder = self.folder_var.get().strip()
        if folder and folder != self.cfg.get("local_folder"):
            self.cfg["local_folder"] = folder
            save_config(self.cfg)
        if not self.cfg.get("local_folder") or \
                not os.path.isdir(self.cfg["local_folder"]):
            self._toast("choose the local site folder first", "warn")
            return False
        threading.Thread(target=self._rebuild_probe_worker,
                         daemon=True).start()
        return True

    def _pull_base_url(self, info):
        """public base URL for pulls — same rule as the CLI gem: custom
        domain when the site has one, else <sitename>.neocities.org."""
        dom = ((info or {}).get("domain") or "").strip()
        if dom:
            return "https://%s/" % dom.split("//")[-1].strip("/")
        site = ((info or {}).get("sitename")
                or self.cfg.get("site_name") or "").strip()
        if not site:
            return None
        return "https://%s.neocities.org/" % site

    def _rebuild_probe_worker(self):
        """phase 1: fresh site listing + counts for the confirm dialog.
        Stays busy while the confirmation is open; hands over to phase 2
        on yes, releases the UI on no / error."""
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            self.ui_q.put(("status", "rebuild — listing live site…", "dim"))
            try:
                info = cli.info()
            except Exception:
                info = {}
            remote = cli.list_all()
            self.remote_map, self.remote_ts = remote, time.time()
            files, dirs, collisions = collect_pull_files(
                remote, self.cfg["excludes"])
            for p in collisions[:5]:
                self.ui_q.put(("log", "rebuild: skipped %s — another path "
                               "differs only by case" % p, "warn"))
            if len(collisions) > 5:
                self.ui_q.put(("log", "rebuild: %d case-collision paths "
                               "skipped in total" % len(collisions), "warn"))
            base = self._pull_base_url(info)
            if not base:
                self.ui_q.put(("toast", "cannot determine site name — "
                               "check the API key", "err"))
                self.ui_q.put(("busy", "", False))
                return
            nfiles = sum(1 for e in remote.values() if not e["is_dir"])
            skipped = nfiles - len(files)
            self.ui_q.put(("log", "rebuild: %d file(s) to pull from %s%s"
                           % (len(files), base,
                              " · %d excluded/skipped" % skipped if skipped
                              else ""), "info"))
            self.ui_q.put(("stats", info, nfiles))
            self.ui_q.put(("rebuild_confirm", files, dirs, base, info))
        except QuietExit:
            self.ui_q.put(("busy", "", False))
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
            self.ui_q.put(("busy", "", False))
        except ApiError as e:
            self.ui_q.put(("toast", "API error: %s" % e, "err"))
            self.ui_q.put(("busy", "", False))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "rebuild failed: %s" % e, "err"))
            self.ui_q.put(("busy", "", False))

    def _rebuild_confirm(self, files, dirs, base_url, info):
        """main thread: ask before anything touches the local folder."""
        go = False
        try:
            folder = self.cfg.get("local_folder") or ""
            site = ((info or {}).get("sitename")
                    or self.cfg.get("site_name") or "site")
            mb = sum(f["size"] for f in files)
            msg = ("Rebuild the local folder from the live site?\n\n"
                   "Site:  %s — %d files (%s)\nInto:  %s\n\n"
                   "• Server files will be downloaded over your local copies\n"
                   "• Files already matching the server are skipped\n"
                   "• Local-only files are KEPT — nothing gets deleted\n"
                   "• Nothing on the server will be changed\n\n"
                   "Continue?" % (site, len(files), human_size(mb), folder))
            go = messagebox.askyesno("Rebuild from server", msg, parent=self)
        except Exception:
            go = False
        if not go:
            self.ui_q.put(("status", "rebuild cancelled", "warn"))
            self.ui_q.put(("log", "rebuild cancelled — nothing was changed",
                           "warn"))
            self.ui_q.put(("busy", "", False))
            return
        threading.Thread(target=self._rebuild_worker,
                         args=(files, dirs, base_url), daemon=True).start()

    def _rebuild_task(self, cli, folder, f, base_url):
        rel = f["path"]
        local = os.path.join(folder, rel.replace("/", os.sep))
        if os.path.isfile(local) and f.get("sha1"):
            try:
                if sha1_file(local) == f["sha1"]:
                    return ("current", f)
            except OSError:
                pass
        cli.download(rel, local, base_url)
        if f.get("sha1"):
            try:
                if sha1_file(local) != f["sha1"]:
                    cli.download(rel, local, base_url)   # one verify retry
                    if sha1_file(local) != f["sha1"]:
                        return ("bad", f)
            except OSError:
                return ("bad", f)
        return ("ok", f)

    def _rebuild_worker(self, files, dirs, base_url):
        """phase 2: pull everything (parallel pool), sha1-verify each file
        against the listing, then rescan + rebuild the plan. Never touches
        the server; never deletes local files."""
        self.ui_q.put(("busy", "", True))
        pulled = current = failed = 0
        try:
            cli = self._ensure_client()
            folder = self.cfg["local_folder"]
            for d in dirs:                      # gem does mkdir_p for dirs
                try:
                    os.makedirs(os.path.join(folder,
                                             d.replace("/", os.sep)),
                                exist_ok=True)
                except OSError:
                    pass
            total = len(files)
            self.ui_q.put(("log", "rebuild: pulling %d file(s) from %s"
                           % (total, base_url), "info"))
            workers = max(1, int(self.cfg.get("workers") or 8))
            done = 0
            with ThreadPoolExecutor(max_workers=workers) as ex:
                futs = {ex.submit(self._rebuild_task, cli, folder, f,
                                  base_url): f for f in files}
                for fut in as_completed(futs):
                    f = futs[fut]
                    try:
                        kind, f2 = fut.result()
                        if kind == "ok":
                            pulled += 1
                            self.ui_q.put(("log", "⬇ pulled %s" % f2["path"],
                                           "plain"))
                        elif kind == "current":
                            current += 1
                            self.ui_q.put(("log", "= current (same sha1): %s"
                                           % f2["path"], "dim"))
                        else:
                            failed += 1
                            self.ui_q.put(("log", "✕ sha1 mismatch after "
                                           "download: %s" % f2["path"],
                                           "err"))
                    except Cancelled:
                        raise
                    except Exception as de:
                        failed += 1
                        self.ui_q.put(("log", "✕ %s — %s" % (f["path"], de),
                                       "err"))
                    done += 1
                    self.ui_q.put(("prog", done, total, "pulled"))
                    self.ui_q.put(("status", "rebuilding %d/%d — %s"
                                   % (done, total, f["path"]), "dim"))
            if self.cancel_event.is_set():
                raise Cancelled()
            try:
                local = scan_folder(folder, self.cfg["excludes"],
                                    self.cancel_event,
                                    sha_cache=self._sha_cache)
            except Exception:
                local = self.local_map
            remote = self.remote_map or {}
            self.ui_q.put(("plan", build_plan(local or {}, remote),
                           local, remote))
            self.cfg["last_sync"] = time.time()
            save_config(self.cfg)
            try:
                self.ui_q.put(("stats", cli.info(),
                               sum(1 for e in remote.values()
                                   if not e["is_dir"])))
            except Exception:
                pass
            self.ui_q.put(("toast", "rebuild complete — %d pulled, %d "
                           "already current%s"
                           % (pulled, current,
                              ", %d failed ✕" % failed if failed else " ✓"),
                           "ok" if not failed else "err"))
            self.ui_q.put(("log", "rebuild complete — %d pulled, %d already "
                           "current, %d failed (local-only files kept)"
                           % (pulled, current, failed),
                           "ok" if not failed else "warn"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
            self.ui_q.put(("log", "rebuild cancelled", "warn"))
        except ApiError as e:
            self.ui_q.put(("toast", "API error: %s" % e, "err"))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "rebuild failed: %s" % e, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # sync ---------------------------------------------------------------
    def start_sync(self):
        if self.busy:
            return
        if not self.plan:
            self._toast("run Scan & Plan first", "warn")
            return
        uploads = [e for e in self.plan if e["action"] in ("new", "chg")]
        dels = [e for e in self.plan if e["action"] == "del"
                and e["path"].lower() != "index.html"]
        if not self.cfg.get("mirror_deletes", True):
            dels = []
        if dels:
            preview = "\n".join("   ✕  " + e["path"] for e in dels[:8])
            if len(dels) > 8:
                preview += "\n   … and %d more" % (len(dels) - 8)
            msg = ("Mirror sync will DELETE %d remote file(s) that no longer "
                   "exist locally:\n\n%s\n\nDeletion cannot be undone. "
                   "Continue?" % (len(dels), preview))
            if not messagebox.askyesno("Confirm deletions", msg, parent=self):
                self._log("sync aborted — deletions not confirmed", "warn")
                return
        if not uploads and not dels:
            self._toast("everything already matches ✓ — nothing to do", "ok")
            return
        threading.Thread(target=self._sync_worker, args=(uploads, dels),
                         daemon=True).start()

    def _upload_task(self, cli, folder, e):
        local = os.path.join(folder, e["path"].replace("/", os.sep))
        if not os.path.isfile(local):          # exists-check right before read
            return ("missing", e, None)
        sha = sha1_file(local)
        cli.upload(e["path"], local)
        return ("ok", e, sha)

    def _sync_worker(self, uploads, dels):
        self.ui_q.put(("busy", "", True))
        fail = 0
        try:
            cli = self._ensure_client()
            folder = self.cfg["local_folder"]
            total = len(uploads) + len(dels)
            done = 0
            results = {}
            if uploads:
                workers = max(1, int(self.cfg.get("workers") or 8))
                self.ui_q.put(("status",
                               "uploading with %d parallel workers…" % workers,
                               "warn"))
                with ThreadPoolExecutor(max_workers=workers) as ex:
                    futs = {ex.submit(self._upload_task, cli, folder, e): e
                            for e in uploads}
                    for f in as_completed(futs):
                        e = futs[f]
                        kind, sha = "fail", None
                        try:
                            kind, e2, sha = f.result()
                            if kind == "ok":
                                self.ui_q.put(("log", "↑ uploaded %s"
                                               % e2["path"], "plain"))
                            else:
                                self.ui_q.put(("log", "✕ missing locally: %s"
                                               % e2["path"], "err"))
                                fail += 1
                        except Cancelled:
                            raise
                        except Exception as ae:
                            self.ui_q.put(("log", "✕ %s — %s"
                                           % (e["path"], ae), "err"))
                            fail += 1
                        results[e["path"]] = (kind, sha)
                        done += 1
                        self.ui_q.put(("prog", done, total, "up"))
                        self.ui_q.put(("status", "uploading %d/%d — %s"
                                       % (done, total, e["path"]), "dim"))
            deleted, delfail = 0, 0
            if dels:
                self.ui_q.put(("status", "deleting %d remote-only files…"
                               % len(dels), "warn"))
                try:
                    dfl = cli.delete([e["path"] for e in dels])
                    deleted, delfail = len(dels) - len(dfl), len(dfl)
                    for p in dfl:
                        self.ui_q.put(("log", "✕ delete failed: %s" % p,
                                       "err"))
                except Cancelled:
                    raise
                done += len(dels)
                self.ui_q.put(("prog", done, total, "del"))
            verified = 0
            remote2, local2 = self.remote_map, self.local_map
            if self.cfg.get("auto_verify", True) and uploads:
                self.ui_q.put(("status", "verifying uploads (fresh site "
                               "listing + sha1)…", "dim"))
                remote2 = cli.list_all()
                self.remote_map, self.remote_ts = remote2, time.time()
                for e in uploads:
                    kind, sha = results.get(e["path"], ("fail", None))
                    if kind != "ok":
                        continue
                    re_ = remote2.get(e["path"])
                    if re_ and not re_["is_dir"] and re_.get("sha1") == sha:
                        verified += 1
                    else:
                        self.ui_q.put(("log", "verify mismatch — retrying %s"
                                       % e["path"], "warn"))
                        try:
                            k2, e2, sha2 = self._upload_task(cli, folder, e)
                            re2 = cli.list_dir(
                                posixpath.dirname(e["path"])).get(e["path"])
                            if re2 and re2.get("sha1") == sha2:
                                verified += 1
                                remote2[e["path"]] = re2
                            else:
                                fail += 1
                                self.ui_q.put(("log", "✕ verification "
                                               "failed: %s" % e["path"],
                                               "err"))
                        except Cancelled:
                            raise
                        except Exception as ve:
                            fail += 1
                            self.ui_q.put(("log", "✕ verify retry %s — %s"
                                           % (e["path"], ve), "err"))
                if not self.cancel_event.is_set():
                    try:
                        local2 = scan_folder(folder, self.cfg["excludes"],
                                             self.cancel_event,
                                             sha_cache=self._sha_cache)
                    except Exception:
                        local2 = self.local_map
            self.cfg["last_sync"] = time.time()
            save_config(self.cfg)
            plan2 = build_plan(local2 or {}, remote2 or {})
            self.ui_q.put(("plan", plan2, local2, remote2))
            try:
                self.ui_q.put(("stats", cli.info(),
                               sum(1 for e in (remote2 or {}).values()
                                   if not e["is_dir"])))
            except Exception:
                self.ui_q.put(("stats", None,
                               sum(1 for e in (remote2 or {}).values()
                                   if not e["is_dir"])))
            self.ui_q.put(("sync_done", max(0, len(uploads) - fail), deleted,
                           verified, fail + delfail))
            self.ui_q.put(("log", "sync complete — %d uploaded, %d deleted, "
                           "%d/%d verified%s"
                           % (max(0, len(uploads) - fail), deleted, verified,
                              len(uploads),
                              "" if not fail else ", %d FAILED ✕" % fail),
                           "ok" if not fail else "err"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
            self.ui_q.put(("log", "sync cancelled", "warn"))
        except ApiError as e:
            self.ui_q.put(("toast", "API error: %s" % e, "err"))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "sync failed: %s" % e, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # drop uploads (quick path) -------------------------------------------------
    def _quick_upload(self, cli, local_path, dest, remote_map, origin):
        try:
            sha = sha1_file(local_path)
        except OSError as e:
            self.ui_q.put(("toast", "can't read file: %s" % e, "err"))
            return
        r = (remote_map or {}).get(dest)
        if r and not r["is_dir"] and r.get("sha1") == sha:
            self.ui_q.put(("toast", "✓ identical copy already on site — %s"
                           % dest, "ok"))
            self.ui_q.put(("log", "= exists (same sha1), upload skipped: %s"
                           % dest, "dim"))
            return
        self.ui_q.put(("status", "uploading → %s" % dest, "warn"))
        try:
            size = os.path.getsize(local_path)
        except OSError:
            size = 0
        self.ui_q.put(("log", "↑ %s  (%s · %s)"
                       % (dest, origin, human_size(size)), "plain"))
        try:
            cli.upload(dest, local_path)
        except Cancelled:
            raise
        except Exception as e:
            self.ui_q.put(("toast", "upload failed — %s" % dest, "err"))
            self.ui_q.put(("log", "✕ %s — %s" % (dest, e), "err"))
            return
        vtxt, vkind = "uploaded — %s (verify skipped)" % dest, "warn"
        try:
            ent = cli.list_dir(posixpath.dirname(dest)).get(dest)
            if ent:
                remote_map[dest] = ent
                if ent.get("sha1") == sha:
                    vtxt, vkind = "✓ uploaded + verified — %s" % dest, "ok"
                else:
                    vtxt, vkind = "⚠ sha1 mismatch after upload — %s" % dest, \
                                  "err"
                    self.ui_q.put(("log", "✕ sha1 mismatch after upload: %s"
                                   % dest, "err"))
            else:
                remote_map[dest] = {"path": dest, "is_dir": False,
                                    "size": size, "sha1": None,
                                    "updated_at": ""}
        except Exception:
            pass
        self.ui_q.put(("toast", vtxt, vkind))
        if vkind != "err":
            self.ui_q.put(("log", vtxt, vkind))

    def _drop_worker(self, files):
        self.ui_q.put(("busy", "", True))
        uploaded = 0
        try:
            cli = self._ensure_client()
            remote = self._ensure_remote(cli)
            root = self.cfg.get("local_folder") or ""
            # candidate folders depend only on (root, remote, excludes) —
            # gather them ONCE per batch, not once per dropped file
            try:
                dirs = gather_dirs(root, remote, self.cfg["excludes"])
            except Exception:
                dirs = []
            for fp in files:
                if self.cancel_event.is_set():
                    break
                fp = os.path.abspath(fp)
                inside, rel = in_root(root, fp)
                if inside and rel:
                    self._quick_upload(cli, fp, rel, remote,
                                       "already in site folder")
                    uploaded += 1
                    continue
                hints = extract_html_hints(fp)
                cands = rank_candidates(fp, dirs,
                                        self.cfg.get("learned_routes"), hints)
                payload = {"file": fp, "cands": cands, "dirs": dirs,
                           "event": threading.Event(), "result": None}
                self.ui_q.put(("guess", payload))
                payload["event"].wait(900)
                res = payload.get("result")
                if not res:
                    self.ui_q.put(("log", "skipped %s — no destination "
                                   "chosen" % os.path.basename(fp), "dim"))
                    continue
                d = res.get("dir") or ""
                dest = (to_posix(d) + "/" + os.path.basename(fp)).lstrip("/") \
                    if d else os.path.basename(fp)
                if res.get("remember"):
                    self.cfg.setdefault("learned_routes", {})[
                        norm_key(os.path.dirname(fp))] = d
                    save_config(self.cfg)
                    self.ui_q.put(("log", "★ remembered: %s → %s"
                                   % (os.path.dirname(fp), d or "(site root)"),
                                   "dim"))
                self._quick_upload(cli, fp, dest, remote, d or "site root")
                uploaded += 1
            if uploaded and self.cfg.get("local_folder") and \
                    os.path.isdir(self.cfg["local_folder"]):
                # only worth re-scanning for small/medium folders
                try:
                    n_loc = count_files_fast(self.cfg["local_folder"],
                                             self.cfg["excludes"])
                except Exception:
                    n_loc = 0
                if n_loc <= 2000:
                    try:
                        local = scan_folder(self.cfg["local_folder"],
                                            self.cfg["excludes"],
                                            self.cancel_event,
                                            sha_cache=self._sha_cache)
                        plan = build_plan(local, remote)
                        self.ui_q.put(("plan", plan, local, remote))
                    except Exception:
                        pass
                else:
                    self.ui_q.put(("log",
                                   "site folder holds %d files — skipped "
                                   "the automatic post-drop re-scan; press "
                                   "Scan & Plan when you want a fresh plan"
                                   % n_loc, "dim"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except ApiError as e:
            self.ui_q.put(("toast", "API error: %s" % e, "err"))
        except Exception as e:
            traceback.print_exc()
            self.ui_q.put(("toast", "drop failed: %s" % e, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    def _open_guess(self, payload):
        GuessDialog(self, payload)

    def _on_close(self):
        if self.busy and not messagebox.askokcancel(
                "Busy", "A job is still running — quit anyway?"):
            return
        self.cancel_event.set()
        for j in (self._auto_job, self._auto_ticker_job):
            if j:
                try:
                    self.after_cancel(j)
                except Exception:
                    pass
        try:
            save_config(self.cfg)
        except Exception:
            pass
        self.destroy()


# ═════════════════════════════════════════════════════════════════════════════
#  DIALOGS — GUESS (top-3 destination picker) + SETTINGS (incl. hidden REBUILD)
# ═════════════════════════════════════════════════════════════════════════════
class GuessDialog(tk.Toplevel):
    """“Where does this file go?” — top-3 candidates + manual folder + remember."""

    def __init__(self, app, payload):
        self.app, self.payload = app, payload
        T = app.T
        super().__init__(app)
        self.configure(bg=T["bg"])
        self.title("Where does this file go?")
        self.geometry("660x520")
        self.resizable(False, False)
        self.transient(app)
        self.after(120, self._modalize)
        self.protocol("WM_DELETE_WINDOW", self._cancel)

        fp = payload["file"]
        cands = payload.get("cands") or []
        parent = os.path.basename(os.path.dirname(fp)) or "this source folder"
        fname = os.path.basename(fp)

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)

        head = tk.Frame(self, bg=T["bg"])
        head.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 0))
        tk.Label(head, text='Where does “%s” go?' % fname, font=app.f_h1,
                 bg=T["bg"], fg=T["fg1"], anchor="w").grid(sticky="w")
        tk.Label(head, text="from  " + fp, font=app.f_mono_sm, bg=T["bg"],
                 fg=T["fg3"], anchor="w", justify="left",
                 wraplength=610).grid(sticky="w", pady=(2, 0))

        if cands:
            tk.Label(head, text="my best guesses — pick one:",
                     font=app.f_label, bg=T["bg"], fg=T["accent"],
                     anchor="w").grid(sticky="w", pady=(8, 0))
        else:
            tk.Label(head, text="no confident match — type the destination "
                                "folder below (blank = site root).",
                     font=app.f_small, bg=T["bg"], fg=T["accent"],
                     anchor="w").grid(sticky="w", pady=(8, 0))

        body = tk.Frame(self, bg=T["bg"])
        body.grid(row=2, column=0, sticky="nsew", padx=12, pady=6)
        body.grid_columnconfigure(0, weight=1)

        self.var = tk.StringVar(value=cands[0]["dir"] if cands else "")
        for i, c in enumerate(cands):
            card = tk.Frame(body, bg=T["bg2"],
                            highlightbackground=T["accent_border"] if i == 0
                            else T["border1"], highlightthickness=1)
            card.grid(sticky="ew", padx=4, pady=4)
            card.grid_columnconfigure(0, weight=1)
            top = tk.Frame(card, bg=T["bg2"])
            top.grid(sticky="ew", padx=10, pady=(9, 0))
            top.grid_columnconfigure(0, weight=1)
            rb = tk.Radiobutton(top, text=c["preview"], variable=self.var,
                                value=c["dir"], font=app.f_mono, bg=T["bg2"],
                                fg=T["fg1"], selectcolor=T["bg4"],
                                activebackground=T["bg2"],
                                activeforeground=T["fg1"],
                                highlightthickness=0, bd=0, anchor="w",
                                cursor="hand2", justify="left")
            rb.grid(sticky="w")
            tk.Label(top, text="%d%% match" % int(round(c["rel"] * 100)),
                     font=app.f_small, bg=T["bg2"], fg=T["accent"]
                     ).grid(row=0, column=1, sticky="e")
            bot = tk.Frame(card, bg=T["bg2"])
            bot.grid(sticky="ew", padx=10, pady=(0, 9))
            bot.grid_columnconfigure(0, weight=1)
            tk.Label(bot, text=c["why"], font=app.f_small, bg=T["bg2"],
                     fg=T["fg3"], anchor="w", wraplength=520,
                     justify="left").grid(row=0, column=0, sticky="w")
            bar = ProgressCanvas(bot, T, width=140, height=4)
            bar.grid(row=0, column=1, sticky="e")
            bar.set(c["rel"])

        manual = tk.Frame(self, bg=T["bg"])
        manual.grid(row=3, column=0, sticky="ew", padx=18, pady=(0, 2))
        manual.grid_columnconfigure(1, weight=1)
        tk.Label(manual, text="or type folder:", font=app.f_small,
                 bg=T["bg"], fg=T["fg3"]).grid(row=0, column=0, padx=(0, 8))
        self.manual_var = tk.StringVar()
        ent = tk.Entry(manual, textvariable=self.manual_var,
                       font=app.f_mono_sm, bg=T["bg3"], fg=T["fg1"],
                       insertbackground=T["fg1"], relief="flat", bd=0,
                       highlightthickness=1,
                       highlightbackground=T["border1"],
                       highlightcolor=T["accent_border"])
        ent.grid(row=0, column=1, sticky="ew", ipady=5)
        if not cands:
            ent.focus_set()

        foot = tk.Frame(self, bg=T["bg"])
        foot.grid(row=4, column=0, sticky="ew", padx=14, pady=12)
        self.remember_var = tk.BooleanVar(value=bool(cands))
        tk.Checkbutton(foot, text='★ remember "%s" → chosen folder' % parent,
                       variable=self.remember_var, font=app.f_small,
                       bg=T["bg"], fg=T["fg2"], selectcolor=T["bg3"],
                       activebackground=T["bg"], activeforeground=T["fg1"],
                       highlightthickness=0, bd=0, anchor="w",
                       cursor="hand2").grid(row=0, column=0, sticky="w")
        Btn(foot, text="Cancel", font=app.f_btn, bg=T["bg4"],
            hover=T["bg5"], fg=T["fg2"], ring=T["border2"],
            command=self._cancel).grid(row=0, column=1, padx=6)
        Btn(foot, text="Upload ⬆", font=app.f_btn, bg=T["accent"],
            hover=T["accent2"], fg="#1a1a1a",
            command=self._confirm).grid(row=0, column=2)
        foot.grid_columnconfigure(0, weight=1)

    def _confirm(self):
        manual = self.manual_var.get().strip().strip("/")
        d = manual if manual else (self.var.get() or "")
        self.payload["result"] = {"dir": d,
                                  "remember": bool(self.remember_var.get())}
        self.payload["event"].set()
        self.destroy()

    def _modalize(self):
        try:
            if self.winfo_exists():
                self.lift()
                self.focus_force()
                self.grab_set()
        except Exception:
            pass

    def _cancel(self):
        self.payload["result"] = None
        self.payload["event"].set()
        self.destroy()


class SettingsDialog(tk.Toplevel):
    def __init__(self, app):
        self.app = app
        T = app.T
        cfg = app.cfg
        super().__init__(app)
        self.title("Settings — %s (lite)" % APP_NAME)
        self.configure(bg=T["bg"])
        self.geometry("680x680")
        self.transient(app)
        self.after(120, self._modalize)
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)

        body = ScrollFrame(self, T["bg"])
        body.grid(row=0, column=0, sticky="nsew", padx=16, pady=(14, 0))
        b = body.inner
        b.grid_columnconfigure(1, weight=1)
        row = {"n": 0}

        def cap(txt):
            tk.Label(b, text=txt.upper(), font=app.f_label, bg=T["bg"],
                     fg=T["accent"], anchor="w"
                     ).grid(row=row["n"], column=0, columnspan=3,
                            sticky="w", pady=(16, 4))
            row["n"] += 1

        def lbl(txt):
            tk.Label(b, text=txt, font=app.f_small, bg=T["bg"], fg=T["fg2"],
                     anchor="w").grid(row=row["n"], column=0, sticky="w",
                                      padx=(0, 10), pady=6)

        def note(txt, r=None):
            tk.Label(b, text=txt, font=app.f_small, bg=T["bg"], fg=T["fg3"],
                     anchor="w", justify="left"
                     ).grid(row=row["n"] if r is None else r, column=1,
                            sticky="w")

        cap("Neocities account")
        lbl("API key")
        self.key_var = tk.StringVar(value=cfg.get("api_key") or "")
        self.key_ent = tk.Entry(b, textvariable=self.key_var, show="•",
                                font=app.f_mono_sm, bg=T["bg3"], fg=T["fg1"],
                                insertbackground=T["fg1"], relief="flat",
                                bd=0, highlightthickness=1,
                                highlightbackground=T["border1"],
                                highlightcolor=T["accent_border"])
        self.key_ent.grid(row=row["n"], column=1, sticky="ew", pady=6,
                          ipady=5)
        Btn(b, text="👁", font=app.f_small, bg=T["bg4"], hover=T["bg5"],
            fg=T["fg2"], padx=8, ipady=3,
            command=self._toggle_key).grid(row=row["n"], column=2,
                                           padx=(8, 0))
        row["n"] += 1
        note("neocities.org/settings → scroll to “Your API key”")
        row["n"] += 1

        cap("Local site folder")
        lbl("folder")
        self.folder_var = tk.StringVar(value=cfg.get("local_folder") or "")
        tk.Entry(b, textvariable=self.folder_var, font=app.f_mono_sm,
                 bg=T["bg3"], fg=T["fg1"], insertbackground=T["fg1"],
                 relief="flat", bd=0, highlightthickness=1,
                 highlightbackground=T["border1"],
                 highlightcolor=T["accent_border"]
                 ).grid(row=row["n"], column=1, sticky="ew", pady=6, ipady=5)
        Btn(b, text="…", font=app.f_btn, bg=T["bg4"], hover=T["bg5"],
            fg=T["fg2"], padx=8, ipady=3,
            command=self._pick).grid(row=row["n"], column=2, padx=(8, 0))
        row["n"] += 1

        cap("Sync behaviour")
        lbl("parallel uploads")
        self.workers_var = tk.IntVar(value=int(cfg.get("workers") or 8))
        self.workers_lbl = tk.Label(b, text="%d" % self.workers_var.get(),
                                    width=3, font=app.f_mono_sm, bg=T["bg"],
                                    fg=T["fg1"])
        sl = tk.Scale(b, from_=1, to=16, orient="horizontal",
                      variable=self.workers_var, showvalue=False,
                      bg=T["bg"], fg=T["fg1"], troughcolor=T["bg4"],
                      highlightthickness=0, bd=0, relief="flat",
                      activebackground=T["accent"], sliderrelief="raised",
                      borderwidth=0, width=12, font=app.f_small,
                      command=lambda v: self.workers_lbl.configure(
                          text="%d" % int(float(v))))
        sl.grid(row=row["n"], column=1, sticky="ew", pady=6)
        self.workers_lbl.grid(row=row["n"], column=2, padx=(8, 0))
        row["n"] += 1

        lbl("auto-sync interval")
        self.auto_var = tk.StringVar(
            value=_secs_choice(int(cfg.get("auto_sync_secs") or 0)))
        om = tk.OptionMenu(b, self.auto_var, *[c[0] for c in AUTO_CHOICES])
        om.configure(font=app.f_small, bg=T["bg3"], fg=T["fg1"],
                     activebackground=T["bg5"], activeforeground=T["accent"],
                     bd=0, highlightthickness=1,
                     highlightbackground=T["border1"],
                     highlightcolor=T["accent_border"], cursor="hand2",
                     anchor="w", padx=10)
        om.grid(row=row["n"], column=1, sticky="ew", pady=6, ipady=4)
        try:
            m = om.nametowidget(om["menu"])
            m.configure(font=app.f_small, bg=T["bg3"], fg=T["fg1"], bd=0,
                        activebackground=T["bg5"],
                        activeforeground=T["accent"])
        except Exception:
            pass
        row["n"] += 1
        note("runs the full Scan & Plan + Sync cycle on a timer — also on "
             "the ⏱ toolbar button")
        row["n"] += 1

        lbl("exclude patterns")
        self.exc_box = tk.Text(b, height=7, font=app.f_mono_sm, bg=T["bg3"],
                               fg=T["fg1"], insertbackground=T["fg1"],
                               relief="flat", bd=0, highlightthickness=1,
                               highlightbackground=T["border1"],
                               highlightcolor=T["accent_border"], padx=8,
                               pady=6, wrap="none")
        self.exc_box.grid(row=row["n"], column=1, columnspan=2,
                          sticky="ew", pady=6)
        self.exc_box.insert("1.0", "\n".join(cfg.get("excludes") or []))
        row["n"] += 1
        note("one per line —  *.psd  ·  node_modules/  ·  assets/drafts/*")
        row["n"] += 1

        self.chk_del = tk.BooleanVar(value=bool(cfg.get("mirror_deletes",
                                                        True)))
        self.chk_ver = tk.BooleanVar(value=bool(cfg.get("auto_verify", True)))
        self.chk_auto = tk.BooleanVar(value=bool(cfg.get("auto_scan_on_open",
                                                         True)))
        self.chk_auto_del = tk.BooleanVar(
            value=bool(cfg.get("auto_sync_deletes", False)))
        for var, txt in (
                (self.chk_del, "mirror deletes — remove remote files that no "
                               "longer exist locally (asked first)"),
                (self.chk_ver, "auto-verify — re-list site after sync and "
                               "sha1-compare every upload"),
                (self.chk_auto, "auto scan on open — build the plan when the "
                                "app launches"),
                (self.chk_auto_del, "auto-sync may delete — interval runs may "
                                    "mirror-delete remote-only files WITHOUT "
                                    "asking (root index.html stays "
                                    "protected)")):
            tk.Checkbutton(b, text=txt, variable=var, font=app.f_small,
                           bg=T["bg"], fg=T["fg2"], selectcolor=T["bg3"],
                           activebackground=T["bg"],
                           activeforeground=T["fg1"], highlightthickness=0,
                           bd=0, anchor="w", cursor="hand2"
                           ).grid(row=row["n"], column=0, columnspan=3,
                                  sticky="w", pady=3)
            row["n"] += 1

        cap("Maintenance")
        tk.Label(b, text="Rebuild — pull every file from the live site into "
                         "your local folder (like the\nCLI's 'neocities pull "
                         ".'). Server files overwrite local ones; "
                         "local-only\nfiles are kept and nothing on the "
                         "server is changed. For when your local\ncopy is "
                         "lost or out of sync.",
                 font=app.f_small, bg=T["bg"], fg=T["fg3"], anchor="w",
                 justify="left").grid(row=row["n"], column=0, columnspan=3,
                                      sticky="w", pady=(0, 6))
        row["n"] += 1
        Btn(b, text="Rebuild from server ⬇", font=app.f_btn,
            bg=T["err_dim"], hover=blend(T["err"], T["bg"], 0.22),
            fg=T["err"], ring=T["err"], ipady=3,
            command=self._rebuild).grid(row=row["n"], column=0,
                                        columnspan=3, sticky="w")
        row["n"] += 1

        cap("Appearance (theme / scrollbar overrides)")
        tk.Label(b, text="dark-gray WWZ §02 tokens + §23 ultra-thin "
                         "scrollbars are built in (lite edition: overrides\n"
                         "apply on next launch). Edit %s:\n"
                         "\"theme\": {\"accent\": \"#ff7847\"}   ·   "
                         "\"scrollbar\": {\"width\": 8}" % CONFIG_PATH,
                 font=app.f_small, bg=T["bg"], fg=T["fg3"], anchor="w",
                 justify="left").grid(row=row["n"], column=0, columnspan=3,
                                      sticky="w", pady=(2, 6))
        row["n"] += 1

        self.test_lbl = tk.Label(b, text="", font=app.f_small, bg=T["bg"],
                                 fg=T["fg3"], anchor="w")
        self.test_lbl.grid(row=row["n"], column=0, columnspan=3, sticky="w")
        row["n"] += 1

        foot = tk.Frame(self, bg=T["bg"])
        foot.grid(row=1, column=0, sticky="ew", padx=16, pady=12)
        foot.grid_columnconfigure(1, weight=1)
        Btn(foot, text="Test connection", font=app.f_btn, bg=T["bg4"],
            hover=T["bg5"], fg=T["fg1"], ring=T["comp"],
            command=self._test).grid(row=0, column=0, sticky="w")
        Btn(foot, text="Cancel", font=app.f_btn, bg=T["bg4"], hover=T["bg5"],
            fg=T["fg2"], ring=T["border2"],
            command=self.destroy).grid(row=0, column=2, padx=6)
        Btn(foot, text="Save ✓", font=app.f_btn, bg=T["accent"],
            hover=T["accent2"], fg="#1a1a1a",
            command=self._save).grid(row=0, column=3)

    def _modalize(self):
        try:
            if self.winfo_exists():
                self.lift()
                self.focus_force()
                self.grab_set()
        except Exception:
            pass

    def _toggle_key(self):
        self.key_ent.configure(show="" if self.key_ent.cget("show") else "•")

    def _pick(self):
        d = filedialog.askdirectory(parent=self,
                                    title="Choose local site folder")
        if d:
            self.folder_var.set(d)

    def _test(self):
        key = self.key_var.get().strip()
        if not key:
            self.test_lbl.configure(text="✕ no key entered",
                                    fg=self.app.T["err"])
            return
        self.test_lbl.configure(text="testing…", fg=self.app.T["fg3"])

        def run():
            try:
                info = Neocities(key).info()
                site = info.get("sitename", "?")
                msg = ("✓ connected — site: %s  ·  %s views / %s hits"
                       % (site, "{:,}".format(info.get("views") or 0),
                          "{:,}".format(info.get("hits") or 0)))
                self.app.ui_q.put(("test_result", msg, "ok"))
            except Exception as e:
                self.app.ui_q.put(("test_result", "✕ failed — %s" % e, "err"))
        threading.Thread(target=run, daemon=True).start()

    def apply_test_result(self, text, kind):
        """runs on the main thread via app.ui_q — never tk from the worker."""
        try:
            self.test_lbl.configure(text=text, fg=self.app.T[kind])
        except Exception:
            pass

    def _rebuild(self):
        if self.app.start_rebuild():
            self.destroy()          # watch the pull live in Activity

    def _save(self):
        cfg = self.app.cfg
        cfg["api_key"] = self.key_var.get().strip()
        cfg["local_folder"] = self.folder_var.get().strip()
        try:
            cfg["workers"] = max(1, min(16, int(self.workers_var.get())))
        except Exception:
            cfg["workers"] = 8
        cfg["excludes"] = [l.strip() for l in
                           self.exc_box.get("1.0", "end").splitlines()
                           if l.strip()]
        cfg["mirror_deletes"] = bool(self.chk_del.get())
        cfg["auto_verify"] = bool(self.chk_ver.get())
        cfg["auto_scan_on_open"] = bool(self.chk_auto.get())
        cfg["auto_sync_deletes"] = bool(self.chk_auto_del.get())
        for label, s in AUTO_CHOICES:
            if label == self.auto_var.get():
                cfg["auto_sync_secs"] = s
                break
        save_config(cfg)
        self.app.folder_var.set(cfg["local_folder"])
        self.app._apply_style()
        self.app.refresh_stats(None, None)
        self.app._arm_auto(announce=True)
        self.app._toast("settings saved ✓", "ok")
        self.destroy()


# ═════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═════════════════════════════════════════════════════════════════════════════
def _fatal_dump():
    tb = traceback.format_exc()
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(os.path.join(CONFIG_DIR, "error.log"), "a",
                  encoding="utf-8") as f:
            f.write("[%s] %s\n" % (datetime.now().isoformat(), tb))
    except Exception:
        pass
    try:
        r = tk.Tk()
        r.withdraw()
        messagebox.showerror(APP_NAME, "NeoSync (lite) failed to start.\n\n"
                             "%s\n\nDetails written to:\n%s"
                             % (tb.strip().splitlines()[-1],
                                os.path.join(CONFIG_DIR, "error.log")))
        r.destroy()
    except Exception:
        pass


def main():
    try:
        app = App()
    except Exception:
        _fatal_dump()
        return
    app._install_wheel_router()
    try:
        app.mainloop()
    except Exception:
        _fatal_dump()


if __name__ == "__main__":
    main()
