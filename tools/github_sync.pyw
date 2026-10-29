# -*- coding: utf-8 -*-
"""
GitSync (lite) — GitHub twin of NeoSync, pure tkinter, single file.
====================================================================
Same app, same WWZ dark UI, same workflow as neocities_sync.pyw:
Scan & Plan → Sync (mirror) · drop-guess engine · auto-sync timer · Verify ·
hidden Rebuild (pull) — but the target is a GitHub repo/branch, and every
file row has a  ⧉ link  button that copies that file's URL to the clipboard.

  pip install requests          # the ONLY hard dependency
  pip install tkinterdnd2       # OPTIONAL — enables drag & drop

SETUP  ⚙ Settings → paste a GitHub token + "owner/repo" + branch.
  Token: github.com/settings/personal-access-tokens (fine-grained, repo
  access → your repo, permission "Contents: Read and write") or a classic
  token with the `repo` scope.

HOW IT PUSHES (why it's different from Neocities)
  * ONE commit per sync (Git Data API: blobs → tree → commit → ref), not one
    commit per file. Text files travel inline inside the tree call, so a
    typical sync costs only a handful of API requests (GitHub's secondary
    rate limit caps content-creating requests at ~80/min; writes are
    throttled to stay under it).
  * Comparison uses git blob SHA-1s ("blob <size>\\0<bytes>"), so it matches
    GitHub's tree listing exactly — no downloading to compare.
  * Mirror deletes are OFF by default (repos hold README/LICENSE/etc.).
    "protected" names are never deleted. Deletions are a new commit, so
    they're recoverable from history.
  * Optional "subfolder in repo" (e.g. docs) → local folder maps to it.

COPY LINK  (toolbar "Link: …" picks the style; per-row ⧉ link; ⧉ Copy links
  copies every file in the current filter; double-click a path to copy it)
    Raw      raw.githubusercontent.com/owner/repo/branch/path
    Pages    owner.github.io/repo/path   (custom base URL in Settings)
    GitHub   github.com/owner/repo/blob/branch/path
    jsDelivr cdn.jsdelivr.net/gh/owner/repo@branch/path
  Note: raw serves .html as text/plain; use Pages or jsDelivr to render it.

CONFIG   ~/.github-sync/config.json
"""
from __future__ import annotations

import os
import re
import json
import time
import base64
import random
import difflib
import fnmatch
import hashlib
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

APP_NAME = "GitSync"
APP_VER = "1.0.0"
API_BASE = "https://api.github.com"
CONFIG_DIR = os.path.join(os.path.expanduser("~"), ".github-sync")
CONFIG_PATH = os.path.join(CONFIG_DIR, "config.json")
REPO_RE = re.compile(r"^[\w.-]+/[\w.-]+$")

MAX_FILE = 100 * 1024 * 1024      # GitHub hard limit per file
INLINE_MAX = 1_500_000            # text files up to this ride inside the tree call
BATCH_BYTES = 6_000_000           # max inline payload per create-tree request
BATCH_COUNT = 250
WRITE_GAP = 0.8                   # s between write requests (~75/min < 80/min limit)

LINK_LABELS = {"raw": "Raw", "pages": "Pages", "blob": "GitHub",
               "jsdelivr": "jsDelivr"}

# ── theme: WWZ unified profile §02 tokens-dark, "Dark · effects off" mode ──
THEME_DEFAULTS = {
    "bg": "#1a1a1a", "bg2": "#222222", "bg3": "#2a2a2a", "bg4": "#333333",
    "bg5": "#3a3a3a", "bg6": "#444444", "black_hl": "#000000",
    "fg1": "#ececed", "fg2": "#a4a4a8", "fg3": "#6f6f73",
    "accent": "#f39a24", "accent2": "#ffad3d", "accent_dark": "#a76a1c",
    "ok": "#5cb47e", "err": "#d96565", "info": "#7ba3d8",
    "border1": "#262626", "border2": "#313131", "comp": "#414141",
    "buy": "#2a2a2e",
    "scrl_width": 6, "scrl_thumb": "#4b5563", "scrl_thumb_hover": "#6b7280",
    "scrl_track": "#000000", "scrl_radius": 3,
}
UI_FONTS = ["Space Grotesk", "Segoe UI Variable Text", "Segoe UI",
            "SF Pro Text", "Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"]
MONO_FONTS = ["JetBrains Mono", "Cascadia Mono", "Cascadia Code", "Consolas",
              "SF Mono", "Menlo", "DejaVu Sans Mono", "Courier New"]

DEFAULT_CONFIG = {
    "token": "",
    "repo": "",                    # owner/name
    "branch": "main",
    "repo_subdir": "",             # optional: local folder maps to this repo folder
    "local_folder": "",
    "workers": 4,
    "mirror_deletes": False,       # repos hold README/LICENSE/…: opt-in
    "auto_verify": True,
    "auto_scan_on_open": True,
    "auto_sync_secs": 0,
    "auto_sync_deletes": False,
    "link_kind": "raw",            # raw | pages | blob | jsdelivr
    "pages_base": "",              # custom Pages base, e.g. https://example.com
    "commit_msg": "GitSync: {n} changed, {d} deleted",   # {n} {d} {time}
    "excludes": ["*.psd", "*.ai", "*.log", "*.tmp", "*.bak", "node_modules/",
                 ".git/", ".DS_Store", "Thumbs.db", "desktop.ini",
                 "__MACOSX/"],
    "protected": ["readme*", "license*", ".gitignore", ".gitattributes",
                  "cname", ".nojekyll", ".github/*"],
    "learned_routes": {},
    "theme": {},
    "scrollbar": {},
    "last_sync": None,
}


# ── small utils ──────────────────────────────────────────────────────────────
def blend(fg: str, bg: str, alpha: float) -> str:
    f, b = fg.lstrip("#"), bg.lstrip("#")
    f = f * (6 // len(f)) if len(f) == 3 else f
    b = b * (6 // len(b)) if len(b) == 3 else b
    r = round(int(f[0:2], 16) * alpha + int(b[0:2], 16) * (1 - alpha))
    g = round(int(f[2:4], 16) * alpha + int(b[2:4], 16) * (1 - alpha))
    bl = round(int(f[4:6], 16) * alpha + int(b[4:6], 16) * (1 - alpha))
    return "#%02x%02x%02x" % (min(r, 255), min(g, 255), min(bl, 255))


def git_sha_bytes(data: bytes) -> str:
    """git blob id of in-memory bytes (matches GitHub's tree listing)."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def git_sha_file(path: str, buf: int = 1 << 20) -> str:
    h = hashlib.sha1()
    h.update(b"blob %d\0" % os.path.getsize(path))
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
    for label, s in AUTO_CHOICES:
        if s == secs:
            return label
    return "Off"


def norm_key(path: str) -> str:
    try:
        p = os.path.normpath(os.path.abspath(path))
    except Exception:
        p = str(path)
    return p.lower().replace("\\", "/")


def to_posix(p: str) -> str:
    return (p or "").replace("\\", "/").strip("/")


def norm_repo(s: str) -> str:
    """accept 'owner/repo', a github.com URL, or a .git clone URL."""
    s = (s or "").strip()
    m = re.match(r"^(?:https?://)?([\w-]+)\.github\.io/([\w.-]+)", s, re.I)
    if m:                                    # a GitHub Pages address
        return "%s/%s" % (m.group(1), m.group(2))
    s = re.sub(r"^(https?://)?(www\.)?github\.com/", "", s, flags=re.I)
    s = re.sub(r"^git@github\.com:", "", s, flags=re.I)
    s = re.sub(r"\.git$", "", s.strip("/"))
    return "/".join(s.split("/")[:2])


def in_root(root: str, path: str):
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
    if low_name == ".git":                       # never sync git internals
        return True
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


def is_protected(rel: str, patterns) -> bool:
    low = (rel or "").lower()
    return any(fnmatch.fnmatch(low, (p or "").strip().lower())
               for p in (patterns or []) if (p or "").strip())


def count_files_fast(root: str, excludes) -> int:
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


def _as_text(data: bytes):
    """str if the bytes are plain UTF-8 text (safe to send inline), else None."""
    if b"\x00" in data:
        return None
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return None


def build_link(cfg: dict, rel: str, kind: str = None) -> str:
    """public URL of one file. `rel` is relative to the local site folder."""
    repo = norm_repo(cfg.get("repo") or "")
    owner, _, name = repo.partition("/")
    branch = (cfg.get("branch") or "main").strip()
    sub = to_posix(cfg.get("repo_subdir"))
    full = (sub + "/" + rel) if sub else rel
    q = lambda s: urllib.parse.quote(s, safe="/")
    kind = kind or cfg.get("link_kind") or "raw"
    if kind == "blob":
        return "https://github.com/%s/%s/blob/%s/%s" % (owner, name, q(branch), q(full))
    if kind == "jsdelivr":
        return "https://cdn.jsdelivr.net/gh/%s/%s@%s/%s" % (owner, name, q(branch), q(full))
    if kind == "pages":
        base = (cfg.get("pages_base") or "").strip().rstrip("/")
        if not base:
            if name.lower() == (owner + ".github.io").lower():
                base = "https://%s.github.io" % owner
            else:
                base = "https://%s.github.io/%s" % (owner, name)
        # when a subfolder is set we assume Pages serves FROM that folder
        return base + "/" + q(rel if sub else full)
    return "https://raw.githubusercontent.com/%s/%s/%s/%s" % (owner, name, q(branch), q(full))


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
            pass
    else:
        save_config(cfg)
    return cfg


def save_config(cfg: dict) -> None:
    os.makedirs(CONFIG_DIR, exist_ok=True)
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)
    os.replace(tmp, CONFIG_PATH)
    try:
        os.chmod(CONFIG_PATH, 0o600)       # holds the token; best effort
    except OSError:
        pass


def build_theme(cfg: dict) -> dict:
    t = deep_merge(THEME_DEFAULTS, (cfg.get("theme") or {}))
    sb = deep_merge({"width": t["scrl_width"], "thumb": t["scrl_thumb"],
                     "thumb_hover": t["scrl_thumb_hover"], "track": t["scrl_track"]},
                    (cfg.get("scrollbar") or {}))
    t["accent_dim"] = blend(t["accent"], t["bg"], 0.10)
    t["accent_border"] = blend(t["accent"], t["bg"], 0.35)
    t["ok_dim"] = blend(t["ok"], t["bg"], 0.12)
    t["err_dim"] = blend(t["err"], t["bg"], 0.12)
    t["info_dim"] = blend(t["info"], t["bg"], 0.12)
    t["scrl_width"] = int(sb["width"]); t["scrl_thumb"] = sb["thumb"]
    t["scrl_thumb_hover"] = sb["thumb_hover"]; t["scrl_track"] = sb["track"]
    return t


# ── errors ───────────────────────────────────────────────────────────────────
class ApiError(Exception):
    def __init__(self, status: int, body: str = ""):
        self.status, self.body = status, (body or "")[:220]
        super().__init__("HTTP %s %s" % (status or "?", self.body))


class Cancelled(Exception):
    pass


class QuietExit(Exception):
    """user-fixable condition already reported to the UI."""


def friendly(e) -> str:
    if isinstance(e, ApiError):
        s = e.status
        if s == 401:
            return "GitHub rejected the token (401) — check ⚙ Settings"
        if s == 403:
            return "GitHub refused (403): %s — token needs Contents: read & write" % e.body
        if s == 404:
            return "repo or branch not found (404) — check owner/repo, branch & token access"
        if s == 409:
            return "repo is empty — create a first commit on GitHub (e.g. add a README), then retry"
        if s == 422:
            return "GitHub rejected the update (422): %s" % e.body
    return str(e)


# ── GitHub REST client (Git Data API) ────────────────────────────────────────
class GitHub:
    """Bearer-auth client. Retries 429/5xx/secondary-rate-limits with backoff,
    throttles writes, honours cancel."""

    def __init__(self, token: str, repo: str, cancel: threading.Event = None):
        self.cancel = cancel or threading.Event()
        self.repo = norm_repo(repo)
        self.sess = requests.Session()
        self.sess.headers.update({
            "Authorization": "Bearer %s" % token.strip(),
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "%s/%s" % (APP_NAME, APP_VER),
        })
        self._tlock, self._tlast = threading.Lock(), 0.0

    # low-level ---------------------------------------------------------------
    def _sleep(self, secs: float):
        end = time.time() + secs
        while time.time() < end:
            if self.cancel.is_set():
                raise Cancelled()
            time.sleep(0.25)

    def _throttle(self):
        with self._tlock:
            wait = self._tlast + WRITE_GAP - time.time()
            if wait > 0:
                time.sleep(wait)
            self._tlast = time.time()

    def _backoff(self, attempt: int, resp=None):
        wait = min(30.0, 1.7 ** attempt) + random.uniform(0.0, 0.5)
        if resp is not None:
            try:
                ra = resp.headers.get("Retry-After")
                if ra:
                    wait = max(wait, min(90.0, float(ra) + 1))
                elif resp.headers.get("X-RateLimit-Remaining") == "0":
                    reset = float(resp.headers.get("X-RateLimit-Reset") or 0)
                    wait = max(wait, min(90.0, reset - time.time() + 1))
            except ValueError:
                pass
        self._sleep(wait)

    @staticmethod
    def _limited(r) -> bool:
        return r.status_code == 403 and (
            r.headers.get("Retry-After")
            or r.headers.get("X-RateLimit-Remaining") == "0"
            or "rate limit" in (r.text or "").lower())

    @staticmethod
    def _msg(r) -> str:
        try:
            return str(r.json().get("message") or "")[:220]
        except Exception:
            return (r.text or "")[:220]

    def _req(self, method: str, path: str, tries: int = 5, raw: bool = False, **kw):
        last = None
        for attempt in range(tries):
            if self.cancel.is_set():
                raise Cancelled()
            if method != "GET":
                self._throttle()
            try:
                r = self.sess.request(method, API_BASE + path,
                                      timeout=(10, 120), **kw)
            except (requests.exceptions.ConnectionError,
                    requests.exceptions.Timeout) as e:
                last = e
                self._backoff(attempt)
                continue
            if r.status_code == 429 or r.status_code >= 500 or self._limited(r):
                last = ApiError(r.status_code, self._msg(r))
                self._backoff(attempt, r)
                continue
            if r.status_code >= 400:
                raise ApiError(r.status_code, self._msg(r))
            if raw:
                return r.content
            if r.status_code == 204 or not r.content:
                return {}
            return r.json()
        raise last if last is not None else RuntimeError("request failed")

    # endpoints ---------------------------------------------------------------
    def repo_info(self) -> dict:
        return self._req("GET", "/repos/%s" % self.repo)

    def head(self, branch: str):
        """(commit sha, tree sha) of the branch tip."""
        j = self._req("GET", "/repos/%s/git/ref/heads/%s"
                      % (self.repo, urllib.parse.quote(branch, safe="/")))
        sha = j["object"]["sha"]
        c = self._req("GET", "/repos/%s/git/commits/%s" % (self.repo, sha))
        return sha, c["tree"]["sha"]

    def list_files(self, branch: str, sub: str = ""):
        """-> ({relpath: {path,is_dir,size,sha1}}, commit sha, tree sha).
        sha1 is the git blob id. With `sub`, only that folder, paths made
        relative to it."""
        head, tree = self.head(branch)
        j = self._req("GET", "/repos/%s/git/trees/%s?recursive=1" % (self.repo, tree))
        if j.get("truncated"):
            raise ApiError(0, "listing truncated — repo has too many files "
                              "for one request (use a subfolder)")
        sub = to_posix(sub)
        pre = sub + "/" if sub else ""
        out = {}
        for e in j.get("tree") or []:
            p = e.get("path") or ""
            if pre:
                if not p.startswith(pre):
                    continue
                p = p[len(pre):]
            if not p:
                continue
            t = e.get("type")
            if t == "tree":
                out[p] = {"path": p, "is_dir": True, "size": 0, "sha1": None}
            elif t == "blob":
                out[p] = {"path": p, "is_dir": False, "size": e.get("size") or 0,
                          "sha1": (e.get("sha") or "").lower()}
        return out, head, tree

    def create_blob(self, data: bytes) -> str:
        j = self._req("POST", "/repos/%s/git/blobs" % self.repo,
                      json={"content": base64.b64encode(data).decode("ascii"),
                            "encoding": "base64"})
        return j["sha"]

    def create_tree(self, base_tree: str, entries: list) -> str:
        j = self._req("POST", "/repos/%s/git/trees" % self.repo,
                      json={"base_tree": base_tree, "tree": entries})
        return j["sha"]

    def create_commit(self, message: str, tree: str, parent: str) -> str:
        j = self._req("POST", "/repos/%s/git/commits" % self.repo,
                      json={"message": message, "tree": tree, "parents": [parent]})
        return j["sha"]

    def update_ref(self, branch: str, sha: str):
        self._req("PATCH", "/repos/%s/git/refs/heads/%s"
                  % (self.repo, urllib.parse.quote(branch, safe="/")),
                  json={"sha": sha, "force": False})

    def push(self, branch, sub, items, dels, message, workers, log, prog):
        """ONE commit for everything. items [(rel, local_abs)], dels [rel].
        Returns (commit sha | None, {rel: git sha} of pushed files, failed rels)."""
        pre = (to_posix(sub) + "/") if sub else ""
        head, base_tree = self.head(branch)
        shas, failed, text_e, bin_f = {}, [], [], []
        for rel, lp in items:
            if self.cancel.is_set():
                raise Cancelled()
            try:
                if os.path.getsize(lp) > MAX_FILE:
                    raise ValueError("over GitHub's 100 MB file limit")
                with open(lp, "rb") as f:
                    data = f.read()
            except (OSError, ValueError) as e:
                failed.append(rel)
                log("✕ %s — %s" % (rel, e), "err")
                continue
            sha = git_sha_bytes(data)
            txt = _as_text(data) if len(data) <= INLINE_MAX else None
            if txt is not None:
                text_e.append((len(data), {"path": pre + rel, "mode": "100644",
                                           "type": "blob", "content": txt}))
                shas[rel] = sha
            else:
                bin_f.append((rel, lp, sha))
            del data
        total = len(items)
        done = len(failed)

        blob_e = []
        if bin_f:
            def blob_task(rel, lp, sha):
                with open(lp, "rb") as f:
                    return rel, sha, self.create_blob(f.read())
            with ThreadPoolExecutor(max_workers=max(1, workers)) as ex:
                futs = {ex.submit(blob_task, *b): b[0] for b in bin_f}
                for fut in as_completed(futs):
                    rel = futs[fut]
                    try:
                        rel, sha, got = fut.result()
                        blob_e.append({"path": pre + rel, "mode": "100644",
                                       "type": "blob", "sha": got})
                        shas[rel] = sha
                        log("↑ blob %s" % rel, "plain")
                    except Cancelled:
                        raise
                    except Exception as e:
                        failed.append(rel)
                        log("✕ %s — %s" % (rel, e), "err")
                    done += 1
                    prog(done, total, "up")

        pend = [(0, {"path": pre + r, "mode": "100644", "type": "blob",
                     "sha": None}) for r in dels]            # null sha = delete
        pend += [(0, e) for e in blob_e]
        pend += text_e
        if not pend:
            return None, shas, failed
        batches, cur, w = [], [], 0
        for wgt, ent in pend:
            if cur and (w + wgt > BATCH_BYTES or len(cur) >= BATCH_COUNT):
                batches.append(cur)
                cur, w = [], 0
            cur.append(ent)
            w += wgt + 200
        if cur:
            batches.append(cur)
        tree = base_tree
        for b in batches:
            if self.cancel.is_set():
                raise Cancelled()
            tree = self.create_tree(tree, b)
            done += sum(1 for e in b if "content" in e)
            prog(done, total, "up")
        commit = self.create_commit(message, tree, head)
        self.update_ref(branch, commit)
        return commit, shas, failed

    def download(self, sha: str, local_path: str) -> bool:
        """pull one blob by id (raw media type), verify its git sha, write
        atomically via a .part~ file."""
        data = self._req("GET", "/repos/%s/git/blobs/%s" % (self.repo, sha),
                         raw=True,
                         headers={"Accept": "application/vnd.github.raw+json"})
        if git_sha_bytes(data) != sha:
            raise ApiError(0, "downloaded bytes do not match blob %s" % sha[:7])
        d = os.path.dirname(local_path)
        if d:
            os.makedirs(d, exist_ok=True)
        tmp = local_path + ".part~"
        with open(tmp, "wb") as f:
            f.write(data)
        os.replace(tmp, local_path)
        return True
# ═════════════════════════════════════════════════════════════════════════════
#  LOCAL SCANNER · MIRROR PLAN · DROP-GUESS ENGINE
# ═════════════════════════════════════════════════════════════════════════════

def scan_folder(root: str, excludes, cancel=None, progress=None,
                sha_cache=None) -> dict:
    """walk local folder -> {posix relpath: {size, mtime, sha1(git blob id)}}.
    sha_cache {rel: (size, mtime, sha)} skips re-hashing unchanged files."""
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
                    sha = git_sha_file(full)
                out[rel] = {"size": st.st_size, "mtime": st.st_mtime, "sha1": sha}
                if sha_cache is not None:
                    sha_cache[rel] = (st.st_size, st.st_mtime, sha)
                n += 1
                if progress:
                    progress(n)
            except OSError:
                continue
    return out


def build_plan(local: dict, remote: dict, protected=()) -> list:
    """compare local git-sha map against the repo tree. Git is case-sensitive,
    so matching is exact. Order: NEW (newest first) -> CHG -> DEL -> SAME."""
    rf = {p: e for p, e in (remote or {}).items() if not e["is_dir"]}
    entries = []
    for lp, le in (local or {}).items():
        re_ = rf.get(lp)
        if re_ is None:
            act, note = "new", ""
        elif re_.get("sha1") != le["sha1"]:
            act, note = "chg", "content differs"
        else:
            act, note = "same", ""
        entries.append({"path": lp, "action": act, "size": le["size"],
                        "mtime": le["mtime"], "note": note})
    for rp, re_ in rf.items():
        if rp in (local or {}):
            continue
        prot = is_protected(rp, protected)
        entries.append({"path": rp, "action": "del", "size": re_.get("size") or 0,
                        "mtime": None, "prot": prot,
                        "note": "protected — never deleted" if prot else ""})
    order = {"new": 0, "chg": 1, "del": 2, "same": 3}
    entries.sort(key=lambda e: (order[e["action"]], -(e["mtime"] or 0.0),
                                e["path"].lower()))
    return entries


def _unsafe_remote_path(p: str) -> bool:
    if not p or p.startswith("/") or "\\" in p:
        return True
    return any(seg in ("..", "") for seg in p.split("/"))


def collect_pull_files(remote: dict, excludes):
    """-> (files [{path,size,sha1}], dirs, collisions) for a server→local pull."""
    files, dirs, collisions, seen = [], [], [], {}
    for p, e in (remote or {}).items():
        if _unsafe_remote_path(p):
            continue
        if e["is_dir"]:
            if not is_excluded(p, p.rsplit("/", 1)[-1], True, excludes):
                dirs.append(p)
            continue
        low = p.lower()
        if low in seen:
            collisions.append(p)
            continue
        seen[low] = p
        if is_excluded(p, p.rsplit("/", 1)[-1], False, excludes):
            continue
        files.append({"path": p, "size": e.get("size") or 0, "sha1": e.get("sha1")})
    files.sort(key=lambda f: f["path"].lower())
    dirs.sort()
    return files, dirs, collisions


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
    """candidate destination folders = repo dirs ∪ local site dirs (pruned)."""
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
    """score every known folder against the dropped file's context; top 3."""
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
#  UI — PURE TKINTER, same WWZ design tokens as NeoSync
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
    """flat button: no relief, steady 1px ring, hover tint; calm while disabled."""

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

    def itemconfig(self, *a, **k):
        return self.configure(*a, **k)


class ScrollFrame(tk.Frame):
    """dark canvas scroll area; wheel() is called by the app-wide wheel router."""

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
        self._win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
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
    """6px slim bar."""

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

        self.title("%s (lite) — GitHub drop & sync" % APP_NAME)
        self.geometry("1180x730")
        self.minsize(980, 620)
        self.configure(bg=self.T["bg"])
        self._setup_ttk_style()

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
        self._search_job = None
        self._row_cap = 400
        self._row_chunk = 40
        self._chunk_gap = 20
        self._rows_shown = 0
        self._render_gen = 0
        self._entries_view = []
        self._last_counts = {"all": 0, "new": 0, "chg": 0, "same": 0, "del": 0}
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
        self._refresh_header()

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(80, self._poll)
        self._arm_auto()

        self._log("GitSync (lite) %s ready — pure tkinter, config: %s"
                  % (APP_VER, CONFIG_PATH), "dim")
        if not self.cfg.get("token") or not self.cfg.get("repo"):
            self._log("No token / repo yet — click ⚙ Settings to add them.", "warn")
        if self.cfg.get("auto_scan_on_open") and self.cfg.get("local_folder") \
                and self.cfg.get("token") and self.cfg.get("repo"):
            self.after(700, self.start_scan)

    # style -------------------------------------------------------------------
    def _setup_ttk_style(self):
        T = self.T
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Vertical.TScrollbar", background=T["scrl_thumb"],
                        troughcolor=T["scrl_track"], bordercolor=T["scrl_track"],
                        arrowcolor=T["scrl_thumb_hover"], arrowsize=10,
                        gripcount=0, relief="flat")
        style.map("Vertical.TScrollbar",
                  background=[("active", T["scrl_thumb_hover"]),
                              ("!active", T["scrl_thumb"])])

    def _pick_fonts(self):
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
        tk.Label(brand, text="GitSync", font=self.f_h1, bg=T["bg2"],
                 fg=T["accent"]).grid(row=0, column=0, sticky="w")
        tk.Label(brand, text="drop · guess · push · lite", font=self.f_label,
                 bg=T["bg2"], fg=T["fg3"]).grid(row=1, column=0, sticky="w")

        site = tk.Frame(hdr, bg=T["bg2"])
        site.grid(row=0, column=1, sticky="w", padx=(10, 6))
        self.site_name_lbl = tk.Label(site, text="not connected", font=self.f_body,
                                      bg=T["bg2"], fg=T["fg1"])
        self.site_name_lbl.grid(row=0, column=0, sticky="w")
        self.site_url_lbl = tk.Label(site, text="—", font=self.f_small,
                                     bg=T["bg2"], fg=T["info"], cursor="hand2")
        self.site_url_lbl.grid(row=1, column=0, sticky="w")
        self.site_url_lbl.bind("<Button-1>", lambda e: self._open_site())

        tiles = tk.Frame(hdr, bg=T["bg2"])
        tiles.grid(row=0, column=3, sticky="e", padx=(6, 10))
        self.tile_vals = {}
        for i, (key, cap) in enumerate([("files", "FILES"), ("branch", "BRANCH"),
                                        ("head", "COMMIT"), ("sync", "LAST SYNC")]):
            tile = tk.Frame(tiles, bg=T["bg"], padx=10, pady=6,
                            highlightbackground=T["border1"], highlightthickness=1)
            tile.grid(row=0, column=i, padx=4)
            v = tk.Label(tile, text="—", font=self.f_num, bg=T["bg"], fg=T["fg1"])
            v.grid(row=0, column=0, sticky="e")
            tk.Label(tile, text=cap, font=self.f_label, bg=T["bg"],
                     fg=T["fg3"]).grid(row=1, column=0, sticky="e")
            self.tile_vals[key] = v
        self.tile_vals["sync"].configure(fg=T["fg2"], font=self.f_small)
        self.tile_vals["branch"].configure(font=self.f_small)
        self.tile_vals["head"].configure(font=self.f_mono_sm)

        self.gear_btn = Btn(hdr, text="⚙", font=self.f_h1, bg=T["bg4"],
                            hover=T["bg5"], fg=T["fg2"], ring=T["border2"],
                            disabled_fg=T["fg3"], padx=8, ipady=2,
                            command=self.open_settings)
        self.gear_btn.grid(row=0, column=4, sticky="e", padx=(2, 16))

    def _repo(self):
        return norm_repo(self.cfg.get("repo") or "")

    def _refresh_header(self):
        repo = self._repo()
        self.site_name_lbl.configure(text=repo or "not connected")
        self.site_url_lbl.configure(
            text=("github.com/%s" % repo) if repo else "—")

    def _open_site(self):
        if self._repo():
            webbrowser.open("https://github.com/%s" % self._repo())

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
                                     font=self.f_mono_sm, bg=T["bg3"], fg=T["fg1"],
                                     insertbackground=T["fg1"], relief="flat", bd=0,
                                     highlightthickness=1,
                                     highlightbackground=T["border1"],
                                     highlightcolor=T["accent_border"])
        self.folder_entry.grid(row=0, column=0, sticky="ew", padx=(14, 6),
                               pady=11, ipady=6)
        self.folder_entry.bind("<Return>", lambda e: self.start_scan())

        self.browse_btn = Btn(tb, text="Browse…", font=self.f_btn, bg=T["bg4"],
                              hover=T["bg5"], fg=T["fg1"], ring=T["comp"],
                              command=self.pick_folder)
        self.browse_btn.grid(row=0, column=1, padx=(0, 10), pady=11)

        self.scan_btn = Btn(tb, text="Scan & Plan", font=self.f_btn, bg=T["bg4"],
                            hover=T["accent_dim"], fg=T["accent"],
                            ring=T["accent_border"], ring_hover=T["accent_border"],
                            command=self.start_scan)
        self.scan_btn.grid(row=0, column=2, padx=(0, 6), pady=11)

        self.sync_btn = Btn(tb, text="Sync Now ⬆", font=self.f_btn, bg=T["accent"],
                            hover=T["accent2"], fg="#1a1a1a", command=self.start_sync)
        self.sync_btn.grid(row=0, column=3, padx=(0, 6), pady=11)

        self.verify_btn = Btn(tb, text="Verify", font=self.f_btn, bg=T["bg4"],
                              hover=T["bg5"], fg=T["fg2"], ring=T["border2"],
                              command=self.start_verify)
        self.verify_btn.grid(row=0, column=4, padx=(0, 6), pady=11)

        self.auto_btn = Btn(tb, text="Auto ⏱ off", font=self.f_btn, bg=T["bg4"],
                            hover=T["bg5"], fg=T["fg2"], ring=T["border2"],
                            command=self._auto_menu)
        self.auto_btn.grid(row=0, column=5, padx=(0, 6), pady=11)

        self.link_btn = Btn(tb, text="", font=self.f_btn, bg=T["bg4"],
                            hover=T["accent_dim"], fg=T["info"],
                            ring=T["border2"], ring_hover=T["accent_border"],
                            command=self._link_menu)
        self.link_btn.grid(row=0, column=6, padx=(0, 14), pady=11)
        self._update_link_btn()

    def pick_folder(self):
        d = filedialog.askdirectory(parent=self, title="Choose local site folder")
        if d:
            self.folder_var.set(d)
            self.cfg["local_folder"] = d
            save_config(self.cfg)

    # link style + clipboard ------------------------------------------------------
    def _update_link_btn(self):
        k = self.cfg.get("link_kind") or "raw"
        self.link_btn.configure(text="Link: %s ▾" % LINK_LABELS.get(k, "Raw"))

    def _link_menu(self):
        m = tk.Menu(self, tearoff=0, font=self.tk_small, bg=self.T["bg3"],
                    fg=self.T["fg1"], bd=0, activebackground=self.T["bg5"],
                    activeforeground=self.T["accent"])
        cur = self.cfg.get("link_kind") or "raw"
        for kind in ("raw", "pages", "blob", "jsdelivr"):
            mark = "✓ " if kind == cur else "    "
            m.add_command(label="%s%s" % (mark, LINK_LABELS[kind]),
                          command=lambda k=kind: self._set_link_kind(k))
        try:
            m.tk_popup(self.link_btn.winfo_rootx(),
                       self.link_btn.winfo_rooty() + self.link_btn.winfo_height())
        finally:
            m.grab_release()

    def _set_link_kind(self, kind):
        self.cfg["link_kind"] = kind
        save_config(self.cfg)
        self._update_link_btn()
        self._toast("link style: %s" % LINK_LABELS[kind], "info")

    def _repo_ok(self):
        if REPO_RE.match(self._repo()):
            return True
        self._toast("set owner/repo in ⚙ Settings first", "warn")
        return False

    def _clip(self, text):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.update()               # flush so the clipboard survives

    def _copy_link(self, rel, act=None):
        if not self._repo_ok():
            return
        url = build_link(self.cfg, rel)
        self._clip(url)
        self._log("⧉ copied %s" % url, "dim")
        if act == "new":
            self._toast("link copied — not on GitHub yet, push first", "warn")
        else:
            self._toast("link copied — %s" % rel, "ok")

    def _copy_all_links(self):
        if not self._repo_ok():
            return
        es = sorted((e for e in self._visible() if e["action"] != "del"),
                    key=lambda e: e["path"].lower())
        if not es:
            self._toast("no files in this view", "warn")
            return
        self._clip("\n".join(build_link(self.cfg, e["path"]) for e in es))
        self._toast("%d links copied" % len(es), "ok")

    # content: tab strip + two pages --------------------------------------------
    def _build_content(self):
        T = self.T
        wrap = tk.Frame(self, bg=T["bg"])
        wrap.grid(row=2, column=0, sticky="nsew", padx=12, pady=(4, 4))
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_rowconfigure(1, weight=1)
        self.content_wrap = wrap

        strip = tk.Frame(wrap, bg=T["bg2"])
        strip.grid(row=0, column=0, sticky="ew")
        self.tab_btns = {}
        for tid, label in (("plan", "Sync Plan"), ("activity", "Activity")):
            b = Btn(strip, text=label, font=self.f_btn, bg=T["bg2"], hover=T["bg2"],
                    fg=T["fg2"], padx=18, ipady=5,
                    command=lambda t=tid: self._show_tab(t))
            b.pack(side="left", padx=(2, 0), pady=3)
            self.tab_btns[tid] = b

        holder = tk.Frame(wrap, bg=T["bg"])
        holder.grid(row=1, column=0, sticky="nsew")
        holder.grid_columnconfigure(0, weight=1)
        holder.grid_rowconfigure(0, weight=1)
        self._tab_frames = {}
        self._build_plan_tab(holder)
        self._build_activity_tab(holder)
        self._show_tab("plan")

    def _show_tab(self, tid):
        T = self.T
        for t, f in self._tab_frames.items():
            f.grid() if t == tid else f.grid_remove()
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

        strip = tk.Frame(tab, bg=T["accent_dim"], height=44,
                         highlightbackground=T["accent_border"], highlightthickness=1)
        strip.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 6))
        strip.grid_columnconfigure(0, weight=1)
        tk.Label(strip, text="⬇  Drop files anywhere on this window — "
                             "I'll guess the folder, you confirm.",
                 font=self.f_small, bg=T["accent_dim"], fg=T["fg1"],
                 anchor="w").grid(row=0, column=0, sticky="w", padx=(14, 4), pady=9)
        self.choose_btn = Btn(strip, text="Choose files…", font=self.f_btn,
                              bg=T["bg4"], hover=T["bg5"], fg=T["accent"],
                              ring=T["accent_border"], ipady=2,
                              command=self.choose_files)
        self.choose_btn.grid(row=0, column=1, padx=(4, 10), pady=7)
        self.drop_strip = strip

        chips = tk.Frame(tab, bg=T["bg"])
        chips.grid(row=1, column=0, sticky="ew", padx=10, pady=(2, 4))
        chips.grid_columnconfigure(5, weight=1)
        self.chips_frame = chips
        self.chip_btns = {}
        for i, fid in enumerate(["all", "new", "chg", "same", "del"]):
            b = Btn(chips, text=fid.upper(), font=self.f_btn, bg=T["bg3"],
                    hover=T["bg4"], fg=T["fg2"], ring=T["border1"], ipady=2,
                    padx=12, command=lambda f=fid: self._on_filter(f))
            b.grid(row=0, column=i, padx=(0, 5), sticky="w")
            self.chip_btns[fid] = b
        tk.Label(chips, text="search", font=self.f_small, bg=T["bg"],
                 fg=T["fg3"]).grid(row=0, column=6, padx=(0, 6))
        self.search_var = tk.StringVar()
        tk.Entry(chips, textvariable=self.search_var, width=22,
                 font=self.f_mono_sm, bg=T["bg3"], fg=T["fg1"],
                 insertbackground=T["fg1"], relief="flat", bd=0,
                 highlightthickness=1, highlightbackground=T["border1"],
                 highlightcolor=T["accent_border"]
                 ).grid(row=0, column=7, padx=(0, 8), ipady=3)
        self.search_var.trace_add("write", lambda *_: self._search_soon())
        self.copyall_btn = Btn(chips, text="⧉ Copy links", font=self.f_btn,
                               bg=T["bg4"], hover=T["accent_dim"], fg=T["accent"],
                               ring=T["accent_border"], ipady=2,
                               command=self._copy_all_links)
        self.copyall_btn.grid(row=0, column=8)

        self.plan_scroll = ScrollFrame(tab, T["bg"])
        self.plan_scroll.grid(row=2, column=0, sticky="nsew", padx=6, pady=(0, 8))

        self.empty_card = tk.Frame(tab, bg=T["accent_dim"],
                                   highlightbackground=T["accent_border"],
                                   highlightthickness=2)
        self.empty_card.grid(row=2, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.empty_card.grid_columnconfigure(0, weight=1)
        tk.Label(self.empty_card, text="⬇", font=self.f_h1, bg=T["accent_dim"],
                 fg=T["accent"]).grid(row=0, column=0, pady=(70, 6))
        tk.Label(self.empty_card, text="Drop an HTML file here", font=self.f_h1,
                 bg=T["accent_dim"], fg=T["fg1"]).grid(row=1, column=0)
        tk.Label(self.empty_card,
                 text="I read its folder name + <title>, guess the destination,\n"
                      "and offer the top 3 matches. Scan & Plan for a full "
                      "mirror sync.",
                 font=self.f_small, bg=T["accent_dim"], fg=T["fg2"],
                 justify="center").grid(row=2, column=0, pady=(6, 4))
        tk.Label(self.empty_card,
                 text="or press Scan & Plan to compare your local folder with "
                      "the repo — every file gets a ⧉ link button",
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
        Btn(top, text="Clear log", font=self.f_small, bg=T["bg3"], hover=T["bg4"],
            fg=T["fg3"], ipady=2, command=self._clear_log).pack(side="right")

        wrap = tk.Frame(tab, bg=T["bg2"], highlightbackground=T["border1"],
                        highlightthickness=1)
        wrap.grid(row=1, column=0, sticky="nsew", padx=10, pady=(6, 10))
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_rowconfigure(0, weight=1)
        self.log_box = tk.Text(wrap, font=self.f_mono_sm, wrap="word", bg=T["bg2"],
                               fg=T["fg2"], insertbackground=T["fg1"],
                               relief="flat", bd=0, highlightthickness=0, padx=10,
                               pady=8, selectbackground=T["bg5"], state="disabled")
        self.log_box.grid(row=0, column=0, sticky="nsew")
        vsb = ttk.Scrollbar(wrap, orient="vertical", command=self.log_box.yview)
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
        self.status_lbl.grid(row=0, column=0, sticky="ew", padx=(16, 8), pady=10)
        self.prog = ProgressCanvas(ft, T, width=250, height=6)
        self.prog.grid(row=0, column=1, padx=8, pady=20)
        self.prog.set(0)
        self.prog_lbl = tk.Label(ft, text="", width=16, font=self.f_mono_sm,
                                 bg=T["bg2"], fg=T["fg3"], anchor="w")
        self.prog_lbl.grid(row=0, column=2, padx=(0, 6))
        self.cancel_btn = Btn(ft, text="✕ Cancel", font=self.f_btn, bg=T["err_dim"],
                              hover=blend(T["err"], T["bg"], 0.22), fg=T["err"],
                              ring=T["err"], ipady=2, command=self._do_cancel)

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

    def _search_soon(self):
        if self._search_job:
            try:
                self.after_cancel(self._search_job)
            except Exception:
                pass
        self._search_job = self.after(250, self.render_plan)

    def _visible(self):
        q = self.search_var.get().strip().lower()
        return [e for e in self.plan
                if (self.filter == "all" or e["action"] == self.filter)
                and (not q or q in e["path"].lower())]

    def render_plan(self):
        T = self.T
        counts = {"all": len(self.plan), "new": 0, "chg": 0, "same": 0, "del": 0}
        for e in self.plan:
            counts[e["action"]] += 1
        labels = {"all": "ALL", "new": "NEW", "chg": "CHANGED", "same": "SAME",
                  "del": "DELETE"}
        for fid, b in self.chip_btns.items():
            on = (fid == self.filter)
            b.configure(text="%s %d" % (labels[fid], counts[fid]),
                        bg=T["accent_dim"] if on else T["bg3"],
                        highlightbackground=T["accent_border"] if on else T["border1"],
                        fg=T["accent"] if on else T["fg2"])

        entries = self._visible()
        summary = ("Plan: %d new · %d changed · %d identical · %d remote-only"
                   % (counts["new"], counts["chg"], counts["same"], counts["del"]))
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
            tk.Label(self.plan_scroll.inner, text="nothing in this view ✓",
                     font=self.f_small, bg=T["bg"], fg=T["fg3"]
                     ).grid(sticky="w", padx=12, pady=10)
            self._set_status(summary, "dim")
        else:
            self._entries_view = entries
            self._rows_shown = 0
            self._last_counts = counts
            self._set_status(summary + " — rendering…", "dim")
            self.after(1, lambda g=self._render_gen: self._render_rows(g))

    def _render_rows(self, gen):
        if gen != self._render_gen or not self._entries_view:
            return
        T = self.T
        entries = self._entries_view
        end = min(self._rows_shown + self._row_chunk, len(entries), self._row_cap)
        badge = {"new": ("NEW", T["ok"], T["ok_dim"]),
                 "chg": ("CHG", T["accent"], T["accent_dim"]),
                 "del": ("DEL", T["err"], T["err_dim"]),
                 "same": ("SAME", T["fg3"], T["bg3"])}
        stat = {"new": ("→ push", "ok"), "chg": ("↑ replace", "warn"),
                "del": ("✕ delete", "err"), "same": ("✓ identical", "dim")}
        for e in entries[self._rows_shown:end]:
            self._plan_row(e, badge, stat)
        self._rows_shown = end
        if end < len(entries):
            if end >= self._row_cap:
                tk.Label(self.plan_scroll.inner,
                         text="… and %d more — use the filter chips / search "
                              "(⧉ Copy links still copies all of them)"
                              % (len(entries) - end),
                         font=self.f_small, bg=T["bg"], fg=T["fg3"]
                         ).grid(sticky="w", padx=12, pady=8)
            else:
                self.after(self._chunk_gap, lambda g=gen: self._render_rows(g))
                return
        c = self._last_counts
        self._set_status("Plan: %d new · %d changed · %d identical · %d remote-only"
                         % (c["new"], c["chg"], c["same"], c["del"]), "dim")

    def _plan_row(self, e, badge, stat):
        T = self.T
        act = e["action"]
        txt, kc, kb = badge[act]
        bg = T["err_dim"] if act == "del" else (T["bg2"] if act != "same" else T["bg"])
        row = tk.Frame(self.plan_scroll.inner, bg=bg,
                       highlightbackground=T["border1"], highlightthickness=1)
        row.grid(sticky="ew", padx=6, pady=2)
        row.grid_columnconfigure(1, weight=1)
        tk.Label(row, text=txt, bg=kb, fg=kc, font=self.tk_tiny_b, padx=6,
                 pady=2).grid(row=0, column=0, padx=(6, 6), pady=6)
        pl = tk.Label(row, text=e["path"], bg=bg,
                      fg=T["fg2"] if act == "del" else T["fg1"],
                      font=self.tk_strike if act == "del" else self.tk_mono,
                      anchor="w")
        pl.grid(row=0, column=1, sticky="ew")
        if act != "del":
            pl.bind("<Double-Button-1>",
                    lambda ev, p=e["path"], a=act: self._copy_link(p, a))
        tk.Label(row, text=human_size(e["size"]), width=11, bg=bg, fg=T["fg3"],
                 font=self.tk_mono, anchor="e").grid(row=0, column=2, padx=4)
        tk.Label(row, text=rel_ago(e["mtime"]) if e["mtime"] else "—", width=10,
                 bg=bg, fg=T["fg3"], font=self.tk_small, anchor="e"
                 ).grid(row=0, column=3, padx=4)
        s_txt, s_kind = stat[act]
        if act == "del" and e.get("prot"):
            s_txt, s_kind = "🔒 protected", "dim"
        tk.Label(row, text=s_txt, width=13, bg=bg, fg=self._kcolor(s_kind),
                 font=self.tk_small, anchor="w"
                 ).grid(row=0, column=4, padx=(4, 6), sticky="w")
        if act == "del":
            tk.Label(row, text="—", width=8, bg=bg, fg=T["fg3"],
                     font=self.tk_small).grid(row=0, column=5, padx=(0, 8))
        else:
            Btn(row, text="⧉ link", font=self.f_small, bg=T["bg3"],
                hover=T["accent_dim"], fg=T["accent"], ring=T["border2"],
                ring_hover=T["accent_border"], padx=8, ipady=0,
                command=lambda p=e["path"], a=act: self._copy_link(p, a)
                ).grid(row=0, column=5, padx=(0, 8), pady=3)

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

    def _busy_btns(self):
        return (self.scan_btn, self.sync_btn, self.verify_btn, self.auto_btn,
                self.browse_btn, self.choose_btn, self.gear_btn)

    def busy_begin(self, label="working"):
        self.busy = True
        self.cancel_event.clear()
        for b in self._busy_btns():
            try:
                b.configure(state="disabled")
            except Exception:
                pass
        self.cancel_btn.grid(row=0, column=3, padx=(2, 14))
        self._prog(0, 0, "")
        self._set_status(label + "…", "warn")

    def busy_end(self):
        self.busy = False
        for b in self._busy_btns():
            try:
                b.configure(state="normal")
            except Exception:
                pass
        self.cancel_btn.grid_forget()

    def _do_cancel(self):
        self.cancel_event.set()
        self._set_status("cancelling — finishing in-flight requests…", "warn")

    # auto-sync timer ---------------------------------------------------------
    def _update_auto_btn(self):
        T = self.T
        secs = int(self.cfg.get("auto_sync_secs") or 0)
        if secs > 0:
            self.auto_btn.configure(
                text="Auto ⏱ %s" % _secs_choice(secs).replace("Every ", ""),
                bg=T["accent_dim"], fg=T["accent"],
                highlightbackground=T["accent_border"])
        else:
            self.auto_btn.configure(text="Auto ⏱ off", bg=T["bg4"], fg=T["fg2"],
                                    highlightbackground=T["border2"])

    def _auto_menu(self):
        m = tk.Menu(self, tearoff=0, font=self.tk_small, bg=self.T["bg3"],
                    fg=self.T["fg1"], bd=0, activebackground=self.T["bg5"],
                    activeforeground=self.T["accent"])
        cur = int(self.cfg.get("auto_sync_secs") or 0)
        for label, secs in AUTO_CHOICES:
            mark = "✓ " if secs == cur else "    "
            m.add_command(label="%s%s" % (mark, label),
                          command=lambda s=secs: self._auto_apply(s))
        try:
            m.tk_popup(self.auto_btn.winfo_rootx(),
                       self.auto_btn.winfo_rooty() + self.auto_btn.winfo_height())
        finally:
            m.grab_release()

    def _auto_apply(self, secs):
        self.cfg["auto_sync_secs"] = int(secs)
        save_config(self.cfg)
        self._arm_auto(announce=True)

    def _arm_auto(self, announce=False):
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
                self._log("auto-sync armed — Scan & Plan + push every %s "
                          "(first run in %ss; one commit per round, only when "
                          "something changed)"
                          % (_secs_choice(secs).replace("Every ", ""), secs), "info")
            if not self._auto_ticker_job:
                self._auto_ticker()
        elif self._auto_ticker_job:
            try:
                self.after_cancel(self._auto_ticker_job)
            except Exception:
                pass
            self._auto_ticker_job = None
        self._update_auto_btn()

    def _auto_ticker(self):
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
            self._log("auto-sync skipped this round — a job is still running", "dim")
        elif not self._configured() or not os.path.isdir(self.cfg["local_folder"]):
            self._log("auto-sync skipped — token / repo / local folder missing", "warn")
        else:
            self.ui_q.put(("log", "auto-sync tick — scanning…", "dim"))
            threading.Thread(target=self._auto_worker, daemon=True).start()
        self._arm_auto()

    def _auto_worker(self):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            plan, local, _n = self._scan_core(cli)
            uploads = [e for e in plan if e["action"] in ("new", "chg")]
            dels = [e for e in plan if e["action"] == "del" and not e.get("prot")]
            n_del = len(dels)
            if not (self.cfg.get("mirror_deletes") and self.cfg.get("auto_sync_deletes")):
                dels = []
            if not uploads and not dels:
                self.ui_q.put(("log", "auto-sync: %d files checked — everything "
                               "matches ✓%s" % (len(local),
                                                " · %d repo-only kept" % n_del
                                                if n_del else ""), "dim"))
                self.ui_q.put(("status", "auto-sync: everything matches ✓", "ok"))
                return
            self._sync_worker(uploads, dels)
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except Exception as e:
            if not isinstance(e, ApiError):
                traceback.print_exc()
            self.ui_q.put(("toast", "auto-sync failed: %s" % friendly(e), "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # header stats ------------------------------------------------------------
    def refresh_stats(self, nfiles=None, head=None):
        T = self.T
        if nfiles is not None:
            self.tile_vals["files"].configure(text=str(nfiles))
        if head:
            self.tile_vals["head"].configure(text=head[:7])
        self.tile_vals["branch"].configure(text=self.cfg.get("branch") or "—")
        self.tile_vals["sync"].configure(
            text=rel_ago(self.cfg.get("last_sync")),
            fg=T["accent"] if self.cfg.get("last_sync") else T["fg2"])
        self._refresh_header()

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
                self._dispatch(self.ui_q.get_nowait())
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
            self.plan, self.local_map, self.remote_map = msg[1], msg[2], msg[3]
            self.remote_ts = time.time()
            self.render_plan()
        elif op == "stats":
            self.refresh_stats(msg[1], msg[2] if len(msg) > 2 else None)
        elif op == "guess":
            GuessDialog(self, msg[1])
        elif op == "open_settings":
            self.open_settings()
        elif op == "test_result":
            d = getattr(self, "settings_dlg", None)
            if d is not None and d.winfo_exists():
                d.apply_test_result(msg[1], msg[2])
        elif op == "sync_done":
            up, dele, ver, fail = msg[1], msg[2], msg[3], msg[4]
            self._toast("push complete — %d pushed, %d deleted%s"
                        % (up, dele, ", %d failed ✕" % fail if fail else " ✓"),
                        "ok" if not fail else "err")
            self._set_status("push complete — %d pushed · %d deleted · %d verified ✓"
                             % (up, dele, ver), "ok" if not fail else "err")

    # drag & drop -------------------------------------------------------------
    def _apply_dnd(self):
        if not HAS_DND:
            self._log("drag & drop unavailable — run  pip install tkinterdnd2  "
                      "to enable it. 'Choose files…' works meanwhile.", "warn")
            return
        try:
            self.drop_target_register(DND_FILES)
            self.dnd_bind("<<Drop>>", self._on_drop)
        except Exception:
            return
        for w in (self.drop_strip, self.empty_card):
            try:
                w.drop_target_register(DND_FILES)
            except Exception:
                pass
        self._log("drag & drop active — drop an HTML file and I'll guess its "
                  "folder (top 3 matches).", "dim")

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
        if any(os.path.isdir(p) for p in paths):
            self._toast("drop files, not folders (for now)", "warn")
        if files:
            threading.Thread(target=self._drop_worker, args=(files,),
                             daemon=True).start()

    def choose_files(self):
        if self.busy:
            return
        fs = filedialog.askopenfilenames(parent=self, title="Choose files to push")
        if fs:
            threading.Thread(target=self._drop_worker, args=(list(fs),),
                             daemon=True).start()

    def open_settings(self):
        d = getattr(self, "settings_dlg", None)
        if d is not None and d.winfo_exists():
            d.lift()
            d.focus_force()
            return
        self.settings_dlg = SettingsDialog(self)

    # shared client/remote helpers (worker-thread context) ----------------------
    def _configured(self):
        return bool((self.cfg.get("token") or "").strip()
                    and REPO_RE.match(self._repo()))

    def _ensure_client(self):
        if not self._configured():
            self.ui_q.put(("toast", "add token + owner/repo first — ⚙ Settings", "warn"))
            self.ui_q.put(("open_settings",))
            raise QuietExit()
        return GitHub(self.cfg["token"], self._repo(), self.cancel_event)

    def _ensure_remote(self, cli, max_age=90.0):
        if self.remote_map is None or (time.time() - self.remote_ts) > max_age:
            self.ui_q.put(("status", "listing repo…", "dim"))
            remote, head, _ = cli.list_files(self.cfg["branch"],
                                             self.cfg.get("repo_subdir"))
            self.remote_map, self.remote_ts = remote, time.time()
            self.ui_q.put(("stats", sum(1 for e in remote.values()
                                        if not e["is_dir"]), head))
            return remote
        return self.remote_map

    def _precheck(self):
        """main-thread guard shared by scan/verify/sync-ish buttons."""
        if self.busy:
            return False
        folder = self.folder_var.get().strip()
        if folder and folder != self.cfg.get("local_folder"):
            self.cfg["local_folder"] = folder
            save_config(self.cfg)
        if not self._configured():
            self._toast("add token + owner/repo first — ⚙ Settings", "warn")
            self.open_settings()
            return False
        if not self.cfg.get("local_folder") or \
                not os.path.isdir(self.cfg["local_folder"]):
            self._toast("choose the local site folder first", "warn")
            return False
        return True

    def _scan_core(self, cli):
        """list repo → hash local (cached) → plan; posts plan + stats to UI."""
        folder = self.cfg["local_folder"]
        self.ui_q.put(("status", "listing %s@%s…" % (cli.repo, self.cfg["branch"]), "dim"))
        remote, head, _ = cli.list_files(self.cfg["branch"], self.cfg.get("repo_subdir"))
        self.remote_map, self.remote_ts = remote, time.time()
        nfiles = sum(1 for e in remote.values() if not e["is_dir"])
        self.ui_q.put(("status", "hashing local files (git sha1)…", "dim"))
        try:
            total = count_files_fast(folder, self.cfg["excludes"])
        except Exception:
            total = 0

        def prog(k):
            if k == 1 or k % 5 == 0:
                self.ui_q.put(("prog", k, total, "hashed"))
        local = scan_folder(folder, self.cfg["excludes"], self.cancel_event, prog,
                            sha_cache=self._sha_cache)
        plan = build_plan(local, remote, self.cfg.get("protected"))
        self.ui_q.put(("plan", plan, local, remote))
        self.ui_q.put(("stats", nfiles, head))
        return plan, local, nfiles

    def _replan(self):
        """refresh the plan from the cached remote listing (post-push)."""
        folder = self.cfg.get("local_folder") or ""
        if self.remote_map is None or not os.path.isdir(folder):
            return
        try:
            if count_files_fast(folder, self.cfg["excludes"]) > 2000:
                self.ui_q.put(("log", "site folder is large — skipped the "
                               "automatic re-scan; press Scan & Plan", "dim"))
                return
            local = scan_folder(folder, self.cfg["excludes"], self.cancel_event,
                                sha_cache=self._sha_cache)
            self.ui_q.put(("plan", build_plan(local, self.remote_map,
                                              self.cfg.get("protected")),
                           local, self.remote_map))
        except Exception:
            pass

    # scan / verify -------------------------------------------------------------
    def start_scan(self, *_):
        if self._precheck():
            threading.Thread(target=self._scan_worker, daemon=True).start()

    def _scan_worker(self):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            plan, local, nfiles = self._scan_core(cli)
            c = {"new": 0, "chg": 0, "same": 0, "del": 0}
            for e in plan:
                c[e["action"]] += 1
            self.ui_q.put(("toast", "plan ready — %d new · %d changed"
                           % (c["new"], c["chg"]), "ok"))
            self.ui_q.put(("log", "scan: %d local vs %d repo files — %d new, %d "
                           "changed, %d identical, %d repo-only"
                           % (len(local), nfiles, c["new"], c["chg"], c["same"],
                              c["del"]), "ok"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except Exception as e:
            if not isinstance(e, ApiError):
                traceback.print_exc()
            self.ui_q.put(("toast", "scan failed: %s" % friendly(e), "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    def start_verify(self):
        if self._precheck():
            threading.Thread(target=self._verify_worker, daemon=True).start()

    def _verify_worker(self):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            plan, _local, _n = self._scan_core(cli)
            c = {"new": 0, "chg": 0, "same": 0, "del": 0}
            for e in plan:
                c[e["action"]] += 1
            ok = (c["new"] == 0 and c["chg"] == 0)
            msg = ("integrity: %d identical ✓ — %d differ, %d missing on GitHub"
                   % (c["same"], c["chg"], c["new"]))
            self.ui_q.put(("toast", msg, "ok" if ok else "warn"))
            self.ui_q.put(("log", msg + ", %d repo-only" % c["del"],
                           "ok" if ok else "warn"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except Exception as e:
            if not isinstance(e, ApiError):
                traceback.print_exc()
            self.ui_q.put(("toast", "verify failed: %s" % friendly(e), "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # rebuild (repo → local pull, Settings ▸ Maintenance) -------------------------
    def start_rebuild(self, parent=None) -> bool:
        """GUI twin of `git pull` into the local folder; ONLY reachable from
        Settings ▸ Maintenance. Never deletes local files, never writes to GitHub."""
        if self.busy:
            self._toast("busy — wait for the current job to finish", "warn")
            return False
        if not self._precheck():
            return False
        msg = ("Rebuild the local folder from GitHub?\n\n"
               "Repo:  %s @ %s%s\nInto:  %s\n\n"
               "• Repo files are downloaded over your local copies\n"
               "• Files already matching are skipped\n"
               "• Local-only files are KEPT — nothing is deleted\n"
               "• Nothing on GitHub is changed\n\nContinue?"
               % (self._repo(), self.cfg["branch"],
                  (" / " + to_posix(self.cfg.get("repo_subdir")))
                  if self.cfg.get("repo_subdir") else "",
                  self.cfg["local_folder"]))
        if not messagebox.askyesno("Rebuild from GitHub", msg, parent=parent or self):
            self._log("rebuild cancelled — nothing was changed", "warn")
            return False
        threading.Thread(target=self._rebuild_worker, daemon=True).start()
        return True

    def _rebuild_task(self, cli, folder, f):
        rel = f["path"]
        local = os.path.join(folder, rel.replace("/", os.sep))
        if os.path.isfile(local) and f.get("sha1"):
            try:
                if git_sha_file(local) == f["sha1"]:
                    return ("current", f)
            except OSError:
                pass
        cli.download(f["sha1"], local)
        return ("ok", f)

    def _rebuild_worker(self):
        self.ui_q.put(("busy", "", True))
        pulled = current = failed = 0
        try:
            cli = self._ensure_client()
            folder = self.cfg["local_folder"]
            self.ui_q.put(("status", "rebuild — listing repo…", "dim"))
            remote, head, _ = cli.list_files(self.cfg["branch"],
                                             self.cfg.get("repo_subdir"))
            self.remote_map, self.remote_ts = remote, time.time()
            files, dirs, collisions = collect_pull_files(remote, self.cfg["excludes"])
            for p in collisions[:5]:
                self.ui_q.put(("log", "rebuild: skipped %s — another path differs "
                               "only by case" % p, "warn"))
            for d in dirs:
                try:
                    os.makedirs(os.path.join(folder, d.replace("/", os.sep)),
                                exist_ok=True)
                except OSError:
                    pass
            total = len(files)
            self.ui_q.put(("log", "rebuild: pulling %d file(s) from %s"
                           % (total, cli.repo), "info"))
            workers = max(1, min(8, int(self.cfg.get("workers") or 4)))
            done = 0
            with ThreadPoolExecutor(max_workers=workers) as ex:
                futs = {ex.submit(self._rebuild_task, cli, folder, f): f
                        for f in files}
                for fut in as_completed(futs):
                    f = futs[fut]
                    try:
                        kind, f2 = fut.result()
                        if kind == "ok":
                            pulled += 1
                            self.ui_q.put(("log", "⬇ pulled %s" % f2["path"], "plain"))
                        else:
                            current += 1
                            self.ui_q.put(("log", "= current (same sha): %s"
                                           % f2["path"], "dim"))
                    except Cancelled:
                        raise
                    except Exception as de:
                        failed += 1
                        self.ui_q.put(("log", "✕ %s — %s" % (f["path"], friendly(de)),
                                       "err"))
                    done += 1
                    self.ui_q.put(("prog", done, total, "pulled"))
                    self.ui_q.put(("status", "rebuilding %d/%d — %s"
                                   % (done, total, f["path"]), "dim"))
            if self.cancel_event.is_set():
                raise Cancelled()
            self._replan()
            self.cfg["last_sync"] = time.time()
            save_config(self.cfg)
            self.ui_q.put(("stats", sum(1 for e in remote.values() if not e["is_dir"]),
                           head))
            self.ui_q.put(("toast", "rebuild complete — %d pulled, %d already "
                           "current%s" % (pulled, current,
                                          ", %d failed ✕" % failed if failed else " ✓"),
                           "ok" if not failed else "err"))
            self.ui_q.put(("log", "rebuild complete — %d pulled, %d current, %d "
                           "failed (local-only files kept)" % (pulled, current, failed),
                           "ok" if not failed else "warn"))
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
            self.ui_q.put(("log", "rebuild cancelled", "warn"))
        except Exception as e:
            if not isinstance(e, ApiError):
                traceback.print_exc()
            self.ui_q.put(("toast", "rebuild failed: %s" % friendly(e), "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # push ------------------------------------------------------------------
    def _commit_msg(self, n, d):
        t = self.cfg.get("commit_msg") or DEFAULT_CONFIG["commit_msg"]
        try:
            return t.format(n=n, d=d, time=datetime.now().strftime("%Y-%m-%d %H:%M"))
        except Exception:
            return "GitSync: %d changed, %d deleted" % (n, d)

    def _do_push(self, cli, items, dels):
        """one commit: items [(rel, abs)] + dels [rel]. Returns
        (pushed, deleted, verified, failed)."""
        cfg = self.cfg
        sub = to_posix(cfg.get("repo_subdir"))
        workers = max(1, min(8, int(cfg.get("workers") or 4)))
        log = lambda t, k="plain": self.ui_q.put(("log", t, k))
        prog = lambda d, t, l="": self.ui_q.put(("prog", d, t, l))
        self.ui_q.put(("status", "pushing %d file(s)%s → %s…"
                       % (len(items), ", %d deletion(s)" % len(dels) if dels else "",
                          cfg["branch"]), "warn"))
        commit, shas, failed = cli.push(cfg["branch"], sub, items, dels,
                                        self._commit_msg(len(items), len(dels)),
                                        workers, log, prog)
        pushed = len(items) - len(failed)
        if commit:
            log("✔ commit %s on %s — %d pushed, %d deleted"
                % (commit[:7], cfg["branch"], pushed, len(dels)), "ok")
        else:
            log("nothing to commit", "warn")
        remote, head, _ = cli.list_files(cfg["branch"], sub)      # fresh listing
        self.remote_map, self.remote_ts = remote, time.time()
        verified = 0
        if commit and cfg.get("auto_verify", True):
            for rel, sha in shas.items():
                r = remote.get(rel)
                if r and r.get("sha1") == sha:
                    verified += 1
                else:
                    log("⚠ sha mismatch after push: %s" % rel, "err")
        if commit:
            cfg["last_sync"] = time.time()
            save_config(cfg)
        self.ui_q.put(("stats", sum(1 for e in remote.values() if not e["is_dir"]),
                       head))
        return pushed, (len(dels) if commit else 0), verified, len(failed)

    def start_sync(self):
        if self.busy:
            return
        if not self.plan:
            self._toast("run Scan & Plan first", "warn")
            return
        uploads = [e for e in self.plan if e["action"] in ("new", "chg")]
        dels = [e for e in self.plan if e["action"] == "del" and not e.get("prot")]
        if not self.cfg.get("mirror_deletes", False):
            dels = []
        if dels:
            preview = "\n".join("   ✕  " + e["path"] for e in dels[:8])
            if len(dels) > 8:
                preview += "\n   … and %d more" % (len(dels) - 8)
            msg = ("Mirror sync will DELETE %d repo file(s) that no longer exist "
                   "locally:\n\n%s\n\nThey are removed in a new commit "
                   "(recoverable from git history). Continue?" % (len(dels), preview))
            if not messagebox.askyesno("Confirm deletions", msg, parent=self):
                self._log("sync aborted — deletions not confirmed", "warn")
                return
        if not uploads and not dels:
            self._toast("everything already matches ✓ — nothing to do", "ok")
            return
        threading.Thread(target=self._sync_worker, args=(uploads, dels),
                         daemon=True).start()

    def _sync_worker(self, uploads, dels):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            folder = self.cfg["local_folder"]
            items = [(e["path"], os.path.join(folder, e["path"].replace("/", os.sep)))
                     for e in uploads]
            res = self._do_push(cli, items, [e["path"] for e in dels])
            self.ui_q.put(("sync_done",) + res)
            self._replan()
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
            self.ui_q.put(("log", "sync cancelled", "warn"))
        except Exception as e:
            if not isinstance(e, ApiError):
                traceback.print_exc()
            msg = friendly(e)
            if isinstance(e, ApiError) and e.status == 422 and "fast" in e.body.lower():
                msg = "the branch moved on GitHub since the scan — Scan & Plan, then retry"
            self.ui_q.put(("toast", "push failed: %s" % msg, "err"))
            self.ui_q.put(("log", "✕ push failed: %s" % msg, "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

    # drop pushes (quick path: ONE commit per drop batch) -------------------------
    def _drop_worker(self, files):
        self.ui_q.put(("busy", "", True))
        try:
            cli = self._ensure_client()
            remote = self._ensure_remote(cli)
            root = self.cfg.get("local_folder") or ""
            try:
                dirs = gather_dirs(root, remote, self.cfg["excludes"])
            except Exception:
                dirs = []
            chosen = {}                                   # dest rel -> local path
            for fp in files:
                if self.cancel_event.is_set():
                    break
                fp = os.path.abspath(fp)
                inside, rel = in_root(root, fp)
                if inside and rel:
                    chosen[rel] = fp
                    continue
                hints = extract_html_hints(fp)
                cands = rank_candidates(fp, dirs, self.cfg.get("learned_routes"), hints)
                payload = {"file": fp, "cands": cands, "dirs": dirs,
                           "event": threading.Event(), "result": None}
                self.ui_q.put(("guess", payload))
                payload["event"].wait(900)
                res = payload.get("result")
                if not res:
                    self.ui_q.put(("log", "skipped %s — no destination chosen"
                                   % os.path.basename(fp), "dim"))
                    continue
                d = res.get("dir") or ""
                dest = (to_posix(d) + "/" + os.path.basename(fp)).lstrip("/") \
                    if d else os.path.basename(fp)
                if res.get("remember"):
                    self.cfg.setdefault("learned_routes", {})[
                        norm_key(os.path.dirname(fp))] = d
                    save_config(self.cfg)
                    self.ui_q.put(("log", "★ remembered: %s → %s"
                                   % (os.path.dirname(fp), d or "(repo root)"), "dim"))
                chosen[dest] = fp
            todo = []
            for rel, fp in chosen.items():
                try:
                    sha = git_sha_file(fp)
                except OSError as e:
                    self.ui_q.put(("log", "✕ can't read %s — %s" % (fp, e), "err"))
                    continue
                r = remote.get(rel)
                if r and not r["is_dir"] and r.get("sha1") == sha:
                    self.ui_q.put(("log", "= identical copy already in repo, "
                                   "skipped: %s" % rel, "dim"))
                    continue
                todo.append((rel, fp))
            if not todo:
                self.ui_q.put(("toast", "✓ nothing to push — already identical", "ok"))
                return
            pushed, _d, verified, failed = self._do_push(cli, todo, [])
            self.ui_q.put(("toast", ("✓ pushed %d file(s), %d verified" % (pushed, verified))
                           if not failed else "pushed %d, %d failed ✕" % (pushed, failed),
                           "ok" if not failed else "err"))
            self._replan()
        except QuietExit:
            pass
        except Cancelled:
            self.ui_q.put(("status", "cancelled", "warn"))
        except Exception as e:
            if not isinstance(e, ApiError):
                traceback.print_exc()
            self.ui_q.put(("toast", "drop failed: %s" % friendly(e), "err"))
        finally:
            self.ui_q.put(("prog", 0, 0, ""))
            self.ui_q.put(("busy", "", False))

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
            tk.Label(head, text="my best guesses — pick one:", font=app.f_label,
                     bg=T["bg"], fg=T["accent"], anchor="w"
                     ).grid(sticky="w", pady=(8, 0))
        else:
            tk.Label(head, text="no confident match — type the destination "
                                "folder below (blank = repo root).",
                     font=app.f_small, bg=T["bg"], fg=T["accent"], anchor="w"
                     ).grid(sticky="w", pady=(8, 0))

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
            tk.Radiobutton(top, text=c["preview"], variable=self.var,
                           value=c["dir"], font=app.f_mono, bg=T["bg2"],
                           fg=T["fg1"], selectcolor=T["bg4"],
                           activebackground=T["bg2"], activeforeground=T["fg1"],
                           highlightthickness=0, bd=0, anchor="w", cursor="hand2",
                           justify="left").grid(sticky="w")
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
        tk.Label(manual, text="or type folder:", font=app.f_small, bg=T["bg"],
                 fg=T["fg3"]).grid(row=0, column=0, padx=(0, 8))
        self.manual_var = tk.StringVar()
        ent = tk.Entry(manual, textvariable=self.manual_var, font=app.f_mono_sm,
                       bg=T["bg3"], fg=T["fg1"], insertbackground=T["fg1"],
                       relief="flat", bd=0, highlightthickness=1,
                       highlightbackground=T["border1"],
                       highlightcolor=T["accent_border"])
        ent.grid(row=0, column=1, sticky="ew", ipady=5)
        if not cands:
            ent.focus_set()

        foot = tk.Frame(self, bg=T["bg"])
        foot.grid(row=4, column=0, sticky="ew", padx=14, pady=12)
        foot.grid_columnconfigure(0, weight=1)
        self.remember_var = tk.BooleanVar(value=bool(cands))
        tk.Checkbutton(foot, text='★ remember "%s" → chosen folder' % parent,
                       variable=self.remember_var, font=app.f_small, bg=T["bg"],
                       fg=T["fg2"], selectcolor=T["bg3"], activebackground=T["bg"],
                       activeforeground=T["fg1"], highlightthickness=0, bd=0,
                       anchor="w", cursor="hand2").grid(row=0, column=0, sticky="w")
        Btn(foot, text="Cancel", font=app.f_btn, bg=T["bg4"], hover=T["bg5"],
            fg=T["fg2"], ring=T["border2"], command=self._cancel
            ).grid(row=0, column=1, padx=6)
        Btn(foot, text="Push ⬆", font=app.f_btn, bg=T["accent"], hover=T["accent2"],
            fg="#1a1a1a", command=self._confirm).grid(row=0, column=2)

    def _confirm(self):
        manual = self.manual_var.get().strip().strip("/")
        d = manual if manual else (self.var.get() or "")
        self.payload["result"] = {"dir": d, "remember": bool(self.remember_var.get())}
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
        self.geometry("720x780")
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
                     ).grid(row=row["n"], column=0, columnspan=3, sticky="w",
                            pady=(16, 4))
            row["n"] += 1

        def lbl(txt):
            tk.Label(b, text=txt, font=app.f_small, bg=T["bg"], fg=T["fg2"],
                     anchor="w").grid(row=row["n"], column=0, sticky="w",
                                      padx=(0, 10), pady=6)

        def note(txt):
            tk.Label(b, text=txt, font=app.f_small, bg=T["bg"], fg=T["fg3"],
                     anchor="w", justify="left"
                     ).grid(row=row["n"], column=1, columnspan=2, sticky="w")
            row["n"] += 1

        def field(label, var, show="", extra=None, hint=None):
            lbl(label)
            e = tk.Entry(b, textvariable=var, show=show, font=app.f_mono_sm,
                         bg=T["bg3"], fg=T["fg1"], insertbackground=T["fg1"],
                         relief="flat", bd=0, highlightthickness=1,
                         highlightbackground=T["border1"],
                         highlightcolor=T["accent_border"])
            e.grid(row=row["n"], column=1, sticky="ew", pady=6, ipady=5)
            if extra is not None:
                extra.grid(row=row["n"], column=2, padx=(8, 0))
            row["n"] += 1
            if hint:
                note(hint)
            return e

        cap("GitHub account & repo")
        self.token_var = tk.StringVar(value=cfg.get("token") or "")
        eye = Btn(b, text="👁", font=app.f_small, bg=T["bg4"], hover=T["bg5"],
                  fg=T["fg2"], padx=8, ipady=3, command=self._toggle_key)
        self.key_ent = field("access token", self.token_var, show="•", extra=eye,
                             hint="fine-grained token with Contents: Read and "
                                  "write on this repo (or classic `repo` scope)")
        self.repo_var = tk.StringVar(value=cfg.get("repo") or "")
        field("repo", self.repo_var, hint="owner/name — a github.com URL works too")
        self.branch_var = tk.StringVar(value=cfg.get("branch") or "main")
        field("branch", self.branch_var, hint="must already exist (a fresh repo "
                                              "needs one commit, e.g. a README)")
        self.sub_var = tk.StringVar(value=cfg.get("repo_subdir") or "")
        field("subfolder in repo", self.sub_var,
              hint="optional, e.g. docs — local folder maps to it (Pages /docs)")

        cap("Local site folder")
        self.folder_var = tk.StringVar(value=cfg.get("local_folder") or "")
        pick = Btn(b, text="…", font=app.f_btn, bg=T["bg4"], hover=T["bg5"],
                   fg=T["fg2"], padx=8, ipady=3, command=self._pick)
        field("folder", self.folder_var, extra=pick)

        cap("Links")
        self.pages_var = tk.StringVar(value=cfg.get("pages_base") or "")
        field("Pages base URL", self.pages_var,
              hint="optional custom domain, e.g. https://example.com — blank = "
                   "<owner>.github.io[/<repo>]")

        cap("Sync behaviour")
        lbl("parallel uploads")
        self.workers_var = tk.IntVar(value=min(8, int(cfg.get("workers") or 4)))
        self.workers_lbl = tk.Label(b, text="%d" % self.workers_var.get(), width=3,
                                    font=app.f_mono_sm, bg=T["bg"], fg=T["fg1"])
        sl = tk.Scale(b, from_=1, to=8, orient="horizontal",
                      variable=self.workers_var, showvalue=False, bg=T["bg"],
                      fg=T["fg1"], troughcolor=T["bg4"], highlightthickness=0,
                      bd=0, relief="flat", activebackground=T["accent"],
                      sliderrelief="raised", borderwidth=0, width=12,
                      font=app.f_small,
                      command=lambda v: self.workers_lbl.configure(
                          text="%d" % int(float(v))))
        sl.grid(row=row["n"], column=1, sticky="ew", pady=6)
        self.workers_lbl.grid(row=row["n"], column=2, padx=(8, 0))
        row["n"] += 1
        note("only binary files need their own upload; text rides inside the "
             "commit. Writes are throttled for GitHub's rate limit.")

        lbl("auto-sync interval")
        self.auto_var = tk.StringVar(
            value=_secs_choice(int(cfg.get("auto_sync_secs") or 0)))
        om = tk.OptionMenu(b, self.auto_var, *[c[0] for c in AUTO_CHOICES])
        om.configure(font=app.f_small, bg=T["bg3"], fg=T["fg1"],
                     activebackground=T["bg5"], activeforeground=T["accent"],
                     bd=0, highlightthickness=1, highlightbackground=T["border1"],
                     highlightcolor=T["accent_border"], cursor="hand2",
                     anchor="w", padx=10)
        om.grid(row=row["n"], column=1, sticky="ew", pady=6, ipady=4)
        try:
            m = om.nametowidget(om["menu"])
            m.configure(font=app.f_small, bg=T["bg3"], fg=T["fg1"], bd=0,
                        activebackground=T["bg5"], activeforeground=T["accent"])
        except Exception:
            pass
        row["n"] += 1
        note("each round = Scan & Plan + ONE commit, only if something changed")

        self.msg_var = tk.StringVar(value=cfg.get("commit_msg") or "")
        field("commit message", self.msg_var,
              hint="placeholders: {n} files pushed · {d} deleted · {time}")

        lbl("exclude patterns")
        self.exc_box = tk.Text(b, height=7, font=app.f_mono_sm, bg=T["bg3"],
                               fg=T["fg1"], insertbackground=T["fg1"],
                               relief="flat", bd=0, highlightthickness=1,
                               highlightbackground=T["border1"],
                               highlightcolor=T["accent_border"], padx=8, pady=6,
                               wrap="none")
        self.exc_box.grid(row=row["n"], column=1, columnspan=2, sticky="ew", pady=6)
        self.exc_box.insert("1.0", "\n".join(cfg.get("excludes") or []))
        row["n"] += 1
        note("one per line —  *.psd  ·  node_modules/  ·  assets/drafts/*")

        self.chk_del = tk.BooleanVar(value=bool(cfg.get("mirror_deletes", False)))
        self.chk_ver = tk.BooleanVar(value=bool(cfg.get("auto_verify", True)))
        self.chk_auto = tk.BooleanVar(value=bool(cfg.get("auto_scan_on_open", True)))
        self.chk_auto_del = tk.BooleanVar(value=bool(cfg.get("auto_sync_deletes", False)))
        for var, txt in (
                (self.chk_del, "mirror deletes — remove repo files that no longer "
                               "exist locally (asked first; README/LICENSE/CNAME/"
                               ".github are protected)"),
                (self.chk_ver, "auto-verify — compare every pushed file's git sha "
                               "with GitHub's tree after the commit"),
                (self.chk_auto, "auto scan on open — build the plan at launch"),
                (self.chk_auto_del, "auto-sync may delete — interval runs may "
                                    "mirror-delete WITHOUT asking (needs "
                                    "'mirror deletes' too)")):
            tk.Checkbutton(b, text=txt, variable=var, font=app.f_small, bg=T["bg"],
                           fg=T["fg2"], selectcolor=T["bg3"],
                           activebackground=T["bg"], activeforeground=T["fg1"],
                           highlightthickness=0, bd=0, anchor="w", cursor="hand2",
                           justify="left"
                           ).grid(row=row["n"], column=0, columnspan=3,
                                  sticky="w", pady=3)
            row["n"] += 1

        cap("Maintenance")
        tk.Label(b, text="Rebuild — download every file from the repo into your "
                         "local folder (like a\npull). Repo files overwrite local "
                         "ones; local-only files are kept and nothing on\nGitHub "
                         "is changed. For when your local copy is lost or out of "
                         "sync.",
                 font=app.f_small, bg=T["bg"], fg=T["fg3"], anchor="w",
                 justify="left").grid(row=row["n"], column=0, columnspan=3,
                                      sticky="w", pady=(0, 6))
        row["n"] += 1
        Btn(b, text="Rebuild from GitHub ⬇", font=app.f_btn, bg=T["err_dim"],
            hover=blend(T["err"], T["bg"], 0.22), fg=T["err"], ring=T["err"],
            ipady=3, command=self._rebuild
            ).grid(row=row["n"], column=0, columnspan=3, sticky="w")
        row["n"] += 1

        cap("Appearance (theme / scrollbar overrides)")
        tk.Label(b, text="WWZ §02 dark tokens + §23 ultra-thin scrollbars are "
                         "built in; overrides apply on next launch.\nEdit %s:\n"
                         "\"theme\": {\"accent\": \"#ff7847\"}   ·   "
                         "\"scrollbar\": {\"width\": 8}\nAlso there: \"protected\" "
                         "(never-delete patterns)." % CONFIG_PATH,
                 font=app.f_small, bg=T["bg"], fg=T["fg3"], anchor="w",
                 justify="left").grid(row=row["n"], column=0, columnspan=3,
                                      sticky="w", pady=(2, 6))
        row["n"] += 1
        self.test_lbl = tk.Label(b, text="", font=app.f_small, bg=T["bg"],
                                 fg=T["fg3"], anchor="w", justify="left",
                                 wraplength=620)
        self.test_lbl.grid(row=row["n"], column=0, columnspan=3, sticky="w")
        row["n"] += 1

        foot = tk.Frame(self, bg=T["bg"])
        foot.grid(row=1, column=0, sticky="ew", padx=16, pady=12)
        foot.grid_columnconfigure(1, weight=1)
        Btn(foot, text="Test connection", font=app.f_btn, bg=T["bg4"],
            hover=T["bg5"], fg=T["fg1"], ring=T["comp"], command=self._test
            ).grid(row=0, column=0, sticky="w")
        Btn(foot, text="Cancel", font=app.f_btn, bg=T["bg4"], hover=T["bg5"],
            fg=T["fg2"], ring=T["border2"], command=self.destroy
            ).grid(row=0, column=2, padx=6)
        Btn(foot, text="Save ✓", font=app.f_btn, bg=T["accent"], hover=T["accent2"],
            fg="#1a1a1a", command=self._save).grid(row=0, column=3)

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
        d = filedialog.askdirectory(parent=self, title="Choose local site folder")
        if d:
            self.folder_var.set(d)

    def _test(self):
        tok = self.token_var.get().strip()
        repo = norm_repo(self.repo_var.get())
        branch = self.branch_var.get().strip() or "main"
        bad = None
        if not tok:
            bad = "✕ the access token box is empty"
        elif not REPO_RE.match(repo):
            bad = ("✕ repo reads as “%s” — it needs owner/name, e.g. "
                   "janedoe/my-site" % (repo or self.repo_var.get().strip() or "(empty)"))
        if bad:
            self.test_lbl.configure(text=bad, fg=self.app.T["err"])
            return
        self.test_lbl.configure(text="testing…", fg=self.app.T["fg3"])

        def run():
            try:
                c = GitHub(tok, repo)
                j = c.repo_info()
                perm = j.get("permissions")
                push = ("push ✓" if perm.get("push") else "push ✕ (token can't write)") \
                    if isinstance(perm, dict) else "push: unknown"
                try:
                    sha, _t = c.head(branch)
                    br = "branch %s ✓ @%s" % (branch, sha[:7])
                    kind = "ok"
                except Exception as be:
                    br = "branch %s ✕ — %s" % (branch, friendly(be))
                    kind = "err"
                msg = "%s — %s · %s · %s" % (
                    "✓ " + str(j.get("full_name")),
                    "private" if j.get("private") else "public", push, br)
                self.app.ui_q.put(("test_result", msg, kind))
            except Exception as e:
                self.app.ui_q.put(("test_result", "✕ failed — %s" % friendly(e), "err"))
        threading.Thread(target=run, daemon=True).start()

    def apply_test_result(self, text, kind):
        try:
            self.test_lbl.configure(text=text, fg=self.app.T[kind])
        except Exception:
            pass

    def _rebuild(self):
        self._save(close=False)
        if self.app.start_rebuild(parent=self):
            self.destroy()

    def _save(self, close=True):
        cfg = self.app.cfg
        cfg["token"] = self.token_var.get().strip()
        cfg["repo"] = norm_repo(self.repo_var.get())
        cfg["branch"] = self.branch_var.get().strip() or "main"
        cfg["repo_subdir"] = to_posix(self.sub_var.get())
        cfg["local_folder"] = self.folder_var.get().strip()
        cfg["pages_base"] = self.pages_var.get().strip()
        cfg["commit_msg"] = self.msg_var.get().strip() or DEFAULT_CONFIG["commit_msg"]
        try:
            cfg["workers"] = max(1, min(8, int(self.workers_var.get())))
        except Exception:
            cfg["workers"] = 4
        cfg["excludes"] = [l.strip() for l in
                           self.exc_box.get("1.0", "end").splitlines() if l.strip()]
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
        self.app.remote_map = None            # repo/branch may have changed
        self.app._apply_style()
        self.app.refresh_stats(None, None)
        self.app._arm_auto(announce=close)
        if close:
            self.app._toast("settings saved ✓", "ok")
            self.destroy()


# ═════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═════════════════════════════════════════════════════════════════════════════
def _fatal_dump():
    tb = traceback.format_exc()
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(os.path.join(CONFIG_DIR, "error.log"), "a", encoding="utf-8") as f:
            f.write("[%s] %s\n" % (datetime.now().isoformat(), tb))
    except Exception:
        pass
    try:
        r = tk.Tk()
        r.withdraw()
        messagebox.showerror(APP_NAME, "GitSync (lite) failed to start.\n\n%s\n\n"
                             "Details written to:\n%s"
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
