#!/usr/bin/env python3
"""fwcheck: does a formalization.yaml say what the repository shows?

Reads a repository's formalization.yaml (Mathlib Initiative schema) and
checks each claim it makes against evidence in the same repository:

  sorry_count            counted in the Lean sources (comments stripped)
  main_results           declaration present in the named file
  comparator_config      config exists and lists the declaration
  axioms                 no custom `axiom` declarations; native_decide noted
  CI                     latest default-branch run per workflow, vs. pushed_at
  pins                   lean-toolchain and Mathlib revision from lake-manifest

It does not check proofs (the kernel does), and it does not judge whether a
Lean statement means what the paper says (a human does). It reports the gap
between what the record claims and what the repository currently shows.

Usage:
  fwcheck.py owner/repo [--ref BRANCH] [--json] [--no-scan]
  fwcheck.py --survey repos.txt --out survey.jsonl
  fwcheck.py --summarize survey.jsonl

Auth: uses `gh auth token` or $GITHUB_TOKEN (needed for rate limits and the
tarball download on larger repos).
"""

from __future__ import annotations

import argparse
import base64
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from typing import Any, Optional

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("fwcheck needs PyYAML: pip install pyyaml")

try:
    import jsonschema
except ImportError:  # pragma: no cover
    jsonschema = None

API = "https://api.github.com"
SCHEMA_BASE = "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MAX_TARBALL_BYTES = 200 * 1024 * 1024

# ----------------------------------------------------------------------------
# GitHub access
# ----------------------------------------------------------------------------


def gh_token() -> Optional[str]:
    tok = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if tok:
        return tok
    try:
        out = subprocess.run(["gh", "auth", "token"], capture_output=True, text=True, timeout=10)
        if out.returncode == 0 and out.stdout.strip():
            return out.stdout.strip()
    except Exception:
        pass
    return None


class GitHub:
    def __init__(self, token: Optional[str]):
        self.token = token
        self.calls = 0

    def _req(self, url: str, accept: str = "application/vnd.github+json") -> urllib.request.Request:
        req = urllib.request.Request(url)
        req.add_header("Accept", accept)
        req.add_header("User-Agent", "fwcheck/0.1")
        if self.token:
            req.add_header("Authorization", f"Bearer {self.token}")
        return req

    def get(self, path: str, params: Optional[dict] = None, raw: bool = False) -> Any:
        url = path if path.startswith("http") else API + path
        if params:
            url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
        for attempt in range(5):
            self.calls += 1
            try:
                with urllib.request.urlopen(self._req(url), timeout=120) as resp:
                    data = resp.read()
                    return data if raw else json.loads(data.decode("utf-8"))
            except urllib.error.HTTPError as e:
                if e.code == 404:
                    return None
                if e.code in (403, 429):
                    remaining = e.headers.get("X-RateLimit-Remaining")
                    reset = e.headers.get("X-RateLimit-Reset")
                    retry_after = e.headers.get("Retry-After")
                    if retry_after:
                        wait = int(retry_after) + 1
                    elif remaining == "0" and reset:
                        wait = max(1, int(reset) - int(time.time()) + 2)
                    else:
                        wait = 30 * (attempt + 1)
                    print(f"  [rate limit] sleeping {wait}s", file=sys.stderr)
                    time.sleep(min(wait, 3600))
                    continue
                if e.code >= 500:
                    time.sleep(5 * (attempt + 1))
                    continue
                raise
            except (urllib.error.URLError, TimeoutError):
                time.sleep(5 * (attempt + 1))
        return None

    def file(self, repo: str, path: str, ref: str) -> Optional[str]:
        j = self.get(f"/repos/{repo}/contents/{urllib.parse.quote(path)}", {"ref": ref})
        if not j or not isinstance(j, dict) or j.get("encoding") != "base64":
            return None
        return base64.b64decode(j["content"]).decode("utf-8", errors="replace")

    def tarball(self, repo: str, ref: str) -> Optional[bytes]:
        data = self.get(f"/repos/{repo}/tarball/{urllib.parse.quote(ref)}", raw=True)
        if data and len(data) > MAX_TARBALL_BYTES:
            return None
        return data


# ----------------------------------------------------------------------------
# Lean source scanning
# ----------------------------------------------------------------------------

_BLOCK = re.compile(r"/-.*?-/", re.S)
_LINE = re.compile(r"--[^\n]*")
_STR = re.compile(r'"(?:[^"\\]|\\.)*"')


def strip_lean(src: str) -> str:
    """Remove block comments (incl. docstrings), line comments, string literals."""
    out, depth, i, n = [], 0, 0, len(src)
    # nested block comments by hand
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        out.append(src[i])
        i += 1
    s = "".join(out)
    s = _STR.sub('""', s)
    s = _LINE.sub("", s)
    return s


_SORRY = re.compile(r"(?<![\w.'])sorry(?![\w'])")
_NATIVE = re.compile(r"(?<![\w.'])native_decide(?![\w'])")
_AXIOM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|scoped\s+)*axiom\s+([\w.'«»]+)", re.M)

# Files that are sorry/axiom by design or outside the formalization proper.
_CHALLENGE_PATH = re.compile(r"(^|/)[^/]*challenge[^/]*\.lean$|(^|/)challenge(s)?/", re.I)
_FIXTURE_PATH = re.compile(r"(^|/)(tests?|fixtures?|controls|expectedfailures|examples?|scripts?|web|site|docs?|blueprint|book|roadmap|future|vendor|archive|legacy[^/]*)/", re.I)


def path_class(p: str) -> str:
    if _CHALLENGE_PATH.search(p):
        return "challenge"
    if _FIXTURE_PATH.search(p):
        return "fixture"
    return "code"
_DECL = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)"


@dataclass
class LeanScan:
    files: int = 0
    sorry_total: int = 0
    sorry_files: dict = field(default_factory=dict)
    native_decide_files: dict = field(default_factory=dict)
    axioms: list = field(default_factory=list)  # (name, file)
    sources: dict = field(default_factory=dict)  # path -> stripped text (for decl lookup)
    toolchains: dict = field(default_factory=dict)  # path -> content
    manifests: dict = field(default_factory=dict)  # path -> parsed json
    challenge_modules: dict = field(default_factory=dict)  # json path -> challenge_module
    skipped_reason: Optional[str] = None


def scan_tarball(data: bytes) -> LeanScan:
    scan = LeanScan()
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
        for m in tf:
            if not m.isfile():
                continue
            parts = m.name.split("/", 1)
            rel = parts[1] if len(parts) > 1 else parts[0]
            if "/.lake/" in "/" + rel or rel.startswith(".lake/"):
                continue
            base = rel.rsplit("/", 1)[-1]
            if base == "lean-toolchain":
                scan.toolchains[rel] = tf.extractfile(m).read().decode("utf-8", "replace").strip()
                continue
            if base == "lake-manifest.json":
                try:
                    scan.manifests[rel] = json.loads(tf.extractfile(m).read().decode("utf-8", "replace"))
                except Exception:
                    scan.manifests[rel] = None
                continue
            if rel.endswith(".json") and m.size < 64 * 1024:
                try:
                    j = json.loads(tf.extractfile(m).read().decode("utf-8", "replace"))
                    if isinstance(j, dict) and j.get("challenge_module"):
                        scan.challenge_modules[rel] = j["challenge_module"]
                except Exception:
                    pass
                continue
            if not rel.endswith(".lean"):
                continue
            if m.size > 8 * 1024 * 1024:
                continue
            src = tf.extractfile(m).read().decode("utf-8", "replace")
            stripped = strip_lean(src)
            scan.files += 1
            scan.sources[rel] = stripped
            k = len(_SORRY.findall(stripped))
            if k:
                scan.sorry_total += k
                scan.sorry_files[rel] = k
            nd = len(_NATIVE.findall(stripped))
            if nd:
                scan.native_decide_files[rel] = nd
            for am in _AXIOM.finditer(stripped):
                scan.axioms.append((am.group(1), rel))
    return scan


def find_decl(scan: LeanScan, name: str, preferred_file: Optional[str]) -> tuple[Optional[str], bool]:
    """Return (file where declared, found_in_preferred)."""
    last = name.split(".")[-1]
    pat = re.compile(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|unsafe\s+|partial\s+|meta\s+|scoped\s+)*"
                     + _DECL + r"\s+(?:[\w.'«»]+\.)?" + re.escape(last) + r"(?![\w'])")
    cands = []
    pf = preferred_file.lstrip("./") if preferred_file else None
    if pf:
        for p in (pf, pf.lstrip("/")):
            if p in scan.sources and pat.search(scan.sources[p]):
                return p, True
    for p, s in scan.sources.items():
        if pat.search(s):
            cands.append(p)
    if not cands:
        return None, False
    # a named root module `X.lean` covers declarations under `X/`
    if pf and pf.endswith(".lean"):
        under = pf[:-5] + "/"
        for p in cands:
            if p.startswith(under):
                return p, True
    # prefer a non-challenge, non-fixture location when reporting
    cands.sort(key=lambda p: (path_class(p) != "code", p))
    return cands[0], False


# ----------------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------------

OK, STALE, MISMATCH, UNVERIFIABLE, MISSING, INFO = "OK", "STALE", "MISMATCH", "UNVERIFIABLE", "MISSING", "INFO"


@dataclass
class Finding:
    check: str
    status: str
    claim: str
    evidence: str


@dataclass
class Report:
    repo: str
    ref: str = ""
    pushed_at: str = ""
    stars: int = 0
    yaml_version: str = ""
    yaml_ok: bool = False
    schema: str = ""
    review_status: str = ""
    automation: str = ""
    role: str = ""
    findings: list = field(default_factory=list)
    api_calls: int = 0
    error: str = ""

    def add(self, check, status, claim, evidence):
        self.findings.append(Finding(check, status, claim, evidence))

    def counts(self) -> dict:
        c = {}
        for f in self.findings:
            c[f.status] = c.get(f.status, 0) + 1
        return c

    def verdict(self) -> str:
        c = self.counts()
        if self.error:
            return f"ERROR: {self.error}"
        bad = c.get(MISMATCH, 0)
        stale = c.get(STALE, 0)
        unv = c.get(UNVERIFIABLE, 0)
        ok = c.get(OK, 0)
        parts = []
        if bad:
            parts.append(f"{bad} contradicted")
        if stale:
            parts.append(f"{stale} stale")
        if unv:
            parts.append(f"{unv} unverifiable")
        parts.append(f"{ok} backed")
        return ", ".join(parts)


def norm_version(v: Any) -> str:
    if v is None:
        return ""
    s = str(v).strip()
    m = re.match(r"v?(\d+\.\d+)", s)
    return f"v{m.group(1)}" if m else s


_schema_cache: dict = {}


def load_schema(version: str) -> Optional[dict]:
    if version in _schema_cache:
        return _schema_cache[version]
    name = {"v0.4": "v0.4.schema.json", "v0.3": "v0.3.schema.json"}.get(version)
    if not name:
        _schema_cache[version] = None
        return None
    try:
        with urllib.request.urlopen(SCHEMA_BASE + name, timeout=60) as r:
            _schema_cache[version] = json.loads(r.read().decode())
    except Exception:
        _schema_cache[version] = None
    return _schema_cache[version]


def parse_iso(s: str) -> Optional[datetime]:
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00"))
    except Exception:
        return None


def check_repo(gh: GitHub, repo: str, ref: Optional[str], do_scan: bool = True) -> Report:
    rep = Report(repo=repo)
    info = gh.get(f"/repos/{repo}")
    if not info:
        rep.error = "repository not found or not accessible"
        return rep
    ref = ref or info.get("default_branch") or "main"
    rep.ref = ref
    rep.pushed_at = info.get("pushed_at", "")
    rep.stars = info.get("stargazers_count", 0)

    # ---- the record -------------------------------------------------------
    text = gh.file(repo, "formalization.yaml", ref)
    if text is None:
        rep.error = "no formalization.yaml at repository root"
        return rep
    try:
        doc = yaml.safe_load(text)
    except Exception as e:
        rep.error = f"formalization.yaml does not parse: {e}"
        return rep
    if not isinstance(doc, dict):
        rep.error = "formalization.yaml is not a mapping"
        return rep
    rep.yaml_ok = True
    rep.yaml_version = norm_version(doc.get("version"))

    schema = load_schema(rep.yaml_version)
    if schema and jsonschema:
        try:
            jsonschema.validate(doc, schema)
            rep.schema = "valid"
            rep.add("schema", OK, f"version {rep.yaml_version}", "validates against the published schema")
        except jsonschema.ValidationError as e:
            rep.schema = "invalid"
            loc = "/".join(str(p) for p in e.absolute_path) or "(root)"
            rep.add("schema", INFO, f"version {rep.yaml_version}", f"schema violation at {loc}: {e.message[:160]}")
    else:
        rep.schema = "unchecked"
        rep.add("schema", UNVERIFIABLE, f"version {rep.yaml_version or '(none)'}",
                "no published schema for this version" if rep.yaml_version else "no version field")

    rv = doc.get("review") or {}
    rep.review_status = str(rv.get("status", "")) if isinstance(rv, dict) else str(rv)
    auto = doc.get("automation") or {}
    methods = auto.get("methods") if isinstance(auto, dict) else None
    if isinstance(methods, list):
        rep.automation = ",".join(sorted({str(m.get("method", "?")) for m in methods if isinstance(m, dict)}))
    elif isinstance(auto, dict) and auto.get("method"):
        rep.automation = str(auto.get("method"))
    repo_block = doc.get("repository") or {}
    rep.role = str(repo_block.get("role", "")) if isinstance(repo_block, dict) else ""

    status = doc.get("status") or {}
    if not isinstance(status, dict):
        status = {}
    claimed_sorry = status.get("sorry_count")
    claimed_axioms = status.get("axioms")
    main_results = status.get("main_results") or []
    if not isinstance(main_results, list):
        main_results = []

    # ---- the code ---------------------------------------------------------
    scan: Optional[LeanScan] = None
    if do_scan and rep.role != "thin-wrapper":
        data = gh.tarball(repo, ref)
        if data is None:
            rep.add("scan", UNVERIFIABLE, "Lean sources", "tarball unavailable or over size limit")
        else:
            try:
                scan = scan_tarball(data)
            except Exception as e:
                rep.add("scan", UNVERIFIABLE, "Lean sources", f"tarball scan failed: {e}")
    elif rep.role == "thin-wrapper":
        rep.add("scan", INFO, "repository.role: thin-wrapper", "no Lean sources expected here; claims refer elsewhere")

    # comparator configs: fetched once; their challenge modules are sorry by design
    configs: dict = {}
    challenge_files: set = set()
    for mr in main_results:
        cc = mr.get("comparator_config") if isinstance(mr, dict) else None
        if not cc or str(cc).strip().lower() in ("n/a", "none", "null", "-", "tbd"):
            continue
        ccs = str(cc).strip().lstrip("./")
        if ccs in configs:
            continue
        cfg_text = gh.file(repo, ccs, ref)
        cfg = None
        if cfg_text is not None:
            try:
                cfg = json.loads(cfg_text)
            except Exception:
                cfg = "not-json"
        configs[ccs] = cfg
        if isinstance(cfg, dict):
            mod = cfg.get("challenge_module") or cfg.get("challenge")
            if mod:
                rel = str(mod).replace(".", "/") + ".lean"
                # module paths are relative to the Lake package root, which may be
                # the repo root, the config's directory, or any ancestor of it
                parts = ccs.split("/")[:-1]
                for i in range(len(parts) + 1):
                    challenge_files.add("/".join(parts[:i] + [rel]) if i else rel)
    # also any file literally named Challenge.lean next to a config or at root
    for ccs in configs:
        parts = ccs.split("/")[:-1]
        for i in range(len(parts) + 1):
            challenge_files.add("/".join(parts[:i] + ["Challenge.lean"]) if i else "Challenge.lean")

    if scan is not None:
        # challenge files: any *Challenge*.lean or Challenge/ dir, and any module
        # named by a comparator-style json found in the tree (sorry by design)
        for p in scan.sources:
            if path_class(p) == "challenge":
                challenge_files.add(p)
        for jp, mod in scan.challenge_modules.items():
            rel = str(mod).replace(".", "/") + ".lean"
            parts = jp.split("/")[:-1]
            for i in range(len(parts) + 1):
                challenge_files.add("/".join(parts[:i] + [rel]) if i else rel)
        fixture_files = {p for p in scan.sources if p not in challenge_files and path_class(p) == "fixture"}
        # sorry_count (+ sorry_in_definitions, which the schema counts separately)
        chal_sorry = {p: k for p, k in scan.sorry_files.items() if p in challenge_files}
        fix_sorry = {p: k for p, k in scan.sorry_files.items() if p in fixture_files}
        counted = {p: k for p, k in scan.sorry_files.items() if p not in challenge_files and p not in fixture_files}
        total = sum(counted.values())
        worst = sorted(counted.items(), key=lambda kv: -kv[1])[:4]
        ev = f"{total} sorry in {len(counted)} of {scan.files} .lean files"
        if worst:
            ev += " (" + ", ".join(f"{p}:{k}" for p, k in worst) + ")"
        if chal_sorry:
            ev += f"; not counted: {sum(chal_sorry.values())} in challenge file(s) " + ", ".join(list(chal_sorry)[:4]) + (", ..." if len(chal_sorry) > 4 else "")
        if fix_sorry:
            ev += f"; not counted: {sum(fix_sorry.values())} in test/doc/script file(s) " + ", ".join(list(fix_sorry)[:4]) + (", ..." if len(fix_sorry) > 4 else "")
        if claimed_sorry is None:
            rep.add("sorry_count", UNVERIFIABLE, "(not stated)", ev)
        else:
            try:
                cs = int(claimed_sorry)
                cd = int(status.get("sorry_in_definitions") or 0)
            except Exception:
                cs, cd = -1, 0
            claim = f"{cs}" + (f" + {cd} in definitions" if cd else "")
            with_chal = total + sum(chal_sorry.values())
            with_all = with_chal + sum(fix_sorry.values())
            if cs + cd == total:
                rep.add("sorry_count", OK, claim, ev)
            elif cs + cd in (with_chal, with_all):
                rep.add("sorry_count", OK, claim, ev + " (claim counts the challenge/test files too)")
            elif cs + cd == 0 and total > 0:
                rep.add("sorry_count", MISMATCH, claim, ev)
            elif cs + cd > total:
                rep.add("sorry_count", STALE, claim, ev + " (fewer than claimed; record not updated?)")
            else:
                rep.add("sorry_count", MISMATCH, claim, ev)

        # axioms: custom axiom declarations and native_decide
        custom = [(n, f) for n, f in scan.axioms if f not in challenge_files and f not in fixture_files]
        aside = [(n, f) for n, f in scan.axioms if f in challenge_files or f in fixture_files]
        nd = scan.native_decide_files
        claimed_set = set(map(str, claimed_axioms)) if isinstance(claimed_axioms, list) else None
        if custom:
            names = ", ".join(f"{n} ({f})" for n, f in custom[:5]) + (", ..." if len(custom) > 5 else "")
            if claimed_set is not None and all(n in claimed_set or n.split(".")[-1] in {c.split(".")[-1] for c in claimed_set} for n, _ in custom):
                rep.add("axioms", OK, ", ".join(sorted(claimed_set)), f"custom axiom declarations are declared in the record: {names}")
            elif claimed_set is None:
                rep.add("axioms", INFO, "(not stated)",
                        f"record does not state axioms; source declares {len(custom)} custom `axiom`: {names}")
            else:
                rep.add("axioms", MISMATCH, ", ".join(sorted(claimed_set)),
                        f"custom `axiom` declarations in source not listed in status.axioms: {names}")
        elif aside:
            rep.add("axioms", INFO, ", ".join(sorted(claimed_set)) if claimed_set else "(not stated)",
                    f"custom `axiom` only in challenge/test files: " + ", ".join(f"{n} ({f})" for n, f in aside[:3]))
        elif claimed_set is not None:
            extra = claimed_set - STANDARD_AXIOMS
            rep.add("axioms", OK, ", ".join(sorted(claimed_set)),
                    "no custom `axiom` declarations in source" + (f"; record also lists {', '.join(sorted(extra))}" if extra else ""))
        else:
            rep.add("axioms", UNVERIFIABLE, "(not stated)", "no custom `axiom` declarations in source")
        if nd:
            files = ", ".join(f"{p}:{k}" for p, k in sorted(nd.items(), key=lambda kv: -kv[1])[:4])
            listed = claimed_set is not None and any("ofReduceBool" in a for a in claimed_set)
            rep.add("native_decide", OK if listed else INFO,
                    "Lean.ofReduceBool listed" if listed else "(ofReduceBool not listed)",
                    f"native_decide used in {len(nd)} files: {files}")

        # main results
        for mr in main_results:
            if not isinstance(mr, dict):
                continue
            decl = str(mr.get("declaration", "")).strip()
            f = mr.get("file")
            f = str(f).strip() if f else None
            if not decl:
                continue
            if " " in decl.strip() and not re.search(r"[/,]| and ", decl):
                rep.add("main_result", UNVERIFIABLE, decl[:60], "declaration field is prose, not a name")
                continue
            # some records list several declarations in one field ("a / b", "a, b")
            decls = [d.strip("` ") for d in re.split(r"\s*[/,]\s*|\s+and\s+", decl) if d.strip("` ")]
            missing, elsewhere, where = [], [], None
            for d in decls:
                w, in_pref = find_decl(scan, d, f)
                if w is None:
                    missing.append(d)
                elif f and not in_pref:
                    elsewhere.append((d, w))
                where = where or w
            if missing:
                rep.add("main_result", MISMATCH, f"{decl} in {f or '?'}",
                        "declaration not found in any .lean file" + (f": {', '.join(missing)}" if len(decls) > 1 else ""))
            elif elsewhere:
                rep.add("main_result", STALE, f"{decl} in {f}",
                        "found in " + ", ".join(sorted({w for _, w in elsewhere})) + ", not in the named file")
            else:
                rep.add("main_result", OK, f"{decl} in {f or where}", f"declared in {where}")
            mrs = mr.get("sorry_count")
            if mrs is not None and where is not None and where not in challenge_files:
                k = len(_SORRY.findall(scan.sources.get(where, "")))
                try:
                    cm = int(mrs)
                except Exception:
                    cm = -1
                if cm == 0 and k > 0:
                    rep.add("main_result_sorry", MISMATCH, f"{decl}: sorry_count 0", f"{k} sorry in {where}")
            cc = mr.get("comparator_config")
            if cc and str(cc).strip().lower() not in ("n/a", "none", "null", "-", "tbd"):
                ccs = str(cc).strip().lstrip("./")
                cfg = configs.get(ccs)
                if cfg is None:
                    rep.add("comparator_config", MISMATCH, f"{decl}: {ccs}", "config file not found")
                elif not isinstance(cfg, dict):
                    rep.add("comparator_config", UNVERIFIABLE, f"{decl}: {ccs}", "config is not JSON")
                else:
                    names = cfg.get("theorem_names") or cfg.get("theorems") or []
                    last = decl.split(".")[-1]
                    if any(str(n) == decl or str(n).split(".")[-1] == last for n in names):
                        rep.add("comparator_config", OK, f"{decl}: {ccs}", f"listed among {len(names)} theorem_names")
                    elif names:
                        # challenge restates the result under another name; the
                        # record does not say which, so the link is not checkable
                        shown = ", ".join(map(str, names[:3])) + (", ..." if len(names) > 3 else "")
                        rep.add("comparator_config", UNVERIFIABLE, f"{decl}: {ccs}",
                                f"config verifies [{shown}], not this name; correspondence not recorded")
                    else:
                        rep.add("comparator_config", MISMATCH, f"{decl}: {ccs}", "config lists no theorem_names")

        # pins
        if scan.toolchains:
            tc = "; ".join(f"{p}: {v}" for p, v in list(scan.toolchains.items())[:2])
            mrev = ""
            for p, m in scan.manifests.items():
                if not m:
                    continue
                for pk in m.get("packages", []):
                    if pk.get("name") == "mathlib":
                        mrev = (pk.get("rev") or "")[:10]
                        break
            rep.add("pins", INFO, "toolchain / mathlib", tc + (f"; mathlib {mrev}" if mrev else "; no mathlib in lake-manifest"))
        else:
            rep.add("pins", INFO, "toolchain", "no lean-toolchain file in the repository")

    # ---- CI ----------------------------------------------------------------
    wfs = gh.get(f"/repos/{repo}/actions/workflows", {"per_page": 30}) or {}
    workflows = [w for w in (wfs.get("workflows") or []) if w.get("state") == "active"]
    pushed = parse_iso(rep.pushed_at) if rep.pushed_at else None
    if not workflows:
        rep.add("ci", UNVERIFIABLE, "build status", "no active GitHub Actions workflows")
    else:
        for w in workflows[:8]:
            runs = gh.get(f"/repos/{repo}/actions/workflows/{w['id']}/runs",
                          {"branch": ref, "per_page": 1, "exclude_pull_requests": "true"}) or {}
            rl = runs.get("workflow_runs") or []
            name = w.get("name") or w.get("path")
            if not rl:
                rep.add("ci", UNVERIFIABLE, f"workflow '{name}'", f"no runs on {ref}")
                continue
            r = rl[0]
            concl = r.get("conclusion") or r.get("status")
            when = (r.get("created_at") or "")[:10]
            sha = (r.get("head_sha") or "")[:7]
            ev = f"latest run on {ref}: {concl} ({when}, {sha})"
            housekeeping = bool(re.search(r"dependabot|pages|release|deploy|update depend|blueprint|docs|doc-gen|website|label", str(name), re.I))
            if concl == "success":
                rep.add("ci", OK, f"workflow '{name}'", ev)
            elif housekeeping and concl in ("failure", "timed_out", "startup_failure"):
                rep.add("ci", INFO, f"workflow '{name}'", ev + " (housekeeping workflow, not a build)")
            elif concl in ("failure", "timed_out", "startup_failure"):
                # how long has it been failing? look back a few runs
                hist = gh.get(f"/repos/{repo}/actions/workflows/{w['id']}/runs",
                              {"branch": ref, "per_page": 30, "exclude_pull_requests": "true"}) or {}
                hr = hist.get("workflow_runs") or []
                streak, last_ok = 0, None
                for h in hr:
                    if h.get("conclusion") == "success":
                        last_ok = (h.get("created_at") or "")[:10]
                        break
                    if h.get("conclusion") in ("failure", "timed_out", "startup_failure"):
                        streak += 1
                ev += f"; {streak} consecutive failures" + (f", last success {last_ok}" if last_ok else ", no success in last 30 runs")
                rep.add("ci", STALE, f"workflow '{name}'", ev)
            else:
                rep.add("ci", INFO, f"workflow '{name}'", ev)
            # record older than the code?
            rd = parse_iso(r.get("created_at") or "")
            if pushed and rd and (pushed - rd).days > 30 and concl == "success":
                rep.add("ci_age", INFO, f"workflow '{name}' last ran {when}",
                        f"repository pushed {rep.pushed_at[:10]}, {(pushed - rd).days} days later (path-filtered, or not triggered?)")

    rep.api_calls = gh.calls
    return rep


# ----------------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------------


def print_report(rep: Report) -> None:
    print(f"{rep.repo} @ {rep.ref}  (pushed {rep.pushed_at[:10]}, {rep.stars} stars)")
    if rep.error:
        print(f"  ERROR  {rep.error}")
        return
    print(f"  formalization.yaml {rep.yaml_version or '(no version)'}: schema {rep.schema}; "
          f"review.status={rep.review_status or '-'}; automation={rep.automation or '-'}"
          + (f"; role={rep.role}" if rep.role else ""))
    width = max((len(f.claim) for f in rep.findings), default=10)
    width = min(width, 64)
    for f in rep.findings:
        claim = f.claim if len(f.claim) <= 64 else f.claim[:61] + "..."
        print(f"  {f.status:<13}{f.check:<18}{claim:<{width}}  {f.evidence}")
    print(f"  verdict: {rep.verdict()}")


def report_json(rep: Report) -> dict:
    d = asdict(rep)
    d["verdict"] = rep.verdict()
    d["counts"] = rep.counts()
    return d


def summarize(path: str) -> None:
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    n = len(rows)
    errs = [r for r in rows if r.get("error")]
    ok_rows = [r for r in rows if not r.get("error")]
    print(f"{n} repositories; {len(errs)} not checkable ({sum(1 for r in errs if 'no formalization.yaml' in r['error'])} without a root yaml)")
    by = {}
    for r in ok_rows:
        for f in r["findings"]:
            key = (f["check"], f["status"])
            by[key] = by.get(key, 0) + 1
    print("\ncheck            OK   STALE  MISMATCH  UNVERIF  INFO")
    for chk in sorted({k[0] for k in by}):
        print(f"{chk:<16}" + "".join(f"{by.get((chk, s), 0):>8}" for s in (OK, STALE, MISMATCH, UNVERIFIABLE, INFO)))
    contradicted = [r for r in ok_rows if r["counts"].get(MISMATCH)]
    stale = [r for r in ok_rows if r["counts"].get(STALE) and not r["counts"].get(MISMATCH)]
    clean = [r for r in ok_rows if not r["counts"].get(MISMATCH) and not r["counts"].get(STALE)]
    print(f"\ncontradicted: {len(contradicted)}   stale only: {len(stale)}   clean: {len(clean)}")
    vers = {}
    for r in ok_rows:
        vers[r["yaml_version"] or "(none)"] = vers.get(r["yaml_version"] or "(none)", 0) + 1
    print("versions: " + ", ".join(f"{k} {v}" for k, v in sorted(vers.items(), key=lambda kv: -kv[1])))
    revs = {}
    for r in ok_rows:
        k = (r["review_status"] or "(none)").strip()
        k = k if len(k) <= 40 else "(free text)"
        revs[k] = revs.get(k, 0) + 1
    print("review.status: " + ", ".join(f"{k} {v}" for k, v in sorted(revs.items(), key=lambda kv: -kv[1])[:12]))
    noci = [r for r in ok_rows if any(f["check"] == "ci" and f["status"] == UNVERIFIABLE and "no active" in f["evidence"] for f in r["findings"])]
    print(f"no CI at all: {len(noci)} of {len(ok_rows)}")
    print("\n-- contradicted (claim vs evidence) --")
    for r in sorted(contradicted, key=lambda r: -r["stars"]):
        bad = [f for f in r["findings"] if f["status"] == MISMATCH]
        print(f"{r['repo']} ({r['stars']}★): " + " | ".join(f"{f['check']}: claimed {f['claim']} / {f['evidence']}" for f in bad[:3]))
    print("\n-- stale --")
    for r in sorted(stale, key=lambda r: -r["stars"]):
        st = [f for f in r["findings"] if f["status"] == STALE]
        print(f"{r['repo']} ({r['stars']}★): " + " | ".join(f"{f['check']}: {f['claim']} / {f['evidence']}" for f in st[:2]))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("repo", nargs="?", help="owner/repo")
    ap.add_argument("--ref", help="branch or commit (default: default branch)")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of text")
    ap.add_argument("--no-scan", action="store_true", help="skip the tarball source scan")
    ap.add_argument("--survey", help="file with one owner/repo per line")
    ap.add_argument("--out", help="jsonl output for --survey")
    ap.add_argument("--summarize", help="summarize a survey jsonl")
    ap.add_argument("--resume", action="store_true", help="skip repos already in --out")
    args = ap.parse_args()
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

    if args.summarize:
        summarize(args.summarize)
        return 0

    gh = GitHub(gh_token())
    if not gh.token:
        print("warning: no GitHub token (gh auth token / GITHUB_TOKEN); rate limits will bite", file=sys.stderr)

    if args.survey:
        if not args.out:
            ap.error("--survey needs --out")
        done = set()
        if args.resume and os.path.exists(args.out):
            for l in open(args.out, encoding="utf-8"):
                if l.strip():
                    done.add(json.loads(l)["repo"])
        repos = [l.strip() for l in open(args.survey, encoding="utf-8-sig") if l.strip() and not l.startswith("#")]
        with open(args.out, "a", encoding="utf-8") as out:
            for i, repo in enumerate(repos, 1):
                if repo in done:
                    continue
                t0 = time.time()
                try:
                    rep = check_repo(gh, repo, None, not args.no_scan)
                except Exception as e:
                    rep = Report(repo=repo, error=f"exception: {e}")
                out.write(json.dumps(report_json(rep)) + "\n")
                out.flush()
                print(f"[{i}/{len(repos)}] {repo}: {rep.verdict()}  ({time.time() - t0:.0f}s, {gh.calls} calls total)", flush=True)
        return 0

    if not args.repo:
        ap.error("repo required")
    rep = check_repo(gh, args.repo, args.ref, not args.no_scan)
    if args.json:
        print(json.dumps(report_json(rep), indent=2))
    else:
        print_report(rep)
    c = rep.counts()
    return 2 if rep.error else (1 if c.get(MISMATCH) or c.get(STALE) else 0)


if __name__ == "__main__":
    sys.exit(main())
