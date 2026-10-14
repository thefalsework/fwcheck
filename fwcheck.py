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

Below the claim-by-claim findings it emits eight "layers": what happens to a
proof after `lake build` is green, and where "verified" can quietly stop
being true.

  1 rebuild     toolchain, Mathlib pin and its age, toolchain consistency
  2 checkers    which checker tools CI uses (comparator, lean4export,
                landrun, nanoda, lean-action) and whether they are pinned
  3 linkage     record main_results <-> comparator theorem_names <->
                challenge module <-> project declaration, all four corners
  4 statements  static triage of each main result: kind, binders, proof
                leader, references to axioms / opaque / sorry-bodied defs
  5 literature  literature_dependencies and sources as declared
  6 review      named human reviewers, alignment table, review artifacts
  7 freshness   when the record last changed vs. the code and CI
  8 citation    a referee's checklist derived from the above, with a score

Usage:
  fwcheck.py owner/repo [--ref BRANCH] [--json] [--no-scan]
  fwcheck.py --survey repos.txt --out survey.jsonl
  fwcheck.py --summarize survey.jsonl [--csv rows.csv]

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
    big_files: list = field(default_factory=list)  # .lean files skipped for size
    skipped_reason: Optional[str] = None
    workflows: dict = field(default_factory=dict)  # .github/workflows/*.yml -> text
    other_files: list = field(default_factory=list)  # md/txt/yaml/json/tex paths (names only)
    _decls: Optional[dict] = None  # lazily built declaration index


_DECL_START = re.compile(
    r"(?m)^(?P<attrs>\s*(?:@\[[^\]]*\]\s*)?)(?P<mods>(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|unsafe\s+|partial\s+|meta\s+|scoped\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+(?P<name>[\w.'«»]+)")
_END_KW = re.compile(r"(?m)^(?:end|namespace|section|open|variable|import|set_option|universe|#\w+)\b")
_PROOF_LEADER = re.compile(r"^\s*(?:by\s+)?(?P<tac>[\w.?!'∘]+)")


@dataclass
class Decl:
    kind: str
    name: str
    file: str
    header: str      # from the name to `:=` / `where` / `|` (the statement, for theorems)
    body: str        # the rest of the chunk
    has_sorry: bool


def decl_index(scan: "LeanScan") -> dict:
    """name (last component and full) -> [Decl]; built once per scan."""
    if scan._decls is not None:
        return scan._decls
    idx: dict = {}
    for path, s in scan.sources.items():
        starts = list(_DECL_START.finditer(s))
        for i, m in enumerate(starts):
            end = starts[i + 1].start() if i + 1 < len(starts) else len(s)
            chunk = s[m.end():end]
            # stop the chunk at a structural keyword at column 0
            e = _END_KW.search(chunk)
            if e:
                chunk = chunk[:e.start()]
            # split header / body at the first top-level `:=`, `where`, or pattern `|`
            cut = None
            for pat in (r":=", r"\bwhere\b", r"(?m)^\s*\|"):
                mm = re.search(pat, chunk)
                if mm and (cut is None or mm.start() < cut):
                    cut = mm.start()
            header = chunk if cut is None else chunk[:cut]
            body = "" if cut is None else chunk[cut:]
            d = Decl(m.group("kind"), m.group("name"), path, header.strip(), body.strip(),
                     bool(_SORRY.search(body)) or m.group("kind") == "axiom")
            for key in {d.name, d.name.split(".")[-1]}:
                idx.setdefault(key, []).append(d)
    scan._decls = idx
    return idx


_SHA40 = re.compile(r"\b[0-9a-f]{40}\b")
_SHA7 = re.compile(r"\b[0-9a-f]{7,40}\b")
_USES = re.compile(r"uses:\s*['\"]?([\w.-]+/[\w.-]+(?:/[\w./-]+)?)@([\w./-]+)")
CHECKER_TOOLS = ("comparator", "lean4export", "landrun", "nanoda", "lean4checker", "lean4lean")


def ref_class(ref: str) -> str:
    if _SHA40.fullmatch(ref):
        return "sha"
    if re.fullmatch(r"v?\d+(\.\d+)*", ref):
        return "tag"
    if ref in ("main", "master", "latest", "HEAD"):
        return "floating"
    return "branch"


def analyze_workflows(wfs: dict) -> dict:
    """What the CI depends on, and whether it is pinned."""
    actions: dict = {}
    tools: dict = {}
    for path, text in wfs.items():
        for m in _USES.finditer(text):
            name, ref = m.group(1), m.group(2)
            if name.startswith("./"):
                continue
            actions.setdefault(name, set()).add(ref_class(ref))
        low = text.lower()
        for t in CHECKER_TOOLS:
            if t not in low:
                continue
            # evidence of pinning anywhere in the file that mentions the tool
            pinned = None
            if _SHA40.search(text):
                pinned = "sha"
            elif re.search(r"(?:--branch|--tag|ref:|checkout)\s+['\"]?v?\d+\.\d+", text):
                pinned = "tag"
            elif re.search(r"(?:checkout|_COMMIT|_REV|_SHA)[:=\s]+['\"]?[0-9a-f]{7,40}\b", text):
                pinned = "sha"
            elif re.search(rf"{t}[^\n]*@(?:v?\d|[0-9a-f]{{7,}})", low):
                pinned = "tag"
            elif re.search(r"@main\b|@master\b|--branch\s+main|git clone\s+https?://\S+/" + t + r"(?:\.git)?\s*$", low, re.M):
                pinned = "unpinned"
            cur = tools.get(t)
            if cur is None or (cur == "unknown" and pinned) or (cur == "unpinned" and pinned in ("sha", "tag")):
                tools[t] = pinned or "unknown"
    lean_action = {k: sorted(v) for k, v in actions.items() if "lean-action" in k}
    floating = sorted(k for k, v in actions.items() if "floating" in v or "branch" in v)
    return {
        "workflow_files": sorted(wfs),
        "actions_used": {k: sorted(v) for k, v in sorted(actions.items())},
        "actions_floating": floating,
        "lean_action": lean_action,
        "checker_tools": tools,
        "has_independent_check": any(t in tools for t in ("comparator", "nanoda", "lean4checker", "lean4lean", "lean4export")),
    }


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
            if rel.startswith(".github/workflows/") and rel.endswith((".yml", ".yaml")) and m.size < 256 * 1024:
                scan.workflows[rel] = tf.extractfile(m).read().decode("utf-8", "replace")
                continue
            if rel.endswith((".md", ".txt", ".yaml", ".yml", ".tex", ".rst", ".csv")):
                scan.other_files.append(rel)
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
            if m.size > 64 * 1024 * 1024:
                scan.big_files.append(rel)
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
    layers: dict = field(default_factory=dict)
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
        if scan.big_files:
            rep.add("scan", UNVERIFIABLE, "Lean sources", f"{len(scan.big_files)} .lean file(s) over 64 MB skipped: " + ", ".join(scan.big_files[:3]))
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
                # the named file usually imports or re-exports it; note, don't accuse
                named_exists = f.lstrip("./") in scan.sources
                rep.add("main_result", INFO if named_exists else STALE, f"{decl} in {f}",
                        "declared in " + ", ".join(sorted({w for _, w in elsewhere}))
                        + (", not literally in the named file" if named_exists else "; the named file does not exist"))
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

    try:
        rep.layers = build_layers(gh, rep, doc, scan, configs, challenge_files, ref, workflows)
    except Exception as e:  # layers are additive; never lose the base report
        rep.layers = {"error": f"{type(e).__name__}: {e}"}
    rep.api_calls = gh.calls
    return rep


# ----------------------------------------------------------------------------
# Layers: what happens to a proof after `lake build` is green
# ----------------------------------------------------------------------------

_dep_cache: dict = {}
_MODEL_NAME = re.compile(r"gpt|claude|codex|gemini|o[1-9]\b|llm|agent|astra|copilot|aristotle|deepseek|grok|model|bot\b|ai\b", re.I)
_REVIEW_ARTIFACT = re.compile(r"(^|/)[^/]*(review|audit|alignment|side[-_]by[-_]side|fidelity|verification|certif|correspondence|statement[-_]check)[^/]*\.(md|txt|yaml|yml|tex|rst|csv)$", re.I)


def dep_commit(gh: GitHub, url: str, rev: str) -> dict:
    """Date and lean-toolchain of a dependency revision; cached across repos."""
    key = (url, rev)
    if key in _dep_cache:
        return _dep_cache[key]
    m = re.search(r"github\.com[/:]([\w.-]+/[\w.-]+?)(?:\.git)?/?$", url or "")
    out: dict = {"repo": m.group(1) if m else None, "date": None, "toolchain": None}
    if out["repo"] and rev:
        c = gh.get(f"/repos/{out['repo']}/commits/{rev}")
        if c:
            out["date"] = ((c.get("commit") or {}).get("committer") or {}).get("date")
            tc = gh.file(out["repo"], "lean-toolchain", rev)
            out["toolchain"] = tc.strip() if tc else None
    _dep_cache[key] = out
    return out


def _tc_match(a: str, b: str):
    if a == b:
        return True
    va = re.search(r"v(\d+)\.(\d+)", a)
    vb = re.search(r"v(\d+)\.(\d+)", b)
    if va and vb and va.groups() == vb.groups():
        return "patch"
    return False


def _days(a: Optional[str], b: Optional[str]) -> Optional[int]:
    da, db = parse_iso(a or ""), parse_iso(b or "")
    return (da - db).days if da and db else None


def _stmt_triage(scan: LeanScan, decl_name: str, preferred: Optional[str], suspects: dict) -> Optional[dict]:
    idx = decl_index(scan)
    cands = idx.get(decl_name) or idx.get(decl_name.split(".")[-1]) or []
    cands = [d for d in cands if path_class(d.file) == "code"] or cands
    if preferred:
        pf = preferred.lstrip("./")
        cands = sorted(cands, key=lambda d: d.file != pf)
    if not cands:
        return None
    d = cands[0]
    header = d.header
    body = d.body.lstrip(":= ").strip()
    leader = _PROOF_LEADER.match(body)
    tac = leader.group("tac") if leader else None
    one_liner = "\n" not in body.strip() and len(body) < 80
    def _refs(text: str) -> dict:
        words = set(re.findall(r"[\w.']+", text))
        out = {k: sorted(w for w in words if w in names or w.split(".")[-1] in names) for k, names in suspects.items()}
        return {k: v for k, v in out.items() if v}
    refs = _refs(header)
    prefs = _refs(d.body)
    return {
        "declaration": d.name,
        "file": d.file,
        "kind": d.kind,
        "statement_chars": len(header),
        "binders": len(re.findall(r"[\(\{\[⦃]\s*[^\)\}\]⦄]*?:", header)),
        "arrows": header.count("→") + header.count("->") + header.count("↔"),
        "proof_leader": tac,
        "proof_one_liner": one_liner,
        "proof_sorry": bool(_SORRY.search(d.body)),
        "proof_native_decide": bool(_NATIVE.search(d.body)),
        "statement_references": refs,  # names in the statement that are axioms / opaque / sorry-bodied defs
        "proof_references": prefs,     # same, in the proof term (direct use only; transitive use needs the kernel)
        "flags": [f for f, on in (
            ("not-a-theorem", d.kind not in ("theorem", "lemma")),
            ("trivial-proof", one_liner and tac in ("rfl", "trivial", "decide", "simp", "norm_num")),
            ("native_decide", bool(_NATIVE.search(d.body))),
            ("sorry-in-proof", bool(_SORRY.search(d.body))),
            ("statement-uses-axiom", "axiom" in refs),
            ("statement-uses-opaque", "opaque" in refs),
            ("statement-uses-sorry-def", "sorry_def" in refs),
            ("proof-uses-axiom", "axiom" in prefs),
            ("proof-uses-sorry-def", "sorry_def" in prefs),
            ("closed-statement", not re.search(r"[\(\{\[⦃]\s*[^\)\}\]⦄]*?:", header) and "→" not in header and "∀" not in header),
        ) if on],
    }


def build_layers(gh: GitHub, rep: Report, doc: dict, scan: Optional[LeanScan], configs: dict,
                 challenge_files: set, ref: str, workflows: list) -> dict:
    status = doc.get("status") if isinstance(doc.get("status"), dict) else {}
    main_results = [m for m in (status.get("main_results") or []) if isinstance(m, dict)] if isinstance(status.get("main_results"), list) else []
    L: dict = {}

    # without a source scan (thin wrapper, oversize tarball) fetch the few
    # files these layers need directly
    toolchains = dict(scan.toolchains) if scan else {}
    manifests = dict(scan.manifests) if scan else {}
    wf_texts = dict(scan.workflows) if scan else {}
    if not scan or (not wf_texts and workflows):
        if not toolchains:
            t = gh.file(rep.repo, "lean-toolchain", ref)
            if t:
                toolchains["lean-toolchain"] = t.strip()
        if not manifests:
            t = gh.file(rep.repo, "lake-manifest.json", ref)
            if t:
                try:
                    manifests["lake-manifest.json"] = json.loads(t)
                except Exception:
                    pass
        for w in workflows:
            p = w.get("path") or ""
            if p and p not in wf_texts:
                t = gh.file(rep.repo, p, ref)
                if t:
                    wf_texts[p] = t

    # 1. rebuildability -----------------------------------------------------
    tc = None
    tc_path = None
    if toolchains:
        tc_path, tc = sorted(toolchains.items(), key=lambda kv: kv[0].count("/"))[0]
    deps = []
    mathlib = None
    if manifests:
        for p, m in sorted(manifests.items(), key=lambda kv: kv[0].count("/")):
            if not m:
                continue
            for pk in m.get("packages", []):
                if pk.get("type") == "path":
                    continue
                d = {"name": pk.get("name"), "url": pk.get("url"), "rev": (pk.get("rev") or "")[:40],
                     "inputRev": pk.get("inputRev"), "inherited": pk.get("inherited")}
                deps.append(d)
            break  # root manifest only
    for d in deps:
        if d["name"] == "mathlib" and d["rev"]:
            info = dep_commit(gh, d["url"], d["rev"])
            mathlib = {"rev": d["rev"][:10], "inputRev": d["inputRev"], "date": info["date"],
                       "age_days": _days(datetime.now(timezone.utc).isoformat(), info["date"]),
                       "toolchain": info["toolchain"]}
    # the manifest pins every rev; inputRev only says what `lake update` would chase
    branch_req = [d["name"] for d in deps if d.get("inputRev") in ("main", "master")]
    L["rebuild"] = {
        "toolchain": tc,
        "toolchain_file": tc_path,
        "manifest": bool(deps) or any(manifests.values()),
        "dependencies": len(deps),
        "dependencies_requested_at_branch": branch_req,
        "mathlib": mathlib,
        # True: identical; "patch": same minor version (builds from source, no cache); False: different
        "toolchain_matches_mathlib": _tc_match(tc, mathlib["toolchain"]) if (tc and mathlib and mathlib.get("toolchain")) else None,
    }

    # 2. checker supply chain -----------------------------------------------
    L["checkers"] = analyze_workflows(wf_texts)
    L["checkers"]["configs"] = len(configs)
    L["checkers"]["workflows_active"] = len(workflows)

    # 3. record <-> config <-> challenge linkage ----------------------------
    links = []
    if scan:
        idx = decl_index(scan)
        for ccs, cfg in configs.items():
            if not isinstance(cfg, dict):
                links.append({"config": ccs, "ok": False, "reason": "config missing or not JSON"})
                continue
            names = [str(n) for n in (cfg.get("theorem_names") or cfg.get("theorems") or [])]
            mod = cfg.get("challenge_module") or cfg.get("challenge")
            # the configured challenge module, wherever the package root is
            chal_paths: set = set()
            if mod:
                rel = str(mod).replace(".", "/") + ".lean"
                parts = ccs.split("/")[:-1]
                for i in range(len(parts) + 1):
                    cand = "/".join(parts[:i] + [rel]) if i else rel
                    if cand in scan.sources:
                        chal_paths.add(cand)
            if not chal_paths:
                chal_paths = {p for p in challenge_files if p in scan.sources}
            in_chal, in_code, nowhere = [], [], []
            for n in names:
                ds = idx.get(n) or idx.get(n.split(".")[-1]) or []
                files = {d.file for d in ds}
                if files & chal_paths:
                    in_chal.append(n)
                if any(f not in chal_paths for f in files):
                    in_code.append(n)
                if not files:
                    nowhere.append(n)
            claimed = {str(m.get("declaration", "")).strip() for m in main_results if m.get("comparator_config") and str(m.get("comparator_config")).strip().lstrip("./") == ccs}
            lasts = {n.split(".")[-1] for n in names}
            linked = [c for c in claimed if c and (c in names or c.split(".")[-1] in lasts)]
            links.append({
                "config": ccs, "challenge_module": mod, "challenge_file_present": bool(chal_paths),
                "theorem_names": len(names), "in_challenge": len(in_chal), "in_code": len(in_code),
                "not_found": nowhere[:5],
                "record_results_linked": len(linked), "record_results_claiming": len(claimed),
                "ok": bool(names) and len(in_chal) == len(names) and len(in_code) == len(names) and len(linked) == len(claimed),
            })
    L["linkage"] = {"configs": links, "complete": all(l["ok"] for l in links) if links else None}

    # 4. statement triage ---------------------------------------------------
    triage = []
    if scan:
        idx = decl_index(scan)
        suspects = {
            "axiom": {d.name for ds in idx.values() for d in ds if d.kind == "axiom" and d.file not in challenge_files},
            "opaque": {d.name for ds in idx.values() for d in ds if d.kind == "opaque"},
            "sorry_def": {d.name for ds in idx.values() for d in ds if d.kind in ("def", "abbrev", "instance", "structure", "inductive") and d.has_sorry and d.file not in challenge_files},
        }
        suspects = {k: {n for n in v} | {n.split(".")[-1] for n in v} for k, v in suspects.items()}
        for m in main_results:
            decl = str(m.get("declaration", "")).strip()
            if not decl or " " in decl:
                continue
            t = _stmt_triage(scan, decl, m.get("file"), suspects)
            if t:
                triage.append(t)
    L["statements"] = {
        "main_results": len(main_results), "triaged": triage,
        "flags": sorted({f for t in triage for f in t["flags"]}),
    }

    # 5. literature dependencies and sources --------------------------------
    lit = []
    for m in main_results:
        for ld in (m.get("literature_dependencies") or []) if isinstance(m.get("literature_dependencies"), list) else []:
            if isinstance(ld, dict):
                lit.append({"result": str(m.get("declaration", ""))[:80], "statement": str(ld.get("statement", ""))[:300], "source": str(ld.get("source", ""))[:200]})
            else:
                lit.append({"result": str(m.get("declaration", ""))[:80], "statement": str(ld)[:300], "source": ""})
    for ld in (status.get("literature_dependencies") or []) if isinstance(status.get("literature_dependencies"), list) else []:
        if isinstance(ld, dict):
            lit.append({"result": "", "statement": str(ld.get("statement", ""))[:300], "source": str(ld.get("source", ""))[:200]})
    srcs = []
    for s in (doc.get("sources") or []) if isinstance(doc.get("sources"), list) else []:
        if isinstance(s, dict):
            srcs.append({"type": str(s.get("type", ""))[:40], "relationship": str(s.get("relationship", ""))[:40],
                         "author_endorsement": str(s.get("author_endorsement", s.get("author_contacted", "")))[:40],
                         "id": str(s.get("id", ""))[:120]})
    fid = doc.get("fidelity") if isinstance(doc.get("fidelity"), dict) else {}
    div = fid.get("divergences") if fid else None
    L["literature"] = {
        "dependencies": lit, "sources": srcs,
        "divergences_chars": len(str(div)) if div else 0,
        "divergences_declared": bool(div) and str(div).strip().lower() not in ("none", "n/a", "", "[]"),
    }

    # 6. review -------------------------------------------------------------
    rv = doc.get("review") if isinstance(doc.get("review"), dict) else {}
    reviewers = rv.get("reviewers") if isinstance(rv.get("reviewers"), list) else []
    rnames = [str(r.get("name") if isinstance(r, dict) else r) for r in reviewers]
    humans = [n for n in rnames if n and not _MODEL_NAME.search(n) and len(n) < 60
              and not re.fullmatch(r"(none|n/?a|tbd|self|author|automated.*|\{\{.*\}\}|\s*)", n.strip(), re.I)]
    proj = doc.get("project") if isinstance(doc.get("project"), dict) else {}
    authors = []
    for a in (proj.get("authors") or []) if isinstance(proj.get("authors"), list) else []:
        authors.append(str(a.get("name") if isinstance(a, dict) else a).strip().lower())
    for a in (proj.get("responsible_maintainers") or []) if isinstance(proj.get("responsible_maintainers"), list) else []:
        authors.append(str(a.get("name") if isinstance(a, dict) else a).strip().lower())

    def _is_author(n: str) -> bool:
        base = re.sub(r"\s*\(.*\)\s*$", "", n).strip().lower()
        return "(self" in n.lower() or base in authors or any(base and base in a for a in authors)
    independent = [n for n in humans if not _is_author(n)]
    st = (rep.review_status or "").lower()
    align = doc.get("alignment") if isinstance(doc.get("alignment"), dict) else {}
    stmts = align.get("statements") if isinstance(align.get("statements"), list) else []
    artifacts = sorted(p for p in (scan.other_files if scan else []) if _REVIEW_ARTIFACT.search(p))[:10]
    L["review"] = {
        "status": rep.review_status, "reviewers": len(rnames), "human_reviewers": humans[:5],
        "independent_reviewers": independent[:5],  # humans who are not the project's authors/maintainers
        "claims_human": bool(humans) or any(k in st for k in ("peer", "human", "author-verified")),
        "alignment_statements": len(stmts), "artifacts": artifacts,
        "notes_chars": len(str(rv.get("notes") or "")),
    }

    # 7. freshness / retraction ---------------------------------------------
    rec_commits = gh.get(f"/repos/{rep.repo}/commits", {"path": "formalization.yaml", "sha": ref, "per_page": 100}) or []
    rec_date = ((rec_commits[0].get("commit") or {}).get("committer") or {}).get("date") if rec_commits else None
    head = gh.get(f"/repos/{rep.repo}/commits", {"sha": ref, "per_page": 1}) or []
    head_date = ((head[0].get("commit") or {}).get("committer") or {}).get("date") if head else None
    datelike = {}
    for sect in ("status", "review", "project"):
        blk = doc.get(sect) if isinstance(doc.get(sect), dict) else {}
        for k, v in blk.items():
            if re.search(r"date|_at$|verified|checked|updated|deprecated|retract|supersed|errat", str(k), re.I):
                datelike[f"{sect}.{k}"] = str(v)[:40]
    for k in ("deprecated_at", "retracted", "errata", "superseded_by", "last_verified", "verified_at", "updated"):
        if k in doc:
            datelike[k] = str(doc[k])[:40]
    L["freshness"] = {
        "record_last_changed": rec_date, "record_commits": len(rec_commits),
        "head_commit": head_date, "record_lag_days": max(0, _days(head_date, rec_date)) if _days(head_date, rec_date) is not None else None,
        "ci_latest_success": max([m.group(1) for f in rep.findings if f.check == "ci" and f.status == OK
                                  for m in [re.search(r"\((\d{4}-\d{2}-\d{2})", f.evidence)] if m], default=None),
        "record_fields": datelike,
    }

    # 8. citation readiness -------------------------------------------------
    c = rep.counts()
    nonci_bad = [f for f in rep.findings if f.status in (MISMATCH, STALE) and f.check not in ("ci", "ci_age")]
    ci_ok = [f for f in rep.findings if f.check == "ci" and f.status == OK]
    indep_ok = [f for f in ci_ok if re.search(r"comparator|kernel|replay|verif|check|export", f.claim, re.I)]
    ci_bad = [f for f in rep.findings if f.check == "ci" and f.status == STALE]
    sorry_ok = any(f.check == "sorry_count" and f.status == OK and f.claim.startswith("0") for f in rep.findings)
    ax_ok = any(f.check == "axioms" and f.status == OK for f in rep.findings)
    items = {
        "build_pinned": bool(tc) and bool(deps),
        "mathlib_under_6_months": (mathlib["age_days"] is not None and mathlib["age_days"] < 183) if mathlib else None,
        "toolchain_consistent": None if L["rebuild"]["toolchain_matches_mathlib"] is None else L["rebuild"]["toolchain_matches_mathlib"] in (True, "patch"),
        "ci_present": bool(workflows),
        "ci_green": bool(ci_ok) and not ci_bad,
        "independent_check_green": bool(indep_ok),
        "checkers_pinned": (all(v in ("sha", "tag") for v in L["checkers"]["checker_tools"].values()) if L["checkers"]["checker_tools"] else None),
        "record_matches_tree": (not nonci_bad) if scan else None,
        "linkage_complete": L["linkage"]["complete"],
        "no_sorry": sorry_ok if scan else None,
        "standard_axioms_only": ax_ok if scan else None,
        "statements_unflagged": (not L["statements"]["flags"]) if triage else None,
        "literature_deps_declared": bool(lit) or None,
        "divergences_declared": L["literature"]["divergences_declared"] or None,
        "human_review_named": bool(humans),
        "independent_review_named": bool(independent),
        "record_fresh": (L["freshness"]["record_lag_days"] is not None and L["freshness"]["record_lag_days"] <= 30),
    }
    applicable = {k: v for k, v in items.items() if v is not None}
    L["citation"] = {"checklist": items, "score": sum(1 for v in applicable.values() if v), "of": len(applicable)}
    return L


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
    if rep.layers:
        print_layers(rep.layers)


def _yn(v) -> str:
    return "-" if v is None else ("yes" if v is True else ("patch-level" if v == "patch" else "NO"))


def print_layers(L: dict) -> None:
    if "error" in L:
        print(f"  layers: error {L['error']}")
        return
    r, c, k, s, lit, rv, fr, ci = (L[x] for x in ("rebuild", "checkers", "linkage", "statements", "literature", "review", "freshness", "citation"))
    print("  -- layers --")
    ml = r.get("mathlib")
    print(f"  1 rebuild     toolchain {r['toolchain'] or '(none)'}; deps {r['dependencies']}"
          + (f"; mathlib {ml['rev']} ({ml['date'][:10] if ml['date'] else '?'}, {ml['age_days']} days old, its toolchain {ml['toolchain'] or '?'}: match {_yn(r['toolchain_matches_mathlib'])})" if ml else "; no mathlib")
          + (f"; lakefile tracks a branch for: {', '.join(r['dependencies_requested_at_branch'])}" if r["dependencies_requested_at_branch"] else ""))
    tools = ", ".join(f"{t}={p}" for t, p in c["checker_tools"].items()) or "none referenced"
    print(f"  2 checkers    workflows {len(c['workflow_files'])}; checker tools: {tools}"
          + (f"; lean-action {c['lean_action']}" if c.get("lean_action") else "")
          + (f"; floating actions: {', '.join(c['actions_floating'][:4])}" if c.get("actions_floating") else ""))
    if k["configs"]:
        for l in k["configs"]:
            if "reason" in l:
                print(f"  3 linkage     {l['config']}: {l['reason']}")
            else:
                print(f"  3 linkage     {l['config']}: {l['theorem_names']} names; in challenge {l['in_challenge']}, in code {l['in_code']}, "
                      f"record results linked {l['record_results_linked']}/{l['record_results_claiming']}"
                      + (f"; not found: {', '.join(l['not_found'])}" if l["not_found"] else "") + f" -> {'ok' if l['ok'] else 'INCOMPLETE'}")
    else:
        print("  3 linkage     no comparator config")
    for t in s["triaged"]:
        print(f"  4 statement   {t['declaration']} ({t['kind']}, {t['binders']} binders, {t['arrows']} arrows, proof: {t['proof_leader'] or '...'}"
              + (f"; statement refs {t['statement_references']}" if t["statement_references"] else "")
              + (f"; proof refs {t['proof_references']}" if t.get("proof_references") else "")
              + (f"; flags: {', '.join(t['flags'])}" if t["flags"] else "") + ")")
    if not s["triaged"]:
        print(f"  4 statement   {s['main_results']} main results, none locatable for triage")
    print(f"  5 literature  {len(lit['dependencies'])} literature dependencies; {len(lit['sources'])} sources"
          + (f" ({', '.join(sorted({x['author_endorsement'] or '?' for x in lit['sources']}))})" if lit["sources"] else "")
          + f"; divergences {'declared (' + str(lit['divergences_chars']) + ' chars)' if lit['divergences_declared'] else 'none'}")
    print(f"  6 review      status {rv['status'] or '(none)'}; reviewers {rv['reviewers']} (human: {', '.join(rv['human_reviewers']) or 'none'}; "
          f"independent of authors: {', '.join(rv['independent_reviewers']) or 'none'}); "
          f"alignment rows {rv['alignment_statements']}; artifacts: {', '.join(rv['artifacts']) or 'none'}")
    print(f"  7 freshness   record last changed {str(fr['record_last_changed'])[:10]} ({fr['record_commits']} commits); head {str(fr['head_commit'])[:10]}; "
          f"record lags head by {fr['record_lag_days']} days; last CI success {fr['ci_latest_success']}"
          + (f"; fields: {fr['record_fields']}" if fr["record_fields"] else ""))
    bad = [n for n, v in ci["checklist"].items() if v is False]
    print(f"  8 citation    {ci['score']}/{ci['of']}" + (f"; failing: {', '.join(bad)}" if bad else ""))


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
    summarize_layers([r for r in ok_rows if r.get("layers") and "error" not in r["layers"]])


def _hist(vals, edges):
    out = []
    for lo, hi in zip(edges, edges[1:] + [None]):
        n = sum(1 for v in vals if v is not None and v >= lo and (hi is None or v < hi))
        out.append(f"{lo}{'-' + str(hi) if hi else '+'}:{n}")
    return "  ".join(out)


def summarize_layers(rows: list) -> None:
    if not rows:
        return
    from collections import Counter
    n = len(rows)
    print(f"\n== layers ({n} repositories with layer data) ==")
    # 1
    R = [r["layers"]["rebuild"] for r in rows]
    ages = [x["mathlib"]["age_days"] for x in R if x.get("mathlib")]
    print(f"1 rebuild: toolchain file {sum(1 for x in R if x['toolchain'])}; manifest {sum(1 for x in R if x['manifest'])}; "
          f"mathlib dependency {len(ages)}; toolchain vs mathlib's: same {sum(1 for x in R if x['toolchain_matches_mathlib'] is True)}, "
          f"patch-level {sum(1 for x in R if x['toolchain_matches_mathlib'] == 'patch')}, different {sum(1 for x in R if x['toolchain_matches_mathlib'] is False)}")
    print(f"   mathlib pin age (days): {_hist(ages, [0, 30, 90, 183, 365])}; median {sorted(ages)[len(ages)//2] if ages else '-'}")
    tcs = Counter((x["toolchain"] or "").split(":")[-1].split("-")[0] for x in R if x["toolchain"])
    print("   toolchains: " + ", ".join(f"{k} {v}" for k, v in tcs.most_common(8)))
    # 2
    C = [r["layers"]["checkers"] for r in rows]
    tools = Counter()
    pin = Counter()
    for x in C:
        for t, p in x["checker_tools"].items():
            tools[t] += 1
            pin[(t, p)] += 1
    print(f"2 checkers: repos referencing a checker tool in CI {sum(1 for x in C if x['checker_tools'])}; "
          + "; ".join(f"{t} {tools[t]} (sha {pin[(t,'sha')]}, tag {pin[(t,'tag')]}, unpinned {pin[(t,'unpinned')]}, unknown {pin[(t,'unknown')]})" for t in sorted(tools)))
    la = Counter(tuple(sorted(v)) for x in C for k, v in x.get("lean_action", {}).items() for v in [v])
    print(f"   lean-action pinned by: {dict(la)}; repos with floating third-party actions {sum(1 for x in C if x.get('actions_floating'))}")
    # 3
    K = [r["layers"]["linkage"] for r in rows if r["layers"]["linkage"]["configs"]]
    cfgs = [c for x in K for c in x["configs"]]
    print(f"3 linkage: repos with configs {len(K)}; configs {len(cfgs)}; complete {sum(1 for c in cfgs if c.get('ok'))}; "
          f"names missing from challenge {sum(1 for c in cfgs if 'in_challenge' in c and c['in_challenge'] < c['theorem_names'])}; "
          f"names missing from code {sum(1 for c in cfgs if 'in_code' in c and c['in_code'] < c['theorem_names'])}; "
          f"record result not among names {sum(1 for c in cfgs if 'record_results_linked' in c and c['record_results_linked'] < c['record_results_claiming'])}")
    # 4
    S = [r["layers"]["statements"] for r in rows]
    tri = [t for x in S for t in x["triaged"]]
    fl = Counter(f for t in tri for f in t["flags"])
    print(f"4 statements: main results {sum(x['main_results'] for x in S)}; triaged {len(tri)}; flags: " + ", ".join(f"{k} {v}" for k, v in fl.most_common()))
    print(f"   proof leaders: " + ", ".join(f"{k} {v}" for k, v in Counter(t['proof_leader'] for t in tri).most_common(10)))
    print(f"   binders: {_hist([t['binders'] for t in tri], [0, 1, 3, 6, 10])}")
    # 5
    Lt = [r["layers"]["literature"] for r in rows]
    deps = [d for x in Lt for d in x["dependencies"]]
    endo = Counter(s["author_endorsement"] or "(blank)" for x in Lt for s in x["sources"])
    print(f"5 literature: repos declaring literature dependencies {sum(1 for x in Lt if x['dependencies'])}; dependencies {len(deps)}; "
          f"divergences declared {sum(1 for x in Lt if x['divergences_declared'])}")
    print("   author endorsement: " + ", ".join(f"{k} {v}" for k, v in endo.most_common(8)))
    # 6
    Rv = [r["layers"]["review"] for r in rows]
    print(f"6 review: human reviewer named {sum(1 for x in Rv if x['human_reviewers'])}; independent of the authors {sum(1 for x in Rv if x.get('independent_reviewers'))}; "
          f"claims human {sum(1 for x in Rv if x['claims_human'])}; "
          f"alignment table {sum(1 for x in Rv if x['alignment_statements'])}; review artifact file {sum(1 for x in Rv if x['artifacts'])}")
    # 7
    F = [r["layers"]["freshness"] for r in rows]
    lags = [x["record_lag_days"] for x in F]
    print(f"7 freshness: record lags head (days): {_hist(lags, [0, 1, 30, 90, 180])}; record commits=1 {sum(1 for x in F if x['record_commits'] == 1)}; "
          f"records with date/retraction fields {sum(1 for x in F if x['record_fields'])}")
    # 8
    Ci = [r["layers"]["citation"] for r in rows]
    fails = Counter(k for x in Ci for k, v in x["checklist"].items() if v is False)
    print(f"8 citation: score {_hist([round(100 * x['score'] / x['of']) if x['of'] else None for x in Ci], [0, 25, 50, 75, 90])} (percent)")
    print("   most-failed items: " + ", ".join(f"{k} {v}" for k, v in fails.most_common(8)))


def write_csv(path: str, out: str) -> None:
    import csv
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    cols = ["repo", "stars", "pushed_at", "yaml_version", "schema", "review_status", "automation", "verdict",
            "toolchain", "mathlib_rev", "mathlib_age_days", "toolchain_matches_mathlib",
            "workflows", "checker_tools", "independent_check",
            "configs", "linkage_complete",
            "main_results", "statement_flags",
            "literature_deps", "sources", "divergences_declared",
            "review_human", "review_independent", "alignment_rows", "review_artifacts",
            "record_last_changed", "record_lag_days", "ci_latest_success",
            "citation_score", "citation_of", "citation_failing"]
    with open(out, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(cols)
        for r in rows:
            L = r.get("layers") or {}
            if r.get("error") or not L or "error" in L:
                w.writerow([r["repo"], r.get("stars"), r.get("pushed_at"), r.get("yaml_version"), r.get("schema"), r.get("review_status"), r.get("automation"), r.get("verdict")] + [""] * (len(cols) - 8))
                continue
            ml = L["rebuild"].get("mathlib") or {}
            w.writerow([
                r["repo"], r["stars"], r["pushed_at"][:10], r["yaml_version"], r["schema"], r["review_status"], r["automation"], r["verdict"],
                L["rebuild"]["toolchain"], ml.get("rev"), ml.get("age_days"), L["rebuild"]["toolchain_matches_mathlib"],
                len(L["checkers"]["workflow_files"]), ";".join(f"{t}={p}" for t, p in L["checkers"]["checker_tools"].items()), L["checkers"]["has_independent_check"],
                len(L["linkage"]["configs"]), L["linkage"]["complete"],
                L["statements"]["main_results"], ";".join(L["statements"]["flags"]),
                len(L["literature"]["dependencies"]), len(L["literature"]["sources"]), L["literature"]["divergences_declared"],
                ";".join(L["review"]["human_reviewers"]), ";".join(L["review"].get("independent_reviewers", [])), L["review"]["alignment_statements"], len(L["review"]["artifacts"]),
                (L["freshness"]["record_last_changed"] or "")[:10], L["freshness"]["record_lag_days"], L["freshness"]["ci_latest_success"],
                L["citation"]["score"], L["citation"]["of"], ";".join(k for k, v in L["citation"]["checklist"].items() if v is False),
            ])
    print(f"wrote {out}: {len(rows)} rows")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("repo", nargs="?", help="owner/repo")
    ap.add_argument("--ref", help="branch or commit (default: default branch)")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of text")
    ap.add_argument("--no-scan", action="store_true", help="skip the tarball source scan")
    ap.add_argument("--survey", help="file with one owner/repo per line")
    ap.add_argument("--out", help="jsonl output for --survey")
    ap.add_argument("--summarize", help="summarize a survey jsonl")
    ap.add_argument("--csv", help="with --summarize: also write one row per repository to this CSV")
    ap.add_argument("--resume", action="store_true", help="skip repos already in --out")
    args = ap.parse_args()
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

    if args.summarize:
        summarize(args.summarize)
        if args.csv:
            write_csv(args.summarize, args.csv)
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
