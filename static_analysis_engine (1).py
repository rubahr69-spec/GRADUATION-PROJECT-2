"""
================================================================================
ScoRev  —  Static Analysis Engine  (v2, "golden")
================================================================================
Deterministic static-analysis engine producing three 0–10 quality scores for
Python source — Security, Complexity, Maintainability — plus a rich, line-
anchored list of issues.  The issue list (not the score) is the primary
artifact: scores summarise, issues explain and ground.

Design contract — every numeric constant is classified:
    [GROUNDED]      backed by a literature reference cited inline.
    [JUSTIFIED]     defensible modelling choice, rationale stated inline.
    [CALIBRATABLE]  tuned later against the silver standard; marked
                    `# CALIBRATABLE`.  Initial values are placeholders whose
                    *ordering* is constrained by evidence, not free.

This header doubles as the methodology index; each scoring function restates
its equation, reference, and constant classification so the paper's
Methodology section can be assembled directly from the source.

--------------------------------------------------------------------------------
REFERENCE INDEX
--------------------------------------------------------------------------------
[McCabe76]   McCabe (1976) "A Complexity Measure", IEEE TSE SE-2(4).
[NIST500235] Watson & McCabe (1996) "Structured Testing", NIST SP 500-235.
[CLRS]       Cormen et al. "Introduction to Algorithms", 3rd ed.
[ColemanOman94] Coleman, Ash, Lowther, Oman (1994) "Using Metrics to Evaluate
             Software System Maintainability", IEEE Computer 27(8):44-49.
[OmanHage92] Oman & Hagemeister (1992), Proc. ICSM.
[Halstead77] Halstead (1977) "Elements of Software Science".
[CVSS31]     FIRST.org, Common Vulnerability Scoring System v3.1 Specification.
[OWASP-RR]   OWASP Risk Rating Methodology.
[UMBC-CWE]   Improved CWE Base Scores, CEUR-WS Vol-3052 (severity→{3,5,7,9},
             representative CVSS base per CWE derived from NVD).
[Schneier]   Schneier — weakest-link / defence-in-depth principle.
[Pamula06]   Pamula et al. (2006) weakest-adversary security metric.
[SonarDup]   SonarSource docs — duplicated_lines_density metric.
[Butler09]   Butler, Wermelinger, Yu, Sharp (2009) "Relating Identifier Naming
             Flaws and Code Quality", WCRE.
[Lawrie06]   Lawrie, Morrell, Feild, Binkley (2006) "What's in a Name?", ICPC.
[PEP257]     PEP 257 — Docstring Conventions.
[PEP484]     PEP 484 — Type Hints.
[PEP8]       PEP 8 — Style Guide for Python Code (naming conventions).
[TypeEmp]    Empirical type-hint studies (e.g. FSE 2022, TSE 2021) — static
             types aid comprehension of undocumented code and surface defects.
--------------------------------------------------------------------------------
"""

from __future__ import annotations

import ast
import io
import json
import keyword
import math
import os
import re
import shutil
import subprocess
import tempfile
import threading
import tokenize
from typing import Dict, List, Optional, Set, Tuple


# ──────────────────────────────────────────────────────────────────────────
# Optional backends
# ──────────────────────────────────────────────────────────────────────────
try:
    from radon.complexity import cc_visit
    from radon.metrics import h_visit
    RADON_AVAILABLE = True
except ImportError:
    RADON_AVAILABLE = False

try:
    from cognitive_complexity.api import get_cognitive_complexity  # noqa: F401
    COGNITIVE_AVAILABLE = True
except ImportError:
    COGNITIVE_AVAILABLE = False


# ══════════════════════════════════════════════════════════════════════════
# CONSTANTS BLOCK  —  every tunable weight lives here, classified.
# Calibration later touches THIS BLOCK ONLY.
# ══════════════════════════════════════════════════════════════════════════

# ---- COMPLEXITY: structural (cyclomatic) -----------------------------------
# CC aggregation: worst-function dominance + file average.   [JUSTIFIED]
CC_AGG_MAX_W = 0.60          # CALIBRATABLE  weight on max(CC)
CC_AGG_AVG_W = 0.40          # CALIBRATABLE  weight on mean(CC)  (= 1 - max_w)

# Structural curve anchors: (CC threshold, score at threshold).
# Thresholds 10/20/50 are [GROUNDED] in [NIST500235]/[McCabe76]
# (low/moderate/high/very-high bands).  Score values are [CALIBRATABLE];
# their DESCENDING ORDER is fixed.  Lambdas are DERIVED analytically from the
# anchors (continuity), never hand-picked — see _structural_score.
STRUCT_ANCHORS = (          # (threshold, score)  — CALIBRATABLE score values
    (10.0, 8.0),
    (20.0, 6.0),
    (50.0, 3.0),
)

# ---- COMPLEXITY: computational (Big-O) -------------------------------------
# Lookup score per complexity class.  Hierarchy ORDER is [GROUNDED] in [CLRS]
# (a mathematical fact); the score VALUES are [CALIBRATABLE] but strictly
# monotonic.  Calibrated anchors (per design discussion): O(n)=8 closes the
# "excellent" band, O(n log n)=6 closes "moderate".
BIGO_SCORE: Dict[str, float] = {   # CALIBRATABLE values, monotonic order fixed
    "O(1)":       10.0,
    "O(log n)":    9.0,
    "O(n)":        8.0,
    "O(n log n)":  6.0,
    "O(n×m)":      4.5,   # independent nested loops; between n log n and n²
    "O(n²)":       3.0,
    "O(n³)":       1.0,
    "O(2^n)":      0.1,
    "O(n!)":       0.0,
}

# Dominance: final computational = min(time, space).  [JUSTIFIED] Big-O
# dominance — the worse asymptotic class governs.  No weights.

# ---- COMPLEXITY: dimension fusion ------------------------------------------
# Computational weighted higher than structural by a meaningful margin:
# asymptotic behaviour governs scaling, CC is local structure.   [JUSTIFIED]
COMPLEXITY_COMP_W = 0.75    # CALIBRATABLE
COMPLEXITY_STRUCT_W = 0.25  # CALIBRATABLE  (= 1 - comp_w)

# ---- SECURITY --------------------------------------------------------------
# impact = (CVSS_base/10) * IMPACT_SCALE * confidence_factor.
# IMPACT_SCALE maps the CVSS 0–10 base onto our internal 0–3 impact band so a
# confirmed critical (CVSS≈9.8) yields impact≈2.94, clearing CRIT_THRESHOLD.
IMPACT_SCALE = 3.0                              # [JUSTIFIED]

# Confidence factor — detection certainty (CVSS/OWASP "likelihood" analogue).
SEC_CONFIDENCE = {                              # CALIBRATABLE
    "LOW": 0.4, "MEDIUM": 0.7, "HIGH": 1.0,
}

# Severity-class separation threshold on impact.  >= → critical class.
# 2.0 lets HIGH/HIGH (2.94) and HIGH/MED (~2.1) in, keeps HIGH/LOW (~1.2) out
# so low-confidence findings are never treated as fatal.   [JUSTIFIED]
SEC_CRIT_THRESHOLD = 2.0                         # CALIBRATABLE

# Dual decay.  Two anchors fix the two rates analytically (see _security_score):
#   one confirmed critical (P_crit=3)  -> SEC_CRIT_ANCHOR       (very-bad band)
#   three accumulated mediums (P_rest=4.2) -> SEC_REST_ANCHOR   (mid band)
# Constraint: crit anchor < rest anchor (a fatal flaw outranks medium buildup).
SEC_CRIT_ANCHOR = 2.5    # CALIBRATABLE  score for 1×HIGH/HIGH
SEC_REST_ANCHOR = 5.0    # CALIBRATABLE  score for 3×MEDIUM/MED
SEC_CRIT_REF_PENALTY = 3.0    # [GROUNDED] impact of one HIGH/HIGH (CVSS-scaled)
SEC_REST_REF_PENALTY = 4.2    # [JUSTIFIED] impact of 3×MEDIUM/MED accumulation

# ---- MAINTAINABILITY: layer fusion -----------------------------------------
# MI is the only empirically-regressed component ([ColemanOman94]); R and T are
# complementary layers we add to cover MI's blind spots.  Per user decision the
# grounded component leads by a large margin; added layers weigh less.
#   beta1 (MI) >> beta2 (R) > beta3 (T)            [JUSTIFIED + user decision]
MAINT_BETA_MI = 0.60     # CALIBRATABLE  structural/volumetric (grounded)
MAINT_BETA_R  = 0.25     # CALIBRATABLE  semantic readability (added)
MAINT_BETA_T  = 0.15     # CALIBRATABLE  architectural structure (added)

# Within R (readability).  naming & types have stronger empirical support than
# docs ([Butler09],[TypeEmp] vs [PEP257]); docs deliberately de-emphasised to
# remove the old engine's over-penalisation.  Constraint: w_n, w_t > w_d.
MAINT_R_NAMING_W = 0.40  # CALIBRATABLE
MAINT_R_TYPES_W  = 0.40  # CALIBRATABLE
MAINT_R_DOCS_W   = 0.20  # CALIBRATABLE

# Within T (architecture). duplication is deterministic & strongly cited
# ([SonarDup]); modularity is a lighter structural signal.
MAINT_T_DUP_W = 0.60     # CALIBRATABLE
MAINT_T_MOD_W = 0.40     # CALIBRATABLE

# ---- OVERALL (advisory only; not reported in the paper) --------------------
OVERALL_SEC_W = 0.35     # CALIBRATABLE
OVERALL_CPX_W = 0.35     # CALIBRATABLE
OVERALL_MNT_W = 0.30     # CALIBRATABLE


# ══════════════════════════════════════════════════════════════════════════
# GENERIC HELPERS
# ══════════════════════════════════════════════════════════════════════════

def _safe_log(x: float) -> float:
    return math.log(max(x, 1e-9))


def _safe_log2(x: float) -> float:
    return math.log2(max(x, 2.0))


def _clamp(value: float, lo: float = 0.0, hi: float = 10.0) -> float:
    return round(max(lo, min(value, hi)), 3)


def _exp_decay(penalty: float, decay: float, scale: float = 10.0) -> float:
    return round(scale * math.exp(-decay * max(penalty, 0.0)), 3)


LOOP_TYPES = (ast.For, ast.While, ast.AsyncFor)


def _parse(code: str) -> Optional[ast.Module]:
    try:
        return ast.parse(code)
    except SyntaxError:
        return None


def _unparse(node: ast.AST) -> str:
    return ast.unparse(node) if hasattr(ast, "unparse") else ""


def _build_parent_map(tree: ast.AST) -> Dict[int, ast.AST]:
    parents: Dict[int, ast.AST] = {}
    for parent in ast.walk(tree):
        for child in ast.iter_child_nodes(parent):
            parents[id(child)] = parent
    return parents


def _functions(tree: ast.AST) -> List[ast.AST]:
    return [n for n in ast.walk(tree)
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]


def _classes(tree: ast.AST) -> List[ast.ClassDef]:
    return [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]


def _call_name(call: ast.Call) -> str:
    def _unwrap(node: ast.AST) -> str:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            p = _unwrap(node.value)
            return f"{p}.{node.attr}" if p else node.attr
        return ""
    return _unwrap(call.func)


def _assigned_names(stmt: ast.AST) -> Set[str]:
    names: Set[str] = set()

    def _collect(t: ast.AST) -> None:
        if isinstance(t, ast.Name):
            names.add(t.id)
        elif isinstance(t, (ast.Tuple, ast.List)):
            for e in t.elts:
                _collect(e)

    if isinstance(stmt, ast.Assign):
        for tgt in stmt.targets:
            _collect(tgt)
    elif isinstance(stmt, (ast.AnnAssign, ast.AugAssign)):
        _collect(stmt.target)
    return names


def _direct_child_loops(loop: ast.AST) -> List[ast.AST]:
    found: List[ast.AST] = []

    def _visit(node: ast.AST) -> None:
        if isinstance(node, LOOP_TYPES):
            found.append(node)
            return
        for child in ast.iter_child_nodes(node):
            _visit(child)

    for stmt in getattr(loop, "body", []):
        _visit(stmt)
    return found


def _contains_name(node: ast.AST, names: Set[str]) -> bool:
    return any(isinstance(n, ast.Name) and n.id in names
               for n in ast.walk(node))


def _has_early_exit(node: ast.AST) -> bool:
    return any(isinstance(n, (ast.Break, ast.Return, ast.Continue))
               for n in ast.walk(node))


def _call_count(node: ast.AST) -> int:
    return sum(1 for n in ast.walk(node) if isinstance(n, ast.Call))


# ══════════════════════════════════════════════════════════════════════════
# SECURITY
# ══════════════════════════════════════════════════════════════════════════
#
# Pipeline:
#   1. impact_i = (CVSS_base(CWE)/10) * IMPACT_SCALE * confidence_factor
#        - CVSS base per CWE: representative value, methodology [UMBC-CWE];
#          one-to-many CWE→CVE is a DECLARED LIMITATION (value is typical,
#          not definitive).  CVSS base = intrinsic severity, constant across
#          environments [CVSS31] — we measure intrinsic severity, NOT
#          contextual/production risk (which a static engine cannot observe).
#        - confidence factor = detection certainty (OWASP "likelihood").
#   2. Severity-class separation at SEC_CRIT_THRESHOLD:
#        P_crit = Σ impact for impact >= threshold   (confirmed-fatal class)
#        P_rest = Σ impact for impact <  threshold   (accumulating class)
#   3. score = 10 · exp(-λ1·P_crit) · exp(-λ2·P_rest)
#        λ1 (sharp)  — one confirmed critical drops below the "very bad" band
#                      (weakest-link: a single confirmed flaw makes code unsafe
#                       [Schneier],[Pamula06]).
#        λ2 (gentle) — mediums degrade gradually ([OWASP-RR] accumulation).
#        Both λ DERIVED from anchors, not chosen.
#
# Bandit + AST findings are merged into ONE deduplicated list and the SAME
# formula is applied; the old arbitrary 0.70/0.30 blend is REMOVED. Tool
# reliability is expressed through each finding's own confidence, not a global
# blend weight.
# ──────────────────────────────────────────────────────────────────────────

# Representative CVSS base score per CWE (NVD-typical; methodology [UMBC-CWE]).
# Injection / unsafe-deserialization → critical band (≈9+);
# weak-crypto / hardcoded-secret → high (≈7.5);
# insecure-temp-file → medium; assert-as-guard → low.
CWE_CVSS_BASE: Dict[str, float] = {     # CALIBRATABLE (representative), GROUNDED method
    "CWE-78":  9.8,   # OS command injection
    "CWE-95":  9.3,   # eval injection (code injection)
    "CWE-89":  9.8,   # SQL injection
    "CWE-502": 9.8,   # deserialization of untrusted data
    "CWE-918": 8.6,   # SSRF
    "CWE-327": 7.5,   # broken/weak crypto
    "CWE-326": 7.5,   # inadequate encryption strength
    "CWE-798": 7.5,   # hardcoded credentials
    "CWE-377": 5.5,   # insecure temporary file
    "CWE-676": 3.1,   # use of dangerous primitive (assert as guard)
    "CWE-703": 3.1,   # improper check (fallback)
}
_CWE_CVSS_FALLBACK = 5.0   # [JUSTIFIED] unknown CWE → neutral medium

# Severity → confidence default when a finding lacks an explicit confidence.
_SEC_DEFAULT_CONF = "MEDIUM"


def _cwe_impact(cwe: str, confidence: str) -> float:
    """impact = (CVSS_base/10) * IMPACT_SCALE * confidence_factor.

    Reference: [UMBC-CWE] (CWE→CVSS), [CVSS31] (intrinsic base),
    [OWASP-RR] (impact × likelihood).
    """
    cvss = CWE_CVSS_BASE.get((cwe or "").upper(), _CWE_CVSS_FALLBACK)
    conf_f = SEC_CONFIDENCE.get((confidence or "").upper(), SEC_CONFIDENCE["LOW"])
    return round((cvss / 10.0) * IMPACT_SCALE * conf_f, 4)


# Derive the two decay rates analytically from the anchors (computed once).
#   10·exp(-λ1·P_crit_ref) = crit_anchor  →  λ1 = ln(10/crit_anchor)/P_crit_ref
#   10·exp(-λ2·P_rest_ref) = rest_anchor  →  λ2 = ln(10/rest_anchor)/P_rest_ref
_SEC_LAMBDA1 = _safe_log(10.0 / SEC_CRIT_ANCHOR) / SEC_CRIT_REF_PENALTY
_SEC_LAMBDA2 = _safe_log(10.0 / SEC_REST_ANCHOR) / SEC_REST_REF_PENALTY


def _security_score(impacts: List[float]) -> float:
    """S_security = 10 · exp(-λ1·P_crit) · exp(-λ2·P_rest).

    Severity-class separation [JUSTIFIED] generalises SonarQube's categorical
    gating into a continuous form; weakest-link dominance [Schneier],[Pamula06];
    medium accumulation [OWASP-RR]. λ1,λ2 derived from anchors.
    """
    p_crit = sum(i for i in impacts if i >= SEC_CRIT_THRESHOLD)
    p_rest = sum(i for i in impacts if i < SEC_CRIT_THRESHOLD)
    raw = 10.0 * math.exp(-_SEC_LAMBDA1 * p_crit) * math.exp(-_SEC_LAMBDA2 * p_rest)
    return _clamp(raw)


_SECRET_RE = re.compile(
    r"(?i)(password|passwd|secret|api[_-]?key|token|auth[_-]?key"
    r"|private[_-]?key|access[_-]?key|client[_-]?secret)\s*=\s*['\"][^'\"]{4,}['\"]"
)
_SQL_KW_RE = re.compile(
    r"(?i)\b(SELECT|INSERT|UPDATE|DELETE|DROP|CREATE|ALTER|EXEC)\b"
)


def _ast_security_issues(code: str, tree: ast.AST) -> List[Dict]:
    """AST-based detector (Bandit fallback / supplement). 11 patterns.

    Returns issues WITHOUT scoring; impact is assigned centrally by
    _finalize_security via _cwe_impact so Bandit and AST findings are scored
    identically.  CWE labels corrected vs the previous engine:
    B610 → CWE-918 (SSRF, not 601); eval/exec → CWE-95 (not 78).
    """
    issues: List[Dict] = []

    def _add(sev: str, conf: str, issue_id: str, desc: str,
             line: int, cwe: str, evidence: str = "") -> None:
        issues.append({
            "type": "security", "issue": issue_id, "test_name": issue_id,
            "severity": sev, "confidence": conf,
            "description": desc, "line": line, "cwe": cwe,
            "evidence": evidence, "source": "ast_fallback",
            "recommendation": _SEC_FIX.get(issue_id, ""),
        })

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        name = _call_name(node)
        lineno = getattr(node, "lineno", 0)

        if name in {"subprocess.run", "subprocess.Popen", "subprocess.call",
                    "subprocess.check_output", "subprocess.check_call"}:
            if any(isinstance(k.value, ast.Constant) and k.value.value is True
                   for k in node.keywords if k.arg == "shell"):
                _add("HIGH", "HIGH", "B602_subprocess_shell_true",
                     f"subprocess call with shell=True at line {lineno}. "
                     "Enables shell injection if any argument is user-controlled.",
                     lineno, "CWE-78", _unparse(node)[:120])

        if name in {"os.system", "os.popen"}:
            _add("HIGH", "MEDIUM", "B605_os_command",
                 f"os.{name.split('.')[-1]}() at line {lineno} executes shell "
                 "commands; vulnerable to injection if input is unsanitised.",
                 lineno, "CWE-78", _unparse(node)[:120])

        if name in {"eval", "exec"}:
            if not (node.args and isinstance(node.args[0], ast.Constant)):
                _add("HIGH", "HIGH", "B307_eval_exec",
                     f"{name}() with non-constant argument at line {lineno}. "
                     "Executes arbitrary Python code.",
                     lineno, "CWE-95", _unparse(node)[:120])

        if name in {"pickle.loads", "pickle.load",
                    "cPickle.loads", "cPickle.load"}:
            _add("HIGH", "HIGH", "B301_pickle",
                 f"{name}() at line {lineno}. Deserialising untrusted pickle "
                 "data can execute arbitrary code.",
                 lineno, "CWE-502", _unparse(node)[:120])

        if name in {"yaml.load", "ruamel.yaml.load"}:
            loader_kw = next((k for k in node.keywords if k.arg == "Loader"), None)
            if loader_kw is None:
                _add("HIGH", "MEDIUM", "B506_yaml_load",
                     f"yaml.load() without Loader= at line {lineno}. "
                     "Use yaml.safe_load() or Loader=yaml.SafeLoader.",
                     lineno, "CWE-502", _unparse(node)[:120])
            else:
                lv = _unparse(loader_kw.value)
                if "SafeLoader" not in lv and "safe" not in lv.lower():
                    _add("MEDIUM", "MEDIUM", "B506_yaml_load_unsafe_loader",
                         f"yaml.load() with unsafe Loader at line {lineno}. "
                         "Use yaml.SafeLoader.",
                         lineno, "CWE-502", _unparse(node)[:120])

        if name in {"hashlib.md5", "hashlib.sha1", "MD5.new", "SHA.new"}:
            enc_func = ""
            for fn in _functions(tree):
                if any(id(n) == id(node) for n in ast.walk(fn)):
                    enc_func = getattr(fn, "name", "").lower()
                    break
            _NON_SEC = {"checksum", "digest", "cache", "etag",
                        "fingerprint", "hash_file", "integrity"}
            conf = "LOW" if any(kw in enc_func for kw in _NON_SEC) else "HIGH"
            _add("MEDIUM", conf, "B303_weak_hash",
                 f"Weak hash {name}() at line {lineno}. MD5/SHA1 are "
                 "cryptographically broken for security use; use SHA-256+.",
                 lineno, "CWE-327", _unparse(node)[:120])

        if name == "tempfile.mktemp":
            _add("MEDIUM", "HIGH", "B306_mktemp",
                 f"tempfile.mktemp() at line {lineno} creates a predictable "
                 "filename (TOCTOU race). Use tempfile.mkstemp().",
                 lineno, "CWE-377", _unparse(node)[:120])

        if name in {"requests.get", "requests.post", "requests.put",
                    "requests.delete", "requests.patch",
                    "requests.head", "requests.request"}:
            url_arg = None
            if node.args:
                url_arg = node.args[0]
            else:
                url_kw = next((k for k in node.keywords if k.arg == "url"), None)
                if url_kw:
                    url_arg = url_kw.value
            if url_arg is not None and isinstance(url_arg, ast.Name):
                _add("MEDIUM", "MEDIUM", "B610_ssrf",
                     f"requests.{name.split('.')[-1]}() at line {lineno} called "
                     "with a variable URL. Validate/whitelist URLs (SSRF).",
                     lineno, "CWE-918", _unparse(node)[:120])

    for node in ast.walk(tree):
        lineno = getattr(node, "lineno", 0)
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
            src = _unparse(node)
            if _SQL_KW_RE.search(src) and any(
                isinstance(n, ast.Name) for n in ast.walk(node)
            ):
                _add("HIGH", "HIGH", "B608_sql_injection",
                     f"SQL query built by string concatenation at line {lineno}. "
                     "Use parameterised queries / ORM.",
                     lineno, "CWE-89", src[:120])
        if isinstance(node, ast.JoinedStr):
            src = _unparse(node)
            if _SQL_KW_RE.search(src) and any(
                isinstance(n, ast.FormattedValue) for n in ast.walk(node)
            ):
                _add("HIGH", "HIGH", "B608_sql_injection_fstring",
                     f"SQL query built via f-string at line {lineno}. "
                     "Use parameterised queries.",
                     lineno, "CWE-89", src[:120])

    for m in _SECRET_RE.finditer(code):
        line_no = code[: m.start()].count("\n") + 1
        _add("MEDIUM", "MEDIUM", "B105_hardcoded_secret",
             f"Possible hardcoded credential near line {line_no}. "
             "Store secrets in env vars / vaults.",
             line_no, "CWE-798", m.group()[:60])

    assert_nodes = [n for n in ast.walk(tree) if isinstance(n, ast.Assert)]
    for anode in assert_nodes[:5]:
        lineno = getattr(anode, "lineno", 0)
        _add("LOW", "LOW", "B101_assert_used",
             f"assert statement at line {lineno}. assert is stripped under -O; "
             "do not use as a security guard.",
             lineno, "CWE-676", _unparse(anode)[:120])

    return issues


_SEC_FIX = {
    "B602_subprocess_shell_true": "Pass a list of args and avoid shell=True.",
    "B605_os_command": "Use the subprocess module with an argument list.",
    "B307_eval_exec": "Avoid eval/exec; use ast.literal_eval or explicit dispatch.",
    "B301_pickle": "Use json or a safe serialiser for untrusted data.",
    "B506_yaml_load": "Use yaml.safe_load().",
    "B506_yaml_load_unsafe_loader": "Use Loader=yaml.SafeLoader.",
    "B303_weak_hash": "Use hashlib.sha256 or stronger for security purposes.",
    "B306_mktemp": "Use tempfile.mkstemp() or NamedTemporaryFile.",
    "B610_ssrf": "Validate and whitelist outbound URLs.",
    "B608_sql_injection": "Use parameterised queries / ORM bindings.",
    "B608_sql_injection_fstring": "Use parameterised queries / ORM bindings.",
    "B105_hardcoded_secret": "Move secrets to environment variables or a vault.",
    "B101_assert_used": "Replace asserts used as guards with explicit checks.",
}


def _normalize_bandit_cwe(raw_cwe) -> str:
    """Bandit emits CWE id as int or dict; normalise to 'CWE-NNN'."""
    if isinstance(raw_cwe, dict):
        raw_cwe = raw_cwe.get("id", "")
    s = str(raw_cwe or "").strip()
    if not s:
        return ""
    if s.upper().startswith("CWE-"):
        return s.upper()
    if s.isdigit():
        return f"CWE-{s}"
    return s.upper()


def run_security(file_path: str, code: str = "") -> Tuple[float, List[Dict]]:
    """Security dimension. Returns (score, issues).

    Merges Bandit (if available) + AST findings, dedups, scores once with the
    severity-class dual-decay model.  No tool-blend weights.
    """
    tree = _parse(code)
    if tree is None and file_path and os.path.exists(file_path):
        try:
            with open(file_path, encoding="utf-8", errors="ignore") as fh:
                code = fh.read()
            tree = _parse(code)
        except OSError:
            pass
    if tree is None:
        return 5.0, [{
            "type": "security", "issue": "parse_error", "severity": "INFO",
            "confidence": "HIGH", "description": "Code could not be parsed.",
            "line": 0, "cwe": "", "evidence": "", "source": "ast_fallback",
            "recommendation": "",
        }]

    ast_issues = _ast_security_issues(code, tree)

    bandit_issues: List[Dict] = []
    bandit_bin = shutil.which("bandit")
    if bandit_bin and file_path and os.path.exists(file_path):
        try:
            proc = subprocess.run(
                [bandit_bin, "-f", "json", "-q", "--silent", file_path],
                capture_output=True, text=True, timeout=30,
            )
            stdout = (proc.stdout or "").strip()
            if stdout:
                data = json.loads(stdout)
                for item in data.get("results", []):
                    bandit_issues.append({
                        "type": "security",
                        "issue": item.get("test_id", item.get("test_name", "")),
                        "test_name": item.get("test_name", ""),
                        "severity": item.get("issue_severity", "LOW"),
                        "confidence": item.get("issue_confidence", "LOW"),
                        "description": item.get("issue_text", ""),
                        "line": item.get("line_number", 0),
                        "cwe": _normalize_bandit_cwe(item.get("issue_cwe", "")),
                        "evidence": (item.get("code", "") or "")[:120],
                        "source": "bandit",
                        "recommendation": "",
                    })
        except (subprocess.TimeoutExpired, OSError, json.JSONDecodeError):
            bandit_issues = []

    # Merge + dedup (Bandit wins on shared test ids).
    bandit_ids = {i["issue"] for i in bandit_issues}
    merged = bandit_issues + [i for i in ast_issues if i["issue"] not in bandit_ids]

    # Central impact assignment (identical formula for both sources).
    for it in merged:
        it["impact"] = _cwe_impact(it.get("cwe", ""), it.get("confidence", "LOW"))

    score = _security_score([it["impact"] for it in merged])
    merged.sort(key=lambda x: x["impact"], reverse=True)
    return score, merged


# ══════════════════════════════════════════════════════════════════════════
# COMPLEXITY
# ══════════════════════════════════════════════════════════════════════════
#
# Two sub-scores fused:
#   structural    — McCabe cyclomatic, mapped via a continuous piecewise-
#                   exponential curve anchored at NIST/McCabe thresholds.
#   computational — time & space Big-O via AST composition rules [CLRS],
#                   scored by monotonic lookup, combined by min-dominance.
#   Complexity = COMPLEXITY_COMP_W·computational + COMPLEXITY_STRUCT_W·structural
#
# Big-O detection reliability (DECLARED): O(1)…O(n³) and O(n×m) detected
# reliably; O(2^n) only for the classic pattern (≥2 self-calls + decrement);
# O(n!) is NOT statically detected (Future Work) though it exists in the scale.
# Other declared limits: interprocedural (helper-in-loop), library-call cost,
# memoization, data-dependent loops.
# ──────────────────────────────────────────────────────────────────────────

BIG_O_RANK: Dict[str, int] = {
    "O(1)": 0, "O(log n)": 1, "O(n)": 2, "O(n log n)": 3,
    "O(n×m)": 4, "O(n²)": 5, "O(n³)": 6, "O(n³+)": 6,
    "O(2^n)": 7, "O(n!)": 8,
}


def _bigo_score(category: str, sub_penalty: float) -> float:
    """Monotonic lookup score for a complexity class.

    [CLRS] hierarchy order is a mathematical fact; BIGO_SCORE values are
    CALIBRATABLE but strictly monotonic.  sub_penalty (0..1) nudges the score
    fractionally toward the next-worse class to reflect heavy loop bodies,
    without crossing the class boundary.
    """
    # Normalise legacy "O(n³+)" to "O(n³)".
    cat = "O(n³)" if category == "O(n³+)" else category
    score = BIGO_SCORE.get(cat)
    if score is None:
        return _clamp(BIGO_SCORE["O(n²)"])
    # Find the next-worse class score to bound the penalty nudge.
    rank = BIG_O_RANK.get(cat, 5)
    worse = [BIGO_SCORE[c] for c, r in BIG_O_RANK.items()
             if r == rank + 1 and c in BIGO_SCORE]
    floor = min(worse) if worse else max(score - 1.0, 0.0)
    return _clamp(score - sub_penalty * (score - floor))


def _worst_category(*categories: str) -> str:
    return max(categories, key=lambda c: BIG_O_RANK.get(c, 0))


# ---- structural (cyclomatic) ----------------------------------------------

def _structural_score(cc_agg: float) -> float:
    """Continuous piecewise-exponential map of CC_agg → [0,10].

    Equation (per segment): score(x) = A · exp(-λ · (x - x0)), where each λ is
    DERIVED so the curve passes exactly through consecutive McCabe anchors:
        λ = ln(A / A_next) / (x_next - x0).
    Thresholds 10/20/50 [GROUNDED] [NIST500235]; anchor scores [CALIBRATABLE].
    Continuous (no jumps), monotonic, always positive, smooth → 0.
    Exponential chosen over linear so near-threshold inputs (e.g. CC 19 vs 21)
    are not split by an abrupt slope change.  [JUSTIFIED]
    """
    anchors = STRUCT_ANCHORS               # ((10,8),(20,6),(50,3))
    x0_prev, a_prev = 0.0, 10.0
    for (x_thr, a_thr) in anchors:
        if cc_agg <= x_thr:
            lam = _safe_log(a_prev / a_thr) / (x_thr - x0_prev)
            return _clamp(a_prev * math.exp(-lam * (cc_agg - x0_prev)))
        x0_prev, a_prev = x_thr, a_thr
    # Tail beyond the last anchor: continue decaying toward 0 with a rate that
    # halves the last anchor score over the last segment's width.
    last_x, last_a = anchors[-1]
    prev_x = anchors[-2][0] if len(anchors) >= 2 else 0.0
    width = max(last_x - prev_x, 1.0)
    lam_tail = _safe_log(2.0) / width      # [JUSTIFIED] half-life over segment width
    return _clamp(last_a * math.exp(-lam_tail * (cc_agg - last_x)))


def _cyclomatic_agg(code: str) -> float:
    """CC_agg = CC_AGG_MAX_W·max(CC) + CC_AGG_AVG_W·mean(CC). [McCabe76]"""
    if RADON_AVAILABLE:
        try:
            blocks = cc_visit(code)
            funcs = [b for b in blocks if hasattr(b, "complexity")]
            if not funcs:
                return 1.0
            vals = [b.complexity for b in funcs]
            return CC_AGG_MAX_W * max(vals) + CC_AGG_AVG_W * (sum(vals) / len(vals))
        except Exception:
            pass
    # Fallback: structural CC via AST branch counting.
    tree = _parse(code)
    if tree is None:
        return 10.0
    _BRANCH = (ast.If, ast.While, ast.For, ast.AsyncFor,
               ast.ExceptHandler, ast.With, ast.AsyncWith)
    funcs = _functions(tree)
    if not funcs:
        return 1.0
    ccs = []
    for f in funcs:
        cc = 1 + sum(1 for n in ast.walk(f) if isinstance(n, _BRANCH))
        cc += sum(len(n.values) - 1 for n in ast.walk(f)
                  if isinstance(n, ast.BoolOp))
        ccs.append(cc)
    return CC_AGG_MAX_W * max(ccs) + CC_AGG_AVG_W * (sum(ccs) / len(ccs))


def _structural_from_code(code: str) -> float:
    return _structural_score(_cyclomatic_agg(code))


# ---- computational: TIME Big-O detection ----------------------------------
# AST asymptotic-composition analyser [CLRS]: nested loops multiply, sequential
# take the dominant term, recursion via Master Theorem patterns, binary search
# (halving) → O(log n), sort calls → O(n log n), independent nested loops →
# O(n×m).  Transferred intact from the validated v1 detector.
class _TimeComplexityAnalyser:
    


    def __init__(self, tree: ast.AST, code: str) -> None:
        self.tree = tree
        self.code = code


    def _is_binary_search(self, func: ast.AST) -> bool:
        

        if not any(isinstance(n, ast.While) for n in ast.walk(func)):
            return False

        midpoint_vars: Set[str] = set()
        for node in ast.walk(func):
            if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                continue
            val = node.value if isinstance(node, ast.Assign) else node.value
            if val is None:
                continue
            if isinstance(val, ast.BinOp) and isinstance(
                val.op, (ast.FloorDiv, ast.RShift)
            ):
                rhs = val.right
                if isinstance(rhs, ast.Constant) and rhs.value in (1, 2):
                    midpoint_vars.update(_assigned_names(node))
            if isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add):
                if isinstance(val.right, ast.BinOp) and isinstance(
                    val.right.op, ast.FloorDiv
                ):
                    midpoint_vars.update(_assigned_names(node))

        if not midpoint_vars:
            func_src = _unparse(func)
            if not re.search(r"//\s*2\b|>>\s*1\b", func_src):
                return False

        has_subscript = any(
            isinstance(n, ast.Subscript)
            and isinstance(n.slice, ast.Name)
            and n.slice.id in midpoint_vars
            for n in ast.walk(func)
        )

        has_compare = any(
            isinstance(n, ast.If)
            and any(isinstance(c, ast.Compare) for c in ast.walk(n.test))
            and _contains_name(n.test, midpoint_vars)
            for n in ast.walk(func)
        )

        bound_updates = sum(
            1 for node in ast.walk(func)
            if isinstance(node, (ast.Assign, ast.AugAssign))
            and _contains_name(
                node.value
                if isinstance(node, ast.Assign)
                else node,
                midpoint_vars,
            )
        )

        name_fallback = bool(re.search(
            r"\b(low|lo|left|high|hi|right)\b", _unparse(func)
        )) if not (has_subscript and has_compare) else True

        has_halving = bool(midpoint_vars) or bool(
            re.search(r"//\s*2\b|>>\s*1\b", _unparse(func))
        )
        value_space_bs = (
            has_halving
            and has_compare
            and bound_updates >= 2
            and not has_subscript
        )

        return (has_subscript and has_compare and (bound_updates >= 1 or name_fallback)
                ) or value_space_bs


    def _independence_factor(
        self,
        outer: ast.For,
        inner: ast.For,
    ) -> float:
        

        def _iter_name(node: ast.AST) -> Optional[str]:
            if isinstance(node, ast.Name):
                return node.id
            if isinstance(node, ast.Attribute):
                return _unparse(node)
            return None

        outer_name = _iter_name(outer.iter)
        inner_name = _iter_name(inner.iter)

        if outer_name is None or inner_name is None:
            return 0.7
        if outer_name == inner_name:
            return 1.0
        if isinstance(outer.target, ast.Name):
            if inner_name == outer.target.id:
                return 0.9
        return 0.5


    def _body_sub_penalty(self, loop: ast.AST) -> float:
        

        n_calls   = _call_count(loop)
        has_heavy = any(
            isinstance(n, ast.Call)
            and isinstance(n.func, (ast.Name, ast.Attribute))
            and getattr(n.func, "id", getattr(n.func, "attr", ""))
               in {"sort", "sorted", "min", "max", "sum", "any", "all",
                   "filter", "map"}
            for n in ast.walk(loop)
        )
        has_exit = _has_early_exit(loop)
        p = min(n_calls / 10.0, 0.5)
        p += 0.25 if has_heavy else 0.0
        p -= 0.20 if has_exit  else 0.0
        return _clamp(p, 0.0, 1.0)


    def _analyse_loop(self, loop: ast.AST, depth: int) -> Tuple[str, float]:
        
        body_sp = self._body_sub_penalty(loop)

        if depth == 1:
            has_sort = any(
                isinstance(n, ast.Call)
                and getattr(getattr(n, "func", None), "id",
                            getattr(getattr(n, "func", None), "attr", ""))
                   in {"sort", "sorted"}
                for n in ast.walk(loop)
            )
            base = "O(n log n)" if has_sort else "O(n)"
        elif depth == 2:
            base = "O(n²)"
        else:
            base = "O(n³+)"

        worst_cat = base
        worst_sp  = body_sp

        for child in _direct_child_loops(loop):
            if isinstance(loop, (ast.For, ast.AsyncFor)) and \
               isinstance(child, (ast.For, ast.AsyncFor)):
                ind = self._independence_factor(loop, child)
            else:
                ind = 0.7

            inner_cat, inner_sp = self._analyse_loop(child, depth + 1)

            if ind < 0.6:
                if inner_cat == "O(n²)":
                    inner_cat = "O(n×m)"
                elif inner_cat == "O(n³+)":
                    inner_cat = "O(n²)"
                inner_sp = _clamp(inner_sp * ind, 0.0, 1.0)

            if BIG_O_RANK.get(inner_cat, 0) > BIG_O_RANK.get(worst_cat, 0):
                worst_cat, worst_sp = inner_cat, inner_sp
            elif inner_cat == worst_cat:
                worst_sp = max(worst_sp, inner_sp)

        return worst_cat, _clamp(worst_sp)

    def _analyse_node(self, node: ast.AST) -> Tuple[str, float]:
        best_cat, best_sp = "O(1)", 0.0
        for child in ast.iter_child_nodes(node):
            if isinstance(child, LOOP_TYPES):
                cat, sp = self._analyse_loop(child, depth=1)
            else:
                cat, sp = self._analyse_node(child)
            if BIG_O_RANK.get(cat, 0) > BIG_O_RANK.get(best_cat, 0):
                best_cat, best_sp = cat, sp
            elif cat == best_cat:
                best_sp = max(best_sp, sp)
        return best_cat, best_sp

    def analyse(self) -> Tuple[str, float]:
        

        funcs = _functions(self.tree)

        for func in funcs:
            if self._is_binary_search(func):
                return "O(log n)", 0.15

        top_src = _unparse(self.tree)
        has_top_sort = bool(re.search(
            r"\b(sorted|heapq\.|bisect\.)\b|\.sort\s*\(", top_src
        ))

        worst_cat, worst_sp = "O(1)", 0.0
        for func in funcs:
            cat, sp = self._analyse_node(func)
            if BIG_O_RANK.get(cat, 0) > BIG_O_RANK.get(worst_cat, 0):
                worst_cat, worst_sp = cat, sp
            elif cat == worst_cat:
                worst_sp = max(worst_sp, sp)

        if not funcs:
            worst_cat, worst_sp = self._analyse_node(self.tree)

        if worst_cat == "O(n)" and has_top_sort:
            worst_cat = "O(n log n)"

        return worst_cat, worst_sp


# ---- computational: SPACE Big-O detection ---------------------------------
# Detects allocation growth: numpy/torch/pandas/TF allocations, containers
# built inside loops, unmemoised recursion (call-stack), copy/deepcopy in
# loops.  Transferred intact from the validated v1 detector.
def _space_rank_from_call(call: ast.Call) -> Tuple[int, str]:
    

    name  = _call_name(call)
    short = name.split(".")[-1]

    _NP_ALLOCS    = {"zeros", "ones", "full", "empty", "eye", "arange", "linspace"}
    _TORCH_ALLOCS = {"zeros", "ones", "full", "empty", "rand", "randn",
                     "randint", "eye", "arange", "linspace"}

    if name.startswith(("np.", "numpy.")):
        if short in _NP_ALLOCS:
            arg0 = call.args[0] if call.args else None
            if arg0 and isinstance(arg0, (ast.Tuple, ast.List)) and \
               len(arg0.elts) >= 2:
                return 2, "numpy 2D allocation → O(n²) space"
            if arg0 and isinstance(arg0, ast.BinOp) and \
               isinstance(arg0.op, ast.Mult):
                return 2, "numpy allocation with multiplied dimension → O(n²)"
            return 1, "numpy array allocation → O(n) space"

    if name.startswith("torch.") and short in _TORCH_ALLOCS:
        n_args = len(call.args)
        if n_args >= 2:
            return 2, "torch multi-dimensional allocation → O(n²) space"
        return 1, "torch tensor allocation → O(n) space"

    if name in {"pd.DataFrame", "pandas.DataFrame",
                "pd.Series",    "pandas.Series"}:
        return 1, "pandas DataFrame/Series allocation → O(n) space"

    if name.startswith("tf.") and short in {"zeros", "ones", "fill", "random"}:
        return 1, "TensorFlow tensor allocation → O(n) space"

    if short == "list" and call.args:
        first = call.args[0]
        if isinstance(first, ast.Call) and _call_name(first) == "range":
            return 1, "list(range(...)) → O(n) memory; prefer range() directly"

    return 0, ""


def _detect_space_complexity(
    tree: ast.AST, code: str
) -> Tuple[str, List[str], float]:
    

    parent_map = _build_parent_map(tree)
    issues: List[str] = []
    max_rank = 0
    sub_pen  = 0.0
    seen_msgs: Set[str] = set()

    def _add(rank: int, msg: str, pen_factor: float) -> None:
        nonlocal max_rank, sub_pen
        if msg and msg not in seen_msgs:
            seen_msgs.add(msg)
            issues.append(msg)
        max_rank = max(max_rank, rank)
        sub_pen  = max(sub_pen, pen_factor * rank)

    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            rank, msg = _space_rank_from_call(node)
            if rank:
                _add(rank, msg, 0.35)

    _CONTAINERS = (
        ast.List, ast.Dict, ast.Set,
        ast.ListComp, ast.DictComp, ast.SetComp,
    )
    for node in ast.walk(tree):
        if not isinstance(node, _CONTAINERS):
            continue
        depth = 0
        p = parent_map.get(id(node))
        while p is not None:
            if isinstance(p, LOOP_TYPES):
                depth += 1
            p = parent_map.get(id(p))
        if depth:
            rank = min(depth, 2)
            _add(rank,
                 f"{type(node).__name__} allocated inside loop "
                 f"(depth={depth}) → O(n) per iteration",
                 0.30)

    memo_re = re.compile(
        r"@\s*(lru_cache|cache|functools\.lru_cache|functools\.cache)"
        r"|memo\[|dp\[|cache\["
    )
    for func in _functions(tree):
        func_src = _unparse(func)
        func_has_memo = bool(memo_re.search(func_src))
        self_calls = {
            c.func.id for c in ast.walk(func)
            if isinstance(c, ast.Call)
            and isinstance(c.func, ast.Name)
            and c.func.id == func.name
        }
        if self_calls and not func_has_memo:
            _add(1,
                 f"Recursive '{func.name}' without memoization "
                 f"→ O(n) call stack depth",
                 0.35)

    for node in ast.walk(tree):
        if isinstance(node, LOOP_TYPES):
            for inner in ast.walk(node):
                if isinstance(inner, ast.Call):
                    fname = (
                        inner.func.attr
                        if isinstance(inner.func, ast.Attribute)
                        else getattr(inner.func, "id", "")
                    )
                    if fname in {"deepcopy", "copy"}:
                        _add(1,
                             "copy/deepcopy inside loop → O(n) extra memory per iteration",
                             0.40)
                        break

    rank_map = {0: "O(1)", 1: "O(n)", 2: "O(n²)", 3: "O(n³+)"}
    category = rank_map.get(min(max_rank, 3), "O(1)")
    return category, issues, _clamp(sub_pen, 0.0, 1.0)


# ---- computational + dimension fusion -------------------------------------

def run_complexity(code: str) -> Tuple[float, List[Dict]]:
    """Complexity dimension. Returns (score, issues).

    computational = min(time_score, space_score)   [JUSTIFIED] Big-O dominance
    Complexity    = COMPLEXITY_COMP_W·computational
                  + COMPLEXITY_STRUCT_W·structural
    """
    issues: List[Dict] = []

    tree = _parse(code)
    if tree is None:
        return 0.0, [{
            "type": "complexity", "issue": "SyntaxError",
            "description": "Code could not be parsed.", "line": 0,
            "evidence": "", "recommendation": "",
        }]

    time_analyser = _TimeComplexityAnalyser(tree, code)
    time_cat, time_sp = time_analyser.analyse()
    time_score = _bigo_score(time_cat, time_sp)

    space_cat, space_msgs, space_sp = _detect_space_complexity(tree, code)
    space_score = _bigo_score(space_cat, space_sp)

    # min-dominance: the worse asymptotic class governs.
    computational = min(time_score, space_score)
    structural = _structural_from_code(code)
    final = _clamp(COMPLEXITY_COMP_W * computational
                   + COMPLEXITY_STRUCT_W * structural)

    # Per-function high-CC issues (more granular than the old file-level note).
    if RADON_AVAILABLE:
        try:
            for b in cc_visit(code):
                if hasattr(b, "complexity") and b.complexity > 10:
                    sev = "HIGH" if b.complexity > 20 else "MEDIUM"
                    issues.append({
                        "type": "complexity", "issue": "high_cyclomatic",
                        "severity": sev, "label": f"CC={b.complexity}",
                        "description": (
                            f"Function '{getattr(b, 'name', '?')}' has cyclomatic "
                            f"complexity {b.complexity} (> McCabe threshold 10). "
                            "Consider decomposition."
                        ),
                        "line": getattr(b, "lineno", 0),
                        "evidence": getattr(b, "name", ""),
                        "recommendation": "Split into smaller functions; reduce branching.",
                    })
        except Exception:
            pass

    if BIG_O_RANK.get(time_cat, 0) >= BIG_O_RANK["O(n²)"]:
        issues.append({
            "type": "complexity", "issue": "time_complexity_high",
            "label": time_cat,
            "description": f"Detected {time_cat} time complexity. "
                           f"Loop-body penalty {time_sp:.2f}.",
            "line": 0, "evidence": "", "recommendation":
            "Reduce nesting or use a more efficient algorithm/data structure.",
        })
    elif BIG_O_RANK.get(time_cat, 0) >= BIG_O_RANK["O(n×m)"]:
        issues.append({
            "type": "complexity", "issue": "time_complexity_independent_nested",
            "label": time_cat,
            "description": f"Independent nested loops ({time_cat}) over "
                           "different collections.",
            "line": 0, "evidence": "", "recommendation":
            "Confirm both dimensions are necessary; consider hashing/indexing.",
        })

    for msg in space_msgs:
        issues.append({
            "type": "complexity", "issue": "space_complexity_elevated",
            "label": space_cat, "description": msg, "line": 0,
            "evidence": "", "recommendation":
            "Allocate outside loops or stream data to reduce memory growth.",
        })

    return final, issues


# ══════════════════════════════════════════════════════════════════════════
# MAINTAINABILITY
# ══════════════════════════════════════════════════════════════════════════
#
# Three complementary layers (MI is volumetric-blind to semantics & to
# duplication/architecture; R and T fill those blind spots):
#   Maintainability = β1·MI_norm + β2·R + β3·T
#       MI_norm — full Coleman–Oman index INCLUDING the -0.23·CC term
#                 [ColemanOman94]. CC is intentionally retained (no
#                 decomposition): we respect the validated formula and accept
#                 the natural complexity↔maintainability relationship. The
#                 three dimensions are CONCEPTUALLY independent, not
#                 statistically orthogonal.
#       R       — semantic readability: naming [Butler09], types [PEP484/TypeEmp],
#                 docs [PEP257].  Within R: w_n,w_t > w_d (stronger evidence);
#                 docs deliberately de-emphasised vs the old engine.
#       T       — architecture: duplication [SonarDup] + modularity (DRY).
#   All β,w are CALIBRATABLE; their ORDER is evidence-constrained.
# ──────────────────────────────────────────────────────────────────────────

def _halstead_volume(code: str) -> float:
    

    if RADON_AVAILABLE:
        try:
            h = h_visit(code)
            total = getattr(h, "total", None)
            if total is not None and hasattr(total, "volume"):
                return max(float(total.volume), 1.0)
            if isinstance(h, (list, tuple)) and h:
                first = h[0]
                v = getattr(first, "volume",
                            getattr(getattr(first, "total", None),
                                    "volume", None))
                if v is not None:
                    return max(float(v), 1.0)
        except Exception:
            pass

    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(code).readline))
    except tokenize.TokenError:
        return 1.0

    _KW_OPS = {
        "if", "else", "elif", "while", "for", "in", "not", "and", "or",
        "return", "yield", "lambda", "import", "from", "class", "def",
        "del", "raise", "pass", "break", "continue", "try", "except",
        "finally", "with", "as", "is", "global", "nonlocal", "assert",
    }
    ops: Set[str] = set()
    opds: Set[str] = set()
    n1 = n2 = 0

    for tok in tokens:
        tt, tv = tok.type, tok.string
        if tt == tokenize.OP:
            ops.add(tv); n1 += 1
        elif tt == tokenize.NAME:
            if tv in _KW_OPS:
                ops.add(tv); n1 += 1
            elif tv not in keyword.kwlist:
                opds.add(tv); n2 += 1
        elif tt in (tokenize.NUMBER, tokenize.STRING):
            opds.add(tv); n2 += 1

    eta = len(ops) + len(opds)
    N   = n1 + n2
    if eta < 2 or N == 0:
        return 1.0
    return max(N * math.log2(eta), 1.0)


# MI normalisation: Microsoft/VS bound the raw MI to [0,100] via *100/171.
# We map to [0,10]: divide raw (clamped at 0) by 17.1.
_MI_RAW_DIVISOR = 17.1   # [GROUNDED] 171/10, from the VS [0,100] convention.


def _mi_full(code: str) -> float:
    """Full Maintainability Index INCLUDING cyclomatic term. [ColemanOman94]

        MI_raw = 171 - 5.2·ln(V) - 0.23·CC - 16.2·ln(LOC)
        MI_norm = clamp(max(MI_raw,0) / 17.1, 0, 10)
    Constants 5.2 / 0.23 / 16.2 are [GROUNDED] (regression-derived, 1994).
    """
    volume = _halstead_volume(code)
    loc = max(len(code.splitlines()), 1)
    cc = _cyclomatic_agg(code)            # reuse the same CC aggregation
    mi_raw = 171.0 - 5.2 * _safe_log(volume) - 0.23 * cc - 16.2 * _safe_log(loc)
    return _clamp(max(mi_raw, 0.0) / _MI_RAW_DIVISOR)


# ---- Layer R: semantic readability ----------------------------------------

_ALLOWED_SHORT = frozenset("ijkxyznefvtslhbcmdpqruw")
_ALLOWED_TWO_LETTER = frozenset({
    "lo", "hi", "ok", "db", "df", "fn", "fp", "tp", "tn", "lr", "op", "io",
    "dx", "dy", "dt", "ax", "ay", "az", "x1", "x2", "y1", "y2", "n1", "n2",
    "t0", "t1",
})
_VAGUE_NAMES = frozenset({
    "data", "val", "temp", "tmp", "var", "obj", "item", "res", "info",
    "stuff", "thing", "value", "result", "output", "input_", "buf", "buffer",
})
_SNAKE_RE = re.compile(r"^[a-z_][a-z0-9_]*$")
_PASCAL_RE = re.compile(r"^_?[A-Z][a-zA-Z0-9]*$")


def _is_vague(name: str, func: Optional[ast.AST]) -> bool:
    is_short = (len(name) <= 2
                and name.lower() not in _ALLOWED_SHORT
                and name.lower() not in _ALLOWED_TWO_LETTER)
    is_vague = name.lower() in _VAGUE_NAMES
    if not (is_short or is_vague):
        return False
    if func is not None:                     # tolerate trivial accessor returns
        body = getattr(func, "body", [])
        if len(body) <= 3:
            for stmt in body:
                if isinstance(stmt, ast.Return) and name in _unparse(stmt):
                    return False
    return True


def _naming_score(tree: ast.AST, funcs: List[ast.AST]) -> Tuple[float, List[Dict]]:
    """Naming quality. [Butler09],[Lawrie06],[PEP8]

    Counts evidence-based flaws — vague/too-short locals AND PEP 8 convention
    violations on function/class names (capitalisation anomaly is one of the
    flaws Butler links to readability).  Score = 10·(1 - flaw_ratio).
    """
    flaws: List[Dict] = []
    total = 0

    for func in funcs:
        fname = getattr(func, "name", "")
        total += 1
        if fname and not _SNAKE_RE.match(fname) and not fname.startswith("__"):
            flaws.append({"name": fname, "line": getattr(func, "lineno", 0),
                          "kind": "function not snake_case (PEP 8)"})
        for node in ast.walk(func):
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
                total += 1
                if _is_vague(node.id, func):
                    flaws.append({"name": node.id,
                                  "line": getattr(node, "lineno", 0),
                                  "kind": "vague/too-short identifier"})

    for cls in _classes(tree):
        total += 1
        if not _PASCAL_RE.match(cls.name):
            flaws.append({"name": cls.name, "line": getattr(cls, "lineno", 0),
                          "kind": "class not PascalCase (PEP 8)"})

    ratio = len(flaws) / max(total, 1)
    return _clamp((1.0 - ratio) * 10.0), flaws


def _types_score(funcs: List[ast.AST]) -> float:
    """Type-annotation coverage. [PEP484],[TypeEmp]

    Ratio of functions with a return annotation or any annotated parameter.
    """
    if not funcs:
        return 10.0
    typed = sum(1 for f in funcs
                if getattr(f, "returns", None)
                or any(a.annotation for a in f.args.args))
    return _clamp((typed / len(funcs)) * 10.0)


def _docs_score(funcs: List[ast.AST], tree: ast.AST) -> float:
    """Docstring coverage, public API weighted higher than private. [PEP257]

    Public symbols (no leading underscore) count double — documenting the API
    surface matters more than private helpers.
    """
    targets = list(funcs) + _classes(tree)
    if not targets:
        return 10.0
    weighted_have = 0.0
    weighted_total = 0.0
    for t in targets:
        name = getattr(t, "name", "")
        w = 1.0 if name.startswith("_") else 2.0   # public weighted higher
        weighted_total += w
        if ast.get_docstring(t):
            weighted_have += w
    return _clamp((weighted_have / max(weighted_total, 1e-9)) * 10.0)


def _readability_layer(tree: ast.AST, funcs: List[ast.AST]
                       ) -> Tuple[float, List[Dict], Dict[str, float]]:
    naming, naming_flaws = _naming_score(tree, funcs)
    types = _types_score(funcs)
    docs = _docs_score(funcs, tree)
    R = (MAINT_R_NAMING_W * naming
         + MAINT_R_TYPES_W * types
         + MAINT_R_DOCS_W * docs)
    return _clamp(R), naming_flaws, {"naming": naming, "types": types, "docs": docs}


# ---- Layer T: architectural structure -------------------------------------

def _duplication_density(code: str) -> Tuple[float, int]:
    """Duplicated-line density via sliding-window token-hashing. [SonarDup]

        duplicated_lines_density = duplicated_lines / LOC × 100
    Deterministic (token-hash of normalised line windows). A block is a run of
    >= _DUP_MIN_LINES identical normalised lines appearing more than once.
    Returns (density_percent, duplicated_line_count).
    """
    _DUP_MIN_LINES = 4           # [JUSTIFIED] lighter than Sonar's 10-stmt rule
    raw_lines = code.splitlines()
    norm = []
    for ln in raw_lines:
        s = ln.strip()
        if not s or s.startswith("#"):
            norm.append(None)         # ignore blanks/comments
        else:
            norm.append(re.sub(r"\s+", " ", s))
    loc = max(sum(1 for x in norm if x is not None), 1)

    seen: Dict[str, int] = {}
    dup_line_ids: Set[int] = set()
    n = len(norm)
    for i in range(n - _DUP_MIN_LINES + 1):
        window = norm[i:i + _DUP_MIN_LINES]
        if any(w is None for w in window):
            continue
        key = "\n".join(window)
        if key in seen:
            for j in range(i, i + _DUP_MIN_LINES):
                dup_line_ids.add(j)
            for j in range(seen[key], seen[key] + _DUP_MIN_LINES):
                dup_line_ids.add(j)
        else:
            seen[key] = i
    density = len(dup_line_ids) / loc * 100.0
    return density, len(dup_line_ids)


def _modularity_score(tree: ast.AST, code: str, funcs: List[ast.AST]) -> float:
    """Architectural decomposition signal. [DRY / single-responsibility]

    Penalises: (a) procedural code with little/no function/class structure,
    (b) oversized functions (single-responsibility violation). Heuristic,
    deterministic.
    """
    loc = max(len(code.splitlines()), 1)
    n_funcs = len(funcs)
    n_classes = len(_classes(tree))

    score = 10.0
    # (a) substantial code with no decomposition at all
    if loc >= 40 and n_funcs == 0 and n_classes == 0:
        score -= 5.0
    # (b) oversized functions
    oversized = 0
    for f in funcs:
        body_lines = (getattr(f, "end_lineno", 0) or 0) - getattr(f, "lineno", 0)
        if body_lines > 60:
            oversized += 1
    if n_funcs:
        score -= min(oversized / n_funcs, 1.0) * 3.0
    return _clamp(score)


def _architecture_layer(tree: ast.AST, code: str, funcs: List[ast.AST]
                        ) -> Tuple[float, List[Dict], Dict[str, float]]:
    density, dup_lines = _duplication_density(code)
    # density 0%→10, ramps down; ~50%+ duplication → ~0.  [JUSTIFIED] linear ramp
    dup_score = _clamp(10.0 - density / 5.0)
    mod_score = _modularity_score(tree, code, funcs)
    T = MAINT_T_DUP_W * dup_score + MAINT_T_MOD_W * mod_score
    issues: List[Dict] = []
    if density > 10.0:
        issues.append({
            "type": "maintainability", "issue": "code_duplication",
            "severity": "MEDIUM" if density < 25 else "HIGH",
            "description": f"{density:.0f}% of lines are duplicated "
                           f"({dup_lines} lines). Refactor repeated blocks (DRY).",
            "line": 0, "evidence": f"{dup_lines} duplicated lines",
            "recommendation": "Extract repeated logic into shared functions.",
        })
    return _clamp(T), issues, {"duplication": dup_score, "modularity": mod_score}


# ---- maintainability dimension fusion -------------------------------------

def run_maintainability(code: str) -> Tuple[float, List[Dict]]:
    """Maintainability dimension. Returns (score, issues).

        Maintainability = β1·MI_norm + β2·R + β3·T
    """
    tree = _parse(code)
    if tree is None:
        return 0.0, [{
            "type": "maintainability", "issue": "SyntaxError",
            "description": "Code could not be parsed.", "line": 0,
            "evidence": "", "recommendation": "",
        }]

    funcs = _functions(tree)

    mi = _mi_full(code)
    R, naming_flaws, r_parts = _readability_layer(tree, funcs)
    T, t_issues, t_parts = _architecture_layer(tree, code, funcs)

    score = _clamp(MAINT_BETA_MI * mi + MAINT_BETA_R * R + MAINT_BETA_T * T)

    issues: List[Dict] = []

    # Documentation note (no harsh penalty — low weight by design).
    if r_parts["docs"] < 5.0:
        issues.append({
            "type": "maintainability", "issue": "low_documentation",
            "severity": "LOW",
            "description": (
                f"Documentation coverage is low (score {r_parts['docs']:.1f}/10). "
                "Public functions/classes benefit most from docstrings."
            ),
            "line": 0, "evidence": "", "recommendation":
            "Add docstrings to public API symbols.",
            "reference": "PEP 257",
        })

    if r_parts["types"] < 3.0:
        issues.append({
            "type": "maintainability", "issue": "missing_type_hints",
            "severity": "LOW",
            "description": (
                f"Type-annotation coverage is low (score {r_parts['types']:.1f}/10). "
                "Type hints aid comprehension and tooling."
            ),
            "line": 0, "evidence": "", "recommendation":
            "Annotate parameters and return types.",
            "reference": "PEP 484",
        })

    # Naming flaws — specific, line-anchored (top few).
    for fl in naming_flaws[:5]:
        issues.append({
            "type": "maintainability", "issue": "naming_flaw",
            "severity": "LOW",
            "description": f"Identifier '{fl['name']}' — {fl['kind']}.",
            "line": fl["line"], "evidence": fl["name"],
            "recommendation": "Use a descriptive, convention-compliant name.",
            "reference": "Butler et al. (2009) WCRE; Lawrie et al. (2006) ICPC; PEP 8",
        })

    issues.extend(t_issues)
    return score, issues


# ══════════════════════════════════════════════════════════════════════════
# FUSION · REPORT · PUBLIC API
# ══════════════════════════════════════════════════════════════════════════

def _label(score: float) -> str:
    if score >= 8.5: return "Excellent"
    if score >= 7.0: return "Good"
    if score >= 5.0: return "Acceptable"
    if score >= 3.0: return "Needs Improvement"
    if score >= 1.5: return "Poor"
    return "Critical"


def _overall(s: float, c: float, m: float) -> float:
    """Advisory aggregate (NOT reported in the paper). Equal-ish weights are
    CALIBRATABLE; no claim of a grounded weighting is made."""
    return round(OVERALL_SEC_W * s + OVERALL_CPX_W * c + OVERALL_MNT_W * m, 2)


def _generate_report(s: float, c: float, m: float, issues: List[Dict],
                     time_cat: str = "", space_cat: str = "") -> str:
    ov = _overall(s, c, m)
    header = (
        f"Code Quality Report | Overall: {ov}/10 ({_label(ov)}) | "
        f"Security: {s}/10 ({_label(s)}) | "
        f"Complexity: {c}/10 ({_label(c)}) | "
        f"Maintainability: {m}/10 ({_label(m)})"
    )
    parts = [header]

    s_issues = [i for i in issues if i.get("type") == "security"]
    c_issues = [i for i in issues if i.get("type") == "complexity"]
    m_issues = [i for i in issues if i.get("type") == "maintainability"]

    critical_sec = [i for i in s_issues
                    if i.get("severity") in ("HIGH", "CRITICAL")]
    if not s_issues or s >= 9.0:
        parts.append("Security: No significant vulnerabilities detected.")
    elif critical_sec:
        top = critical_sec[0]
        parts.append(
            f"Security: {len(critical_sec)} high-severity issue(s). "
            f"Priority: {top.get('test_name', top.get('issue', ''))} "
            f"({top.get('cwe', '?')}, line {top.get('line', '?')})."
        )
    else:
        parts.append(f"Security: {len(s_issues)} low/medium note(s). "
                     "No critical vulnerabilities.")

    if time_cat or space_cat:
        parts.append(f"Complexity: Time {time_cat or 'O(n)'}, "
                     f"Space {space_cat or 'O(1)'}.")
    if c >= 8.5:
        parts.append("Efficient algorithmic structure.")
    elif c < 5.0 and c_issues:
        parts.append(f"Performance concern: {c_issues[0]['description'][:100]}")

    if m_issues:
        parts.append(f"Maintainability: {m_issues[0]['description'][:120]}")
    elif m >= 8.0:
        parts.append("Maintainability: Well-documented, typed, clean naming.")

    return " ".join(parts)


_SKIP_NAMES = frozenset({
    "settings", "config", "constants", "conf", "__init__", "setup",
    "migrations", "conftest", "manage", "wsgi", "asgi", "urls", "admin",
})
_SKIP_PATHS = frozenset({
    "migrations", "docs", "test", "tests", "fixtures", "examples",
    "example", "vendor", "venv", ".venv",
})


def is_valid_code_file(file_path: str, min_chars: int = 100,
                       max_chars: int = 50_000) -> bool:
    """Dataset filter: real, substantive Python source only."""
    try:
        with open(file_path, "r", encoding="utf-8", errors="ignore") as fh:
            code = fh.read()
        if not (min_chars <= len(code.strip()) <= max_chars):
            return False
        path_parts = set(file_path.lower().replace("\\", "/").split("/"))
        if path_parts & _SKIP_PATHS:
            return False
        fname = os.path.basename(file_path).lower().removesuffix(".py")
        if any(kw in fname for kw in _SKIP_NAMES):
            return False
        lines = [ln for ln in code.splitlines() if ln.strip()]
        comments = [ln for ln in lines if ln.strip().startswith("#")]
        if lines and len(comments) / len(lines) > 0.60:
            return False
        tree = ast.parse(code)
        return any(isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)) for n in ast.walk(tree))
    except Exception:
        return False


SYSTEM_PROMPT = (
    "You are a senior software engineer performing expert code review.\n"
    "\n"
    "You receive Python source code together with the issues a static-analysis "
    "engine has already reported. Your task is to add what static analysis "
    "cannot: problems that require semantic understanding of the code's intent "
    "and meaning. Do not restate issues the engine already found.\n"
    "\n"
    "Report only issues you can locate in the code, and cite the line number "
    "for each. Do not describe behavior that is not present; if a category has "
    "no genuine issue, leave it empty rather than inventing one.\n"
    "\n"
    "Conclude with three overall quality scores - security, complexity, and "
    "maintainability - each from 0 to 10 where 10 is best, reflecting the "
    "code's quality after accounting for both the engine's findings and your "
    "own.\n"
    "\n"
    "Return a single JSON object with these keys, in this order: "
    "complementary_issues, insights, recommendations, scores."
)


def _assemble(code: str, s_score, s_issues, c_score, c_issues,
              m_score, m_issues) -> Dict:
    all_issues = s_issues + c_issues + m_issues
    ov_score = _overall(s_score, c_score, m_score)
    time_cat = next((i.get("label", "") for i in c_issues
                     if "time" in i.get("issue", "")), "")
    space_cat = next((i.get("label", "") for i in c_issues
                      if "space" in i.get("issue", "")), "")
    report = _generate_report(s_score, c_score, m_score, all_issues,
                              time_cat, space_cat)
    payload = {
        "scores": {
            "security": round(s_score, 2), "complexity": round(c_score, 2),
            "maintainability": round(m_score, 2), "overall": ov_score,
        },
        "labels": {
            "security": _label(s_score), "complexity": _label(c_score),
            "maintainability": _label(m_score), "overall": _label(ov_score),
        },
        "issues": all_issues, "report": report,
    }
    return {
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user",
             "content": f"Analyse this Python code:\n\n{code}"},
            {"role": "assistant",
             "content": json.dumps(payload, ensure_ascii=False)},
        ]
    }


def analyze_code(code: str, source_path: str = "<string>") -> Optional[Dict]:
    """Analyse a code string → ChatML training sample (or None if unsuitable)."""
    if len(code.strip()) < 30:
        return None
    tree = _parse(code)
    if tree is not None and not any(
        isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        for n in ast.walk(tree)
    ):
        return None

    _tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".py", delete=False, encoding="utf-8"
        ) as tmp:
            tmp.write(code)
            _tmp_path = tmp.name
        s_score, s_issues = run_security(_tmp_path, code=code)
    finally:
        if _tmp_path and os.path.exists(_tmp_path):
            os.unlink(_tmp_path)

    c_score, c_issues = run_complexity(code)
    m_score, m_issues = run_maintainability(code)
    return _assemble(code, s_score, s_issues, c_score, c_issues,
                     m_score, m_issues)


def analyze_file(file_path: str) -> Optional[Dict]:
    """Analyse a file on disk → ChatML training sample (or None)."""
    try:
        with open(file_path, "r", encoding="utf-8", errors="ignore") as fh:
            code = fh.read()
    except OSError:
        return None
    if len(code.strip()) < 30:
        return None
    tree = _parse(code)
    if tree is None or not any(
        isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        for n in ast.walk(tree)
    ):
        return None

    s_score, s_issues = run_security(file_path, code=code)
    c_score, c_issues = run_complexity(code)
    m_score, m_issues = run_maintainability(code)
    return _assemble(code, s_score, s_issues, c_score, c_issues,
                     m_score, m_issues)


def analyze_with_timeout(file_path: str, timeout: int = 30) -> Optional[Dict]:
    """Run analyze_file under a hard wall-clock timeout (thread-based)."""
    result_box: List[Optional[Dict]] = [None]

    def _worker() -> None:
        try:
            result_box[0] = analyze_file(file_path)
        except Exception:
            pass

    t = threading.Thread(target=_worker, daemon=True)
    t.start()
    t.join(timeout)
    return result_box[0]
