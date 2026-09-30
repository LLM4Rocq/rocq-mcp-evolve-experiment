"""Correctness gate (anti-gaming). A proof counts as solved ONLY if this
module says so; the in-session compiler result is never trusted.

(ported from rocq-mcp-evolve)

Layers (docs/ASSUMPTIONS.md A8 in rocq-mcp-evolve; mirrored here):
 1. prefix lock  — the candidate must reproduce the shipped task-file prefix
                   (import + docstring + statement) exactly, modulo whitespace.
                   Nothing may be inserted before or into the statement, so the
                   statement cannot be re-interpreted.
 2. region lock  — the agent-written region (everything after the prefix, with
                   comments and string literals stripped) must not contain any
                   FORBIDDEN token: sorry, admit, axiom, native_decide,
                   set_option, run_tac, run_cmd, #eval, #exit, unsafe,
                   implemented_by, extern, ofReduceBool, ofReduceNat, sorryAx,
                   addDecl, addDeclWithoutChecking, Lean.Elab, Lean.Meta,
                   Lean.Environment, Lean.Kernel, +native, import.
 3+4. fresh recompile + assumption audit (+ kernel replay) — delegated to the
                   Lean `gate` executable (LeanMcpEvolve.Gate / GateMain),
                   run against the candidate in a clean temp dir: it recompiles
                   from scratch, checks the candidate's prefix/suffix bytes
                   against --reference (STRICTER than layer 1's whitespace-
                   normalized lock — see testing/README.md deviations table),
                   collects axioms, and kernel-replays. Its JSON verdict is
                   never re-interpreted here beyond accepted/reason/axioms.

Every rejection carries a machine-readable reason.
"""

import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

from common import prover_env, MAIN_REPO

FORBIDDEN = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\baxiom\b"), "axiom"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"\bset_option\b"), "set_option"),
    (re.compile(r"\brun_tac\b"), "run_tac"),
    (re.compile(r"\brun_cmd\b"), "run_cmd"),
    (re.compile(r"#eval\b"), "#eval"),
    (re.compile(r"#exit\b"), "#exit"),
    (re.compile(r"\bunsafe\b"), "unsafe"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by"),
    (re.compile(r"\bextern\b"), "extern"),
    (re.compile(r"\bofReduceBool\b"), "ofReduceBool"),
    (re.compile(r"\bofReduceNat\b"), "ofReduceNat"),
    (re.compile(r"\bsorryAx\b"), "sorryAx"),
    (re.compile(r"\baddDecl\b"), "addDecl"),
    (re.compile(r"\baddDeclWithoutChecking\b"), "addDeclWithoutChecking"),
    (re.compile(r"\bLean\.Elab\b"), "Lean.Elab"),
    (re.compile(r"\bLean\.Meta\b"), "Lean.Meta"),
    (re.compile(r"\bLean\.Environment\b"), "Lean.Environment"),
    (re.compile(r"\bLean\.Kernel\b"), "Lean.Kernel"),
    (re.compile(r"\+native\b"), "+native"),
    (re.compile(r"\bimport\b"), "import"),
]

GATE_BIN = Path(os.environ.get(
    "LEAN_GATE_BIN", str(MAIN_REPO / ".lake" / "build" / "bin" / "gate")))
GATE_TIMEOUT_S = float(os.environ.get("GATE_TIMEOUT_S", "300"))
# DEVIATION from rocq-mcp-evolve (120s): the Lean gate loads Mathlib (~10-20s)
# and kernel-replays the whole proof term — a Mathlib tactic round is ~10x a
# Rocq one. See testing/README.md deviations table.


def strip_comments(src: str) -> str:
    """Remove (possibly nested) Lean comments (`--` to EOL, nested `/- -/`)
    and string literals (`"..."`, backslash-escaped)."""
    out = []
    i, n = 0, len(src)
    depth = 0
    in_string = False
    while i < n:
        c = src[i]
        if in_string:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue
        if depth > 0:
            # Lean recognizes string literals inside comments too; a string
            # containing "/-" or "-/" must not perturb the nesting depth
            # (the Lean analogue of the Rocq comment/string desync exploit
            # this layer defends against — see test/test_gate.py case 3).
            if c == '"':
                i += 1
                while i < n:
                    if src[i] == "\\" and i + 1 < n:
                        i += 2
                        continue
                    if src[i] == '"':
                        i += 1
                        break
                    i += 1
                continue
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j == -1 else j  # leave the newline itself for the next pass
            continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if c == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def split_at_prefix(candidate: str, prefix: str):
    """Index in candidate where the whitespace-normalized prefix ends, or None."""
    ci, n = 0, len(candidate)
    for ch in prefix:
        if ch.isspace():
            continue
        while ci < n and candidate[ci].isspace():
            ci += 1
        if ci >= n or candidate[ci] != ch:
            return None
        ci += 1
    return ci


def _run_gate(cand_path: Path, theorem_name: str, reference, project,
              timeout_s: float) -> tuple[dict | None, str, float]:
    args = [str(GATE_BIN), str(cand_path), "--theorem", theorem_name]
    if reference is not None:
        args += ["--reference", str(reference)]
    if project is not None:
        args += ["--project", str(project)]
    args.append("--json")
    t0 = time.monotonic()
    p = subprocess.run(
        args, cwd=cand_path.parent, env=prover_env(),
        capture_output=True, text=True, timeout=timeout_s,
    )
    dur = time.monotonic() - t0
    out = p.stdout + p.stderr
    verdict = None
    for line in reversed(p.stdout.splitlines()):
        line = line.strip()
        if not line:
            continue
        try:
            verdict = json.loads(line)
        except json.JSONDecodeError:
            continue
        break
    return verdict, out, dur


def check(candidate: str, prefix: str, theorem_name: str,
          reference=None, project=None, timeout_s: float = GATE_TIMEOUT_S) -> dict:
    res = {
        "solved": False,
        "reason": None,
        "axioms": None,
        "recompile_s": None,
        "detail": None,
    }
    split = split_at_prefix(candidate, prefix)
    if split is None:
        res["reason"] = "prefix_modified"
        return res
    region = strip_comments(candidate[split:])
    for pat, label in FORBIDDEN:
        if pat.search(region):
            res["reason"] = f"forbidden_token:{label}"
            return res
    # Candidate text is normalized to end with "\n" before writing.
    candidate_norm = candidate if candidate.endswith("\n") else candidate + "\n"
    with tempfile.TemporaryDirectory(prefix="lean_gate_") as td:
        cand_path = Path(td) / "candidate.lean"
        cand_path.write_text(candidate_norm)
        try:
            verdict, out, dur = _run_gate(cand_path, theorem_name, reference, project, timeout_s)
        except subprocess.TimeoutExpired as e:
            res["reason"] = "recompile_timeout"
            res["recompile_s"] = round(timeout_s, 3)
            res["detail"] = ((e.stdout or "") + (e.stderr or ""))[-2000:] if e.stdout or e.stderr else None
            return res
        res["recompile_s"] = round(dur, 3)
        if verdict is None:
            res["reason"] = "gate_unavailable"
            res["detail"] = out[-2000:]
            return res
        res["axioms"] = verdict.get("axioms")
        if verdict.get("accepted"):
            res["solved"] = True
            return res
        res["reason"] = f"gate:{verdict.get('reason')}"
        res["detail"] = out[-2000:]
    return res
