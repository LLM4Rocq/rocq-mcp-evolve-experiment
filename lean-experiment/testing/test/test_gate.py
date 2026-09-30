#!/usr/bin/env python3
"""Suite D — correctness-gate soundness (ported from rocq-mcp-evolve's
test/test_gate.py; see rocq-mcp-evolve's test/ARCHITECTURE.md for the suite
naming convention this mirrors).

(ported from rocq-mcp-evolve)

Integration-level, no unit-test framework: imports the REAL gate
(testing/harness/gate.py) and drives its `check` against crafted candidates,
one case per contract/regression. TAP-ish output ("ok - <name>" /
"FAIL - <name>"), prints a summary, and exits 1 on any failure.

The gate shells out to the built `gate` Lean executable
(<repo>/.lake/build/bin/gate), which in turn needs `lake`/`lean` on PATH and
a real Mathlib project (LEAN_EVAL_PROJECT) to elaborate against -- each such
call loads Mathlib (~10-30s) and kernel-replays, so this suite budgets
several minutes, not seconds (see PORT_SPEC.md's ground rules: run with a
generous timeout, e.g. `timeout 300`... actually several gate calls are
made, so the CALLER of this script should budget more, e.g. 600s wall).
"""

import os
import shutil
import sys
import tempfile
from pathlib import Path

# --- resolve testing/harness relative to THIS SCRIPT (not cwd) --------------
_HERE = Path(__file__).resolve().parent
_HARNESS = _HERE.parent / "harness"
sys.path.insert(0, str(_HARNESS))

import common  # noqa: E402
import datasets  # noqa: E402
import gate  # noqa: E402  (gate.py; also pulls in harness/common.py)

PROJECT = os.environ.get("LEAN_EVAL_PROJECT", "/Users/jviennot/Documents/Cours/LEAN_2026")
GATE_TIMEOUT_S = float(os.environ.get("GATE_TIMEOUT_S", "300"))

# --- tiny TAP-ish runner -----------------------------------------------------
_count = 0
_failures = 0


def ok(cond, name, detail=""):
    global _count, _failures
    _count += 1
    if cond:
        print(f"ok - {name}", flush=True)
    else:
        _failures += 1
        suffix = f"  # {detail}" if detail else ""
        print(f"FAIL - {name}{suffix}", flush=True)


# --- fixtures ----------------------------------------------------------------
# Trivial statement for the forbidden/tamper/recompile cases (fast, no heavy
# imports beyond Mathlib itself, which every task file requires).
FOO_REF = "import Mathlib\n\ntheorem foo : True :=\n  sorry\n"
FOO_PREFIX = datasets.putnam_prefix(FOO_REF)  # "import Mathlib\n\ntheorem foo : True :=\n"

# D1 fixture: a genuine, trivial proof (mirrors putnam_1988_b1's shape: a
# small closed-form numeric fact) -- the canonical legit solve.
T_OK_REF = "import Mathlib\n\ntheorem t_ok : (2 : ℕ) + 2 = 4 :=\n  sorry\n"
T_OK_PREFIX = datasets.putnam_prefix(T_OK_REF)

# D5 fixture: a REFERENCE with a real statement, deliberately paired with a
# WEAKER prefix/candidate (a different, trivial statement) -- the python
# whitespace-normalized prefix lock (layer 1) cannot catch this (the
# candidate reproduces ITS OWN given prefix exactly); only the Lean gate
# binary's stricter byte-level statement comparison against --reference
# catches it (testing/README.md deviations table: "stricter").
STRONG_REF = "import Mathlib\n\ntheorem foo : (0 : ℕ) < 1 + 1 :=\n  sorry\n"
WEAK_PREFIX = "import Mathlib\n\ntheorem foo : True :=\n"

# D7 fixture: a false statement -- any proof attempt must fail to compile.
WRONG_REF = "import Mathlib\n\ntheorem wrong_thm (n : ℕ) : n + 1 = n + 2 :=\n  sorry\n"
WRONG_PREFIX = datasets.putnam_prefix(WRONG_REF)


def write_ref(tmpdir, name, content):
    p = Path(tmpdir) / name
    p.write_text(content)
    return p


def main():
    if not gate.GATE_BIN.exists():
        print(f"Bail out! gate binary not found at {gate.GATE_BIN} "
              f"(build it first: lake build gate).", flush=True)
        sys.exit(1)

    with tempfile.TemporaryDirectory(prefix="lean_test_gate_") as td:
        # D1 — legit accept: a genuine proof of a putnam_1988_b1-style
        # trivial theorem must be solved.
        t_ok_ref_path = write_ref(td, "t_ok_ref.lean", T_OK_REF)
        r = gate.check(
            T_OK_PREFIX + "  by norm_num\n", T_OK_PREFIX, "t_ok",
            reference=t_ok_ref_path, project=PROJECT, timeout_s=GATE_TIMEOUT_S,
        )
        ok(r["solved"] is True, "D1 legit-accept (norm_num proof of t_ok)", r["reason"])

        # D2 — sorry in the region is rejected outright (forbidden token).
        r = gate.check(FOO_PREFIX + "sorry\n", FOO_PREFIX, "foo")
        ok(not r["solved"] and str(r["reason"]) == "forbidden_token:sorry",
           "D2 forbidden-token sorry", r["reason"])

        # D3 — comment/string desync exploit (Lean analogue of the Rocq
        # measurement-review critical finding): a crafted block comment
        # containing a string literal that itself contains "-/" must not
        # perturb the nesting depth. If it did (naive stripper), `sorry`
        # would end up wrongly hidden "inside" the comment and slip past the
        # forbidden-token scan. With the correct depth tracking, `sorry`
        # ends up VISIBLE here (see gate.py's strip_comments docstring) and
        # is caught; either way this candidate must never be accepted.
        exploit = FOO_PREFIX + '\n/- "-/" -/ sorry\n'
        r = gate.check(exploit, FOO_PREFIX, "foo")
        ok(r["solved"] is False, "D3 comment-desync exploit rejected", r["reason"])

        # D4 — tampering with the shipped prefix is caught by the (python)
        # prefix lock.
        r = gate.check("theorem foo : False :=\n  trivial\n", FOO_PREFIX, "foo")
        ok(not r["solved"] and r["reason"] == "prefix_modified",
           "D4 prefix-tamper", r["reason"])

        # D5 — statement weakened: the CANDIDATE'S OWN prefix is internally
        # consistent (so layer 1 passes), but it is a strictly weaker
        # statement than --reference's. Only the gate binary's stricter
        # byte-level statement comparison catches this.
        strong_ref_path = write_ref(td, "strong_ref.lean", STRONG_REF)
        r = gate.check(
            WEAK_PREFIX + "  trivial\n", WEAK_PREFIX, "foo",
            reference=strong_ref_path, project=PROJECT, timeout_s=GATE_TIMEOUT_S,
        )
        ok(not r["solved"] and r["reason"] in ("gate:statement_modified", "prefix_modified"),
           "D5 statement-weakened rejected by binary gate", r["reason"])

        # D6 — native_decide is a forbidden token (Lean-specific anti-gaming
        # rule with no Rocq analogue: native_decide can prove false things
        # under a miscompiled/malicious `native_decide` extension).
        r = gate.check(FOO_PREFIX + "by native_decide\n", FOO_PREFIX, "foo")
        ok(not r["solved"] and str(r["reason"]) == "forbidden_token:native_decide",
           "D6 forbidden-token native_decide", r["reason"])

        # D7 — fresh recompile: a false statement cannot be validly proved;
        # any attempt fails to compile.
        wrong_ref_path = write_ref(td, "wrong_ref.lean", WRONG_REF)
        r = gate.check(
            WRONG_PREFIX + "  by omega\n", WRONG_PREFIX, "wrong_thm",
            reference=wrong_ref_path, project=PROJECT, timeout_s=GATE_TIMEOUT_S,
        )
        ok(not r["solved"] and str(r["reason"]).startswith("gate:compile_error"),
           "D7 wrong-proof rejected (gate:compile_error)", r["reason"])

        # D8 — trailing-newline normalization: a candidate with NO trailing
        # newline must still be accepted (gate.py normalizes it before
        # writing, exactly as rocq-mcp-evolve did).
        candidate_no_nl = (T_OK_PREFIX + "  by norm_num").rstrip("\n")
        assert not candidate_no_nl.endswith("\n")
        r = gate.check(
            candidate_no_nl, T_OK_PREFIX, "t_ok",
            reference=t_ok_ref_path, project=PROJECT, timeout_s=GATE_TIMEOUT_S,
        )
        ok(r["solved"] is True, "D8 trailing-newline normalization accepted", r["reason"])

    print(f"# suite D: {_count} checks, {_failures} failures", flush=True)
    sys.exit(1 if _failures else 0)


if __name__ == "__main__":
    main()
