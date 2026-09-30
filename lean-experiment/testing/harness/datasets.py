"""Dataset access layer for the Lean eval harness — PutnamBench-60.

(ported from rocq-mcp-evolve)

Dataset (lives inside THIS repo, unlike rocq-mcp-evolve's sibling checkouts):

  <repo>/dataset/{easy,medium,hard}/putnam_*.lean   -- 60 problems total
  <repo>/dataset/manifest.json                      -- id, tier, file, ... per problem

Every file is `import Mathlib` ... `theorem putnam_YYYY_xN ... := ... sorry`
(verified: all 60 files end with `:=`, optional `by`, then `sorry`).

HELD-OUT DISCIPLINE
====================
DEVIATION from rocq-mcp-evolve (documented in testing/README.md): there, the
miniF2F *test* split was held out while a completely separate pool (the
workbook, plus miniF2F *valid*) served all dev/smoke needs, so the guard's
"never touch file contents outside the guard" rule had a disjoint pool to
fall back on. Here PutnamBench-60 is the ONLY Lean dataset there is — there
is no separate dev pool — so the pre-registered smoke set (smoke2, section 2
of PORT_SPEC.md) necessarily draws 2 of the SAME 60 problems, and is
EXPLICITLY exempted from the guard below (debug-only; never reported as a
held-out result). The guard's real purpose survives intact: it is the sole
gate in front of ``load_putnam60()``, the function that assembles the FULL
60-problem manifest used for the single final scored run, mirroring
rocq-mcp-evolve's ``load_minif2f("test")`` — it refuses to run — raising
``RuntimeError("held-out putnam60 split is locked")`` -- unless BOTH:

  1. the file ``<repo>/testing/FINAL_UNLOCK`` exists, and
  2. the environment variable ``LEAN_FINAL_EVAL`` equals ``"1"``.

When (and only when) both conditions hold, an audit line with an ISO
timestamp and the calling PID is appended to
``<repo>/testing/logs/unlock.log`` *before* any data is returned.

Python 3 stdlib only.
"""

import datetime
import json
import os
import re

# <repo>/testing = .../lean-mcp-evolve/testing (this file lives in
# <repo>/testing/harness/).
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # testing/
MAIN_REPO_ROOT = os.path.dirname(REPO_ROOT)  # lean-mcp-evolve/

DATASET_DIR = os.path.join(MAIN_REPO_ROOT, "dataset")
DATASET_MANIFEST = os.path.join(DATASET_DIR, "manifest.json")

# --------------------------------------------------------------------------
# task representation (replaces rocq-mcp-evolve's statement_prefix)
# --------------------------------------------------------------------------

# Everything up to and including the target theorem's `:=`, dropping an
# optional `by` and the trailing `sorry` (section 2 of PORT_SPEC.md). Matched
# at the END of the file (DOTALL so `.` also eats newlines before `sorry`).
_TRAILING_SORRY_RE = re.compile(r":=\s*(?:by\s+)?sorry\s*\Z", re.DOTALL)


def putnam_prefix(content: str) -> str:
    """task.lean content -> prefix ending in ':=\\n' (agent appends a proof
    after it). Raises ValueError if content does not end with the expected
    `:= [by] sorry` tail.
    """
    m = _TRAILING_SORRY_RE.search(content)
    if m is None:
        raise ValueError("content does not end with `:= [by] sorry`")
    return content[: m.start()] + ":=\n"


# --------------------------------------------------------------------------
# manifest.json (metadata only: id, tier, file — no proof content; reading
# this is the Lean analogue of rocq-mcp-evolve's permitted filename `ls`)
# --------------------------------------------------------------------------


def load_manifest_records() -> list[dict]:
    """Raw dataset/manifest.json rows (id, tier, file, ... 60 total)."""
    with open(DATASET_MANIFEST, encoding="utf-8") as f:
        return json.load(f)


def _manifest_record(row: dict) -> dict:
    pid = row["id"]
    return {
        "problem_id": pid,
        "source": "putnam60",
        "difficulty": row["tier"],
        "source_tier": row["tier"],
        "theorem_name": pid,
        "path": os.path.join("dataset", row["file"]),  # relative to MAIN_REPO_ROOT
    }


def bucket_of(manifest_rec: dict) -> str:
    """Difficulty bucket for any manifest record (tier passes straight
    through — no tier->bucket map needed, unlike miniF2F's coarser tiers)."""
    return manifest_rec.get("difficulty", "?")


def load_putnam60() -> list[dict]:
    """HELD OUT. Assembles the full 60-problem manifest (list of dicts with
    keys problem_id, source, difficulty, source_tier, theorem_name, path).

    Raises RuntimeError("held-out putnam60 split is locked") unless
    <repo>/testing/FINAL_UNLOCK exists AND LEAN_FINAL_EVAL=1, in which case an
    audit line is appended to <repo>/testing/logs/unlock.log before any data
    is returned. This guard is the ONLY code path in the repo allowed to
    assemble the full putnam60 manifest (see module docstring).
    """
    unlock_file = os.path.join(REPO_ROOT, "FINAL_UNLOCK")
    if not (os.path.exists(unlock_file) and os.environ.get("LEAN_FINAL_EVAL") == "1"):
        raise RuntimeError("held-out putnam60 split is locked")
    log_dir = os.path.join(REPO_ROOT, "logs")
    os.makedirs(log_dir, exist_ok=True)
    stamp = datetime.datetime.now().astimezone().isoformat()
    with open(os.path.join(log_dir, "unlock.log"), "a", encoding="utf-8") as f:
        f.write(f"{stamp} pid={os.getpid()} unlocked putnam60 split\n")
    return [_manifest_record(r) for r in load_manifest_records()]


def smoke2_records(ids=("putnam_1977_a3", "putnam_1988_b1")) -> list[dict]:
    """2 named putnam60 problems for debug-only smoke runs. UNGUARDED by
    design (PORT_SPEC.md section 2/6): unlike rocq-mcp-evolve, there is no
    separate dev pool to draw smoke problems from, so smoke2 necessarily
    reuses 2 of the same 60 held-out problems. Never reported as a held-out
    result; see testing/README.md deviations table.
    """
    rows = {r["id"]: r for r in load_manifest_records()}
    return [_manifest_record(rows[i]) for i in ids]
