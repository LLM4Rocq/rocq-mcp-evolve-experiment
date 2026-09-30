#!/usr/bin/env python3
"""Held-out PutnamBench-60 table generator (ported from rocq-mcp-evolve's
A74/A76/A80/A81 matrix generator).

(ported from rocq-mcp-evolve)

    python3 harness/final_tables.py            # refuses unless all gates pass
    python3 harness/final_tables.py --force    # print anyway, loudly flagged

Deterministic and safe by construction: it REFUSES to emit numbers unless
every arm passes its integrity gates (row counts, zero live quota-poisoning
markers, zero machine_slept). It emits (a) a human table, (b) formatted table rows, (c) a JSON artifact with full provenance. Always run THIS script and paste its output — never hand-compute.

Reporting conventions are pinned by the trail: pass@1 = rep0 solves /
problems; pass@2 = either-rep solves; $/solve = total cost of ALL attempts
(failures included) / solved attempts; latency = mean wall over SOLVED
attempts only; kill rate = wall-killed attempts. Wilson 95% CIs on
pass@1. No other statistics are computed here; anything further needs a
new pre-registration.
"""

import argparse
import glob
import json
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import common

# run_id, label, expected_n -- the 12 Lean arms of PORT_SPEC.md section 4/8,
# each FINAL_<config_id>. n = 120 (60 problems x 2 reps) except the opus
# arms, run at 1 rep (n = 60) per the Rocq A104 convention this mirrors.
ARMS = [
    ("FINAL_frozen",                    "evolve (haiku, phase-1 frozen config)",                       120),
    ("FINAL_frozen_wallonly",           "evolve (haiku, phase-1 config, wall-only A100)",               120),
    ("FINAL_baseline_sonnet",           "naive control (sonnet, guided)",                                120),
    ("FINAL_session_try_hints_auto_sonnet", "evolve (sonnet, guided)",                                   120),
    ("FINAL_lean_lsp_mcp_fair_sonnet",  "lean-lsp-mcp fair (sonnet, guided)",                            120),
    ("FINAL_af_pf_baseline",            "naive control (sonnet, prompt-free A80)",                       120),
    ("FINAL_af_pf_session",             "evolve (sonnet, prompt-free A80, tailed)",                      120),
    ("FINAL_af_pf_session2",            "evolve (sonnet, prompt-free A108, strategy-tail removed)",      120),
    ("FINAL_af_pf_lean_lsp_mcp",        "lean-lsp-mcp fair (sonnet, prompt-free A99, project-bridged)",  120),
    ("FINAL_af_pf_baseline_opus",       "naive control (opus, prompt-free A104, 1 rep)",                 60),
    ("FINAL_af_pf_session2_opus",       "evolve (opus, prompt-free A104, 1 rep, tail removed)",          60),
    ("FINAL_af_pf_lean_lsp_mcp_opus",   "lean-lsp-mcp fair (opus, prompt-free A104, project-bridged, 1 rep)", 60),
]
POISON_MARKERS = ['"api_error_status": 429', '"api_error_status":429',
                  "session limit", "You've hit your",
                  '"api_error_status": 529']
BUCKETS = ["easy", "medium", "hard"]


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def audit(run):
    """Integrity gates. Returns list of failures (empty = clean)."""
    problems = []
    rd = common.LOGS / "runs" / run
    rows = common.read_jsonl(rd / "results.jsonl")
    if not rows:
        return [f"{run}: no results"]
    slept = [r for r in rows if r.get("machine_slept")]
    if slept:
        problems.append(f"{run}: {len(slept)} machine_slept rows — run "
                        f"harness/repair_run.py then resume the runner")
    live_poison = 0
    for tp in glob.glob(str(rd / "attempts" / "*" / "transcript.jsonl")):
        try:
            txt = open(tp, errors="replace").read()
        except OSError:
            continue
        if any(m in txt for m in POISON_MARKERS):
            live_poison += 1
    if live_poison:
        problems.append(f"{run}: {live_poison} LIVE quota-poisoned transcripts "
                        f"— quarantine + redo those slots")
    # truly-dead rows = transcript shows NO model activity at all (no
    # assistant events AND no thinking_tokens progress). Extended thinking
    # emits system/thinking_tokens events only — such attempts are
    # LEGITIMATE failures, not infrastructure.
    dead = 0
    for r in rows:
        tp = (rd / "attempts" / f"{r['problem_id']}__rep{r.get('rep', 0)}"
              / "transcript.jsonl")
        try:
            alive = False
            for l in open(tp, errors="replace"):
                if ('"type": "assistant"' in l or '"type":"assistant"' in l
                        or '"subtype": "thinking_tokens"' in l
                        or '"subtype":"thinking_tokens"' in l):
                    alive = True
                    break
            dead += (not alive)
        except OSError:
            dead += 1
    if dead:
        problems.append(f"{run}: {dead} rows with ZERO model activity "
                        f"(true dead streams) — quarantine + redo")
    # a solved row must be backed by ITS OWN attempt — assistant turns AND
    # tool use in its transcript. Solved without them means the verdict came
    # from stale/shared grading artifacts left in the attempt dir by a
    # parked or concurrent predecessor, not from anything this attempt
    # produced.
    fp = 0
    for r in rows:
        if not r.get("solved"):
            continue
        tp = (rd / "attempts" / f"{r['problem_id']}__rep{r.get('rep', 0)}"
              / "transcript.jsonl")
        try:
            txt = open(tp, errors="replace").read()
        except OSError:
            fp += 1
            continue
        if not (('"type": "assistant"' in txt or '"type":"assistant"' in txt)
                and ('"type": "tool_use"' in txt or '"type":"tool_use"' in txt)):
            fp += 1
    if fp:
        problems.append(f"{run}: {fp} solved rows without own-transcript "
                        f"activity (stale-artifact false positives) — "
                        f"quarantine + redo")
    # every reported held-out arm must be WALL-bound — a turn cap that fires
    # is a covert tool-call tax. The phase-1 haiku arm is exempt: its cap-30
    # registration mirrors rocq-mcp-evolve's own phase-1 exemption and stays
    # in the record as the measured demonstration of the tax.
    if run != "FINAL_frozen":
        capped = sum(1 for r in rows
                     if str(r.get("stop_reason")) == "error_max_turns")
        if capped:
            problems.append(f"{run}: {capped} turn-cap-terminated rows — "
                            f"held-out arms must be wall-bound")
    return problems


def metrics(run, expected_n):
    rows = common.read_jsonl(common.LOGS / "runs" / run / "results.jsonl")
    out = {"run": run, "n": len(rows), "expected_n": expected_n,
           "complete": len(rows) == expected_n}
    probs = {}
    for r in rows:
        probs.setdefault(r["problem_id"], {})[r.get("rep", 0)] = r
    per_bucket = {}
    for b in BUCKETS:
        bp = {p: v for p, v in probs.items()
              if (v.get(0) or v.get(1) or {}).get("difficulty") == b}
        n = len(bp)
        k1 = sum(1 for v in bp.values() if (v.get(0) or {}).get("solved"))
        k2 = sum(1 for v in bp.values() if any(x.get("solved") for x in v.values()))
        brows = [r for v in bp.values() for r in v.values()]
        cost = sum(r.get("total_cost_usd") or 0 for r in brows)
        srows = [r for r in brows if r.get("solved")]
        lat = (sum(r["wall_s"] for r in srows) / len(srows)) if srows else None
        kills = sum(1 for r in brows if r.get("attempt_timed_out"))
        lo, hi = wilson(k1, n)
        per_bucket[b] = {
            "n_problems": n, "pass1": k1 / n if n else None,
            "pass1_ci": (round(lo, 3), round(hi, 3)),
            "pass2": k2 / n if n else None,
            "cost_per_solve": (cost / len(srows)) if srows else None,
            "latency_solved_s": round(lat, 1) if lat else None,
            "kill_rate": f"{kills}/{len(brows)}",
        }
    out["buckets"] = per_bucket
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()

    failures = []
    for run, _, n in ARMS:
        failures += audit(run)
        rows = common.read_jsonl(common.LOGS / "runs" / run / "results.jsonl")
        if len(rows) != n:
            failures.append(f"{run}: {len(rows)}/{n} rows — INCOMPLETE")
    if failures and not args.force:
        print("REFUSING to emit table; integrity gates failed:")
        for f in failures:
            print("  -", f)
        print("\nFix per the runbook, or --force to preview (flagged).")
        sys.exit(1)
    if failures:
        print("!! FORCED OUTPUT — gates failing:", *failures, sep="\n!!   ")

    art = {"arms": []}
    print(f"\n{'arm':60s} {'pass@1 e/m/h':>20s} {'pass@2 e/m/h':>20s}")
    latex = []
    for run, label, n in ARMS:
        m = metrics(run, n)
        art["arms"].append({"label": label, **m})
        b = m["buckets"]
        p1 = " / ".join(f"{b[x]['pass1']:.2f}" if b[x]["pass1"] is not None
                        else "--" for x in BUCKETS)
        p2 = " / ".join(f"{b[x]['pass2']:.2f}" if b[x]["pass2"] is not None
                        else "--" for x in BUCKETS)
        print(f"{label:60s} {p1:>20s} {p2:>20s}")
        cost = " / ".join(f"{b[x]['cost_per_solve']:.2f}"
                          if b[x]["cost_per_solve"] else "--" for x in BUCKETS)
        lat = " / ".join(f"{b[x]['latency_solved_s']:.0f}"
                         if b[x]["latency_solved_s"] else "--" for x in BUCKETS)
        latex.append(f"{run} | {label} | {p1} | {p2} | {cost} | {lat}")
    out = common.LOGS / "final_heldout_table.json"
    out.write_text(json.dumps(art, indent=1))
    print(f"\nartifact: {out}\n\n==== delimited rows (run | label | pass@1 | pass@2 | $/solve | latency) ====")
    print("\n".join(latex))
    print("\nCIs and kill rates are in the JSON artifact; archive it with "
          "the run records.")


if __name__ == "__main__":
    main()
