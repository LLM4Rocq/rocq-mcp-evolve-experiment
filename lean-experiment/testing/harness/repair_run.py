#!/usr/bin/env python3
"""Remove sleep-contaminated attempt records from a run so the (resumable)
runner redoes exactly those slots.

(ported from rocq-mcp-evolve; unchanged except this header — nothing in this
file is Rocq/OCaml-specific)

    python3 harness/repair_run.py <run_id>          # then re-invoke run_eval
                                                    # with the original args

An attempt is contaminated iff machine_slept=True (the wall-clock watchdog
killed it after a macOS sleep gap, so both its outcome and its timings are
invalid), or (Lean port additions) reject_reason is harness_error*/
recompile_timeout, or the transcript holds a connection-level api_retry
(network cut mid-attempt). The dropped records are preserved in
results.quarantine.jsonl for audit.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import common


def main():
    run_dir = Path(sys.argv[1])
    if not run_dir.exists():
        run_dir = common.LOGS / "runs" / sys.argv[1]
    res = run_dir / "results.jsonl"
    rows = common.read_jsonl(res)

    def contaminated(r):
        # machine_slept and harness_error as in rocq-mcp-evolve; recompile_timeout
        # added 2026-09-10: the out-of-process gate timing out (300 s) under
        # external machine load is infrastructure, not a verdict (12 such rows
        # in putnam60_pf_ws_session5; candidates were intact on disk).
        return (bool(r.get("machine_slept"))
                or str(r.get("reject_reason", "")).startswith("harness_error")
                or r.get("reject_reason") == "recompile_timeout"
                or connection_cut(r))

    def connection_cut(r):
        # added 2026-09-10 (wifi outage during putnam60_pf_ws_session5_r2): a
        # connection-level API retry (claude CLI `api_retry` event with no HTTP
        # status — the stream was cut, not rate-limited) restarts the request
        # and loses the thinking done so far; under the wall-only budget that
        # is lost time, i.e. infrastructure, not a verdict. HTTP-status retries
        # (429/529/401) are left alone: they are the API's own behaviour.
        d = r.get("attempt_dir")
        if not d:
            return False
        tr = (common.LOGS / d / "transcript.jsonl")
        if not tr.exists():
            tr = Path(d) / "transcript.jsonl"
        try:
            for line in tr.read_text(errors="replace").splitlines():
                if '"api_retry"' not in line:
                    continue
                try:
                    e = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if e.get("subtype") == "api_retry" and e.get("error_status") is None:
                    return True
        except OSError:
            return False
        return False

    keep = [r for r in rows if not contaminated(r)]
    drop = [r for r in rows if contaminated(r)]
    if not drop:
        print("no contaminated records")
        return
    with open(run_dir / "results.quarantine.jsonl", "a") as f:
        for r in drop:
            f.write(json.dumps(r, sort_keys=True) + "\n")
    res.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in keep))
    # move the attempt dirs aside so reruns start clean BUT the evidence for the
    # quarantine (transcript with the api_retry / sleep gap, server log) survives
    # (Lean port, 2026-09-12: the Rocq original deleted them, which made the 11
    # connection-cut quarantines of putnam60_pf_ws_session5_r2 unverifiable
    # afterwards except through the CLI's own ~/.claude/projects session files).
    import shutil
    import time

    qdir = run_dir / "attempts_quarantined"
    stamp = time.strftime("%Y%m%dT%H%M%S")
    for r in drop:
        aid = f"{r['problem_id']}__rep{r['rep']}"
        adir = run_dir / "attempts" / aid
        if adir.exists():
            qdir.mkdir(exist_ok=True)
            shutil.move(str(adir), str(qdir / f"{aid}.{stamp}"))
    print(f"quarantined {len(drop)} records ({[r['problem_id'] for r in drop[:5]]}...); "
          f"re-run run_eval with the original arguments to redo them")


if __name__ == "__main__":
    main()
