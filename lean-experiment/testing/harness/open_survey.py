#!/usr/bin/env python3
"""Open-ability survey: start the evolve server exactly as run_eval.py does
(direct binary, no LEAN_PATH, cwd outside any project, LEAN_TASK_FILE preset)
on every manifest problem and record what `state{}` returns. A healthy file
reports its goal; an infrastructure regression shows up as the same refusal on
every file (the 2026-09-06 "pattern-matching decl" incident, README "Resolved
issue"). Debug tooling only — never part of a registered run.

    python3 testing/harness/open_survey.py [--manifest putnam60|smoke2] [--parallel 4]
"""
import argparse, json, os, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import common
PROJECT = os.environ.get("LEAN_EVAL_PROJECT", "/Users/jviennot/Documents/Cours/LEAN_2026")  # same default as run_eval.py

def one(rec, parallel_dir):
    f = str(common.MAIN_REPO / rec["path"])
    wd = Path(parallel_dir) / rec["problem_id"]; wd.mkdir(parents=True, exist_ok=True)
    env = {"PATH": f"{common.ELAN_BIN}:/usr/bin:/bin", "HOME": os.environ.get("HOME", ""),
           "LEAN_PROJECT_ROOT": PROJECT, "LEAN_WORKDIR": str(wd), "LEAN_TASK_FILE": f,
           "LEAN_ENABLE_TOOLS": "step,rollback,state,try,auto_close", "LEAN_PRELOAD": "0", "LEAN_ENV_V2": "1"}
    msgs = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "state", "arguments": {}}}]
    t0 = time.time()
    try:
        p = subprocess.run([str(common.MAIN_REPO / ".lake" / "build" / "bin" / "lean-mcp-evolve")],
                           input="".join(json.dumps(m) + "\n" for m in msgs), capture_output=True,
                           text=True, env=env, cwd=wd, timeout=900)
        out = p.stdout
    except subprocess.TimeoutExpired:
        out = ""
    txt = "TIMEOUT"
    for l in out.splitlines():
        try:
            j = json.loads(l)
        except json.JSONDecodeError:
            continue
        if j.get("id") == 2:
            r = j.get("result") or j.get("error") or {}
            txt = (r.get("content") or [{}])[0].get("text", json.dumps(r))
    ok = txt.startswith("proving ") and "goals:" in txt
    return rec["problem_id"], round(time.time() - t0, 1), ok, txt[:200].replace("\n", " | ")

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--manifest", default="putnam60"); ap.add_argument("--parallel", type=int, default=4)
    a = ap.parse_args()
    recs = common.load_manifest(a.manifest)
    d = tempfile.mkdtemp(prefix="open_survey_")
    n_ok = 0
    with ThreadPoolExecutor(a.parallel) as ex:
        for pid, dt, ok, txt in ex.map(lambda r: one(r, d), recs):
            n_ok += ok
            print(f"{'ok ' if ok else 'BAD'} {pid} {dt}s {txt}", flush=True)
    print(f"# {n_ok}/{len(recs)} files open to a goal")
    sys.exit(0 if n_ok == len(recs) else 1)

if __name__ == "__main__":
    main()
