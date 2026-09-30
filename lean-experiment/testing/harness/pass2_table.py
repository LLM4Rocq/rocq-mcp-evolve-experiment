#!/usr/bin/env python3
"""pass@1 / pass@2 table with wall time and cost for the prompt-free campaign (run from the repo
root). Reps: rep 0 = the load-clean first attempt, rep 1 = the second attempt (2026-09-11/12).
Cost as in cost_table.py: exact CLI total_cost_usd where the CLI emitted a result event; wall-killed
attempts estimated from the transcript (calibrated on the priced attempts)."""
import json, collections
man = json.load(open("dataset/manifest.json")); items = man if isinstance(man, list) else man.get("problems", man.get("items", []))
tier = {(p.get("id") or p.get("name")): (p.get("tier") or p.get("bucket") or p.get("difficulty")) for p in items}
RUNS = [("compiler-only", "putnam60_pf_ws_baseline"), ("lean-mcp-evolve (5 tools)", "putnam60_pf_ws_session5_r2"), ("lean-lsp-mcp", "putnam60_pf_ws_lean_lsp_mcp_r2")]
K = ("input_tokens", "cache_creation_input_tokens", "cache_read_input_tokens", "output_tokens")
W = {"input_tokens": 1, "cache_creation_input_tokens": 1.25, "cache_read_input_tokens": 0.1, "output_tokens": 5}
def f(v):
    try: return float(v or 0)
    except Exception: return 0.0
def scan(path):
    per_msg = {}; think = 0; chars = 0
    for l in open(path):
        if not l.startswith("{"): continue
        try: e = json.loads(l)
        except Exception: continue
        if e.get("subtype") == "thinking_tokens": think += e.get("estimated_tokens_delta") or 0
        elif e.get("type") == "assistant":
            m = e.get("message") or {}; us = m.get("usage") or {}; cur = per_msg.setdefault(m.get("id"), {k: 0 for k in K})
            for k in K: cur[k] = max(cur[k], us.get(k, 0))
            for c in m.get("content", []):
                if c.get("type") == "text": chars += len(c.get("text", ""))
                elif c.get("type") == "tool_use": chars += len(json.dumps(c.get("input")))
    return {k: sum(v[k] for v in per_msg.values()) for k in K}, think, chars
rows = {}; per = {}; cal = []
for name, run in RUNS:
    for l in open(f"testing/logs/runs/{run}/results.jsonl"):
        x = json.loads(l); key = (name, x["problem_id"], x["rep"]); rows[key] = x
        u, think, chars = scan("testing/logs/" + x["attempt_dir"] + "/transcript.jsonl"); per[key] = (u, think, chars)
        if f(x.get("total_cost_usd")) > 0:
            ru = x.get("usage") or {}; cal.append((ru["output_tokens"], think, chars / 4.0, ru, f(x["total_cost_usd"])))
Sxx = sum(t*t for _, t, _, _, _ in cal); Sxy = sum(t*c for _, t, c, _, _ in cal); Syy = sum(c*c for _, _, c, _, _ in cal)
Sxo = sum(t*o for o, t, _, _, _ in cal); Syo = sum(c*o for o, _, c, _, _ in cal); det = Sxx*Syy - Sxy*Sxy
a = (Sxo*Syy - Syo*Sxy) / det; bc = (Syo*Sxx - Sxo*Sxy) / det
num = den = 0
for o, t, c, ru, cost in cal:
    w = sum(W[k]*ru.get(k, 0) for k in K); num += w*cost; den += w*w
p = num / den
def cost_of(key):
    x = rows[key]; c = f(x.get("total_cost_usd"))
    if c > 0: return c
    u, think, chars = per[key]; uu = dict(u); uu["output_tokens"] = a*think + bc*chars/4
    return p * sum(W[k]*uu.get(k, 0) for k in K)
print(f"calibration: {len(cal)} priced attempts; out ≈ {a:.2f}·thinking + {bc:.2f}·chars/4; price scale ${p*1e6:.2f}/Mtok")
print(f"{'arm':26s} {'bucket':6s} {'rep0':>5s} {'rep1':>5s} {'both':>4s} {'pass@2':>6s} {'wall Σ (2 reps)':>15s} {'cost Σ (2 reps)':>15s} {'$/pass@2 solve':>14s}")
out = {}
for name, run in RUNS:
    T = collections.defaultdict(lambda: {"r0": set(), "r1": set(), "wall": 0.0, "cost": 0.0, "n": 0})
    for (nm, pid, rep), x in rows.items():
        if nm != name: continue
        for b in (tier[pid], "all"):
            t = T[b]; t["n"] += 1; t["wall"] += f(x["wall_s"]); t["cost"] += cost_of((nm, pid, rep))
            if x["solved"]: t["r0" if rep == 0 else "r1"].add(pid)
    for b in ("easy", "medium", "hard", "all"):
        t = T[b]; u = t["r0"] | t["r1"]; out[(name, b)] = {"rep0": sorted(t["r0"]), "rep1": sorted(t["r1"]), "pass2": sorted(u), "wall_s": t["wall"], "cost": t["cost"], "n": t["n"]}
        print(f"{name:26s} {b:6s} {len(t['r0']):5d} {len(t['r1']):5d} {len(t['r0'] & t['r1']):4d} {len(u):6d} {t['wall']/60:13.1f} m {t['cost']:13.2f} $ {(t['cost']/len(u) if u else float('nan')):13.2f} $")
    print()
allp = {b: set() for b in ("easy", "medium", "hard", "all")}
for (name, b), v in out.items(): allp[b] |= set(v["pass2"])
print("union of the three arms, pass@2:", {b: len(v) for b, v in allp.items()})
print("solved by all three arms (pass@2):", {b: len(set.intersection(*[set(out[(n, b)]["pass2"]) for n, _ in RUNS])) for b in ("easy", "medium", "hard", "all")})
for name, _ in RUNS:
    others = set().union(*[set(out[(n, "all")]["pass2"]) for n, _ in RUNS if n != name])
    print(f"only {name}: {sorted(set(out[(name,'all')]['pass2']) - others)}")
json.dump({f"{k[0]}|{k[1]}": v for k, v in out.items()}, open("testing/logs/pass2_summary.json", "w"), indent=1)
