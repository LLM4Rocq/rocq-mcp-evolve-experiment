#!/usr/bin/env python3
"""Wall time / gate time / token / cost table per arm and bucket for the prompt-free campaign
(run from the repo root). Cost: exact CLI total_cost_usd where the CLI emitted a final result event;
wall-killed attempts (no result event) are estimated from the transcript: cache/input tokens from the
per-message usage, output tokens from the CLI thinking_tokens counters + visible text (calibrated on the
priced attempts: median 2% error), priced with a single scale fitted to the CLI-priced rows."""
import json,collections
man=json.load(open("dataset/manifest.json")); items = man if isinstance(man,list) else man.get("problems", man.get("items", []))
tier={ (p.get("id") or p.get("name")): (p.get("tier") or p.get("bucket") or p.get("difficulty")) for p in items}
def load(r): return {json.loads(l)["problem_id"]:(r,json.loads(l)) for l in open(f"testing/logs/runs/{r}/results.jsonl")}
base=load("putnam60_pf_ws_baseline"); s5=load("putnam60_pf_ws_session5_r2"); l1=load("putnam60_pf_ws_lean_lsp_mcp"); l2=load("putnam60_pf_ws_lean_lsp_mcp_r2")
lsp={p:(l2[p] if p in l2 else l1[p]) for p in l1}
arms=[("compiler-only",base),("lean-mcp-evolve (5 tools)",s5),("lean-lsp-mcp",lsp)]
K=("input_tokens","cache_creation_input_tokens","cache_read_input_tokens","output_tokens")
def f(v):
    try: return float(v or 0)
    except: return 0.0
def scan(run,pid):
    per_msg={}; think=0; chars=0
    for l in open(f"testing/logs/runs/{run}/attempts/{pid}__rep0/transcript.jsonl"):
        if not l.startswith("{"): continue
        try: e=json.loads(l)
        except: continue
        if e.get("subtype")=="thinking_tokens": think+=e.get("estimated_tokens_delta") or 0
        elif e.get("type")=="assistant":
            m=e.get("message") or {}; us=m.get("usage") or {}; mid=m.get("id")
            cur=per_msg.setdefault(mid,{k:0 for k in K})
            for k in K: cur[k]=max(cur[k],us.get(k,0))
            for c in m.get("content",[]):
                if c.get("type")=="text": chars+=len(c.get("text",""))
                elif c.get("type")=="tool_use": chars+=len(json.dumps(c.get("input")))
    u={k:sum(v[k] for v in per_msg.values()) for k in K}
    return u,len(per_msg),think,chars
per={}; cal=[]
for name,rows in arms:
    for pid,(run,x) in rows.items():
        u,nm,think,chars=scan(run,pid); per[(name,pid)]=(u,nm,think,chars)
        if f(x.get("total_cost_usd"))>0:
            ru=x.get("usage") or {}; cal.append((ru["output_tokens"],think,chars/4.0,ru,f(x["total_cost_usd"])))
Sxx=sum(t*t for _,t,_,_,_ in cal); Sxy=sum(t*c for _,t,c,_,_ in cal); Syy=sum(c*c for _,_,c,_,_ in cal); Sxo=sum(t*o for o,t,_,_,_ in cal); Syo=sum(c*o for o,_,c,_,_ in cal)
det=Sxx*Syy-Sxy*Sxy; a=(Sxo*Syy-Syo*Sxy)/det; bc=(Syo*Sxx-Sxo*Sxy)/det
W={"input_tokens":1,"cache_creation_input_tokens":1.25,"cache_read_input_tokens":0.1,"output_tokens":5}
num=den=0
for o,t,c,ru,cost in cal:
    w=sum(W[k]*ru.get(k,0) for k in K); num+=w*cost; den+=w*w
p=num/den
print(f"{'arm':26s} {'bucket':6s} {'n':>2s} {'solv':>4s} {'wall Σ':>7s} {'wall μ':>6s} {'killed':>6s} {'gate Σ':>7s} {'turns':>5s} {'out tok':>8s} {'cache_r tok':>11s} {'est $':>6s} {'CLI $ (n)':>10s} {'$/solve':>7s}")
summary={}
for name,rows in arms:
    T=collections.defaultdict(collections.Counter)
    for pid,(run,x) in rows.items():
        u,nm,think,chars=per[(name,pid)]
        c=f(x.get("total_cost_usd"))
        if c>0: out=(x.get("usage") or {})["output_tokens"]; est=c
        else: out=a*think+bc*chars/4; uu=dict(u); uu["output_tokens"]=out; est=p*sum(W[k]*uu.get(k,0) for k in K)
        for bb in (tier[pid],"all"):
            t=T[bb]; t["n"]+=1; t["solved"]+=bool(x["solved"]); t["wall"]+=f(x["wall_s"]); t["killed"]+=bool(x.get("attempt_timed_out")); t["gate"]+=f((x.get("gate") or {}).get("recompile_s"))
            t["turns"]+=nm; t["out"]+=out; t["cr"]+=u["cache_read_input_tokens"]; t["est"]+=est
            if c>0: t["cli"]+=c; t["cli_n"]+=1
    for b in ["easy","medium","hard","all"]:
        t=T[b]; summary[(name,b)]=dict(t)
        print(f"{name:26s} {b:6s} {t['n']:2d} {t['solved']:4d} {t['wall']/60:6.1f}m {t['wall']/t['n']:5.0f}s {t['killed']:6d} {t['gate']/60:6.1f}m {t['turns']:5d} {t['out']:8.0f} {t['cr']:11d} {t['est']:6.2f} {t['cli']:5.2f} ({t['cli_n']:2d}) {(t['est']/t['solved'] if t['solved'] else float('nan')):7.2f}")
    print()
