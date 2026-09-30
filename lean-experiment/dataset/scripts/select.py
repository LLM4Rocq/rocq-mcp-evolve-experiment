import json,math,collections
rows=json.load(open('scores.json')); solved=json.load(open('solved.json')); hist=json.load(open('filehist.json'))
year=lambda p:int(p.split('_')[1])
U=[p for p in rows if year(p)<=2024]
WEAK=['GPT-4o','COPRA (GPT-4o)','Deepseek R1','Goedel-Prover-SFT','ABEL','InternLM2.5-StepProver','Self-play Theorem Prover',
 'gemini-2.0-flash-thinking-121','gemini-2.5-pro-exp-0325','Kimina-Prover-7B-Distill','o4-mini-high','DeepSeek-Prover-V2','DSP+','Bourbaki',
 'Goedel-Prover-V2','Ax-Prover (Axiomatic AI)','GPT-5 (ReAct, 10 turns)','TIR Conjecturor','Enumerate-Conjecture-Prove']
DISC=['Seed-Prover 1.5 (ByteDance)','Goedel-Architect','Aleph Prover (Logical Intelligence) #2','Goedel-Architect #2']
w={a:1/math.log(1+len(solved[a])) for a in WEAK}
def easy_score(p): return sum(w[a] for a in rows[p]['weak'])
def prim(p):
    t=rows[p]['tags']; return t[0] if t else 'other'
# EASY
easy=sorted(U,key=lambda p:(-easy_score(p),-rows[p]['nw'],p))[:20]
print('EASY'); [print(f"  {p} score={easy_score(p):.2f} nw={rows[p]['nw']} {rows[p]['tags']} last={hist[p]['last']}") for p in easy]
# MEDIUM pool
medpool=[p for p in U if rows[p]['nw']==0 and rows[p]['nm']==4]
# HARD pool
hardpool=[p for p in U if rows[p]['nw']==0 and rows[p]['nm']==0 and sum(a in DISC for a in rows[p]['strong'])<=2]
print('\nHARD POOL',len(hardpool))
for p in sorted(hardpool,key=lambda p:(sum(a in DISC for a in rows[p]['strong']),p)):
    print(f"  {p} disc={sum(a in DISC for a in rows[p]['strong'])} ns={rows[p]['ns']} {rows[p]['tags']} last={hist[p]['last']} n={hist[p]['n']}")
print('\nMED POOL by tag',collections.Counter(prim(p) for p in medpool))
print('HARD POOL by tag',collections.Counter(prim(p) for p in hardpool))
json.dump({'easy':easy,'medpool':medpool,'hardpool':hardpool},open('pools.json','w'),indent=1)
