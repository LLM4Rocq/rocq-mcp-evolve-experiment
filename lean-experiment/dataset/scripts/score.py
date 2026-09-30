import json,re,os,collections
d=json.load(open('PutnamBench/docs/results.json'))
probs=sorted(f[:-5] for f in os.listdir('PutnamBench/lean4/src') if f.endswith('.lean'))
pset=set(probs)
tags={p['problem_name']:p['tags'] for p in json.load(open('PutnamBench/informal/putnam.json'))}
def ids_of(note):
    return {f'putnam_{y}_{ab.lower()}{n}' for y,ab,n in re.findall(r'(19\d\d|20\d\d)[ _]([ABab])[ _]?(\d)',note)} & pset
solved={}
seen=collections.Counter()
for k,v in d.items():
    k=k.strip(); seen[k]+=1
    name=k if seen[k]==1 else f'{k} #{seen[k]}'
    solved[name]=ids_of(v.get('note',''))
WEAK=['GPT-4o','COPRA (GPT-4o)','Deepseek R1','Goedel-Prover-SFT','ABEL','InternLM2.5-StepProver','Self-play Theorem Prover',
 'gemini-2.0-flash-thinking-121','gemini-2.5-pro-exp-0325','Kimina-Prover-7B-Distill','o4-mini-high','DeepSeek-Prover-V2','DSP+','Bourbaki',
 'Goedel-Prover-V2','Ax-Prover (Axiomatic AI)','GPT-5 (ReAct, 10 turns)','TIR Conjecturor','Enumerate-Conjecture-Prove']
MID=['Seed-Prover (ByteDance)','AxProverBase (Axiomatic AI)','Hilbert','Aleph Prover (Logical Intelligence)']
STRONG=['Seed-Prover 1.5 (ByteDance)','Goedel-Architect','Aleph Prover (Logical Intelligence) #2','Goedel-Architect #2','Aleph Prover (Logical Intelligence) #3']
for n in WEAK+MID+STRONG: assert n in solved, n
rows={}
for p in probs:
    w=[n for n in WEAK if p in solved[n]]; m=[n for n in MID if p in solved[n]]; s=[n for n in STRONG if p in solved[n]]
    rows[p]={'weak':w,'mid':m,'strong':s,'tags':tags.get(p,[]),'nw':len(w),'nm':len(m),'ns':len(s)}
json.dump(rows,open('scores.json','w'),indent=1)
c=collections.Counter((r['nw']>0, r['nm'], r['ns']) for r in rows.values())
print('(#weak>0, #mid, #strong) -> count')
for k in sorted(c): print(k,c[k])
print('\n== EASY candidates: sorted by #weak desc ==')
for p,r in sorted(rows.items(), key=lambda x:-x[1]['nw'])[:40]:
    print(f"{p:18s} nw={r['nw']:2d} nm={r['nm']} ns={r['ns']} {r['tags']}")
print('\n== MEDIUM candidates: nw=0, nm=4 ==')
med=[(p,r) for p,r in rows.items() if r['nw']==0 and r['nm']==4]
print(len(med))
for p,r in med: print(f"{p:18s} ns={r['ns']} {r['tags']}")
print('\n== HARD candidates: nw=0, nm=0, sorted by ns ==')
hard=sorted([(p,r) for p,r in rows.items() if r['nw']==0 and r['nm']==0], key=lambda x:x[1]['ns'])
print(len(hard))
for p,r in hard: print(f"{p:18s} ns={r['ns']} {[x.split(' ')[0]+x[-2:] for x in r['strong']]} {r['tags']}")
