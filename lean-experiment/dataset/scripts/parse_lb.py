import json,re,os
d=json.load(open('PutnamBench/docs/results.json'))
probs=sorted(f[:-5] for f in os.listdir('PutnamBench/lean4/src') if f.endswith('.lean'))
pset=set(probs)
solved={}   # approach -> set of problem ids
meta={}
for k,v in d.items():
    ns=v.get('num-solved',{})
    if not any('lean' in x for x in ns): continue
    note=v.get('note','')
    ids=set()
    for m in re.finditer(r'(19\d\d|20\d\d)[ _]([ABab])[ _]?(\d)',note):
        ids.add(f'putnam_{m.group(1)}_{m.group(2).lower()}{m.group(3)}')
    if 'all problems' in note.lower() or 'aced all' in note.lower() or 'problems: all' in note.lower():
        ids=set(pset)
    k=k.strip()
    name=k
    i=2
    while name in solved: name=f'{k} #{i}'; i+=1
    solved[name]=ids
    meta[name]={'link':v.get('link'),'num':ns,'budget':v.get('condensed-compute-budget'),'listed':len(ids),'unknown':sorted(ids-pset)}
for n,m in meta.items():
    print(f"{n:45s} num={m['num']} listed={m['listed']} budget={m['budget']} unknown={m['unknown'][:5]}")
json.dump({n:sorted(s) for n,s in solved.items()},open('solved.json','w'),indent=1)
json.dump(meta,open('meta.json','w'),indent=1)
