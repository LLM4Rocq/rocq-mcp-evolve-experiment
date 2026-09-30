import json,collections
rows=json.load(open('scores.json')); pools=json.load(open('pools.json')); hist=json.load(open('filehist.json'))
year=lambda p:int(p.split('_')[1])
def prim(p):
    t=rows[p]['tags']; return t[0] if t else 'other'
easy=pools['easy']
hard=['putnam_1963_a3','putnam_1967_b1','putnam_1969_b4','putnam_1970_b6','putnam_1974_b1','putnam_2000_b3','putnam_2019_a4','putnam_2021_a6','putnam_2022_a5',
      'putnam_1962_a2','putnam_1989_b6','putnam_1995_a6','putnam_2004_a5','putnam_2014_b6','putnam_2015_b4','putnam_2017_b6','putnam_2022_b6','putnam_2023_b5','putnam_2024_a3','putnam_2024_b5']
assert all(h in pools['hardpool'] for h in hard) and len(set(hard))==20
quota={'analysis':6,'algebra':6,'number_theory':3,'linear_algebra':1,'geometry':1,'combinatorics':1,'abstract_algebra':1,'set_theory':1}
bytag=collections.defaultdict(list)
for p in sorted(pools['medpool'],key=year):
    if hist[p]['last']<='2025-08-31': bytag[prim(p)].append(p)   # statement stable before the mid-tier evaluations
medium=[]
for t,k in quota.items():
    c=bytag[t]; n=len(c)
    idx=sorted({round((i+0.5)*n/k-0.5) for i in range(k)})
    medium+= [c[i] for i in idx]
assert len(medium)==20, len(medium)
for name,S in [('easy',easy),('medium',medium),('hard',hard)]:
    print(name, collections.Counter(prim(p) for p in S), sorted(year(p) for p in S)[::4])
sel={'easy':easy,'medium':sorted(medium),'hard':sorted(hard)}
assert len(set(sum(sel.values(),[])))==60
json.dump(sel,open('selection.json','w'),indent=1)
print(json.dumps(sel))
