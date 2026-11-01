# v0.3 W1: generator of tests/regress/V03_boundaries.bend (from the v0.3 Astra review). Run from the repo root.
from pathlib import Path
import random,json
out=Path('bench/v03')  # writes boundaries.bend and boundaries_expected.json; the committed test is tests/regress/V03_boundaries.bend
s=['import Base','import ./../../frame.bend as DF','import ./../../src/dtype.bend as D','import ./../../tests/regress/lib/rx.bend as R']
expected={}; calls=[]
def arr(a): return '['+', '.join('R.null()' if x is None else f'R.u({x})' for x in a)+']'
def frame(name,cols):
 s.append(f'def {name}() -> DF.ResT(DF.Frame()):\n  R.frame(['+', '.join(f'R.mk("{k}", {arr(v)}, D.TU32{{}})' for k,v in cols.items())+'])')
def case(name,expression,rows):
 calls.append(f'    IO.print("CASE {name}\\n" ++ DF.dump({expression}))');expected[name]=rows
rng=random.Random(20261101)
for i in range(20):
 nl,nr=[(1,7),(7,1),(0,4),(4,0),(5,9)][i%5]
 pool=[0,1,2,None] if i<10 else [0,65535,65536,4294967295,None]
 l=[rng.choice(pool) for _ in range(nl)];r=[rng.choice(pool) for _ in range(nr)]
 l2=[rng.choice(pool) for _ in l];r2=[rng.choice(pool) for _ in r]
 frame(f'l{i}',{'k':l,'q':l2,'li':list(range(nl))});frame(f'r{i}',{'k':r,'q':r2,'ri':list(range(nr))})
 keys=['k'] if i%2 else ['k','q']; lit=json.dumps(keys)
 for kind in ['inner','left','semi','anti']:
  expr=f'DF.then(l{i}(), l => DF.then(r{i}(), r => DF.{kind}_join(l, r, {lit}, {lit})))'
  expr=f'DF.then({expr}, f => DF.select(f, [DF.col("li")'+('' if kind in ['semi','anti'] else ', DF.col("ri")')+']))'
  rows=[]
  for a in range(nl):
   hits=[b for b in range(nr) if l[a] is not None and r[b]==l[a] and (len(keys)==1 or l2[a] is not None and l2[a]==r2[b])]
   if kind=='semi' and hits or kind=='anti' and not hits: rows.append([a])
   if kind in ['inner','left']:
    rows += [[a,b] for b in hits]
    if kind=='left' and not hits: rows.append([a,None])
  case(f'j{i}_{kind}',expr,rows)
for n in [0,1,8,16,32,64]:
 for k in sorted(set([0,1,n//8,min(n,n//8+1),n])):
  if k>n:continue
  frame(f'f{n}_{k}',{'id':list(range(n)), 'v':[None if i%3==0 else i for i in range(n)]})
  case(f'f{n}_{k}',f'DF.then(f{n}_{k}(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32({k}))))',[[i,None if i%3==0 else i] for i in range(k)])
s.append('def main() -> IO(Unit):\n  do IO<Unit>:\n'+'\n'.join(calls))
(out/'boundaries.bend').write_text('\n\n'.join(s)+'\n');(out/'boundaries_expected.json').write_text(json.dumps(expected))
