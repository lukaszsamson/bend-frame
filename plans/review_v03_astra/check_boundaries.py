from pathlib import Path
import json
p=Path(__file__).parent
want=json.loads((p/'boundaries_expected.json').read_text())
got={}
for block in (p/'boundaries.out').read_text().split('CASE ')[1:]:
 lines=block.splitlines(); tag=lines[0]
 if 'error\t' in block: raise AssertionError(block)
 got[tag]=[[None if c=='null' else int(c) for c in l.split('\t')[1:]] for l in lines if l.startswith('row\t')]
assert got.keys()==want.keys(), (got.keys(),want.keys())
for name, rows in want.items(): assert got[name]==rows, (name,rows,got[name])
print(f'{len(want)} independent expected-result cases passed')
