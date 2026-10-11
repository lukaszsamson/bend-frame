"""List constructor ids of an emitted Bend C file with arity and hot (refcount-sealed) flag.
    python3 tools/hot.py build/x.c [NAME ...]     # every hot ctr, or just the named ones
A hot constructor's fields are rfc_seal'ed at every construction (one extra heap cell per
field holding a boxed value) and taking a hot node apart is ctr_take on a counted cell.
"""
import re
import sys

src = open(sys.argv[1]).read()
names = {int(i): n for n, i in re.findall(r"#define CID_([A-Z0-9_]+) (\d+)\n", src)}
tab = re.search(r"CID_T\[\]\[2\] = \{(.*?)\};", src, re.S).group(1)
rows = [tuple(map(int, t)) for t in re.findall(r"\{ (\d+), (\d+) \}", tab)]
args = sys.argv[2:]
cold = "--cold" in args
want = {w.upper() for w in args if w != "--cold"}
print(f"# {len(rows)} constructors, {sum(h for _, h in rows)} hot")
for i, (ar, hot) in enumerate(rows):
    n = names.get(i, f"#{i}")
    if (want and any(w in n for w in want)) or (not want and hot != cold):
        print(f"{i:4d} {n:32s} arity={ar} hot={hot}")
