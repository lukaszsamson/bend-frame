#!/usr/bin/env python3
"""Per-spin-loop allocation / refcount audit of a Bend-emitted C file (bend x.bend -o x.c).
For every `INLINE Term spin_N(...)` function: its parameter count and the counts of term_keep,
ctr_take, rfc_seal (refcount traffic), blk_new / blk_copy / blk_half / blk_node (block allocation
and copies) and term_ctr (boxed constructor allocation) inside its body. A flat kernel loop should
show zero keeps / takes / seals / blk_copy / blk_half / blk_node and no term_ctr per iteration.
Usage: cstats.py build/s1.c [--min-params 8] [--names spin_27,spin_28]"""
import re, sys

path = sys.argv[1]
min_params = 0
names = None
if '--min-params' in sys.argv:
    min_params = int(sys.argv[sys.argv.index('--min-params') + 1])
if '--names' in sys.argv:
    names = set(sys.argv[sys.argv.index('--names') + 1].split(','))
src = open(path).read()
funcs = list(re.finditer(r'^INLINE Term (spin_\d+)\(([^)]*)\) \{', src, re.M))
tokens = ['term_keep', 'ctr_take', 'rfc_seal', 'blk_new', 'blk_copy', 'blk_half', 'blk_node', 'term_ctr', 'blk_get', 'blk_set']
print(f"{'spin':9}{'line':>6}{'params':>7} " + ' '.join(f'{t:>9}' for t in tokens))
for i, m in enumerate(funcs):
    start = m.end()
    end = funcs[i + 1].start() if i + 1 < len(funcs) else len(src)
    body = src[start:end]
    # the body ends at the first line that is just "}" at column 0
    cut = re.search(r'^\}', body, re.M)
    if cut:
        body = body[:cut.start()]
    params = [p for p in m.group(2).split(',') if p.strip()]
    nparams = len(params) - 2  # Env e, THR Term* o
    if nparams < min_params:
        continue
    if names and m.group(1) not in names:
        continue
    line = src[:m.start()].count('\n') + 1
    counts = [body.count(t) for t in tokens]
    print(f"{m.group(1):9}{line:>6}{nparams:>7} " + ' '.join(f'{c:>9}' for c in counts))
