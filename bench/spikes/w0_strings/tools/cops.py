"""Per spin_N loop of an emitted Bend C file: the count / copy / allocation operations it contains.
    python3 tools/cops.py build/x.c [needle ...]
Prints every spin function that contains all the needles (substrings of its body, e.g. a
constant like 16777216 that identifies a kernel), with its counts of term_keep / rfc_seal /
ctr_take (refcount traffic), blk_copy / blk_half / blk_node (array copies), heap_alloc and
task_node (allocation, forks) and blk_read / blk_write (flat array access). A flat kernel shows
only blk_read / blk_write; a cons walk shows ctr_take per cell (an atomic on a hot type).
"""
import re
import sys

src = open(sys.argv[1]).read()
needles = sys.argv[2:]
starts = [m.start() for m in re.finditer(r"\nINLINE Term spin_\d+\(|\nstatic [^\n]*\(|\nOUTLINE [^\n]*\(", src)] + [len(src)]
ops = ["term_keep", "rfc_seal", "ctr_take", "blk_copy", "blk_half", "blk_node", "heap_alloc", "task_node", "blk_read", "blk_write", "spin_"]
for a, b in zip(starts, starts[1:]):
    body = src[a:b]
    m = re.match(r"\nINLINE Term (spin_\d+)\(", body)
    if not m or not all(n in body for n in needles):
        continue
    calls = sorted(set(re.findall(r"(spin_\d+)\(e", body)) - {m.group(1)})
    cnt = {o: body.count(o + "(") for o in ops if o != "spin_"}
    print(f"{m.group(1):9s} lines={body.count(chr(10)):4d} " + " ".join(f"{k}={v}" for k, v in cnt.items() if v) + (f" calls={','.join(calls)}" if calls else ""))
