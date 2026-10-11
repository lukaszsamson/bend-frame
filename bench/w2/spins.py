"""Per spin_N loop of an emitted Bend C file: its parameter names (the Bend parameters, as the
emitted C keeps them in `u32 _name_k = rK;` lines), and the count / copy / allocation operations in
its body, so a kernel's spin loop can be NAMED and checked for per-iteration allocation.

    python3 bench/w2/spins.py build/w2/w2.c [name-fragment ...]

Prints every spin function whose parameter list contains ALL the fragments (all of them when none
are given), with: rfc_seal / ctr_take / term_keep (refcount traffic), blk_copy / blk_half / blk_node
(array copies), heap_alloc / task_node (allocation, forks), blk_read / blk_write (flat array
access), and the spin loops it calls. A flat kernel loop shows only blk_read / blk_write; one that
shows heap_alloc or rfc_seal allocates every iteration (a boxed record or pair). Names follow
tools/cops.py of bench/spikes/w0_strings.
"""
import re
import sys

src = open(sys.argv[1]).read()
frags = sys.argv[2:]
starts = [m.start() for m in re.finditer(r"\nINLINE Term spin_\d+\(|\nstatic [^\n]*\(|\nOUTLINE [^\n]*\(", src)] + [len(src)]
ops = ["term_keep", "rfc_seal", "ctr_take", "blk_copy", "blk_half", "blk_node", "heap_alloc", "task_node", "blk_read", "blk_write"]
for a, b in zip(starts, starts[1:]):
    body = src[a:b]
    m = re.match(r"\nINLINE Term (spin_\d+)\(", body)
    if not m:
        continue
    names = re.findall(r"\b(?:u32|Term|u64) _([a-z0-9_]+?)_\d+ = r\d+;", body)
    if not all(any(f == n or f in n for n in names) for f in frags):
        continue
    calls = sorted(set(re.findall(r"(spin_\d+)\(e", body)) - {m.group(1)})
    cnt = {o: body.count(o + "(") for o in ops}
    print(f"{m.group(1):9s} lines={body.count(chr(10)):4d} params={','.join(names)}")
    print("          " + (" ".join(f"{k}={v}" for k, v in cnt.items() if v) or "(no count / copy / alloc ops)") + (f"  calls={','.join(calls)}" if calls else ""))
