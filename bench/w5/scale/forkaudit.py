#!/usr/bin/env python3
"""bench/w5/scale/forkaudit.py -- find the fork-tree stall shape in an emitted Bend C file.

  ~/.bend/bin/bend x.bend -o x.c && python3 -I bench/w5/scale/forkaudit.py x.c [NAME_SUBSTRING ...]

The runtime (2.0.36) grows a fork tree breadth-first (the grow pass) by running the tasks whose def can
fork; a task whose def is fork-free (FID_T flag 2) is never run by the grow pass. A forking def that CALLS a
non-flat fork-free def before its parallel let compiles that call to `task_node(.., 0); return term_tsk(..)`
in non-sequential mode: the call becomes a task of its own, the grow pass pushes it back and stops growing
the row, and the drain then runs it in sequential mode together with its continuation, the parallel let
included, so the whole subtree below runs on one thread (DESIGN.md 16.10). This script lists every
`return term_tsk(FID_Y ..)` inside a segment of a forking def (a `WL_CASE` whose FID is not fork-free),
i.e. every call that can stall a fork tree, as `forking def -> called def`. The join continuations after
a parallel let are fork-free and are not listed; a call there runs in place. A def that forks only at its
ROOT (called from the sequential program, not from inside another fork tree) is harmless and shows up
too: read the list against the recursion (is the forking def the recursive walker itself?).
"""
import re
import sys


def main():
    path = sys.argv[1]
    want = sys.argv[2:]
    src = open(path).read()
    fids = {int(m.group(2)): m.group(1) for m in re.finditer(r"#define (FID_\w+) (\d+)\n", src)}
    tab = re.search(r"CONSTV u8 FID_T\[\]\[3\] = \{(.*?)\};", src, re.S).group(1)
    rows = re.findall(r"\{ (\d+), (\d+), (\d+) \}", tab)
    nofk = {fids[i]: (int(fl) & 2) >> 1 for i, (ar, rw, fl) in enumerate(rows) if i in fids}
    cases = re.split(r"\n  WL_CASE\((FID_\w+)\)\n", src)
    found = []
    for i in range(1, len(cases), 2):
        name, body = cases[i], cases[i + 1]
        if nofk.get(name, 1):
            continue
        for m in re.finditer(r"return term_tsk\((FID_\w+),", body):
            callee = m.group(1)
            if not nofk.get(callee, 0):
                continue  # a forking callee is entered directly (WL_JMP); the guard is fid_nofk(callee)
            if want and not any(w in name or w in callee for w in want):
                continue
            found.append((name, callee))
    for name, callee in found:
        print(f"{name} -> {callee}")
    print(f"{len(found)} call task(s) inside forking segments")


if __name__ == "__main__":
    main()
