#!/usr/bin/env python3
"""bench/w5/scale/fids.py -- the task-table flags of the defs in an emitted C file.

  python3 -I bench/w5/scale/fids.py FILE.c [SUBSTRING ...]

Prints `fid name arity nofk` for every def whose FID name contains one of the substrings (all defs when
none is given). `nofk` = the runtime's fork-free flag (FID_T[x][2] & 2): a fork-free def called from a
forking def in non-sequential mode becomes a task of its own, which the grow pass of the scheduler does
not run (monk_step skips it: "a growing lane skips a fork-free one").
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
    for i, (ar, rw, fl) in enumerate(rows):
        name = fids.get(i, "?")
        if not want or any(w in name for w in want):
            print(i, name, "arity", ar, "resw", rw, "nofk", (int(fl) & 2) >> 1)


if __name__ == "__main__":
    main()
