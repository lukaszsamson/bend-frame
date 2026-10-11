#!/usr/bin/env python3
"""bench/w5/scale/sample.py -- start a native probe and take a `sample` of its threads while it runs.

  python3 -I bench/w5/scale/sample.py OUT.txt SECONDS -- BINARY ARGS...

Writes the sample report (every thread's call stacks, the runtime's C function names are kept) to OUT.txt
and prints the top-level summary lines (the thread states: which fraction of the samples each thread
spent in sched_yield / pthread_cond_wait / the leaf loops / the fault handler).
"""
import subprocess
import sys
import time


def main():
    args = sys.argv[1:]
    out = args.pop(0)
    secs = args.pop(0)
    assert args.pop(0) == "--"
    p = subprocess.Popen(args, stdout=subprocess.DEVNULL)
    time.sleep(0.05)
    s = subprocess.run(["sample", str(p.pid), secs, "-mayDie", "-file", out], capture_output=True, text=True)
    p.wait()
    print(s.stdout[-400:], s.stderr[-400:])


if __name__ == "__main__":
    main()
