#!/usr/bin/env python3
"""bench/w5/scale/matrix.py -- the controlled scaling matrix over bench/w5/scale/probe.bend (PROVISIONAL
numbers: shared machine; the 1-minute load is recorded per process).

  ~/.bend/bin/bend bench/w5/scale/probe.bend -o build/scale/probe
  python3 -I bench/w5/scale/matrix.py OUT.jsonl [--modes 0 2 4 5 9 11] [--threads 1 2 4 8 12] [--depth 10]
                                                [--procs 3] [--reps 8] [--gap 0]
  python3 -I bench/w5/scale/matrix.py --report OUT.jsonl

One fresh process per (mode, threads, round), the cells interleaved round by round; each process runs
`reps` reps in the io style and reports per-rep ms; the process's sample is the median of its reps after the
first (the cold one). The report prints, per mode and thread count, the median of the process samples, the
raw samples, the CPU time (user + sys, /usr/bin/time -l) and the load, and the speedup over 1 thread.
"""
import argparse
import json
import os
import re
import statistics as S
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
EXE = os.path.join(ROOT, "build/scale/probe")
NAMES = {0: "fold (leaf back)", 1: "fold, input dropped", 2: "fresh map, input dropped", 3: "fresh map, borrow",
         4: "in-place map", 5: "fresh map + fold (both die)", 6: "fold, no fork (sequential)", 9: "no leaf work",
         10: "fold, flat helper in branch arg", 11: "fold over a List, Lst.pmap (T5.3's shape)"}


def one(mode, threads, depth, reps, gap):
    argv = ["/usr/bin/time", "-l", EXE, "+RTS", "--threads", str(threads), "-RTS", str(mode), str(depth), str(reps), "io", str(gap)]
    l0 = os.getloadavg()[0]
    p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=600)
    l1 = os.getloadavg()[0]
    out = json.loads(p.stdout.strip().splitlines()[-1])
    ms = [x for x in out["ms"][:-1]]
    m = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", p.stderr)
    row = {"mode": mode, "threads": threads, "depth": depth, "reps": ms, "check": out["check"], "load0": round(l0, 2),
           "load1": round(l1, 2), "sample": S.median(ms[1:]) if len(ms) > 1 else ms[0]}
    if m:
        row["real"], row["user"], row["sys"] = (float(x) for x in m.groups())
    for line in p.stderr.splitlines():
        if line.strip().endswith("page reclaims"):
            row["reclaims"] = int(line.split()[0])
        if line.strip().endswith("involuntary context switches"):
            row["icsw"] = int(line.split()[0])
    return row


def report(path):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    cells = {}
    for r in rows:
        cells.setdefault((r["mode"], r["threads"]), []).append(r)
    modes = sorted({r["mode"] for r in rows})
    threads = sorted({r["threads"] for r in rows})
    loads = [r["load0"] for r in rows]
    print(f"load (1-min) over the run: {min(loads)}-{max(loads)}; {len(rows)} processes; depth {rows[0]['depth']}")
    print("| mode | " + " | ".join(f"{t} thr" for t in threads) + " | speedup (max thr vs 1) | checks equal |")
    print("|---|" + "---|" * (len(threads) + 2))
    for m in modes:
        med = {}
        cols = []
        for t in threads:
            rs = cells.get((m, t), [])
            if not rs:
                cols.append("-")
                continue
            samples = [r["sample"] for r in rs]
            med[t] = S.median(samples)
            cpu = S.median([r.get("user", 0) + r.get("sys", 0) for r in rs])
            cols.append(f"{med[t]:.1f} ms (raw {', '.join(f'{s:g}' for s in samples)}; cpu {cpu:.2f} s)")
        sp = f"{med[threads[0]] / med[threads[-1]]:.1f}x" if threads[0] in med and threads[-1] in med and med[threads[-1]] > 0 else "-"
        checks = {r["check"] for t in threads for r in cells.get((m, t), [])}
        print(f"| {m} {NAMES.get(m, '')} | " + " | ".join(cols) + f" | {sp} | {'yes' if len(checks) == 1 else 'NO'} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--modes", type=int, nargs="+", default=[0, 2, 4, 5, 9, 11])
    ap.add_argument("--threads", type=int, nargs="+", default=[1, 2, 4, 8, 12])
    ap.add_argument("--depth", type=int, default=10)
    ap.add_argument("--procs", type=int, default=3)
    ap.add_argument("--reps", type=int, default=8)
    ap.add_argument("--gap", type=int, default=0)
    a = ap.parse_args()
    if a.report:
        report(a.out)
        return
    with open(a.out, "a") as f:
        for rnd in range(a.procs):
            for m in a.modes:
                for t in a.threads:
                    r = one(m, t, a.depth, a.reps, a.gap)
                    f.write(json.dumps(r) + "\n")
                    f.flush()
                    print(f"r{rnd} mode={m} t={t} sample={r['sample']} reps={r['reps']} load={r['load0']}", flush=True)
    report(a.out)


if __name__ == "__main__":
    main()
