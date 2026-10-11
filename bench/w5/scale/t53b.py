#!/usr/bin/env python3
"""bench/w5/scale/t53b.py -- the pre-chunked compute of the chunked engine BATCHED above the 1 ms clock
(bench/w5/t53.bend mode 3: K = 8 chunked copies of the sales frame run in one window, the window reported in
microseconds per run). PROVISIONAL numbers: shared machine, the 1-minute load recorded per process.

  ~/.bend/bin/bend bench/w5/t53.bend -o build/t53/t53
  python3 -I bench/w5/scale/t53b.py OUT.jsonl [--ops q1 q2 filter q3 q5] [--threads 1 4 12] [--procs 5] [--reps 6]
  python3 -I bench/w5/scale/t53b.py --report OUT.jsonl

One process per (op, threads, round), interleaved; a process's sample is the median of its reps after the
first two (microseconds per run, /1000 = ms). The report gives medians, raw samples, the load range and the
12-vs-1 and 4-vs-1 ratios, with the 16.8 thresholds beside them.
"""
import argparse
import json
import os
import statistics as S
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
EXE = os.path.join(ROOT, "build/t53/t53")
SALES = "bench/data/sales_1000000.csv"
PRODS = "bench/data/products.csv"
PARAM = {"filter": 50}
G2 = {"q1": 3.0, "q2": 3.0, "q3": 2.0, "q5": 1.5, "filter": 3.0}


def one(op, threads, reps):
    argv = [EXE, "--threads", str(threads), SALES, PRODS, op, "3", str(reps), str(PARAM.get(op, 0))]
    l0 = os.getloadavg()[0]
    p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=1800)
    l1 = os.getloadavg()[0]
    j = json.loads(p.stdout.strip().splitlines()[-1])
    rows = [r for r in j["reps"] if r]
    us = [r[1] for r in rows]
    return {"op": op, "threads": threads, "us": us, "sample_ms": S.median(us[2:]) / 1000 if len(us) > 2 else us[-1] / 1000,
            "out_ms": S.median(r[2] for r in rows), "chk": j["chk"], "load0": round(l0, 2), "load1": round(l1, 2), "stats": j["stats"]}


def report(path):
    recs = [json.loads(l) for l in open(path) if l.strip()]
    cells = {}
    for r in recs:
        cells.setdefault((r["op"], r["threads"]), []).append(r)
    loads = [r["load0"] for r in recs] + [r["load1"] for r in recs]
    ops = sorted({r["op"] for r in recs})
    threads = sorted({r["threads"] for r in recs})
    print(f"# {len(recs)} processes, 1-minute load {min(loads)}..{max(loads)}; compute = CX.run_x over a pre-chunked "
          f"source, ms per run (window of 8 runs / 8)")
    print("| op | " + " | ".join(f"{t} thr: median (raw per process)" for t in threads) + " | 4-vs-1 | 12-vs-1 | 16.8 G2 | hashes |")
    print("|---|" + "---|" * (len(threads) + 4))
    for op in ops:
        med = {}
        cols = []
        for t in threads:
            rs = cells.get((op, t), [])
            if not rs:
                cols.append("-")
                continue
            ss = [r["sample_ms"] for r in rs]
            med[t] = S.median(ss)
            cols.append(f"{med[t]:.2f} ({', '.join(f'{s:.2f}' for s in ss)})")
        r4 = f"{med[1] / med[4]:.2f}x" if 1 in med and 4 in med else "-"
        r12 = f"{med[1] / med[12]:.2f}x" if 1 in med and 12 in med else "-"
        chks = {r["chk"] for t in threads for r in cells.get((op, t), [])}
        print(f"| {op} | " + " | ".join(cols) + f" | {r4} | {r12} | >= {G2.get(op, '-')}x | {'equal' if len(chks) == 1 else 'DIFFER'} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--ops", nargs="+", default=["q1", "q2", "filter", "q3", "q5"])
    ap.add_argument("--threads", type=int, nargs="+", default=[1, 4, 12])
    ap.add_argument("--procs", type=int, default=5)
    ap.add_argument("--reps", type=int, default=6)
    a = ap.parse_args()
    if a.report:
        report(a.out)
        return
    with open(a.out, "a") as f:
        for rnd in range(a.procs):
            for op in a.ops:
                for t in a.threads:
                    r = one(op, t, a.reps)
                    f.write(json.dumps(r) + "\n")
                    f.flush()
                    print(f"r{rnd} {op} t{t} sample={r['sample_ms']:.2f} ms us={r['us']} load={r['load0']}", flush=True)
    report(a.out)


if __name__ == "__main__":
    main()
