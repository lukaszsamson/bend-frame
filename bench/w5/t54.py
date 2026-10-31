#!/usr/bin/env python3
"""T5.4 micro-bench runner: interleaves the baseline and candidate builds of bench/w5/t54.bend (one stage
timed `reps` times per process), records the 1-minute load before and after every process, prints medians
and the raw per-process medians.

  python3 bench/w5/t54.py --k 10 --threads 1 12 --procs 5 --reps 15 [--bins base cand]

Binaries: build/t54/<name> (built by `bend bench/w5/t54.bend -o build/t54/cand`; the baseline from the
pinned checkout's copy of the file). The first rep of every process includes first-touch page faults:
it is reported separately and not in the median."""
import argparse, json, os, statistics, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def load1():
    return os.getloadavg()[0]


def run(binary, threads, k, reps, sales, prods):
    argv = [os.path.join(ROOT, "build/t54", binary), "+RTS", "--threads", str(threads), "-RTS", sales, prods, str(k), str(reps)]
    l0 = load1()
    t = time.time()
    p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=900)
    wall = time.time() - t
    l1 = load1()
    out = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
    try:
        j = json.loads(out)
    except json.JSONDecodeError:
        raise SystemExit(f"bad output from {binary}: {p.stdout!r} {p.stderr!r}")
    ms = j["ms"][1:-1]  # drop the placeholder 0 and the trailing 0
    return ms, (l0, l1), wall


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, nargs="+", default=[10])
    ap.add_argument("--threads", type=int, nargs="+", default=[1, 12])
    ap.add_argument("--procs", type=int, default=5)
    ap.add_argument("--reps", type=int, default=15)
    ap.add_argument("--bins", nargs="+", default=["base", "cand"])
    ap.add_argument("--sales", default="bench/data/sales_1000000.csv")
    ap.add_argument("--prods", default="bench/data/products.csv")
    a = ap.parse_args()
    print(f"# load at start {os.getloadavg()}")
    for k in a.k:
        res = {}
        for rep in range(a.procs):
            for t in a.threads:
                for b in a.bins:
                    ms, ld, wall = run(b, t, k, a.reps, a.sales, a.prods)
                    res.setdefault((b, t), []).append((ms, ld))
        print(f"## stage k={k}  procs={a.procs} reps={a.reps}  (ms per stage; per-process median in [], first rep kept out)")
        for t in a.threads:
            for b in a.bins:
                runs = res[(b, t)]
                allms = [x for ms, _ in runs for x in ms]
                meds = [statistics.median(ms) for ms, _ in runs]
                loads = [f"{l0:.1f}/{l1:.1f}" for _, (l0, l1) in runs]
                print(f"  {b:5s} t={t:2d}  median {statistics.median(allms):7.2f}  proc-medians {meds}  load {loads}")
        for t in a.threads:
            if len(a.bins) == 2:
                m0 = statistics.median([x for ms, _ in res[(a.bins[0], t)] for x in ms])
                m1 = statistics.median([x for ms, _ in res[(a.bins[1], t)] for x in ms])
                print(f"  t={t:2d}  {a.bins[1]}/{a.bins[0]} = {m1 / m0:.3f}")
        if len(a.threads) >= 2 and len(a.bins) == 2:
            for b in a.bins:
                m1 = statistics.median([x for ms, _ in res[(b, a.threads[0])] for x in ms])
                m12 = statistics.median([x for ms, _ in res[(b, a.threads[-1])] for x in ms])
                print(f"  {b}: {a.threads[0]}-vs-{a.threads[-1]} threads scaling {m1 / m12:.2f}x")
        print("  raw samples (ms), per process:")
        for t in a.threads:
            for b in a.bins:
                for ms, _ in res[(b, t)]:
                    print(f"    {b} t={t}: {ms}")


if __name__ == "__main__":
    main()
