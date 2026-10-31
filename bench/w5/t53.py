#!/usr/bin/env python3
"""T5.3 runner (PROVISIONAL numbers, plans/M_02.txt section 5): interleaved fresh processes of bench/w5/t53.bend's
native binary (build/t53/t53): for every op, round and thread count, mode 0 (reference collect), mode 1 (chunked
collect from a flat env frame: the conversions inside the compute window) and mode 2 (chunked over a pre-chunked
source: in / compute / out apart, G6). Every process does `reps` reps; the first two reps of a process are dropped
(first-touch page faults, warm-up) and the median of the rest is the process's sample. The 1-minute load is
recorded before and after every process. One JSON line per process goes to the output file; then medians,
ranges and raw samples per cell, and the 12-vs-1 scaling of compute.

  python3 -I bench/w5/t53.py OUT.jsonl [--ops q1 q2 q3 q5 filter] [--threads 1 4 12] [--procs 5] [--reps 12]
  python3 -I bench/w5/t53.py --report OUT.jsonl
"""
import argparse, json, os, statistics as S, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
EXE = os.path.join(ROOT, "build/t53/t53")
SALES = "bench/data/sales_1000000.csv"
PRODS = "bench/data/products.csv"
PARAM = {"filter": 50}


def one(op, mode, threads, reps):
    argv = [EXE, "+RTS", "--threads", str(threads), "-RTS", SALES, PRODS, op, str(mode), str(reps), str(PARAM.get(op, 0))]
    l0 = os.getloadavg()[0]
    t = time.time()
    p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=1800)
    wall = time.time() - t
    l1 = os.getloadavg()[0]
    j = json.loads(p.stdout.strip().splitlines()[-1])
    rows = [r for r in j["reps"] if r][2:]
    med = [S.median(c) for c in zip(*rows)]
    return {"op": op, "mode": mode, "threads": threads, "reps": rows, "in": med[0], "compute": med[1], "out": med[2],
            "check": med[3], "chk": j["chk"], "stats": j.get("stats", ""), "load_before": round(l0, 2),
            "load_after": round(l1, 2), "wall_s": round(wall, 2)}


def report(path):
    recs = [json.loads(l) for l in open(path)]
    cells = {}
    for r in recs:
        cells.setdefault((r["op"], r["mode"], r["threads"]), []).append(r)
    loads = [r["load_before"] for r in recs] + [r["load_after"] for r in recs]
    print(f"# {len(recs)} processes, 1-minute load {min(loads)}..{max(loads)}")
    print("| op | mode | thr | in ms | compute ms | out ms | compute+out | raw compute (per process) |")
    print("|---|---|---|---|---|---|---|---|")
    med = {}
    for k in sorted(cells):
        rs = cells[k]
        f = lambda key: S.median(r[key] for r in rs)
        co = S.median(r["compute"] + r["out"] for r in rs)
        med[k] = (f("compute"), co)
        print(f"| {k[0]} | {k[1]} | {k[2]} | {f('in')} | {f('compute')} | {f('out')} | {co} | {[r['compute'] for r in rs]} |")
    print()
    print("| op | mode | compute 1 thr | compute 12 thr | 12-vs-1 | compute+out 12-vs-1 |")
    print("|---|---|---|---|---|---|")
    for (op, mode, t), (c, co) in sorted(med.items()):
        if t == 1 and (op, mode, 12) in med:
            c12, co12 = med[(op, mode, 12)]
            print(f"| {op} | {mode} | {c} | {c12} | {c / c12 if c12 else float('inf'):.2f} | {co / co12 if co12 else float('inf'):.2f} |")
    chks = {}
    for r in recs:
        chks.setdefault(r["op"], set()).add(r["chk"])
    print("\nresult hashes per op (one value = every mode agrees):", {k: sorted(v) for k, v in chks.items()})


def main():
    if sys.argv[1:2] == ["--report"]:
        return report(sys.argv[2])
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--ops", nargs="+", default=["q1", "q2", "q3", "q5", "filter"])
    ap.add_argument("--threads", type=int, nargs="+", default=[1, 4, 12])
    ap.add_argument("--modes", type=int, nargs="+", default=[0, 1, 2])
    ap.add_argument("--procs", type=int, default=5)
    ap.add_argument("--reps", type=int, default=12)
    a = ap.parse_args()
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    with open(a.out, "a") as f:
        for rnd in range(a.procs):
            for op in a.ops:
                for t in a.threads:
                    for m in a.modes:
                        r = one(op, m, t, a.reps)
                        r["round"] = rnd
                        f.write(json.dumps(r) + "\n")
                        f.flush()
                        print(f"r{rnd} {op} m{m} t{t} in={r['in']} compute={r['compute']} out={r['out']} load={r['load_before']}", flush=True)
    report(a.out)


if __name__ == "__main__":
    main()
