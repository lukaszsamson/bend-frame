"""M6 re-measured benchmark (plans/M_01.txt section 7 M6): q1..q6 at 1k/100k/1M, Bend (default Auto
strings, default optimizer) vs Bend with `optimize_full` (BF_OPT=full) vs Polars 2.0.0, at 1 and 12
threads, ONE measurement per process, `--reps` processes per cell (median reported), peak RSS from
/usr/bin/time -l, the 1-minute load average recorded before every run. The variants are interleaved
within each repetition (order rotated) so a load change hits all of them alike.

  uv run --project bench python bench/m6.py run [--sizes 1000 100000 1000000] [--queries q1 ..] [--reps 5]
        [--variants bend full polars] [--out bench/results/m6.jsonl]
  uv run --project bench python bench/m6.py table bench/results/m6.jsonl     # markdown tables
  uv run --project bench python bench/m6.py pworker q n                       # (internal) a Polars measurement

Bend: ./build/bench [--threads 1] sales.csv q 1 <batch> <label>; batches as scripts/bench.sh (1k: 500 for q1/q2,
40 otherwise; 100k q2: 8; 1M q2: 3; else 1). Polars: parsed untimed, 5 collects in the process; "first" = the
first collect (a cold process, like Bend's), "best" = the minimum of the five (run_polars.py's number).
"threads": 1 or "default" (= all 12 cores for both engines; Polars: POLARS_MAX_THREADS unset / =1).
"""
import argparse
import json
import os
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def batch_for(n, q):
    if n == 1000:
        return 500 if q in ("q1", "q2") else 40
    if n == 100000:
        return 8 if q == "q2" else 1
    return 3 if q == "q2" else 1


def run_cmd(cmd, env=None):
    e = dict(os.environ)
    e.update(env or {})
    p = subprocess.run(["/usr/bin/time", "-l"] + cmd, cwd=ROOT, env=e, capture_output=True, text=True)
    m = re.search(r"(\d+)\s+maximum resident set size", p.stderr)
    line = next((l for l in p.stdout.splitlines() if l.startswith("{")), None)
    return line, (int(m.group(1)) if m else None), (p.stdout + p.stderr)[-300:]


def pworker(q, n):
    sys.path.insert(0, str(HERE))
    from queries import QUERIES, load
    sales, products = load(HERE / "data" / f"sales_{n}.csv", HERE / "data" / "products.csv")
    ts = []
    for _ in range(5):
        a = time.perf_counter()
        QUERIES[q](sales, products).collect()
        ts.append(time.perf_counter() - a)
    print(json.dumps({"first": ts[0], "best": min(ts), "all": ts}))


def measure(variant, q, n, th):
    csv = f"bench/data/sales_{n}.csv"
    if variant in ("bend", "full"):
        cmd = ["./build/bench"] + (["--threads", "1"] if th == "1" else []) + [csv, q, "1", str(batch_for(n, q)), th]
        line, rss, tail = run_cmd(cmd, {"BF_OPT": "full"} if variant == "full" else {})
        sec = json.loads(line)["seconds"] if line else None
        return {"seconds": sec, "rss": rss} if sec is not None else {"error": tail, "rss": rss}
    cmd = [sys.executable, str(HERE / "m6.py"), "pworker", q, str(n)]
    line, rss, tail = run_cmd(cmd, {"POLARS_MAX_THREADS": "1"} if th == "1" else {})
    if not line:
        return {"error": tail}
    r = json.loads(line)
    return {"seconds": r["first"], "best": r["best"], "rss": rss}


def run_mode(a):
    out = open(a.out, "a")
    for n in a.sizes:
        for q in a.queries:
            for rep in range(a.reps):
                combos = [(v, th) for v in a.variants for th in ("1", "default")]
                k = rep % len(combos)
                for v, th in combos[k:] + combos[:k]:
                    l0 = os.getloadavg()[0]
                    r = measure(v, q, n, th)
                    r.update({"variant": v, "q": q, "n": n, "threads": th, "rep": rep, "load1": round(l0, 1)})
                    out.write(json.dumps(r) + "\n")
                    out.flush()
                    print(r, flush=True)


def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def fms(x):
    if x is None:
        return "n/a"
    v = x * 1000
    return f"{v:.2f}" if v < 100 else f"{v:.0f}"


def fr(a, b):
    return "n/a" if not a or not b else (f"{a / b:.0f}x" if a / b >= 10 else f"{a / b:.1f}x")


def fmb(x):
    return "n/a" if x is None else f"{x / 1e6:.0f}"


def table_mode(a):
    recs = [json.loads(l) for p in a.files for l in open(p) if l.strip()]
    cell = {}
    for r in recs:
        if "error" in r and r.get("seconds") is None:
            print("ERROR", r)
            continue
        cell.setdefault((r["n"], r["q"], r["variant"], r["threads"]), []).append(r)

    def m(n, q, v, th, key=None):
        # Polars' headline number is the warm one (best of the 5 collects in the process, median over the
        # processes: run_polars.py's methodology); its cold first collect is the second table
        key = key or ("best" if v == "polars" else "seconds")
        return med([r.get(key) for r in cell.get((n, q, v, th), [])])

    def spread(n, q, v, th):
        xs = [r["seconds"] for r in cell.get((n, q, v, th), [])]
        return (min(xs), max(xs)) if xs else (None, None)

    keys = sorted({(n, q) for n, q, _, _ in cell}, key=lambda k: (k[0], k[1]))
    print("| q | n | Bend 1t ms | Polars 1t ms | ratio | Bend 12t ms | Polars 12t ms | ratio | Bend RSS MB (1t) | Polars RSS MB (1t) | load1 min..max |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|")
    for n, q in keys:
        loads = [r["load1"] for t in ("1", "default") for v in ("bend", "polars") for r in cell.get((n, q, v, t), [])]
        b1, p1, ba, pa = m(n, q, "bend", "1"), m(n, q, "polars", "1"), m(n, q, "bend", "default"), m(n, q, "polars", "default")
        print(f"| {q} | {n:,} | {fms(b1)} | {fms(p1)} | {fr(b1, p1)} | {fms(ba)} | {fms(pa)} | {fr(ba, pa)} | "
              f"{fmb(m(n, q, 'bend', '1', 'rss'))} | {fmb(m(n, q, 'polars', '1', 'rss'))} | {min(loads):.0f}..{max(loads):.0f} |")
    print()
    print("Polars cold: the FIRST collect of a fresh process (like Bend's one measurement per process), median over processes, ms;")
    print("ratio = Bend / Polars-cold")
    print("| q | n | Polars cold 1t | ratio | Polars cold 12t | ratio |")
    print("|---|---:|---:|---:|---:|---:|")
    for n, q in keys:
        c1, ca = m(n, q, "polars", "1", "seconds"), m(n, q, "polars", "default", "seconds")
        print(f"| {q} | {n:,} | {fms(c1)} | {fr(m(n, q, 'bend', '1'), c1)} | {fms(ca)} | {fr(m(n, q, 'bend', 'default'), ca)} |")
    print()
    print("optimize_full vs default (Bend, median ms; ratio full/default; per-cell min..max of the 5 runs for default)")
    print("| q | n | default 1t | full 1t | full/default | default 12t | full 12t | full/default |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for n, q in keys:
        d1, f1, da, fa = m(n, q, "bend", "1"), m(n, q, "full", "1"), m(n, q, "bend", "default"), m(n, q, "full", "default")
        if f1 is None and fa is None:
            continue
        print(f"| {q} | {n:,} | {fms(d1)} | {fms(f1)} | {fr(f1, d1)} | {fms(da)} | {fms(fa)} | {fr(fa, da)} |")
    print()
    print("spread (min..max ms) of the Bend default runs")
    for n, q in keys:
        lo1, hi1 = spread(n, q, "bend", "1")
        loa, hia = spread(n, q, "bend", "default")
        print(f"- {q} {n:,}: 1t {fms(lo1)}..{fms(hi1)}, 12t {fms(loa)}..{fms(hia)}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("mode")
    ap.add_argument("rest", nargs="*")
    ap.add_argument("--sizes", nargs="+", type=int, default=[1000, 100000, 1000000])
    ap.add_argument("--queries", nargs="+", default=["q1", "q2", "q3", "q4", "q5", "q6"])
    ap.add_argument("--variants", nargs="+", default=["bend", "full", "polars"])
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--out", default=str(HERE / "results" / "m6.jsonl"))
    a = ap.parse_args()
    if a.mode == "pworker":
        pworker(a.rest[0], int(a.rest[1]))
    elif a.mode == "run":
        run_mode(a)
    else:
        a.files = a.rest
        table_mode(a)
