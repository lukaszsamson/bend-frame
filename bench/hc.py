"""M6 high-cardinality workloads: generator, Polars reference and comparison.

  uv run --project bench python bench/hc.py gen 100000 1000000     # bench/data/hc/{t,dim}_<n>.csv
  uv run --project bench python bench/hc.py run [--sizes 100000 1000000] [--reps 5] [--threads 1 12] [--out F.jsonl]

t(k str, v u32, x f32): n rows, every k DISTINCT (random 8..14 lowercase letters + a base-36 row id).
dim(k str, w u32): 90 % of t's keys, shuffled, plus n/10 keys that are not in t. Operations (bench/m6.bend `hc`):
  group   t.group_by(k).agg(sum v as vs, len as n)        (first-appearance order)
  unique  t.select(k).unique(subset k)                     (first-appearance order)
  join    t.join(dim, k, inner)
`run` times each op in Bend (build/m6, one process per measurement, peak RSS from /usr/bin/time -l, load average
recorded) and checks the result CSV against Polars 2.0.0 on the same files: group/unique as ordered frames
(Polars `maintain_order=True` / `unique(maintain_order=True)`), join as a multiset (rows sorted by k) because
the join's row order is not part of the contract. Polars is timed (median of `reps` processes' first collect and
min-of-5 in-process) with the same files.
"""
import argparse
import json
import os
import random
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = HERE / "data" / "hc"
LETTERS = "abcdefghijklmnopqrstuvwxyz"
B36 = "0123456789abcdefghijklmnopqrstuvwxyz"


def b36(i: int) -> str:
    s = ""
    while True:
        s = B36[i % 36] + s
        i //= 36
        if i == 0:
            return s


def gen(n: int) -> None:
    DATA.mkdir(parents=True, exist_ok=True)
    rng = random.Random(n)
    keys = ["".join(rng.choice(LETTERS) for _ in range(rng.randint(8, 14))) + b36(i) for i in range(n)]
    assert len(set(keys)) == n, "keys not distinct"
    with open(DATA / f"t_{n}.csv", "w") as f:
        f.write("k,v,x\n")
        for i, k in enumerate(keys):
            f.write(f"{k},{i % 1000},{(i % 977) / 8:.2f}\n")
    dim = [k for i, k in enumerate(keys) if i % 10 != 3]
    dim += ["zz_missing_" + b36(i) for i in range(n // 10)]
    rng.shuffle(dim)
    with open(DATA / f"dim_{n}.csv", "w") as f:
        f.write("k,w\n")
        for i, k in enumerate(dim):
            f.write(f"{k},{(i * 7) % 100003}\n")


def polars_ref(op: str, n: int):
    import polars as pl
    t = pl.read_csv(DATA / f"t_{n}.csv", schema={"k": pl.String, "v": pl.UInt32, "x": pl.Float32})
    d = pl.read_csv(DATA / f"dim_{n}.csv", schema={"k": pl.String, "w": pl.UInt32})
    return t, d


def polars_query(op, t, d):
    import polars as pl
    lt = t.lazy()
    if op == "group":
        return lt.group_by("k", maintain_order=True).agg(pl.col("v").sum().alias("vs"), pl.len().alias("n"))
    if op == "unique":
        return lt.select("k").unique(subset=["k"], maintain_order=True)
    return lt.join(d.lazy(), on="k", how="inner")


def polars_worker(op, n):
    import polars as pl
    t, d = polars_ref(op, n)
    ts = []
    for _ in range(5):
        a = time.perf_counter()
        polars_query(op, t, d).collect()
        ts.append(time.perf_counter() - a)
    print(json.dumps({"first": ts[0], "best": min(ts)}))


def run_cmd(cmd, env=None):
    e = dict(os.environ)
    e.update(env or {})
    a = time.time()
    p = subprocess.run(["/usr/bin/time", "-l"] + cmd, cwd=ROOT, env=e, capture_output=True, text=True)
    m = re.search(r"(\d+)\s+maximum resident set size", p.stderr)
    line = next((l for l in p.stdout.splitlines() if l.startswith("{") or l.startswith("error")), p.stdout[-200:] + p.stderr[-200:])
    return line, int(m.group(1)) if m else None, time.time() - a


def compare(op, n, out) -> str:
    import polars as pl
    t, d = polars_ref(op, n)
    exp = polars_query(op, t, d).collect()
    got = pl.read_csv(out, schema=exp.schema)
    if op == "join":
        cols = sorted(exp.columns)
        exp, got = exp.select(cols).sort(cols), got.select(cols).sort(cols)
    elif got.columns != exp.columns:
        return f"FAIL columns {got.columns} != {exp.columns}"
    if got.height != exp.height:
        return f"FAIL rows {got.height} != {exp.height}"
    if exp.equals(got, null_equal=True):
        return f"identical ({exp.height} rows)"
    return "FAIL contents differ"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode")
    ap.add_argument("rest", nargs="*")
    ap.add_argument("--sizes", nargs="+", type=int, default=[100000, 1000000])
    ap.add_argument("--ops", nargs="+", default=["group", "unique", "join"])
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--threads", nargs="+", default=["1", "12"])
    ap.add_argument("--out", default=str(HERE / "results" / "m6_hc.jsonl"))
    a = ap.parse_args()
    if a.mode == "gen":
        for n in map(int, a.rest):
            gen(n)
        return
    if a.mode == "pworker":
        polars_worker(a.rest[0], int(a.rest[1]))
        return
    out = open(a.out, "a")
    for n in a.sizes:
        for op in a.ops:
            res = f"build/hc_{op}_{n}.csv"
            for th in a.threads:
                for rep in range(a.reps):
                    l0 = os.getloadavg()[0]
                    cmd = ["./build/m6"] + (["+RTS", "--threads", th, "-RTS"] if th != "default" else []) + ["hc", op, f"bench/data/hc/t_{n}.csv", f"bench/data/hc/dim_{n}.csv", res]
                    line, rss, wall = run_cmd(cmd)
                    rec = {"engine": "bend", "op": op, "n": n, "threads": th, "rep": rep, "load1": l0, "rss": rss, "wall": round(wall, 2)}
                    try:
                        rec.update(json.loads(line))
                    except Exception:
                        rec["error"] = line
                    if rep == 0 and "error" not in rec:
                        rec["check"] = compare(op, n, ROOT / res)
                    out.write(json.dumps(rec) + "\n"); out.flush()
                    print(rec, flush=True)
                penv = {} if th == "default" else {"POLARS_MAX_THREADS": th}
                for rep in range(a.reps):
                    l0 = os.getloadavg()[0]
                    line, rss, wall = run_cmd([sys.executable, str(HERE / "hc.py"), "pworker", op, str(n)], penv)
                    rec = {"engine": "polars", "op": op, "n": n, "threads": th, "rep": rep, "load1": l0, "rss": rss}
                    try:
                        rec.update(json.loads(line))
                    except Exception:
                        rec["error"] = line
                    out.write(json.dumps(rec) + "\n"); out.flush()
                    print(rec, flush=True)


if __name__ == "__main__":
    main()
