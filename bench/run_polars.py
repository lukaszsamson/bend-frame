"""Time q1..q6 per generated size (best of 5, default collect()), all threads and 1 thread.
Usage: uv run --project bench python bench/run_polars.py"""
import json
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).parent
DATA, RESULTS = HERE / "data", HERE / "results"
REPS = 5


def worker() -> None:
    """Runs inside a subprocess so POLARS_MAX_THREADS is set before polars is imported."""
    from queries import QUERIES, load
    out = []
    for f in sorted(DATA.glob("sales_*.csv"), key=lambda p: int(p.stem.split("_")[1])):
        n = int(f.stem.split("_")[1])
        sales, products = load(f, DATA / "products.csv")
        for name, q in QUERIES.items():
            best = float("inf")
            for _ in range(REPS):
                t = time.perf_counter()
                q(sales, products).collect()
                best = min(best, time.perf_counter() - t)
            out.append({"query": name, "n": n, "seconds": best})
    print(json.dumps(out))


def run(threads: int | None) -> list[dict]:
    env = {k: v for k, v in os.environ.items() if k != "POLARS_MAX_THREADS"}
    if threads:
        env["POLARS_MAX_THREADS"] = str(threads)
    r = subprocess.run([sys.executable, __file__, "--worker"], env=env, check=True,
                       capture_output=True, text=True)
    return json.loads(r.stdout.strip().splitlines()[-1])


if __name__ == "__main__":
    if "--worker" in sys.argv:
        worker()
        sys.exit()
    import polars as pl
    multi, single = run(None), run(1)
    rows = [{**m, "threads": "default", "seconds_1t": s["seconds"]} for m, s in zip(multi, single)]
    RESULTS.mkdir(exist_ok=True)
    flat = [{**r, "threads": "default"} for r in multi] + [{**r, "threads": 1} for r in single]
    (RESULTS / "polars.json").write_text(json.dumps(flat, indent=1))
    print(f"polars {pl.__version__}, {os.cpu_count()} cpus, best of {REPS}, seconds\n")
    print("| query | n | default threads (s) | 1 thread (s) |\n|---|---:|---:|---:|")
    for r in rows:
        print(f"| {r['query']} | {r['n']:,} | {r['seconds']:.5f} | {r['seconds_1t']:.5f} |")
