"""Merge bench/results/{bend,polars}.json into a markdown table (Bend vs Polars, 1 thread and all threads).

usage: python compare.py [--jsonl bend.jsonl]    (run via: uv run --project bench python bench/compare.py)
With --jsonl, the JSON lines printed by build/bench (one {"query","n","seconds","threads"} per process
run) are first collected into results/bend.json, keeping the fastest run per query/n/threads. Missing Bend rows (e.g. a query that failed) show "n/a".
Ratio = Bend / Polars (> 1: Bend is slower). Speedup = Bend 1 thread / Bend all threads.
"""
import argparse
import json
from pathlib import Path

RESULTS = Path(__file__).parent / "results"


def load(path: Path) -> dict:
    out = {}
    if path.exists():
        for r in json.loads(path.read_text()):
            out[(r["query"], int(r["n"]), str(r["threads"]))] = r["seconds"]
    return out


def ms(x):
    if x is None:
        return "n/a"
    v = x * 1000
    return f"{v:.2f}" if v < 100 else f"{v:.0f}"


def ratio(a, b):
    return "n/a" if a is None or b is None or b == 0 else f"{a / b:.0f}x" if a / b >= 10 else f"{a / b:.1f}x"


def table(bend: dict, polars: dict) -> str:
    keys = sorted({(q, n) for q, n, _ in list(bend) + list(polars)}, key=lambda k: (k[1], k[0]))
    out = ["| query | n | Bend 1t (ms) | Polars 1t (ms) | ratio 1t | Bend all (ms) | Polars all (ms) | ratio all | Bend 1t/all |",
           "|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for q, n in keys:
        b1, p1 = bend.get((q, n, "1")), polars.get((q, n, "1"))
        ba, pa = bend.get((q, n, "default")), polars.get((q, n, "default"))
        out.append(f"| {q} | {n:,} | {ms(b1)} | {ms(p1)} | {ratio(b1, p1)} | {ms(ba)} | {ms(pa)} | {ratio(ba, pa)} | {ratio(b1, ba)} |")
    return "\n".join(out)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--jsonl", help="JSON lines from build/bench; collected into results/bend.json first")
    a = ap.parse_args()
    if a.jsonl:
        best = {}  # one line per process run: keep the fastest per (query, n, threads)
        for line in Path(a.jsonl).read_text().splitlines():
            if line.startswith("{"):
                r = json.loads(line)
                k = (r["query"], r["n"], str(r["threads"]))
                if k not in best or r["seconds"] < best[k]["seconds"]:
                    best[k] = r
        rows = list(best.values())
        RESULTS.mkdir(exist_ok=True)
        (RESULTS / "bend.json").write_text(json.dumps(rows, indent=1))
    print(table(load(RESULTS / "bend.json"), load(RESULTS / "polars.json")))
