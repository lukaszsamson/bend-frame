"""M6 repeated-query workload: the same query N times in ONE process (build/m6 repeat), results compared and
RSS sampled.

  uv run --project bench python bench/repeat.py --sizes 100000 1000000 --queries q1 q2 q3 q4 q5 q6 --reps 20 [--out F.jsonl]

For every (n, q): a run with 1 iteration and one with `reps` iterations (peak RSS from /usr/bin/time -l), and
for the long run a ps(1) sample of the RSS every 50 ms. Reported: whether all `reps` result hashes are equal (the
hash is over the CSV rendering with 4 decimals), the per-iteration times (first, median, last), the peak RSS of
both runs, growth = peak(reps) - peak(1), and the median RSS of the first and the last third of the samples.
Each iteration runs over fresh clones of one parse (the parse is not repeated), so a flat RSS means that
a collect leaves nothing behind.
"""
import argparse
import json
import os
import re
import statistics
import subprocess
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def one(q, n, reps, sample):
    csv = f"bench/data/sales_{n}.csv"
    t = time.time()
    p = subprocess.Popen(["/usr/bin/time", "-l", "./build/m6", "repeat", q, csv, str(reps)], cwd=ROOT, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    samples = []
    stop = threading.Event()

    def sampler():
        # /usr/bin/time is the parent of ./build/m6: sample the child (pgrep -P)
        child = None
        while not stop.is_set():
            if child is None:
                r = subprocess.run(["pgrep", "-P", str(p.pid)], capture_output=True, text=True)
                child = r.stdout.split()[0] if r.stdout.split() else None
            if child:
                r = subprocess.run(["ps", "-o", "rss=", "-p", child], capture_output=True, text=True)
                if r.stdout.strip():
                    samples.append(int(r.stdout.strip()) * 1024)
            time.sleep(0.05)

    th = None
    if sample:
        th = threading.Thread(target=sampler)
        th.start()
    out, err = p.communicate()
    stop.set()
    if th:
        th.join()
    m = re.search(r"(\d+)\s+maximum resident set size", err)
    its = [json.loads(l) for l in out.splitlines() if l.startswith('{"iter"')]
    return {"peak_rss": int(m.group(1)) if m else None, "iters": its, "ok": '{"done":true}' in out,
            "err": [l for l in out.splitlines() if l.startswith("error")], "samples": samples, "wall": round(time.time() - t, 1)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", nargs="+", type=int, default=[100000, 1000000])
    ap.add_argument("--queries", nargs="+", default=["q1", "q2", "q3", "q4", "q5", "q6"])
    ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--out", default=str(ROOT / "bench" / "results" / "m6_repeat.jsonl"))
    a = ap.parse_args()
    out = open(a.out, "a")
    for n in a.sizes:
        for q in a.queries:
            l0 = os.getloadavg()[0]
            r1 = one(q, n, 1, False)
            rn = one(q, n, a.reps, True)
            hs = [i["hash"] for i in rn["iters"]]
            ms = [i["ms"] for i in rn["iters"]]
            s = rn["samples"]
            third = max(1, len(s) // 3)
            rec = {"q": q, "n": n, "reps": a.reps, "load1": round(l0, 1), "iterations": len(hs), "all_hashes_equal": len(set(hs)) == 1 and len(hs) == a.reps,
                   "hash_1run_equal": [i["hash"] for i in r1["iters"]] == hs[:1], "ms_first": ms[0] if ms else None,
                   "ms_median": statistics.median(ms) if ms else None, "ms_last": ms[-1] if ms else None,
                   "peak_rss_1": r1["peak_rss"], "peak_rss_n": rn["peak_rss"],
                   "growth": (rn["peak_rss"] - r1["peak_rss"]) if rn["peak_rss"] and r1["peak_rss"] else None,
                   "rss_first_third": statistics.median(s[:third]) if s else None, "rss_last_third": statistics.median(s[-third:]) if s else None,
                   "samples": len(s), "ok": rn["ok"] and r1["ok"], "err": rn["err"] + r1["err"], "wall_n": rn["wall"]}
            out.write(json.dumps(rec) + "\n")
            out.flush()
            print(rec, flush=True)


if __name__ == "__main__":
    main()
