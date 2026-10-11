"""Median / range of chosen JSON fields per command of a run.py results file.
    python3 tools/summ.py results/x.jsonl [field ...]     (default fields: ms)
"""
import collections
import json
import statistics
import sys

path, fields = sys.argv[1], (sys.argv[2:] or ["ms"])
rows = collections.OrderedDict()
for line in open(path):
    r = json.loads(line)
    rows.setdefault(r["cmd"], []).append(r)
for cmd, rs in rows.items():
    cells = []
    for f in fields:
        if f in ("max_rss_mb", "user_s", "real_s"):
            xs = [r[f] for r in rs if r.get(f) is not None]
        elif f == "load":
            xs = [r["load_before"][0] for r in rs]
        else:
            xs = [r["out"][-1][f] for r in rs if r["out"] and isinstance(r["out"][-1].get(f), (int, float))]
        cells.append(f"{f}={statistics.median(xs):g} [{min(xs):g}..{max(xs):g}]" if xs else f"{f}=-")
    short = cmd.replace("bench/spikes/w0_strings/build/", "").replace("bench/data/", "").replace("./build/", "")
    print(f"n={len(rs)}  " + "  ".join(cells) + "  :: " + short)
