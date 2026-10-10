#!/usr/bin/env python3
"""Summarise a W0 spike JSONL (one process per line, `#` comments skipped): per (mode, grain, threads)
the median / min / max of ms per rep (ms_total / reps), the sample count, the load range, and whether
the checksums agree within the cell. Usage: summarize.py results/s1.jsonl [more.jsonl ...]"""
import json, sys, statistics
from collections import defaultdict

rows = []
for path in sys.argv[1:]:
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        line = line.replace(':True', ':true').replace(':False', ':false')
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            print('skip malformed:', line[:80], file=sys.stderr)

cells = defaultdict(list)
for r in rows:
    key = (r.get('spike', '?'), r['mode'], r.get('grain_log2', 0), r.get('threads', 1))
    cells[key].append(r)

print(f"{'spike':5} {'mode':18} {'g':>3} {'thr':>3} {'n':>2} {'med ms/rep':>10} {'min':>7} {'max':>7} {'load1 min-max':>14} checks")
for key in sorted(cells):
    rs = cells[key]
    per = [r['ms_total'] / max(1, r.get('reps', 1)) for r in rs]
    loads = [float(r.get('load1', 0)) for r in rs]
    checks = {(r.get('check_k'), r.get('check_s')) for r in rs}
    agree = 'same' if len(checks) == 1 else f'DIFFER({len(checks)})'
    print(f"{key[0]:5} {key[1]:18} {key[2]:>3} {key[3]:>3} {len(rs):>2} {statistics.median(per):>10.2f} {min(per):>7.2f} {max(per):>7.2f} {min(loads):>6.1f}-{max(loads):<6.1f} {agree}")
