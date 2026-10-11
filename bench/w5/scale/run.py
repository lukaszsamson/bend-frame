#!/usr/bin/env python3
"""bench/w5/scale/run.py -- run one native probe process under /usr/bin/time -l and record a JSONL row.

  python3 -I bench/w5/scale/run.py OUT.jsonl [--tag T] [--repeat K] -- BINARY [--threads N] ARGS...

One row per process: the program's own stdout (parsed as JSON when it is one), the 1-minute load before and
after, wall / user / sys seconds, page reclaims + faults, voluntary / involuntary context switches,
instructions retired and cycles elapsed (macOS `time -l` fields). With --repeat K the process runs K times
(fresh processes, the rows interleaved by the caller's loop order).
"""
import json
import os
import re
import subprocess
import sys
import time

FIELDS = {
    "maximum resident set size": "rss",
    "page reclaims": "reclaims",
    "page faults": "faults",
    "voluntary context switches": "vcsw",
    "involuntary context switches": "icsw",
    "instructions retired": "instr",
    "cycles elapsed": "cycles",
    "peak memory footprint": "peak",
}


def run_once(argv, tag):
    l0 = os.getloadavg()[0]
    t0 = time.time()
    p = subprocess.run(["/usr/bin/time", "-l"] + argv, capture_output=True, text=True)
    wall = time.time() - t0
    l1 = os.getloadavg()[0]
    row = {"tag": tag, "argv": argv, "load0": round(l0, 2), "load1": round(l1, 2), "wall_s": round(wall, 4), "rc": p.returncode}
    out = p.stdout.strip().splitlines()
    row["stdout"] = out[-1] if out else ""
    try:
        row["result"] = json.loads(row["stdout"])
    except Exception:
        row["result"] = None
    err = p.stderr
    m = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", err)
    if m:
        row["real"], row["user"], row["sys"] = (float(x) for x in m.groups())
    for line in err.splitlines():
        line = line.strip()
        for k, v in FIELDS.items():
            if line.endswith(k):
                row[v] = int(line.split()[0])
    return row


def main():
    args = sys.argv[1:]
    out = args.pop(0)
    tag = ""
    repeat = 1
    while args and args[0] != "--":
        if args[0] == "--tag":
            tag = args[1]
            args = args[2:]
        elif args[0] == "--repeat":
            repeat = int(args[1])
            args = args[2:]
        else:
            raise SystemExit("unknown option " + args[0])
    argv = args[1:]
    with open(out, "a") as f:
        for _ in range(repeat):
            row = run_once(argv, tag)
            f.write(json.dumps(row) + "\n")
            r = row.get("result")
            print(json.dumps({k: row.get(k) for k in ("tag", "load0", "real", "user", "sys", "faults", "reclaims", "vcsw", "icsw")}), r)


if __name__ == "__main__":
    main()
