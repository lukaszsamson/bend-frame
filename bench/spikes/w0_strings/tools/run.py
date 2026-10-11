"""W0 strings/reader spike harness: fresh processes, interleaved, load recorded, raw samples kept.

    python3 tools/run.py OUT.jsonl REPS 'cmd one' 'cmd two' ...

Each repetition runs every command once, in a rotated order (interleaving), each as a fresh
process under /usr/bin/time -l. A record per process goes to OUT.jsonl (appended): the command,
the rep, the 1/5/15-minute load before and after, wall/user/sys seconds and max RSS from
time(1), and every JSON line the program printed (its own timers and checksum). At the end a
summary table prints the median and range of the program's "ms" field (else wall time) and of
max RSS per command. Numbers on a shared machine are PROVISIONAL (plans/M_02.txt section 5).
"""
import json
import os
import re
import shlex
import statistics
import subprocess
import sys
import time


def run_one(cmd):
    load0 = os.getloadavg()
    t0 = time.time()
    p = subprocess.run(["/usr/bin/time", "-l"] + shlex.split(cmd), capture_output=True, text=True)
    t1 = time.time()
    load1 = os.getloadavg()
    err = p.stderr
    m = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", err)
    rss = re.search(r"(\d+)\s+maximum resident set size", err)
    outs = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                outs.append(json.loads(line))
            except ValueError:
                outs.append({"raw": line})
        elif line:
            outs.append({"raw": line})
    return {
        "cmd": cmd, "exit": p.returncode,
        "load_before": [round(x, 2) for x in load0], "load_after": [round(x, 2) for x in load1],
        "real_s": float(m.group(1)) if m else round(t1 - t0, 3),
        "user_s": float(m.group(2)) if m else None, "sys_s": float(m.group(3)) if m else None,
        "max_rss_mb": round(int(rss.group(1)) / 1048576, 1) if rss else None,
        "out": outs, "when": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }


def main():
    out, reps, cmds = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    recs = {c: [] for c in cmds}
    with open(out, "a") as f:
        for r in range(reps):
            order = cmds[r % len(cmds):] + cmds[:r % len(cmds)]
            for c in order:
                rec = run_one(c)
                rec["rep"] = r
                f.write(json.dumps(rec) + "\n")
                f.flush()
                recs[c].append(rec)
                o = rec["out"][-1] if rec["out"] else {}
                print(f"rep {r} load {rec['load_before'][0]:6.1f} ms {o.get('ms', o.get('read_ms', '-'))!s:>7} "
                      f"real {rec['real_s']:6.2f} user {rec['user_s']} rss {rec['max_rss_mb']} exit {rec['exit']} :: {c}",
                      flush=True)
    print("\nsummary (median [min..max]); ms = the program's own timer")
    for c in cmds:
        rs = recs[c]
        ms = [r["out"][-1].get("ms") for r in rs if r["out"] and isinstance(r["out"][-1].get("ms"), (int, float))]
        us = [r["user_s"] for r in rs if r["user_s"] is not None]
        rss = [r["max_rss_mb"] for r in rs if r["max_rss_mb"] is not None]
        ld = [r["load_before"][0] for r in rs]
        chk = sorted({str(r["out"][-1].get("chk")) for r in rs if r["out"]})

        def s(xs):
            return f"{statistics.median(xs):.0f} [{min(xs):.0f}..{max(xs):.0f}]" if xs else "-"
        print(f"ms {s(ms):>22}  user_s {statistics.median(us) if us else '-'}  rss_mb {s(rss):>18}  "
              f"load {s(ld):>14}  chk {','.join(chk)}  :: {c}")


if __name__ == "__main__":
    main()
