"""W6.1 / W6.2 bench runner: fresh processes, interleaved, load recorded, raw samples kept.

    python3 bench/w6/run_probe.py OUT.jsonl REPS 'cmd one' 'cmd two' ...

Each repetition runs every command once (rotated order, so no command always goes first), each as a
fresh process under /usr/bin/time -l. One JSON record per process is appended to OUT.jsonl: the command,
the repetition, the 1-minute load before and after, wall / user / sys seconds, max RSS, `instructions
retired` and `cycles elapsed` (far less sensitive to the machine's load than wall time: the machine is
shared, so numbers are PROVISIONAL, plans/M_02.txt section 5) and the program's own JSON line (read_ms,
fork_ms, checksums). The summary prints the median and the range of the chosen fields per command.
Gate numbers are the orchestrator's (bench/m2, a quiet machine), not these.
"""
import json
import os
import re
import shlex
import statistics
import subprocess
import sys
import time

FIELDS = ["read_ms", "fork_ms", "ms", "user_s", "instr_g", "cycles_g", "rss_mb", "load"]


def run_one(cmd):
    load0 = os.getloadavg()
    p = subprocess.run(["/usr/bin/time", "-l"] + shlex.split(cmd), capture_output=True, text=True)
    load1 = os.getloadavg()
    err = p.stderr
    m = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", err)
    rss = re.search(r"(\d+)\s+maximum resident set size", err)
    ins = re.search(r"(\d+)\s+instructions retired", err)
    cyc = re.search(r"(\d+)\s+cycles elapsed", err)
    out = {}
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                out = json.loads(line)
            except ValueError:
                out = {"raw": line}
    rec = {
        "cmd": cmd, "exit": p.returncode,
        "load_before": round(load0[0], 2), "load_after": round(load1[0], 2),
        "real_s": float(m.group(1)) if m else None, "user_s": float(m.group(2)) if m else None,
        "sys_s": float(m.group(3)) if m else None,
        "rss_mb": round(int(rss.group(1)) / 1048576, 1) if rss else None,
        "instr_g": round(int(ins.group(1)) / 1e9, 3) if ins else None,
        "cycles_g": round(int(cyc.group(1)) / 1e9, 3) if cyc else None,
        "out": out, "when": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }
    return rec


def val(r, f):
    if f == "load":
        return r["load_before"]
    if f in r and r[f] is not None:
        return r[f]
    return r["out"].get(f) if isinstance(r["out"], dict) else None


def summarize(recs, cmds):
    print("\nsummary: median [min..max] over the repetitions; raw samples in the JSONL")
    for c in cmds:
        rs = [r for r in recs if r["cmd"] == c]
        cells = []
        for f in FIELDS:
            xs = [val(r, f) for r in rs if isinstance(val(r, f), (int, float))]
            if xs:
                cells.append(f"{f} {statistics.median(xs):g} [{min(xs):g}..{max(xs):g}]")
        chk = sorted({str(r["out"].get("chk")) for r in rs if isinstance(r["out"], dict) and "chk" in r["out"]})
        print(f"n={len(rs)} " + "  ".join(cells) + (f"  chk {','.join(chk)}" if chk else "") + f"  :: {c}")


def main():
    out, reps, cmds = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    recs = []
    with open(out, "a") as f:
        for r in range(reps):
            order = cmds[r % len(cmds):] + cmds[:r % len(cmds)]
            for c in order:
                rec = run_one(c)
                rec["rep"] = r
                f.write(json.dumps(rec) + "\n")
                f.flush()
                recs.append(rec)
                print(f"rep {r} load {rec['load_before']:6.1f} fork {val(rec, 'fork_ms')} read {val(rec, 'read_ms')} "
                      f"user {rec['user_s']} instr {rec['instr_g']}G :: {c}", flush=True)
    summarize(recs, cmds)


if __name__ == "__main__":
    main()
