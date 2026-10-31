"""T4.1 probe runner: fused kernels vs today's unfused passes (bench/w4/fused.bend), PROVISIONAL numbers.

    ~/.bend/bin/bend bench/w4/fused.bend -o build/w4/fused
    python3 -I bench/w4/run.py build/w4/fused OUT.jsonl ROUNDS REPS [mode ...]

Each round runs every mode once as a fresh process (`--threads 1 <mode> REPS`), in a rotated order
(interleaving), recording the 1-minute load before and after. A record per process goes to OUT.jsonl:
the mode, the round, the loads, the program's own JSON (ms_total over REPS repetitions, checksums).
The summary prints, per mode, the median and the raw per-repetition times (ms_total / REPS), the load
range, and the checksums, which must agree between a query's today / fused modes (the run fails
otherwise). Numbers on a shared machine are PROVISIONAL (plans/M_02.txt section 5).
"""
import json
import os
import statistics
import subprocess
import sys
import time

MODES = ["q1today", "q1today3", "q1fused", "q2today", "q2fused", "q2ntoday", "q2nfused"]


def run_one(exe, mode, reps):
    l0 = os.getloadavg()[0]
    p = subprocess.run([exe, "+RTS", "--threads", "1", "-RTS", mode, str(reps)], capture_output=True, text=True, stdin=subprocess.DEVNULL)
    l1 = os.getloadavg()[0]
    out = {}
    for line in p.stdout.splitlines():
        if line.startswith("{"):
            out = json.loads(line)
    return {"mode": mode, "exit": p.returncode, "load_before": round(l0, 2), "load_after": round(l1, 2), "out": out,
            "when": time.strftime("%Y-%m-%dT%H:%M:%S")}


def main():
    exe, path, rounds, reps = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    modes = sys.argv[5:] or MODES
    recs = {m: [] for m in modes}
    with open(path, "a") as f:
        for r in range(rounds):
            for m in modes[r % len(modes):] + modes[:r % len(modes)]:
                rec = run_one(exe, m, reps)
                rec["round"] = r
                f.write(json.dumps(rec) + "\n")
                f.flush()
                recs[m].append(rec)
    ok = True
    checks = {}
    print(f"rows 2^20, 1 thread, {reps} repetitions per process, {rounds} processes per mode (interleaved)")
    for m in modes:
        rs = recs[m]
        per = [r["out"]["ms_total"] / reps for r in rs if r["out"]]
        ld = [r["load_before"] for r in rs] + [r["load_after"] for r in rs]
        chk = sorted({(r["out"].get("check_k"), r["out"].get("check_s")) for r in rs if r["out"]})
        checks[m] = chk
        print(f"{m:9s} median {statistics.median(per):6.2f} ms  raw {' '.join(f'{x:.2f}' for x in per)}  "
              f"load {min(ld):.1f}..{max(ld):.1f}  check {chk}")
    for a, b in [("q1today", "q1fused"), ("q1today3", "q1fused"), ("q2today", "q2fused"), ("q2ntoday", "q2nfused")]:
        if a in checks and b in checks and checks[a] != checks[b]:
            print(f"CHECKSUM MISMATCH {a} {checks[a]} vs {b} {checks[b]}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
