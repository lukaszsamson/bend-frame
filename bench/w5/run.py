#!/usr/bin/env python3
"""T5.1 probe runner (PROVISIONAL numbers, plans/M_02.txt section 5): interleaved fresh processes of
bench/w5/chunks.bend's native binary, every mode at 1 / 4 / 12 threads, `procs` rounds, `reps` reps per
process; each sample records the 1-minute load before the process. Writes one JSON line per sample and
prints medians (ms per rep), ranges and the derived costs:
  build    = build - clone            (one 1M-row column chunked, per rep)
  flatten  = rt - (build - clone)     (one column flattened back)
  rechunk  = rechunk - build10        (1024 leaves of 1024 rows -> 64 leaves)
  fbuild   = fbuild - fclone          (7 columns chunked, forked across columns)
  fflatten = frt - (fbuild - fclone)  (7 columns flattened, forked across columns)
usage: python3 -I bench/w5/run.py build/w5/chunks bench/w5/results/t51.jsonl [procs=5] [reps=10]
"""
import json, os, statistics, subprocess, sys

def main():
    exe, out = sys.argv[1], sys.argv[2]
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    reps = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    modes = ["clone", "build", "rt", "build10", "rechunk", "fclone", "fbuild", "frt"]
    threads = [1, 4, 12]
    samples = []
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        for rnd in range(procs):
            for t in threads:
                for m in modes:
                    load = os.getloadavg()[0]
                    r = subprocess.run([exe, "--threads", str(t), m, str(reps)], capture_output=True, text=True, timeout=600)
                    line = r.stdout.strip().splitlines()[-1]
                    rec = json.loads(line)
                    rec.update({"threads": t, "round": rnd, "load1": round(load, 2), "ms_per_rep": rec["ms_total"] / rec["reps"]})
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    samples.append(rec)
    med = {}
    for t in threads:
        for m in modes:
            xs = [s["ms_per_rep"] for s in samples if s["threads"] == t and s["mode"] == m]
            checks = {s["check"] for s in samples if s["threads"] == t and s["mode"] == m}
            med[(t, m)] = statistics.median(xs)
            print(f"t={t:2d} {m:8s} median {med[(t, m)]:7.2f} ms/rep  range {min(xs):.2f}-{max(xs):.2f}  raw {xs}  checks {sorted(checks)}")
    for t in threads:
        g = lambda m: med[(t, m)]
        print(f"t={t:2d} derived: build {g('build') - g('clone'):.2f}  flatten {g('rt') - (g('build') - g('clone')):.2f}  "
              f"rechunk {g('rechunk') - g('build10'):.2f}  fbuild(7 cols) {g('fbuild') - g('fclone'):.2f}  "
              f"fflatten(7 cols) {g('frt') - (g('fbuild') - g('fclone')):.2f}  ms")
    loads = [s["load1"] for s in samples]
    print(f"load1 during the run: min {min(loads)} median {statistics.median(loads)} max {max(loads)}")

if __name__ == "__main__":
    main()
