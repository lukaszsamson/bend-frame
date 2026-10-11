#!/usr/bin/env python3
"""T5.2 probe runner (PROVISIONAL numbers, plans/M_02.txt section 5): interleaved fresh processes of
bench/w5/ckernels.bend's native binary, every mode at 1 / 4 / 12 threads, `procs` rounds; each sample records
the 1-minute load before and after the process. Writes one JSON line per sample, then prints medians (ms per
rep), ranges, raw samples, the derived costs and the 12-vs-1 scaling:
  fsum: flat = fsumflat - fclone, walk = twalk - tclone, walk_recursive = twalkr - tclone,
        flatten_fallback = tflat - tclone, ffold (borrowed flat fold, no clone)
  gather: fused = gfused - gclone, flat_then_build = gflat - gclone
and checks that the flat and chunked cells of one query print the same checksum.
usage: python3 -I bench/w5/run_t52.py build/w5/ckernels bench/w5/results/t52.jsonl [procs=5] [reps=40]
       python3 -I bench/w5/run_t52.py --report bench/w5/results/t52.jsonl
"""
import json, os, statistics, subprocess, sys

MODES = ["q1flat", "q1chunk", "q2flat", "q2chunk", "q2chunk1", "q2nflat", "q2nchunk", "sumflat", "sumchunk",
         "fclone", "fsumflat", "ffold", "tclone", "twalk", "twalkr", "tflat", "gclone", "gfused", "gflat"]
THREADS = [1, 4, 12]
SAME = [("q1flat", "q1chunk"), ("q2flat", "q2chunk", "q2chunk1"), ("q2nflat", "q2nchunk"), ("sumflat", "sumchunk"),
        ("fsumflat", "ffold", "twalk", "twalkr", "tflat"), ("gfused", "gflat")]


def main():
    exe, out = sys.argv[1], sys.argv[2]
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    reps = int(sys.argv[4]) if len(sys.argv) > 4 else 40
    os.makedirs(os.path.dirname(out), exist_ok=True)
    samples = []
    with open(out, "w") as f:
        for rnd in range(procs):
            for t in THREADS:
                for m in MODES:
                    l0 = os.getloadavg()[0]
                    r = subprocess.run([exe, "--threads", str(t), m, str(reps)], capture_output=True, text=True, timeout=900)
                    l1 = os.getloadavg()[0]
                    rec = json.loads(r.stdout.strip().splitlines()[-1])
                    rec.update({"threads": t, "round": rnd, "load1_before": round(l0, 2), "load1_after": round(l1, 2),
                                "ms_per_rep": rec["ms_total"] / rec["reps"]})
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    samples.append(rec)
    report(samples)


def report(samples):
    med = {}
    for t in THREADS:
        for m in MODES:
            xs = [s["ms_per_rep"] for s in samples if s["threads"] == t and s["mode"] == m]
            if not xs:
                continue
            med[(t, m)] = statistics.median(xs)
            print(f"t={t:2d} {m:9s} median {med[(t, m)]:7.3f} ms/rep  range {min(xs):.3f}-{max(xs):.3f}  raw {[round(x, 3) for x in xs]}")
    nan = float("nan")
    for t in THREADS:
        g = lambda m: med.get((t, m), nan)
        print(f"t={t:2d} fsum: flat {g('fsumflat') - g('fclone'):.3f}  ffold {g('ffold'):.3f}  walk {g('twalk') - g('tclone'):.3f}  "
              f"walk_recursive {g('twalkr') - g('tclone'):.3f}  flatten_fallback {g('tflat') - g('tclone'):.3f}  "
              f"gather: fused {g('gfused') - g('gclone'):.3f}  flat_then_build {g('gflat') - g('gclone'):.3f}  ms")
    for m in ["q1flat", "q1chunk", "q2flat", "q2chunk", "q2chunk1", "q2nflat", "q2nchunk", "sumflat", "sumchunk"]:
        if (1, m) in med and (12, m) in med:
            print(f"scaling {m:9s} 1->4 {med[(1, m)] / med[(4, m)]:.2f}x  1->12 {med[(1, m)] / med[(12, m)]:.2f}x")
    for grp in SAME:
        checks = {(s["mode"], s["check"]) for s in samples if s["mode"] in grp}
        vals = {c for _, c in checks}
        print(f"checksums {'/'.join(grp)}: {'SAME' if len(vals) == 1 else 'DIFFER'} {sorted(checks)}")
    loads = [s["load1_before"] for s in samples] + [s["load1_after"] for s in samples]
    print(f"load1 during the run: min {min(loads)} median {statistics.median(loads)} max {max(loads)}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--report":
        report([json.loads(l) for l in open(sys.argv[2])])
    else:
        main()
