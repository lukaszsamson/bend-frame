"""Run N generated cases for a seed against the current main and compare.

    cd bench && uv run python diff/run.py --seed 1 --n 1000
    python run.py --reductions --seed 1 --n 2000   # T2.3, see reduce.py
    python run.py --csv --seed 1 --n 1000          # W6.4, see csvfuzz.py (make csv-fuzz)
    python run.py --seed 1 --n 1000 [--backend interp|native|both] [--batch 200] [--jobs 6]
                  [--out failures.json] [--features reductions] [--all] [--keep]

Comparisons (plans/M_01.txt T2):
  T2.1  eager vs raw-lazy vs optimised-lazy dumps: exact (bench/check.py compare_dumps; only the
        contract's NaN-payload relaxation), errors and row order included. Cases the oracle
        proves inadmissible (a runtime error in an inner eager verb vs a static error in an outer
        verb: eager and lazy MAY differ there) are counted apart.
  T2.2  the actual dumps against oracle.py's expected dump (Polars 2.0.0 + the contract's departures).
  T2.4  with --backend both: the interpreter against the natively compiled program, same text.

Bend runs many cases per program (interpreted: ~1 s per 200 cases; a native compile is ~25 s per
200 cases, so native is for the backend comparison only). A crashing or hanging case is isolated
by bisection. Exit status: 1 when ANY case fails (a mismatch, a crash, an oracle error), whether or
not classify.py recognises it as a known defect: classification only labels a failure in the
report, it never excuses it. --strict is kept for old command lines and changes nothing.
"""
from __future__ import annotations

import argparse
import collections
import json
import multiprocessing as mp
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.append(str(HERE.parent))

import bendrun  # noqa: E402
import check  # noqa: E402
import shrink  # noqa: E402
import evalcase  # noqa: E402
from evalcase import compare, evaluate  # noqa: E402,F401
import gen  # noqa: E402
import model as M  # noqa: E402


def _oracle_one(args):
    seed, idx, all_, features = args
    import evalcase
    c = gen.gen_case(seed, idx, all_, features)
    return idx, evalcase.oracle_result(c)


def main(argv=None):
    # T2.3 (F32 reductions against an exact reference) lives in reduce.py; `run.py --reductions ...`
    # hands the remaining arguments to it (bench/diff/README.md, "T2.3")
    argv = sys.argv[1:] if argv is None else list(argv)
    if "--reductions" in argv:
        argv.remove("--reductions")
        import reduce as _reduce
        return _reduce.main(argv)
    # W6.4: the CSV reader fuzz harness (v0.2 reader against v0.1) lives in csvfuzz.py; `run.py --csv ...`
    if "--csv" in argv:
        argv.remove("--csv")
        import csvfuzz as _csvfuzz
        return _csvfuzz.main(argv)
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--backend", choices=["interp", "native", "both"], default="interp")
    ap.add_argument("--batch", type=int, default=200)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--timeout", type=float, default=300.0)
    ap.add_argument("--out", help="failures JSON (default: build/diff/seed<seed>/failures.json)")
    ap.add_argument("--scratch")
    ap.add_argument("--features", default="", help="comma list; 'noreductions' (no reducers outside group_by: masks B04-a), 'noselfjoin', 'deep' (more rows up to 300, plans up to 6 verbs)")
    ap.add_argument("--all", action="store_true", help="use every grammar row (the facade may not have it: those cases fail)")
    ap.add_argument("--no-oracle", action="store_true")
    ap.add_argument("--no-shrink", action="store_true")
    ap.add_argument("--strict", action="store_true", help="accepted for compatibility: any failure always exits 1, classified or not")
    ap.add_argument("--shrink-secs", type=float, default=90.0, help="time budget per failure group for the minimiser")
    ap.add_argument("--keep", action="store_true", help="keep the scratch programs")
    ap.add_argument("--dict", action="store_true", help="M4: every str input column in the Dictionary storage (BEND_DIFF_DICT=1)")
    ap.add_argument("--chunked", action="store_true", help="G1 (v0.2 T5.3): also run every case by the chunked engine at grains 2^0 / 2^2 / 2^4 / 2^14 and compare with the reference runs exactly (BEND_DIFF_CHUNKED=1)")
    a = ap.parse_args(argv)
    if a.dict:
        os.environ["BEND_DIFF_DICT"] = "1"
    if a.chunked:
        os.environ["BEND_DIFF_CHUNKED"] = "1"
    features = {f for f in a.features.split(",") if f}
    scratch = Path(a.scratch) if a.scratch else M.ROOT / f"build/diff/seed{a.seed}"
    import shutil
    for sub in ("interp", "native", "label", "shrink", "final"):
        shutil.rmtree(scratch / sub, ignore_errors=True)
    scratch.mkdir(parents=True, exist_ok=True)
    out_json = Path(a.out) if a.out else scratch / "failures.json"
    t0 = time.time()
    idxs = list(range(a.start, a.start + a.n))
    cases = [gen.gen_case(a.seed, i, a.all, features) for i in idxs]
    t_gen = time.time() - t0

    # oracle in a pool, concurrently with the Bend runs
    pool = mp.Pool(min(8, mp.cpu_count()))
    t1 = time.time()
    orc_async = None if a.no_oracle else pool.map_async(_oracle_one, [(a.seed, i, a.all, features) for i in idxs], chunksize=20)

    results = {}
    crashes = {}
    backends = ["interp", "native"] if a.backend == "both" else [a.backend]
    per_backend = {}
    stats_all = {}
    for be in backends:
        tb = time.time()
        res, crash, st = bendrun.run_all(cases, scratch / be, batch=a.batch, jobs=a.jobs, mode=be, timeout=a.timeout)
        per_backend[be] = res
        stats_all[be] = {"runs": st["runs"], "wall": round(time.time() - tb, 1), "crashes": len(crash)}
        if be == backends[0]:
            results, crashes = res, crash
    t_bend = time.time() - t1
    oracle_res = {}
    if orc_async is not None:
        for idx, r in orc_async.get():
            oracle_res[idx] = r
    pool.close()
    t_orc = time.time() - t1

    failures, counts = [], collections.Counter()
    nunc = nerr = ninad = 0
    for i, c in zip(idxs, cases):
        exp = oracle_res.get(i)
        if exp is not None and exp[0] == "uncertain":
            nunc += 1
        if exp is not None and exp[0] == "oracle_error":
            nerr += 1
        if exp is not None and exp[0] == "ok" and not exp[1]["admissible"]:
            ninad += 1
        if c.id in crashes:
            counts["crash"] += 1
            failures.append({"id": c.id, "classes": ["crash"], "diffs": {"crash": [crashes[c.id][:300]]}, "case": c.to_json()})
            continue
        got = results.get(c.id)
        rec = evaluate(c, got, exp)
        if "native" in per_backend and a.backend == "both":
            gn = per_backend["native"].get(c.id)
            if gn is not None and got is not None:
                for how in __import__("emit").runs():
                    d = compare(got[how], gn[how])
                    if d:
                        rec["classes"].append(f"T2.4 {how} interp!=native")
                        rec["diffs"][f"T2.4 {how}"] = d[:6]
        if exp is not None and exp[0] in ("oracle_error",):
            rec["classes"].append("oracle error")
            rec["diffs"]["oracle"] = [exp[1]]
        if rec["classes"]:
            rec["case"] = c.to_json()
            failures.append(rec)
            for k in rec["classes"]:
                counts[k] += 1

    import hashlib
    import subprocess
    h = hashlib.sha1()
    for p in sorted((M.ROOT / "src").glob("*.bend")) + [M.ROOT / "frame.bend"]:
        h.update(p.read_bytes())
    try:
        head = subprocess.run(["git", "-C", str(M.ROOT), "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
        dirty = bool(subprocess.run(["git", "-C", str(M.ROOT), "status", "--porcelain", "src", "frame.bend"], capture_output=True, text=True).stdout.strip())
    except Exception:  # noqa: BLE001
        head, dirty = "?", False
    summary = {
        "main": f"{head}{'+dirty' if dirty else ''} src-sha1 {h.hexdigest()[:10]}",
        "seed": a.seed, "n": a.n, "backend": a.backend, "features": sorted(features), "chunked": bool(a.chunked), "dict": bool(a.dict),
        "failing_cases": len(failures), "by_class": dict(counts),
        "oracle_uncertain": nunc, "oracle_errors": nerr, "inadmissible_for_T2.1": ninad,
        "invalid_cases": sum(1 for c in cases if c.kind == "invalid"),
        "runtime_s": {"gen": round(t_gen, 1), "bend": round(t_bend, 1), "oracle+bend": round(t_orc, 1)},
        "backends": stats_all,
    }
    print(json.dumps(summary, indent=1))

    report = []
    if not a.no_shrink and failures:
        t2 = time.time()
        try:
            report = shrink.group_and_shrink(failures, scratch, out_json, summary, quiet=False, jobs=a.jobs, budget=a.shrink_secs)
            print(f"shrink+classify: {time.time() - t2:.1f}s")
        except Exception as e:  # noqa: BLE001  a shrinker bug must not hide the failures it was handed
            print(f"shrink+classify FAILED ({type(e).__name__}: {e}); reporting the unshrunk failures")
            out_json.write_text(json.dumps({"summary": summary, "failures": failures}, indent=1))
    else:
        out_json.write_text(json.dumps({"summary": summary, "failures": failures}, indent=1))
    print(f"total {time.time() - t0:.1f}s; failures: {out_json}")
    if not a.keep:
        pass
    # Any correctness failure fails the run. The shrinker's classification (known defect vs NEW) is
    # a label in the report, never a reason to exit 0: a reintroduced known bug must fail too.
    if failures:
        print(f"FAIL: {len(failures)} failing case(s): " + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
