"""Exit-status regression of the differential drivers (bench/diff/run.py, bench/diff/reduce.py).

    cd bench && uv run python diff/tests/test_exit.py        # make diff-driver-check

The v0.1 review found that `run.py` without --strict returned 0 when the shrinker classified a
failure as a known defect, so a reintroduced known bug passed. The rule is: ANY correctness failure
(mismatch, crash, oracle error) makes the driver exit 1, classified or not; classification only
labels it. This test drives the real `main()` of both drivers with Bend replaced by a mock that
answers with the oracle's own dumps (so nothing needs the Bend binary), then injects failures:

    clean run                                   -> 0
    one mismatch, shrinker labels it "B01"      -> 1   (default, --strict and --no-shrink alike)
    one mismatch, shrinker labels it NEW        -> 1
    shrinker raises                             -> 1
    one crash                                   -> 1
    oracle error                                -> 1
    a dirty null slot (P0 report "BAD ..."), all dumps agreeing -> 1   (post-review B1)
    a missing P0 report                         -> 1
    reduce.py: clean -> 0; a finding of any kind (known kind, new kind, crash) -> 1
"""
from __future__ import annotations

import contextlib
import io
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.append(str(HERE.parents[1]))

import bendrun  # noqa: E402
import evalcase  # noqa: E402
import gen  # noqa: E402
import reduce as reduce_mod  # noqa: E402  (bench/diff/reduce.py; not the stdlib functools.reduce)
import run  # noqa: E402
import shrink  # noqa: E402

SEED, N = 1, 6
FAILS = []


class SerialPool:
    """mp.Pool stand-in so that the patches below are visible to the oracle calls."""

    def __init__(self, *a, **k):
        pass

    def map_async(self, fn, items, chunksize=None):
        res = [fn(x) for x in items]
        return type("R", (), {"get": lambda self: res})()

    def close(self):
        pass


def good_results(cases):
    """What a correct Bend would print: the oracle's eager dump, and its lazy dump for the lazy runs."""
    out = {}
    for c in cases:
        kind, exp = evalcase.oracle_result(c)
        assert kind == "ok", f"{c.id}: oracle {kind}: {exp}"
        out[c.id] = {"eager": exp["eager"], "raw": exp["lazy"], "opt": exp["lazy"], "full": exp["lazy"],
                     bendrun.P0_KEY: {"eager": "ok", "raw": "ok", "opt": "ok", "full": "ok"}}
    return out


def drive(argv, *, bad=(), crash=(), shrink_ret=None, shrink_raises=False, oracle_error=False, dirty=(), no_p0=()):
    """run.main(argv) with a mocked Bend; returns the exit status. `bad`: indices of cases whose eager
    dump is replaced by a different one; `crash`: indices reported as crashes; `dirty`: indices whose
    opt run reports a null slot that is not the default (every dump still agrees: post-review B1);
    `no_p0`: indices whose raw run printed no P0 report."""
    cases = [gen.gen_case(SEED, i, False, set()) for i in range(N)]
    base = good_results(cases)
    for i in dirty:
        base[cases[i].id][bendrun.P0_KEY]["opt"] = 'BAD [col "x": 1 null slot(s) not the default, first row 0 holds 0x80000000; 0 validity word(s) not 0/1; 0 bool word(s) not 0/1]'
    for i in no_p0:
        base[cases[i].id][bendrun.P0_KEY].pop("raw")
    for i in bad:
        txt = base[cases[i].id]["eager"]
        base[cases[i].id]["eager"] = "error\tInvalidOperation: injected mismatch\n" if not txt.startswith("error") else "frame\nheight\t0\nwidth\t0\n"
    crashes = {cases[i].id: "mock crash" for i in crash}
    for cid in crashes:
        base.pop(cid)

    def fake_run_all(cs, scratch, batch=25, jobs=6, mode="interp", timeout=300.0, progress=None):
        return base, crashes, {"runs": 1, "secs": 0.0}

    def fake_shrink(failures, scratch, out_json, summary, **kw):
        if shrink_raises:
            raise RuntimeError("mock shrinker bug")
        out_json.write_text("{}")
        return [{"id": shrink_ret, "class": f["classes"][0], "count": 1} for f in failures]

    real_oracle = evalcase.oracle_result
    patches = [(bendrun, "run_all", fake_run_all), (run.mp, "Pool", SerialPool), (shrink, "group_and_shrink", fake_shrink)]
    if oracle_error:
        patches.append((evalcase, "oracle_result", lambda c: ("oracle_error", "mock oracle bug") if c.id == cases[0].id else real_oracle(c)))
    saved = [(o, n, getattr(o, n)) for o, n, _ in patches]
    for o, n, v in patches:
        setattr(o, n, v)
    try:
        with tempfile.TemporaryDirectory() as d, contextlib.redirect_stdout(io.StringIO()):
            return run.main(["--seed", str(SEED), "--n", str(N), "--scratch", d, "--jobs", "1"] + list(argv))
    finally:
        for o, n, v in saved:
            setattr(o, n, v)


def drive_reduce(*, finding_kind=None, crash=False):
    """reduce.main over 3 cases with a mocked Bend and a mocked checker that reports one finding."""
    def fake_run_all(cases, scratch, extra, jobs=6, timeout=400.0):
        res = {c["id"]: {"in": ""} for c in cases}
        crashes = {cases[0]["id"]: "mock crash"} if crash else {}
        return res, crashes

    def fake_check(c, got, stats, findings, extra):
        if finding_kind and c["id"].endswith("1"):
            findings.append({"id": c["id"], "cls": c["cls"], "kind": finding_kind, "path": "p", "q": "q", "where": "w", "detail": "mock"})

    saved = (reduce_mod.run_all, reduce_mod.check_case)
    reduce_mod.run_all, reduce_mod.check_case = fake_run_all, fake_check
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            return reduce_mod.main(["--seed", "1", "--n", "3", "--out", str(Path(tempfile.mkdtemp()) / "f.json")])
    finally:
        reduce_mod.run_all, reduce_mod.check_case = saved


def expect(label, got, want):
    ok = got == want
    print(("PASS " if ok else "FAIL ") + f"{label}: exit {got}" + ("" if ok else f", want {want}"))
    if not ok:
        FAILS.append(label)


def main():
    expect("run.py clean", drive([]), 0)
    expect("run.py clean --strict", drive(["--strict"]), 0)
    expect("run.py clean --no-shrink", drive(["--no-shrink"]), 0)
    # a mismatch the shrinker CLASSIFIES as a known defect must still fail (the review's reproduction)
    expect("run.py classified mismatch, default", drive([], bad=[2], shrink_ret="B01"), 1)
    expect("run.py classified mismatch, --strict", drive(["--strict"], bad=[2], shrink_ret="B01"), 1)
    expect("run.py classified mismatch, --no-shrink", drive(["--no-shrink"], bad=[2], shrink_ret="B01"), 1)
    expect("run.py unclassified mismatch", drive([], bad=[2], shrink_ret=None), 1)
    expect("run.py shrinker raises", drive([], bad=[2], shrink_raises=True), 1)
    expect("run.py crash", drive([], crash=[3], shrink_ret="B01"), 1)
    expect("run.py crash, --no-shrink", drive(["--no-shrink"], crash=[3]), 1)
    expect("run.py oracle error", drive([], oracle_error=True, shrink_ret="B01"), 1)
    expect("run.py oracle error, --no-shrink", drive(["--no-shrink"], oracle_error=True), 1)
    expect("run.py dirty null slot (P0)", drive([], dirty=[1], shrink_ret=None), 1)
    expect("run.py dirty null slot (P0), --no-shrink", drive(["--no-shrink"], dirty=[1]), 1)
    expect("run.py missing P0 report", drive(["--no-shrink"], no_p0=[4]), 1)
    # the parser: the P0 line is split off the dump, the dump compares as before
    parsed = bendrun.parse_output("-- d0001 eager\nframe\nheight\t0\nwidth\t0\np0 ok\n\n-- d0001 raw\nerror\tX\np0 BAD [col]\n")
    expect("parse_output splits the P0 line", 0 if parsed == {"d0001": {"eager": "frame\nheight\t0\nwidth\t0\n", "raw": "error\tX\n", bendrun.P0_KEY: {"eager": "ok", "raw": "BAD [col]"}}} else 1, 0)
    expect("reduce.py clean", drive_reduce(), 0)
    for kind in reduce_mod.DEFECT_KINDS + ("infra", "a-kind-added-later"):
        expect(f"reduce.py finding {kind}", drive_reduce(finding_kind=kind), 1)
    expect("reduce.py crash", drive_reduce(crash=True), 1)
    import test_oracle_join  # the oracle's joins against the brute-force contract (d1588)
    if test_oracle_join.main() != 0:
        FAILS.append("test_oracle_join")
    if FAILS:
        print(f"\ntest_exit: {len(FAILS)} FAILED: {FAILS}")
        return 1
    print("\ntest_exit: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
