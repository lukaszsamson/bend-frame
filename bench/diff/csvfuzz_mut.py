"""W6.4 detection-power check of the CSV fuzz harness: mutants of the v0.2 reader against csvfuzz.py.

    python3 bench/diff/csvfuzz_mut.py [--n 1500] [--seed 1] [--only SUBSTRING]      # ~10 min

The mutants are bench/w6/mut63.py's list (read from that file, one definition): each one is applied to a COPY
of the sources (build/csvfuzz/mut/tree, never to src/), a mutant runner is built from the copy, and
`csvfuzz.py --runner <mutant runner> --no-shrink` runs N cases. A mutant is KILLED when the fuzz run fails.
Prints, per mutant, KILLED (the number of failing cases) / SURVIVED. Not part of `make ci`.
"""
from __future__ import annotations

import ast
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BEND = os.environ.get("BEND", str(Path.home() / ".bend/bin/bend"))


# mutants of the producer and the lane (W6.1 / W6.2 code): what the piece sizes and the byte level generator reach
EXTRA = [
    ("src/csvprod.bend", "+term = Bool.and(islf, U32.is_eq(q2, 0))", "+term = islf", "producer cuts at an LF inside quotes"),
    ("src/csvlane.bend", "Bool.and(U32.is_ge(b, 9), U32.is_le(b, 13))", "Bool.and(U32.is_ge(b, 9), U32.is_le(b, 12))", "trim keeps a CR"),
    ("src/csvlane.bend", "Bool.or(U32.is_eq(b, 32), Bool.and(U32.is_ge(b, 9)", "Bool.or(U32.is_eq(b, 31), Bool.and(U32.is_ge(b, 9)", "trim keeps a space"),
    ("src/csvlane.bend", "Bool.to_u32(U32.is_le(x, 2147483648))", "Bool.to_u32(U32.is_lt(x, 2147483648))", "i32 min rejected"),
    ("src/csvlane.bend", "Ln.sel(U32.is_eq(b, 224), 160,", "Ln.sel(U32.is_eq(b, 224), 128,", "UTF-8 overlong E0 accepted"),
    ("src/csvlane.bend", "Bool.or(U32.is_eq(b0, 116), U32.is_eq(b0, 84))", "U32.is_eq(b0, 116)", "bool: no capital True"),
    ("src/csvlane.bend", "U32.is_le(m, 16777216)", "U32.is_le(m, 33554432)", "f32 fast path mantissa limit"),
    ("src/csvlane.bend", "U32.is_le(fd, 10)", "U32.is_le(fd, 12)", "f32 fast path fraction digits limit"),
]


def load_mutants():
    tree = ast.parse((ROOT / "bench/w6/mut63.py").read_text())
    for node in tree.body:
        if isinstance(node, ast.Assign) and getattr(node.targets[0], "id", "") == "muts":
            return ast.literal_eval(node.value)
    sys.exit("no `muts` list in bench/w6/mut63.py")


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=20261004, help="a seed with a golden file under diff/golden/ is checked against it too")
    ap.add_argument("--only", default="")
    ap.add_argument("--extra", choices=["yes", "no", "only"], default="yes", help="the producer / lane mutants of this file (EXTRA) in addition to mut63.py's")
    ap.add_argument("--jobs", type=int, default=8)
    a = ap.parse_args()
    # the reference is the (mutated) reader itself at 1 MiB pieces: the golden hashes, frozen from the removed
    # v0.1 reader, are what kills a mutant that is wrong at every piece size
    gp = HERE / "golden" / f"seed{a.seed}.json"
    golden = ["--golden", str(gp)] if gp.exists() else []
    work = ROOT / "build/csvfuzz/mut"
    tree = work / "tree"
    killed = survived = 0
    muts = ([] if a.extra == "only" else load_mutants()) + ([] if a.extra == "no" else EXTRA)
    for f, old, new, name in muts:
        if a.only and a.only not in name:
            continue
        shutil.rmtree(tree, ignore_errors=True)
        (tree / "bench/diff").mkdir(parents=True)
        (tree / "bench/w6").mkdir(parents=True)
        (tree / "tests").mkdir(parents=True)
        shutil.copytree(ROOT / "src", tree / "src")
        shutil.copy(ROOT / "frame.bend", tree / "frame.bend")
        shutil.copytree(ROOT / "tests/lib", tree / "tests/lib")
        for p in (ROOT / "bench/w6").glob("*.bend"):
            shutil.copy(p, tree / "bench/w6" / p.name)
        shutil.copy(ROOT / "bench/diff/csvfuzz.bend", tree / "bench/diff/csvfuzz.bend")
        src = (tree / f).read_text()
        if src.count(old) != 1:
            print(f"SKIP (pattern count {src.count(old)}): {name}")
            continue
        (tree / f).write_text(src.replace(old, new))
        exe = work / "mutant_runner"
        if exe.exists():
            exe.unlink()
        t = time.time()
        b = subprocess.run([BEND, "bench/diff/csvfuzz.bend", "-o", str(exe)], capture_output=True, text=True, cwd=tree)
        if b.returncode != 0 or not exe.exists():
            print(f"BUILD FAILED: {name}: {(b.stdout + b.stderr)[-200:]}")
            continue
        r = subprocess.run([sys.executable, str(HERE / "csvfuzz.py"), "--seed", str(a.seed), "--n", str(a.n), "--no-shrink", "--jobs", str(a.jobs), "--runner", str(exe), "--out", str(work / "mut.json")] + golden, capture_output=True, text=True, cwd=ROOT)
        out = r.stdout
        line = [ln for ln in out.splitlines() if ln.startswith("FAIL:")]
        if r.returncode != 0:
            killed += 1
            first = [ln for ln in out.splitlines() if ln.startswith("  c0") or ln.startswith("  s0")][:1]
            print(f"KILLED   {name}: {line[0] if line else r.returncode} {first[0][:150] if first else ''}  ({time.time() - t:.0f}s)")
        else:
            survived += 1
            print(f"SURVIVED {name}  ({time.time() - t:.0f}s)")
        sys.stdout.flush()
    print(f"killed {killed}, survived {survived}")


if __name__ == "__main__":
    main()
