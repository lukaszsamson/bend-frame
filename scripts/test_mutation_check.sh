#!/usr/bin/env bash
# make test-mutation-check (v0.3 W3): the fast paths that are TESTED, not proven, guarded by their tests.
# Each mutation is applied in place to a copy of the tree, and the named tests must FAIL there (the way
# scripts/mutation_check.sh requires `bend PROOF.bend` to fail for the proven functions). The mutations are
# the v0.3 Fable review's proof-coverage audit's (plans/REVIEW_V03_FABLE.txt, Fact 1): proofs do not catch
# them, so the tests below are their only guard. The unmutated copy must pass the same tests first.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
exec python3 -I - "$@" <<'PY'
import os, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path.cwd()
TESTS = ["tests/regress/V03_fastpaths.bend", "tests/regress/V03_boundaries.bend"]
MUTATIONS = [
    ("join direct-id probe off by one (Dd.put.p answers t, not t - 1)", "src/join.bend",
     "Array.set(U32, out, i, Bool.pick(U32, Bool.and(ok, U32.is_ne(t, 0)), U32.sub(t, 1), Join.dead()))",
     "Array.set(U32, out, i, Bool.pick(U32, Bool.and(ok, U32.is_ne(t, 0)), t, Join.dead()))"),
    ("group_by direct code merges the minimum with the null group (x - min, not x - min + 1)", "src/groupby.bend",
     "U32.and(U32.inc(U32.sub(x, k)), U32.sub(0, v))",
     "U32.and(U32.sub(x, k), U32.sub(0, v))"),
    ("Kernel.where: the cursor advances every row (also a proof mutation: LAWS section 23)", "src/kernels.bend",
     "Kernel.where.go(p, j, U32.add(k, bit), Array.set(U32, out, k, i), ",
     "Kernel.where.go(p, j, U32.add(k, 1), Array.set(U32, out, k, i), "),
]


def copy_tree(dst):
    for name in ["frame.bend", "src", "tests", "bench/w6", "scripts"]:
        s, d = ROOT / name, dst / name
        d.parent.mkdir(parents=True, exist_ok=True)
        if s.is_dir():
            shutil.copytree(s, d, ignore=shutil.ignore_patterns("__pycache__"))
        else:
            shutil.copy2(s, d)


def run_tests(tree):
    r = subprocess.run(["scripts/test.sh"] + TESTS, cwd=tree, capture_output=True, text=True)
    return r.returncode, r.stdout.strip().splitlines()[-1:] if r.stdout else []


t0 = time.time()
fails = 0
with tempfile.TemporaryDirectory(prefix="tmut") as tmp:
    base = Path(tmp) / "base"
    copy_tree(base)
    rc, tail = run_tests(base)
    if rc != 0:
        print("test-mutation-check: the UNMUTATED copy fails its tests:", tail)
        sys.exit(1)
    for i, (label, path, old, new) in enumerate(MUTATIONS):
        tree = Path(tmp) / ("m%d" % i)
        copy_tree(tree)
        src = (tree / path).read_text()
        if src.count(old) != 1:
            print("STALE     %s: the pattern occurs %d times in %s" % (label, src.count(old), path))
            fails += 1
            continue
        (tree / path).write_text(src.replace(old, new))
        rc, tail = run_tests(tree)
        if rc != 0:
            print("CAUGHT    %s  (%s)" % (label, " ".join(tail)))
        else:
            print("SURVIVED  %s" % label)
            fails += 1
print("test-mutation-check: %s, %d of %d mutations caught by tests, unmutated copy passes (%.0f s)" % (
    "ok" if fails == 0 else "FAILED", len(MUTATIONS) - fails, len(MUTATIONS), time.time() - t0))
sys.exit(1 if fails else 0)
PY
