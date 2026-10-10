#!/usr/bin/env bash
# Mutation check of the proof graph (plans/REVIEW_V01_*: "a wrong production function must be
# rejected", not merely "a renamed wrong copy").
#
#   make mutation-check              (scripts/mutation_check.sh)
#   MUT_JOBS=4 MUT_ONLY=gather scripts/mutation_check.sh     # parallelism / a name filter
#
# For each mutation below: copy the proof-relevant tree (src/ and the root *.bend: LAWS, PROOF*,
# frame) into a fresh temp dir, patch ONE production function IN PLACE (the patch must match exactly
# once, or the mutation itself is reported as broken), run `bend PROOF.bend` there and require
# "SOME PROOFS FAIL". A mutation the proofs do not catch is a finding and fails this script; nothing
# is weakened to make it pass. An unmutated copy is run first and must answer ALL PROOFS CHECK, so
# a failure under a mutation is the mutation's doing and not the copy's.
#
# The tests/proof_negative/ fixtures are a different, weaker check (they mutate renamed copies and
# reuse the production proof terms); this one mutates the production definitions themselves.
cd "$(dirname "$0")/.." || exit 1
exec python3 -I - "$@" <<'PY'
import os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(os.environ["MUT_ROOT"]) if os.environ.get("MUT_ROOT") else Path(os.getcwd())
os.chdir(ROOT)
BEND = os.environ.get("BEND", str(Path.home() / ".bend/bin/bend"))
TIMEOUT = float(os.environ.get("MUT_TIMEOUT", "600"))
JOBS = int(os.environ.get("MUT_JOBS", "3"))
ONLY = os.environ.get("MUT_ONLY", "")

# (name, file, old text, new text); `old` must occur exactly once in `file`
MUTATIONS = [
    ("Kernel.gather: reads src at the wrong index", "src/kernels.bend",
     "Kernel.gather.put(~T, out, j, Array.get(T, src, i))",
     "Kernel.gather.put(~T, out, j, Array.get(T, src, U32.inc(i)))"),
    ("Kernel.compact_keep: flipped mask", "src/kernels.bend",
     "Kernel.compact_keep.go(~T, p, j, U32.add(k, bit),",
     "Kernel.compact_keep.go(~T, p, j, U32.add(k, U32.xor(bit, 1)),"),
    ("Kernel.compact: flipped mask", "src/kernels.bend",
     "Kernel.compact.go(~T, p, j, U32.add(k, bit),",
     "Kernel.compact.go(~T, p, j, U32.add(k, U32.xor(bit, 1)),"),
    ("Opt.hmin: the outer limit wins", "src/plan.bend",
     "U32.min(m, k)", "k"),
    ("Opt.hmerge: Head merge drops the pending limit", "src/plan.bend",
     "Opt.hmerge(x, Some{Opt.hmin(m, n)})", "Opt.hmerge(x, Some{m})"),
    ("Opt.hmerge: the limit sinks below Select", "src/plan.bend",
     "Opt.hwrap(n, Select{es, Opt.hmerge(x, None{})})", "Select{es, Opt.hmerge(x, n)}"),
    ("Kernel.choose: inverted mask", "src/kernels.bend",
     "Bool.pick(T, U32.is_ne(w, 0), x, y)", "Bool.pick(T, U32.is_eq(w, 0), x, y)"),
    ("Kernel.append: b copied one slot too far right", "src/kernels.bend",
     "Kernel.copy_into(~T, nb, na, ", "Kernel.copy_into(~T, nb, U32.inc(na), "),
    ("Kernel.copy_into: ignores the offset", "src/kernels.bend",
     "Array.set(T, out, U32.add(off, i), x)", "Array.set(T, out, i, x)"),
    ("Dict.code: a new entry answers an old code", "src/strs.bend",
     "(Dict.add(k, dd, strs, b, tag, h, s, (t, i)), k)", "(Dict.add(k, dd, strs, b, tag, h, s, (t, i)), 0)"),
    ("Enc.put: every row reuses code 0", "src/strs.bend",
     "(dict, Array.set(U32, out, i, c))", "(dict, Array.set(U32, out, i, 0))"),
    ("Dict.rc.put: map entry written at the wrong slot", "src/strs.bend",
     "(dst, Array.set(U32, out, c, x))", "(dst, Array.set(U32, out, U32.inc(c), x))"),
    ("Eval.un: Neg over i32 answers a u32 column", "src/eval.bend",
     "Done{C.CI32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}}",
     "Done{C.CU32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}}"),
    ("Eval.fit: does not broadcast", "src/eval.bend",
     "def Eval.fit(k: SKind, c: C.Column, +n: U32) -> C.Column:\n  match k:\n    case KFull{}:\n      c\n    case _:\n      Eval.bcast(c, n)",
     "def Eval.fit(k: SKind, c: C.Column, +n: U32) -> C.Column:\n  match k:\n    case KFull{}:\n      c\n    case _:\n      c"),
]


def make_copy(dst: Path):
    dst.mkdir(parents=True)
    shutil.copytree(ROOT / "src", dst / "src")
    for f in ROOT.glob("*.bend"):
        shutil.copy2(f, dst / f.name)


def prove(d: Path):
    t0 = time.time()
    try:
        r = subprocess.run([BEND, "PROOF.bend"], cwd=d, capture_output=True, text=True, timeout=TIMEOUT, stdin=subprocess.DEVNULL)
        return r.returncode, r.stdout + r.stderr, time.time() - t0
    except subprocess.TimeoutExpired:
        return "timeout", "", time.time() - t0


def failing_laws(out: str):
    locs = [l.strip() for l in out.splitlines() if l.strip().startswith("Location:")]
    if locs:
        return list(dict.fromkeys(locs))[:3]
    return [l.strip()[:110] for l in out.splitlines() if "expected" in l][:1]


def run_mutation(args):
    tmp, (name, rel, old, new) = args
    d = Path(tmp)
    make_copy(d)
    p = d / rel
    text = p.read_text()
    n = text.count(old)
    if n != 1:
        return name, "BROKEN", f"the patch matched {n} times in {rel} (want exactly 1): the mutation table is stale", 0.0
    p.write_text(text.replace(old, new))
    assert p.read_text() != text
    rc, out, secs = prove(d)
    if rc == "timeout":
        return name, "BROKEN", f"timeout after {TIMEOUT:.0f} s", secs
    if "SOME PROOFS FAIL" in out:
        return name, "CAUGHT", "; ".join(failing_laws(out)), secs
    if "ALL PROOFS CHECK" in out:
        return name, "MISSED", "bend PROOF.bend still answers ALL PROOFS CHECK", secs
    return name, "BROKEN", f"the mutated tree gave neither verdict (exit {rc}): " + out.strip()[-300:].replace("\n", " | "), secs


def main():
    t0 = time.time()
    base = tempfile.mkdtemp(prefix="mutcheck.")
    try:
        # control: the unmutated copy must check
        c = Path(base) / "unmutated"
        make_copy(c)
        rc, out, secs = prove(c)
        if rc != 0 or "ALL PROOFS CHECK" not in out:
            print(f"mutation-check: FAILED: the UNMUTATED copy does not answer ALL PROOFS CHECK (exit {rc}):\n" + out[-1500:])
            return 1
        print(f"control   ok      unmutated copy: ALL PROOFS CHECK ({secs:.1f} s)")
        muts = [m for m in MUTATIONS if ONLY in m[0]]
        if not muts:
            print(f"mutation-check: FAILED: MUT_ONLY={ONLY!r} matches no mutation")
            return 1
        jobs = [(str(Path(base) / f"m{i:02d}"), m) for i, m in enumerate(muts)]
        bad = []
        with ThreadPoolExecutor(max_workers=JOBS) as ex:
            for name, verdict, detail, secs in ex.map(run_mutation, jobs):
                print(f"{verdict:9s} {name}  ({secs:.1f} s)" + (f"\n          {detail}" if detail else ""), flush=True)
                if verdict != "CAUGHT":
                    bad.append((name, verdict))
        if bad:
            print(f"mutation-check: FAILED: {len(bad)} of {len(muts)} mutation(s) not caught: " + "; ".join(f"{n} [{v}]" for n, v in bad))
            return 1
        print(f"mutation-check: ok, {len(muts)} of {len(muts)} mutations rejected, unmutated copy accepted ({time.time() - t0:.0f} s)")
        return 0
    finally:
        shutil.rmtree(base, ignore_errors=True)


sys.exit(main())
PY
