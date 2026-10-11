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
    ("Kernel.range: writes one slot too far right", "src/kernels.bend",
     "Kernel.range.go(~T, p, j, off, Array.set(T, out, k, x), ",
     "Kernel.range.go(~T, p, j, off, Array.set(T, out, j, x), "),
    ("Kernel.range: ignores the offset in the loop", "src/kernels.bend",
     "Array.get(T, a, U32.add(off, j)))", "Array.get(T, a, j))"),
    ("Valid.range: the slice's mask is not shifted", "src/column.bend",
     "Mask{K.Kernel.range(~U32, m, d, off, mk, 0)}", "Mask{K.Kernel.range(~U32, m, d, 0, mk, 0)}"),
    ("Dict.code: a new entry answers an old code", "src/strs.bend",
     "(Dict.add(k, dd, strs, b, tag, h, s, (t, i)), k)", "(Dict.add(k, dd, strs, b, tag, h, s, (t, i)), 0)"),
    ("Enc.put: every row reuses code 0", "src/strs.bend",
     "(dict, Array.set(U32, out, i, c))", "(dict, Array.set(U32, out, i, 0))"),
    ("Dict.rc.put: map entry written at the wrong slot", "src/strs.bend",
     "(dst, Array.set(U32, out, c, x))", "(dst, Array.set(U32, out, U32.inc(c), x))"),
    ("Eval.un: Neg over i32 answers a u32 column", "src/eval.bend",
     "Done{C.CI32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}}",
     "Done{C.CU32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}}"),
    ("Sort.gh.k: the bounded gather keeps one row too many", "src/sort.bend",
     "Sort.gather.k(U32.min(n, h), Sort.gcols(cols, U32.min(n, h), (perm, Nil{})))",
     "Sort.gather.k(U32.min(U32.inc(n), h), Sort.gcols(cols, U32.min(U32.inc(n), h), (perm, Nil{})))"),
    ("Sort.fh.c: Sort+Head skips the missing-key check", "src/sort.bend",
     "    case Some{e}:\n      Fail{e}\n    case None{}:\n      Sort.fh.a(n, Sort.argsort(f, keys))",
     "    case Some{e}:\n      Sort.fh.a(n, Sort.argsort(f, keys))\n    case None{}:\n      Sort.fh.a(n, Sort.argsort(f, keys))"),
    ("Sort.frame_head: no keys keeps every row", "src/sort.bend",
     "      Done{C.Frame.head(f, n)}", "      Done{f}"),
    ("Exec.run_phys.h: the Sort+Head step keeps one row too many", "src/exec.bend",
     "Exec.fin(Exec.sorthead(ks, n, Exec.loop(", "Exec.fin(Exec.sorthead(ks, U32.inc(n), Exec.loop("),
    # T4.3 (LAWS section 20: fc_filter_mask, select_filter_mask, filter_select_step, filter_select_run):
    # the Filter + Select step must keep every selected column, its validity, its name, the kept
    # count, and fire only on lists of plain columns
    ("Exec.fc.k3: the fused group drops a selected column", "src/exec.bend",
     "(m, C.Named{n3, Exec.mk(s3, o3, kept, d, C.AllValid{})} <> C.Named{n2, Exec.mk(s2, o2, kept, d, C.AllValid{})} <> ",
     "(m, C.Named{n3, Exec.mk(s3, o3, kept, d, C.AllValid{})} <> "),
    ("Exec.fz.v: a column with a validity mask joins a group (its mask is lost)", "src/exec.bend",
     "FzNo{Exec.mk(sh, b, len, depth, C.Mask{v})}", "FzOk{len, depth, sh, b}"),
    ("Exec.fc.k4: an output column loses its name", "src/exec.bend",
     "(m, C.Named{n4, Exec.mk(s4, o4, kept, d, C.AllValid{})}", "(m, C.Named{\"literal\", Exec.mk(s4, o4, kept, d, C.AllValid{})}"),
    ("Exec.fs.p: the kept count is the predicate's length", "src/exec.bend",
     "Exec.fs.q(f, es, K.Kernel.popcount(n, m))", "Exec.fs.q(f, es, (m, n))"),
    ("Exec.run_phys.s: the step fires on non-plain selects (aliases: the output name is lost)", "src/exec.bend",
     "Exec.run_phys.f(Exec.plain(es), es, pred, y, env)", "Exec.run_phys.f(Bool.not(Exec.plain(es)), es, pred, y, env)"),
    ("Exec.run_phys.s: the step fires on every select (computed expressions, select([]))", "src/exec.bend",
     "Exec.run_phys.f(Exec.plain(es), es, pred, y, env)", "Exec.run_phys.f(True{}, es, pred, y, env)"),
    ("Eval.fit: does not broadcast", "src/eval.bend",
     "def Eval.fit(k: SKind, c: C.Column, +n: U32) -> C.Column:\n  match k:\n    case KFull{}:\n      c\n    case _:\n      Eval.bcast(c, n)",
     "def Eval.fit(k: SKind, c: C.Column, +n: U32) -> C.Column:\n  match k:\n    case KFull{}:\n      c\n    case _:\n      c"),
    # T3.1 (LAWS section 16, lend_observes): a move must answer the column itself and leave the
    # stand-in in its place, at the column the name picks
    ("Frame.lend: answers the hollow stand-in and leaves the column in the frame", "src/column.bend",
     "(Named{n, hole} <> acc, Some{c})", "(Named{n, c} <> acc, Some{hole})"),
    ("Frame.lend: lends every column but the named one", "src/column.bend",
     "Cols.lend.go(rest, name, Cols.lend.step(String.eq(name, n), n, col, r))",
     "Cols.lend.go(rest, name, Cols.lend.step(Bool.not(String.eq(name, n)), n, col, r))"),
    # T3.1 (mark_moves_ok): the liveness pass may move only the last read of a column the
    # operator does not keep
    ("Eval.mark: moves a column a later expression still reads", "src/eval.bend",
     "Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(Eval.reads(rest), n)))",
     "Bool.not(C.Names.has(Eval.reads(rest), n))"),
    ("Eval.mark: moves a column the operator keeps", "src/eval.bend",
     "Eval.mark.c(Bool.and(Bool.or(all, C.Names.has(dead, n)), ",
     "Eval.mark.c(Bool.and(True{}, "),
    # T4.1 (LAWS section 17, the fused kernels): wrong slot, wrong mask, cursor off by one,
    # validity not ANDed, a wrong hand-back, per kernel
    ("W4 Kernel.map_pb: writes one slot too far right", "src/kernels.bend",
     "Kernel.map_pb.go(~T, ~P, ~U, ~f, q, j, p, Array.set(U, out, i, f(p, x)),",
     "Kernel.map_pb.go(~T, ~P, ~U, ~f, q, j, p, Array.set(U, out, j, f(p, x)),"),
    ("W4 Kernel.map_pb: reads the operand one row ahead", "src/kernels.bend",
     "Kernel.map_pb.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0))",
     "Kernel.map_pb.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 1))"),
    ("W4 Kernel.zipb: writes one slot too far right", "src/kernels.bend",
     "Kernel.zipb.go(~T, ~U, ~V, ~f, p, j, Array.set(V, out, i, f(x, y)),",
     "Kernel.zipb.go(~T, ~U, ~V, ~f, p, j, Array.set(V, out, j, f(x, y)),"),
    ("W4 Kernel.zipb: reads the second operand one row ahead", "src/kernels.bend",
     "Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0))",
     "Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 1))"),
    ("W4 Kernel.zipv: validity not ANDed (va only)", "src/kernels.bend",
     "      +w = U32.and(wa, wb)\n", "      +w = U32.and(wa, 1)\n"),
    ("W4 Kernel.zipv: null slots not reset to the default", "src/kernels.bend",
     "Bool.pick(V, U32.is_ne(w, 0), f(x, y), z)", "Bool.pick(V, U32.is_ne(w, 2), f(x, y), z)"),
    ("W4 Kernel.zipv: validity written one slot too far right", "src/kernels.bend",
     "Array.set(U32, vout, i, w)", "Array.set(U32, vout, j, w)"),
    ("W4 Kernel.zipv: hands back vb as va", "src/kernels.bend",
     "      ZV{out, vout, a, va, b, vb}", "      ZV{out, vout, a, vb, b, va}"),
    ("W4 Kernel.pred_count: the count ignores the mask words", "src/kernels.bend",
     "Kernel.pred_count.go(~T, ~U, ~P, ~f, q, j, U32.add(k, w), p,",
     "Kernel.pred_count.go(~T, ~U, ~P, ~f, q, j, U32.add(k, U32.and(w, 0)), p,"),
    ("W4 Kernel.pred_count: the count starts at 1", "src/kernels.bend",
     "Kernel.pred_count.go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p,",
     "Kernel.pred_count.go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 1, p,"),
    ("W4 Kernel.pred_count: validity not ANDed (va only)", "src/kernels.bend",
     "+w = Bool.pick(U32, U32.is_ne(U32.and(wa, wb), 0), f(p, x, y), 0)",
     "+w = Bool.pick(U32, U32.is_ne(wa, 0), f(p, x, y), 0)"),
    ("W4 Kernel.pred_count: mask written one slot too far right", "src/kernels.bend",
     "p, Array.set(U32, out, i, w), Array.get(T, a, j)", "p, Array.set(U32, out, j, w), Array.get(T, a, j)"),
    ("W4 Kernel.pred_count: hands back vb as va", "src/kernels.bend",
     "      PC{out, k, a, va, b, vb}", "      PC{out, k, a, vb, b, va}"),
    ("W4 Kernel.compact3: cursor off by one", "src/kernels.bend",
     "Kernel.compact3.go(~A, ~B, ~C, p, j, U32.add(k, bit),",
     "Kernel.compact3.go(~A, ~B, ~C, p, j, U32.add(U32.inc(k), bit),"),
    ("W4 Kernel.compact3: flipped mask", "src/kernels.bend",
     "Kernel.compact3.go(~A, ~B, ~C, p, j, U32.add(k, bit),",
     "Kernel.compact3.go(~A, ~B, ~C, p, j, U32.add(k, U32.xor(bit, 1)),"),
    ("W4 Kernel.compact3: second buffer written at the row, not the cursor", "src/kernels.bend",
     "Array.set(B, o2, k, x2), Array.set(C, o3, k, x3), Array.get(U32, m, j)",
     "Array.set(B, o2, i, x2), Array.set(C, o3, k, x3), Array.get(U32, m, j)"),
    ("W4 Kernel.compact3: answers the cursor plus one", "src/kernels.bend",
     "      C3{o1, o2, o3, m, a1, a2, a3, k}", "      C3{o1, o2, o3, m, a1, a2, a3, U32.inc(k)}"),
    ("W4 Kernel.compact4: cursor off by one", "src/kernels.bend",
     "Kernel.compact4.go(~A, ~B, ~C, ~D, p, j, U32.add(k, bit),",
     "Kernel.compact4.go(~A, ~B, ~C, ~D, p, j, U32.add(U32.inc(k), bit),"),
    ("W4 Kernel.compact4: fourth buffer reads the row ahead", "src/kernels.bend",
     "Array.get(C, a3, j), Array.get(D, a4, j))",
     "Array.get(C, a3, j), Array.get(D, a4, U32.inc(j)))"),
    ("W4 Kernel.compact4: the mask word of the next row", "src/kernels.bend",
     "Array.new(D, d, z4), Array.get(U32, m, 0),", "Array.new(D, d, z4), Array.get(U32, m, 1),"),
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
