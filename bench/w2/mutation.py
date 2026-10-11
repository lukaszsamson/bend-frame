"""Mutation controls for the W2.1 / W2.2 tests (tests/hcode_*.bend, tests/ranks_*.bend, bench/w2/w2diff.bend).

    python3 bench/w2/mutation.py [id-prefix ...]       (about 5 minutes)

Each mutant changes ONE expression of src/hcode.bend or src/ranks.bend in a temporary copy of the tree
(build/w2/mut*) and runs the tests that cover the file; a test run that still matches its `#|` lines is
a SURVIVOR. Expected: every mutant KILLED except the ones marked EQUIVALENT below (they change speed or
an encoding detail the contract cannot see, so no test of the VALUES can kill them).
The `W*` mutants (the code-point fallback of the rank stage) need the native binary: the interpreter
refuses a Chr above U+10FFFF, so bench/w2/w2diff.bend runs them.
"""
import os
import shutil
import subprocess
import sys

root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
bend = os.path.expanduser("~/.bend/bin/bend")
work = os.path.join(root, "build", "w2", "mut")

HC = ["tests/hcode_diff.bend", "tests/hcode_unit.bend"]
RK = ["tests/ranks_diff.bend", "tests/ranks_unit.bend"]

# (id, file, old, new, tests, note)
muts = [
    ("H1 eq always true", "src/hcode.bend", "(a, Hc.eq(t, s, True{}))", "(a, True{})", HC, ""),
    ("H2 u8 off by one at 2048", "src/hcode.bend", "Bool.to_u32(U32.is_ge(c, 2048))", "Bool.to_u32(U32.is_gt(c, 2048))", HC, ""),
    ("H3 next not incremented", "src/hcode.bend", "HC{U32.inc(next), a, Array.set(U32, hs, j, h)", "HC{next, a, Array.set(U32, hs, j, h)", HC, ""),
    ("H4 every non-empty slot compared (hash ignored)", "src/hcode.bend", "Bool.and(Bool.not(e), U32.is_eq(x, h)), a, U32.sub(r, 1), s)", "Bool.not(e), a, U32.sub(r, 1), s)", HC, "EQUIVALENT: only slower"),
    ("H5 fr off by one row", "src/hcode.bend", "Array.set(U32, fr, e, i)", "Array.set(U32, fr, e, U32.inc(i))", HC, ""),
    ("H6 probe step 2", "src/hcode.bend", "Hc.look(h, U32.and(U32.inc(j), mask), s, a, hs, rp, ids)", "Hc.look(h, U32.and(U32.add(j, 2), mask), s, a, hs, rp, ids)", HC, "EQUIVALENT at load <= 1/2 on these sizes: the same slots are reached in every probe sequence"),
    ("H7 first not applied to ids", "src/hcode.bend", "Array.set(U32, ids, j, next)", "Array.set(U32, ids, j, U32.sub(next, first))", HC, ""),
    ("H8 bl of a new entry dropped", "src/hcode.bend", "Array.set(U32, bls, e, bn)", "Array.set(U32, bls, e, 0)", HC, ""),
    ("R1 left key zero", "src/ranks.bend", "(RX{wo, bl, pk, gid, upr}, U32.min(U32.mul(U32.sub(n, lo), Bool.to_u32(U32.is_gt(n, lo))), upr))", "(RX{wo, bl, pk, gid, upr}, 0)", RK, ""),
    ("R2 continuation byte 192 + x", "src/ranks.bend", "U32.add(128, U32.and(U32.shrn(c, sh), 63))", "U32.add(192, U32.and(U32.shrn(c, sh), 63))", RK, "EQUIVALENT: a monotone recoding of the continuation bytes keeps the order"),
    ("R3 rounds fuel 1", "src/ranks.bend", "U32.add(U32.div(mx, upr), 2)", "1", RK, ""),
    ("R4 ties ignored (one round only)", "src/ranks.bend", "Rx.round.if(U32.is_ne(ties, 0), k, kd, r, rx, perm, ties, rounds)", "Rx.round.if(U32.is_lt(r, 1), k, kd, r, rx, perm, ties, rounds)", RK, ""),
    ("R5 flip not applied", "src/ranks.bend", "Array.set(U32, rk, x, U32.xor(p, flip))", "Array.set(U32, rk, x, p)", RK, ""),
    ("R6 word 2r + 1 dropped", "src/ranks.bend", "Rx.word(e, U32.inc(U32.mul(r, 2)), other)", "(other, 0)", RK, ""),
    ("R7 dict lengths zero", "src/ranks.bend", "~(s => H.Hc.blen(s, 0)), U32.to_nat(k), 0, RLS{strs", "~(s => 0), U32.to_nat(k), 0, RLS{strs", RK, ""),
    ("R8 word offset sentinel dropped", "src/ranks.bend", "RW{tot, mx, bl, Array.set(U32, wo, c, tot)}", "RW{tot, mx, bl, wo}", RK, "EQUIVALENT: the words read past the last entry are the zero padding of pk unless the index wraps, and a tie that long never reaches them (the left key separated the entry in an earlier round)"),
    ("R9 packing: last partial word not kept", "src/ranks.bend", "U32.mul(acc2, U32.sub(1, fu))", "0", RK, ""),
]

# native: the fallback for code points above U+10FFFF
native = [
    ("W1 fallback branch packs bytes", "src/ranks.bend", "      Rk.wide(k, kd, flip, kd1, a, fr, bl)\n    case False{}:", "      Rk.run(k, kd, flip, 8, mx, a, fr, wo, bl, pk)\n    case False{}:", ""),
    ("W3 fallback round width 8", "src/ranks.bend", "Rk.run(k, kd, flip, 2, mx, a, fr, wo, bl, pk)", "Rk.run(k, kd, flip, 8, mx, a, fr, wo, bl, pk)", ""),
    ("W4 fallback code point counts as bytes", "src/ranks.bend", "Rl.go(~(s => Rl.cps(s, 0)), U32.to_nat(k), 0, RLS{a, fr, bl})", "Rl.go(~(s => H.Hc.blen(s, 0)), U32.to_nat(k), 0, RLS{a, fr, bl})", "EQUIVALENT: longer lengths only add rounds and zero words; the ranks do not change"),
]


def fresh(files):
    if os.path.exists(work):
        shutil.rmtree(work)
    os.makedirs(os.path.join(work, "tests"))
    shutil.copytree(os.path.join(root, "src"), os.path.join(work, "src"))
    shutil.copytree(os.path.join(root, "tests", "lib"), os.path.join(work, "tests", "lib"))
    for t in files:
        shutil.copy(os.path.join(root, t), os.path.join(work, t))


def expected(path):
    out = [l[2:] for l in open(path).read().splitlines() if l.startswith("#|")]
    return "\n".join(x.rstrip() for x in out).strip()


only = sys.argv[1:]
survivors = 0
for mid, f, old, new, tests, note in muts:
    if only and not any(mid.startswith(o) for o in only):
        continue
    fresh(tests)
    p = os.path.join(work, f)
    s = open(p).read()
    if s.count(old) != 1:
        print("%-52s PATTERN COUNT %d" % (mid, s.count(old)))
        survivors += 1
        continue
    open(p, "w").write(s.replace(old, new))
    killed = False
    for t in tests:
        r = subprocess.run([bend, os.path.join(work, t)], capture_output=True, text=True, timeout=900)
        got = "\n".join(x.rstrip() for x in (r.stdout + r.stderr).strip().splitlines()).strip()
        if got != expected(os.path.join(root, t)):
            killed = True
            break
    status = "KILLED" if killed else ("SURVIVED" + (" (" + note + ")" if note else ""))
    if not killed and not note.startswith("EQUIVALENT"):
        survivors += 1
        status = "SURVIVED  <-- not documented as equivalent"
    print("%-52s %s" % (mid, status))

for mid, f, old, new, note in native:
    if only and not any(mid.startswith(o) for o in only):
        continue
    fresh([])
    os.makedirs(os.path.join(work, "bench"), exist_ok=True)
    shutil.copytree(os.path.join(root, "bench", "w2"), os.path.join(work, "bench", "w2"), dirs_exist_ok=True)
    shutil.copytree(os.path.join(root, "tests"), os.path.join(work, "tests"), dirs_exist_ok=True)
    shutil.copy(os.path.join(root, "frame.bend"), os.path.join(work, "frame.bend"))
    p = os.path.join(work, f)
    s = open(p).read()
    if s.count(old) != 1:
        print("%-52s PATTERN COUNT %d" % (mid, s.count(old)))
        survivors += 1
        continue
    open(p, "w").write(s.replace(old, new))
    exe = os.path.join(work, "w2diff")
    r = subprocess.run([bend, os.path.join(work, "bench/w2/w2diff.bend"), "-o", exe], capture_output=True, text=True)
    if r.returncode != 0:
        print("%-52s BUILD FAILED %s" % (mid, (r.stdout + r.stderr)[-300:]))
        survivors += 1
        continue
    bad = []
    for n in ("181", "1000", "3000"):
        o = subprocess.run([exe, "wide", n], capture_output=True, text=True).stdout
        bad += [l for l in o.splitlines() if "BAD" in l]
    if bad:
        print("%-52s KILLED" % mid)
    elif note.startswith("EQUIVALENT"):
        print("%-52s SURVIVED (%s)" % (mid, note))
    else:
        print("%-52s SURVIVED  <-- not documented as equivalent" % mid)
        survivors += 1

shutil.rmtree(work, ignore_errors=True)
print("survivors not documented as equivalent: %d" % survivors)
sys.exit(1 if survivors else 0)
