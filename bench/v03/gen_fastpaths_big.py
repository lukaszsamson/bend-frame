"""v0.3 W1: generator of tests/regress/V03_fastpaths_big.bend (native), the big-n sides of the fast-path
switch-over points that the interpreter-sized V03_fastpaths.bend cannot reach:
  group_by  span = 2n - 1 (direct) / 2n / 2n + 1 (rank) at n = 600,000 (2n > 2^20, so 2n is the bound)
  join      span = 2(nl + nr) - 1 (direct ids) / 2(nl + nr) / 2(nl + nr) + 1 (pair table) at nl + nr = 40,000
            (2(nl + nr) > 65536), with the left side smaller, the right side smaller, and equal sides
  multi-key two u32 keys of 2,500 distinct values each: code ranges 2,501 x 2,501 > 2^22 and distinct
            counts 2,500 x 2,500 > 2^22, so the key combine takes the pair rank (Grp.prank)
Frames are built in Bend from the formulas below (V.ucol over iota); the expected line of each case is
the model's "h=<height> ck=<checksum>" (V.ck: per column, per row, h = (h * 1000003) xor (valid ? word :
0xDEADBEEF), from 2166136261), computed here by brute force. Run from the repo root:
python3 bench/v03/gen_fastpaths_big.py
"""
from pathlib import Path

OUT = Path("tests/regress/V03_fastpaths_big.bend")
M = (1 << 32) - 1
defs, calls, expect = [], [], []


def ck(cols):
    h = 2166136261
    for col in cols:
        for v in col:
            h = ((h * 1000003) & M) ^ (0xDEADBEEF if v is None else v)
    return h


def res(cols):
    return "h=%d ck=%d" % (len(cols[0]) if cols else 0, ck(cols))


fns = {}


def fn(body):
    """a named def `+i -> U32` for a formula (a template lambda may use its argument once only)"""
    if body not in fns:
        fns[body] = "fx%d" % len(fns)
        defs.append("def %s(+i: U32) -> U32:\n  %s" % (fns[body], body))
    return fns[body]


def col(name, fexpr, zexpr, n):
    """a Bend column term: values fexpr(i) where zexpr(i) = 1 (fexpr must be 0 at null rows)"""
    return 'C.Named{"%s", V.ucol(~(i => %s(i)), ~(i => %s(i)), %d)}' % (name, fn(fexpr), fn(zexpr), n)


def frame(name, cols):
    defs.append("def %s() -> DF.ResT(DF.Frame()):\n  DF.from_columns([%s])" % (name, ", ".join(cols)))


def case(name, expr, cols):
    calls.append('    IO.print("CASE %s " ++ V.ck(%s))' % (name, expr))
    expect.append("CASE %s %s" % (name, res(cols)))


# ---- group_by: one u32 key, n = 600,000 ------------------------------------------------------------
N = 600000
for S in [2 * N - 1, 2 * N, 2 * N + 1]:
    def key(i):
        if i % 97 == 50:
            return None
        return S if i == N - 1 else (i * 1999) % S
    # Bend: the null rows answer 0; the last row answers S
    f = "Bool.pick(U32, U32.is_eq(U32.mod(i, 97), 50), 0, Bool.pick(U32, U32.is_eq(i, %d), %d, U32.mod(U32.mul(i, 1999), %d)))" % (N - 1, S, S)
    z = "Bool.pick(U32, U32.is_eq(U32.mod(i, 97), 50), 0, 1)"
    nm = "gb_%d" % S
    frame("f_" + nm, [col("k", f, z, N), col("v", "i", "1", N)])
    order, acc = [], {}
    for i in range(N):
        k = key(i)
        if k not in acc:
            acc[k] = [0, 0]
            order.append(k)
        acc[k][0] += 1
        acc[k][1] = (acc[k][1] + i) & M
    case(nm, 'DF.then(f_%s(), f => DF.group_by(f, [DF.col("k")], [DF.alias(DF.len(), "n"), DF.alias(DF.sum(DF.col("v")), "s")]))' % nm,
         [order, [acc[k][0] for k in order], [acc[k][1] for k in order]])
    seen, uk, uv = set(), [], []
    for i in range(N):
        k = key(i)
        if k not in seen:
            seen.add(k)
            uk.append(k)
            uv.append(i)
    case("uq_%d" % S, 'DF.then(f_%s(), f => DF.unique(f, ["k"]))' % nm, [uk, uv])

# ---- joins: nl + nr = 40,000 -----------------------------------------------------------------------
for nl, nr in [(20000, 20000), (10000, 30000), (30000, 10000)]:
    B = 2 * (nl + nr)
    for S in [B - 1, B, B + 1]:
        def lk(i):
            if i % 101 == 7:
                return None
            return S if i == nl - 1 else (i * 1999) % S

        def rk(j):
            if j % 103 == 11:
                return None
            return S if j == 0 else (0 if j == nr - 1 else (j * 3001 + 17) % S)
        fl = "Bool.pick(U32, U32.is_eq(U32.mod(i, 101), 7), 0, Bool.pick(U32, U32.is_eq(i, %d), %d, U32.mod(U32.mul(i, 1999), %d)))" % (nl - 1, S, S)
        zl = "Bool.pick(U32, U32.is_eq(U32.mod(i, 101), 7), 0, 1)"
        fr = ("Bool.pick(U32, U32.is_eq(U32.mod(i, 103), 11), 0, Bool.pick(U32, U32.is_eq(i, 0), %d, "
              "Bool.pick(U32, U32.is_eq(i, %d), 0, U32.mod(U32.add(U32.mul(i, 3001), 17), %d))))") % (S, nr - 1, S)
        zr = "Bool.pick(U32, U32.is_eq(U32.mod(i, 103), 11), 0, 1)"
        nm = "jn_%d_%d_%d" % (nl, nr, S)
        frame("l_" + nm, [col("k", fl, zl, nl), col("li", "i", "1", nl)])
        frame("r_" + nm, [col("k", fr, zr, nr), col("ri", "i", "1", nr)])
        bykey = {}
        for j in range(nr):
            k = rk(j)
            if k is not None:
                bykey.setdefault(k, []).append(j)
        for kind in ["inner", "left"]:
            li, ri = [], []
            for i in range(nl):
                k = lk(i)
                hits = bykey.get(k, []) if k is not None else []
                for j in hits:
                    li.append(i)
                    ri.append(j)
                if kind == "left" and not hits:
                    li.append(i)
                    ri.append(None)
            case("%s_%s" % (nm, kind),
                 'DF.then(DF.then(l_%s(), l => DF.then(r_%s(), r => DF.%s_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))' % (nm, nm, kind),
                 [li, ri])

# ---- two keys over the pair rank -------------------------------------------------------------------
NM = 5000
fa = "U32.mod(U32.mul(i, 37), 2500)"
fb = "U32.mod(U32.add(U32.mul(i, 53), 11), 2500)"
frame("f_mk", [col("a", fa, "1", NM), col("b", fb, "1", NM), col("v", "i", "1", NM)])
order, acc = [], {}
for i in range(NM):
    k = ((i * 37) % 2500, (i * 53 + 11) % 2500)
    if k not in acc:
        acc[k] = [0, 0]
        order.append(k)
    acc[k][0] += 1
    acc[k][1] = (acc[k][1] + i) & M
case("gb_mk", 'DF.then(f_mk(), f => DF.group_by(f, [DF.col("a"), DF.col("b")], [DF.alias(DF.len(), "n"), DF.alias(DF.sum(DF.col("v")), "s")]))',
     [[k[0] for k in order], [k[1] for k in order], [acc[k][0] for k in order], [acc[k][1] for k in order]])

head = '''#! native  (600,000-row frames: the interpreter would take minutes)
# v0.3 W1: the big-n sides of the fast-path switch-over points (group_by's 2n bound, the join's 2(nl + nr)
# bound, the two-key pair rank). GENERATED by bench/v03/gen_fastpaths_big.py; every expected checksum comes
# from its brute-force Python model, not from bend-frame. Edit the generator, not this file.
import Base
import ./../../frame.bend as DF
import ./../../src/column.bend as C
import ./lib/v03.bend as V
'''
src = head + "\n" + "\n\n".join(defs) + "\n\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(calls) + "\n"
src += "".join("#|" + line + "\n" for line in expect)
OUT.write_text(src)
print("wrote %s: %d cases" % (OUT, len(expect)))
