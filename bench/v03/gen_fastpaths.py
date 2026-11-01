"""v0.3 W1: generator of tests/regress/V03_fastpaths.bend, the targeted tests of the v0.2 fast paths.

Run from the repo root:  python3 bench/v03/gen_fastpaths.py
Every expected line comes from the brute-force model below (Python, independent of bend-frame), rendered
in DF.dump's text format (DESIGN.md 15.1). The cases sit on the switch-over points of the fast paths:
  group_by / unique  a word key is coded directly when its span < max(2^20, 2n) (Grp.direct), else by rank;
                     two keys combine without densify when the product of their code ranges is <= 2^22
                     (Grp.fits; a direct code range is span + 2), else densify first
  join               a word key gets direct-address ids when its span < max(65536, 2(nl + nr))
                     (Join.narrow), else the pair table; the smaller side builds
  filter             kept * 8 <= height gathers the kept rows (Kernel.where + Frame.take_rows),
                     otherwise the mask compaction
The big-n sides of these boundaries (2n > 2^20, 2(nl + nr) > 65536) are in V03_fastpaths_big.bend
(native; bench/v03/gen_fastpaths_big.py).
"""
from pathlib import Path

OUT = Path("tests/regress/V03_fastpaths.bend")
M32 = 1 << 32
I32MIN, I32MAX = -(1 << 31), (1 << 31) - 1

defs, calls, expect = [], [], []


# ---- model: DF.dump text --------------------------------------------------------------------------
def cell(t, x):
    if x is None:
        return "null"
    if t == "str":
        return '"%s"' % x
    return str(x)


def dump(cols, err=None):
    """cols: [(name, dtype, values)]"""
    if err is not None:
        return "error\t%s\n" % err
    h = len(cols[0][2]) if cols else 0
    s = "frame\nheight\t%d\nwidth\t%d\n" % (h, len(cols))
    for n, t, _ in cols:
        s += 'col\t%s\t"%s"\n' % (t, n)
    for i in range(h):
        s += "row\t" + "\t".join(cell(t, v[i]) for _, t, v in cols) + "\n"
    return s


# ---- Bend source helpers ----------------------------------------------------------------------------
def scal(t, x):
    if x is None:
        return "R.null()"
    if t == "u32":
        return "R.u(%d)" % x
    if t == "i32":
        return "R.i(%d)" % (x % M32)
    if t == "str":
        return 'R.s("%s")' % x
    raise ValueError(t)


TY = {"u32": "D.TU32{}", "i32": "D.TI32{}", "str": "D.TStr{}"}


def frame(name, cols, dict_strings=False):
    body = "R.frame([" + ", ".join(
        'R.mk("%s", [%s], %s)' % (n, ", ".join(scal(t, x) for x in v), TY[t]) for n, t, v in cols) + "])"
    if dict_strings:
        body = "DF.then(%s, f => Done{DF.encode_strings(f, True{})})" % body
    defs.append("def %s() -> DF.ResT(DF.Frame()):\n  %s" % (name, body))


def case(name, expr, text, io=False):
    """expr: a DF.ResT(DF.Frame()) term, or (io=True) an IO(DF.ResT(DF.Frame())) term"""
    if io:
        calls.append('    r_%s : DF.ResT(DF.Frame()) <- %s\n    IO.print("CASE %s\\n" ++ DF.dump(r_%s))' % (name, expr, name, name))
    else:
        calls.append('    IO.print("CASE %s\\n" ++ DF.dump(%s))' % (name, expr))
    expect.append("CASE %s\n%s\n" % (name, text))


# ---- model: verbs -----------------------------------------------------------------------------------
def group_by(rows, keyix, vix):
    """first-appearance groups (null is a key value); per group: len and the u32 sum of v (nulls skipped)"""
    order, acc = [], {}
    for r in rows:
        k = tuple(r[i] for i in keyix)
        if k not in acc:
            acc[k] = [0, 0]
            order.append(k)
        acc[k][0] += 1
        if r[vix] is not None:
            acc[k][1] = (acc[k][1] + r[vix]) % M32
    return order, acc


def unique(rows, keyix):
    seen, out = set(), []
    for r in rows:
        k = tuple(r[i] for i in keyix)
        if k not in seen:
            seen.add(k)
            out.append(r)
    return out


def join(l, r, kind):
    """rows (li, ri) of an inner / left join on key lists l, r (null never matches), left order then right order"""
    out = []
    for a, x in enumerate(l):
        hits = [b for b, y in enumerate(r) if x is not None and y == x]
        out += [(a, b) for b in hits]
        if kind == "left" and not hits:
            out.append((a, None))
    return out


def cols_of(rows, spec):
    return [(n, t, [r[i] for r in rows]) for i, (n, t) in enumerate(spec)]


# ---- group_by and unique ----------------------------------------------------------------------------
GB = 'DF.then(%s(), f => DF.group_by(f, [%s], [DF.alias(DF.len(), "n"), DF.alias(DF.sum(DF.col("v")), "s")]))'


def gb_case(name, kspec, rows):
    """kspec: [(name, dtype)] of the keys; rows: key values then v (u32)"""
    spec = kspec + [("v", "u32")]
    frame("f_" + name, cols_of(rows, spec))
    keys = ", ".join('DF.col("%s")' % n for n, _ in kspec)
    order, acc = group_by(rows, list(range(len(kspec))), len(kspec))
    out = [list(k) + acc[k] for k in order]
    case("gb_" + name, GB % ("f_" + name, keys), dump(cols_of(out, kspec + [("n", "u32"), ("s", "u32")])))
    sub = ", ".join('"%s"' % n for n, _ in kspec)
    case("uq_" + name, 'DF.then(f_%s(), f => DF.unique(f, [%s]))' % (name, sub),
         dump(cols_of(unique(rows, list(range(len(kspec)))), spec)))


# one u32 key: span 2^20 - 1 is coded directly, 2^20 by rank (n = 8: 2n is far below 2^20)
for S in [(1 << 20) - 1, 1 << 20]:
    ks = [0, S, 5, S, None, 5, 0, 1]
    gb_case("u_%d" % S, [("k", "u32")], [(k, v) for k, v in zip(ks, [1, 2, 3, 4, 5, 6, 7, 8])])
# i32 extremes (span 2^32 - 1: rank) and a narrow range across zero (direct)
gb_case("i_ext", [("k", "i32")], [(k, v) for k, v in zip([I32MIN, I32MAX, 0, -1, I32MIN, None, -1, I32MAX], range(1, 9))])
gb_case("i_narrow", [("k", "i32")], [(k, v) for k, v in zip([-3, 3, 0, -3, None, 2, 3], range(10, 17))])
# two u32 keys: code ranges s1 + 2 and 2046 + 2 = 2048; the product fits 2^22 for s1 + 2 <= 2048
for s1 in [2045, 2046, 2047]:
    k1 = [0, s1, 5, 0, s1, None, 5, s1, 0]
    k2 = [0, 2046, 7, 0, 7, 7, None, 2046, 2046]
    gb_case("m_%d" % s1, [("a", "u32"), ("b", "u32")], [(a, b, v) for a, b, v in zip(k1, k2, range(1, 10))])

# ---- joins -----------------------------------------------------------------------------------------
JN = 'DF.then(DF.then(%s(), l => DF.then(%s(), r => DF.%s_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))'


def jn_cases(name, lt, lk, rt, rk):
    frame("jl_" + name, [("k", lt, lk), ("li", "u32", list(range(len(lk))))])
    frame("jr_" + name, [("k", rt, rk), ("ri", "u32", list(range(len(rk))))])
    for kind in ["inner", "left"]:
        rows = join(lk, rk, kind)
        case("jn_%s_%s" % (name, kind), JN % ("jl_" + name, "jr_" + name, kind),
             dump([("li", "u32", [a for a, _ in rows]), ("ri", "u32", [b for _, b in rows])]))


# span 65535 gives direct ids, 65536 the pair table (nl + nr = 12: 2(nl + nr) is far below 65536);
# smaller left (left builds), smaller right, equal sizes
for S in [65535, 65536]:
    L = [0, S, 7, None, 7]
    R = [S, 7, 7, 0, 3, None, S]
    jn_cases("u%d_sl" % S, "u32", L, "u32", R)
    jn_cases("u%d_sr" % S, "u32", R, "u32", L)
    jn_cases("u%d_eq" % S, "u32", L + [S, 1], "u32", R)
jn_cases("i_ext", "i32", [I32MIN, I32MAX, 0, None, -1], "i32", [I32MAX, I32MIN, I32MIN, 5, -1])
jn_cases("i_narrow", "i32", [-2, 2, 0, None], "i32", [2, -2, -2, 0, 9, None])
# strings: the build side is always the right one; here the right table is the larger one
jn_cases("s_bigr", "str", ["a", "b", "c", None, "b"], "str", ["b", "a", "x", "b", "y", "z", None, "a", "c"])
jn_cases("s_bigl", "str", ["b", "a", "x", "b", "y", "z", None, "a", "c"], "str", ["a", "b", "c", None, "b"])
# both empty, one empty
jn_cases("empty_l", "u32", [], "u32", [1, 2, None])
jn_cases("empty_r", "u32", [1, None, 1], "u32", [])
jn_cases("empty_both", "u32", [], "u32", [])
# a key dtype mismatch: the same error in the eager verb and both lazy engines
frame("jm_l", [("k", "u32", [1, 2]), ("li", "u32", [0, 1])])
frame("jm_r", [("k", "i32", [1, 2]), ("ri", "u32", [0, 1])])
ERR = "TypeMismatch in join: expected u32, got i32"
case("jn_mismatch_eager", 'DF.then(jm_l(), l => DF.then(jm_r(), r => DF.inner_join(l, r, ["k"], ["k"])))', dump(None, ERR))
# (the lazy engines' agreement on join errors is covered by tests/regress B04)

# ---- selective filters -----------------------------------------------------------------------------
H = 200
ids = list(range(H))
vs = [None if i % 7 == 3 else i for i in ids]
ss = ["s%d" % (i % 13) for i in ids]
frame("ff_raw", [("id", "u32", ids), ("v", "u32", vs), ("s", "str", ss)])
frame("ff_dict", [("id", "u32", ids), ("v", "u32", vs), ("s", "str", ss)], dict_strings=True)


def k_for(kept):
    """the smallest K with #{i : v[i] != null and v[i] < K} = kept"""
    for K in range(0, H + 2):
        if sum(1 for v in vs if v is not None and v < K) == kept:
            return K
    raise ValueError(kept)


FOLLOW = {
    "none": (None, lambda r: [("id", "u32", [x[0] for x in r]), ("v", "u32", [x[1] for x in r]), ("s", "str", [x[2] for x in r])]),
    "sel": ('[DF.col("id"), DF.col("s")]', lambda r: [("id", "u32", [x[0] for x in r]), ("s", "str", [x[2] for x in r])]),
    "expr": ('[DF.alias(DF.mul(DF.col("id"), DF.lit_u32(2)), "id2"), DF.col("s")]',
             lambda r: [("id2", "u32", [2 * x[0] for x in r]), ("s", "str", [x[2] for x in r])]),
}
nonnull = sum(1 for v in vs if v is not None)
for kept in [0, 1, H // 8, H // 8 + 1, 16, 32, 64, 128, nonnull]:
    K = k_for(kept)
    pred = 'DF.lt(DF.col("v"), DF.lit_u32(%d))' % K
    rows = [(i, v, s) for i, v, s in zip(ids, vs, ss) if v is not None and v < K]
    assert len(rows) == kept
    for fname, (sel, model) in FOLLOW.items():
        text = dump(model(rows))
        eager = "DF.filter(f, %s)" % pred
        lazyq = "DF.lazy_filter(p, %s)" % pred
        if sel:
            eager = "DF.then(%s, g => DF.select(g, %s))" % (eager, sel)
            lazyq = "DF.lazy_select(%s, %s)" % (lazyq, sel)
        storages = ["raw", "dict"] if fname == "none" else ["raw"]
        for st in storages:
            nm = "fl_%d_%s_%s" % (kept, fname, st)
            case(nm, "DF.then(ff_%s(), f => %s)" % (st, eager), text)
            if kept in (0, H // 8, H // 8 + 1, nonnull) or fname == "expr":
                for g in [2, 4]:
                    case("%s_cx%d" % (nm, g), "DF.then_io(ff_%s(), f => V.cx(%dn, p => %s, f))" % (st, g, lazyq), text, io=True)
                case("%s_lazy" % nm, "DF.then_io(ff_%s(), f => V.lz(p => %s, f))" % (st, lazyq), text, io=True)

# ---- write -----------------------------------------------------------------------------------------
head = '''# v0.3 W1: targeted tests of the v0.2 fast paths (group_by / unique direct codes and the key combine, the
# join's direct-address ids and build side, selective filters through Kernel.where + Frame.take_rows),
# at their switch-over points. GENERATED by bench/v03/gen_fastpaths.py; the expected lines come from its
# brute-force Python model, not from bend-frame. Edit the generator, not this file.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./lib/rx.bend as R
import ./lib/v03.bend as V
'''
src = head + "\n" + "\n\n".join(defs) + "\n\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(calls) + "\n"
src += "".join("#|" + line + "\n" for line in "".join(expect).rstrip("\n").split("\n"))
OUT.write_text(src)
print("wrote %s: %d cases, %d expected lines" % (OUT, len(expect), sum(e.count("\n") for e in expect)))
