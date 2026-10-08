"""The T2.2 oracle: the expected DF.dump text of a generated case, computed with Polars 2.0.0
(structure, element-wise arithmetic, comparison, Kleene logic, sort, group keys, joins) and, where
DESIGN.md 15 DEPARTS from Polars, by the contract itself. Nothing is ignored wholesale: every
departure below is a named function with a section number.

Departures (each is one place in this file):
  15.3   strict typing and the exact TypeMismatch/ColumnNotFound texts: model.py (static check
         of the whole plan before anything runs; Polars would coerce or raise its own texts)
  15.4   cardinality: select height = 1 unless an expression is row-wise; with_columns/filter
         broadcast scalars and reductions to the input height; zero-column frames keep a height
  15.5.1 u32/i32 wrap (Polars wraps too); floor_div/mod null on zero; i32 MIN // -1 is null
         (Polars: MIN); `/` only for f32
  15.5.3 f32 sums by Neumaier with a non-finite guard, in row order (np.float32 arithmetic);
         mean/std/var of integers via f32 (Polars: f64)
  15.5.2 f32 equality/order/keys: Polars 2.0.0 agrees (verified in the contract); min/max skip NaN
  15.5.4 std/var/median as written there
  15.5.5 cast / try_cast conversions and the `cast <from> to <to>: row <i> holds <cell>` error
  15.2   verbs: group_by always first-appearance order; empty subset of unique = all columns;
         joins' `_right` suffix against ANY left name; null keys never match

Two results are produced: `eager` (verbs run one by one: a runtime error in an inner verb wins
over a static error in an outer one) and `lazy` (collect: the whole plan is typed first). They
differ only for programs that are not admissible for the T2.1 three-way comparison.
"""
from __future__ import annotations

import math
import re
import sys
from pathlib import Path

import numpy as np
import polars as pl

sys.path.append(str(Path(__file__).resolve().parents[1]))
import dump_polars as DP  # noqa: E402

import model as M  # noqa: E402
from model import KRED, KROW, KSCALAR, Ex, Pl  # noqa: E402

PLT = {"bool": pl.Boolean, "u32": pl.UInt32, "i32": pl.Int32, "f32": pl.Float32, "str": pl.String}
F32 = np.float32
CAST_FAIL_ROWS = None


class RuntimeErr(Exception):
    """A data-dependent error (cast failure): .text is Err.show's rendering."""

    def __init__(self, text):
        super().__init__(text)
        self.text = text


class Uncertain(Exception):
    """The oracle cannot answer faithfully (case marked T2.1-only, and counted)."""


def mkseries(name, dt, vals):
    return pl.Series(name, vals, dtype=PLT[dt])


def dtn(s: pl.Series) -> str:
    return DP.dtype_name(s.dtype)


class OF:
    """An oracle frame: named Series and an explicit height (a zero-column frame has one)."""

    def __init__(self, cols, h):
        self.cols = [c for c in cols]
        self.h = h

    @staticmethod
    def of(f: M.Frame):
        return OF([mkseries(c.name, c.dtype, c.vals) for c in f.cols], f.height)

    def get(self, n):
        for c in self.cols:
            if c.name == n:
                return c
        raise KeyError(n)

    def df(self):
        return pl.DataFrame(self.cols)


# ---- 15.4 broadcasting -----------------------------------------------------------------------

def bc(s: pl.Series, h: int) -> pl.Series:
    if len(s) == h:
        return s
    assert len(s) == 1, (len(s), h)
    return s.new_from_index(0, h)


def bc2(a, b):
    if len(a) == len(b):
        return a, b
    if len(a) == 1:
        return a.new_from_index(0, len(b)), b
    if len(b) == 1:
        return a, b.new_from_index(0, len(a))
    raise AssertionError((len(a), len(b)))


# ---- 15.5.3 accumulation ------------------------------------------------------------------------

def _fin(x):
    return bool(np.isfinite(x))


def neumaier(xs):
    """Sum of f32 values in order (15.5.3). xs: iterable of np.float32."""
    with np.errstate(all="ignore"):
        s = F32(0.0)
        c = F32(0.0)
        for x in xs:
            x = F32(x)
            t = F32(s + x)
            if _fin(t):
                if abs(s) >= abs(x):
                    c = F32(c + F32(F32(s - t) + x))
                else:
                    c = F32(c + F32(F32(x - t) + s))
            s = t
        return F32(s + c) if _fin(s) else s


def to_f32s(dt, vals):
    return [F32(v) for v in vals]


def fkey(dt, v):
    return M.val_key(dt, v)


def fmin2(a, b):
    if math.isnan(a):
        return b
    if math.isnan(b):
        return a
    if a < b:
        return a
    if b < a:
        return b
    return a if math.copysign(1.0, a) < 0 else b


def fmax2(a, b):
    if math.isnan(a):
        return b
    if math.isnan(b):
        return a
    if a > b:
        return a
    if b > a:
        return b
    return a if math.copysign(1.0, a) > 0 else b


def wrap_u32(v):
    return v % 2**32


def wrap_i32(v):
    v = v % 2**32
    return v - 2**32 if v >= 2**31 else v


def f(x):
    return float(F32(x))


def reduce_(op, dt, vals):
    """(result dtype, value) of the reducer over a list of cells (None = null)."""
    valid = [v for v in vals if v is not None]
    n = len(valid)
    if op == "len":
        return "u32", len(vals)
    if op == "count":
        return "u32", n
    if op == "first":
        return dt, (vals[0] if vals else None)
    if op == "last":
        return dt, (vals[-1] if vals else None)
    if op == "n_unique":
        return "u32", len({fkey(dt, v) for v in vals})
    if op == "sum":
        if dt == "u32":
            return dt, wrap_u32(sum(valid))
        if dt == "i32":
            return dt, wrap_i32(sum(valid))
        return dt, f(neumaier(F32(v) for v in valid))
    if op == "mean":
        if n == 0:
            return "f32", None
        with np.errstate(all="ignore"):
            return "f32", f(F32(neumaier(F32(v) for v in valid) / F32(n)))
    if op in ("min", "max"):
        if n == 0:
            return dt, None
        if dt == "f32":
            fn = fmin2 if op == "min" else fmax2
            r = valid[0]
            for v in valid[1:]:
                r = fn(r, v)
            return dt, r
        return dt, (min(valid) if op == "min" else max(valid))
    if op in ("std", "var"):
        if n < 2:
            return "f32", None
        xs = [F32(v) for v in valid]
        with np.errstate(all="ignore"):
            m = F32(neumaier(xs) / F32(n))
            terms = [F32(F32(x - m) * F32(x - m)) for x in xs]
            v = F32(neumaier(terms) / F32(n - 1))
            if any(math.isnan(float(x)) or math.isinf(float(x)) for x in xs):
                v = F32(float("nan"))
            return "f32", f(np.sqrt(v) if op == "std" else v)
    if op == "median":
        if n == 0:
            return "f32", None
        xs = [float(F32(v)) for v in valid]
        xs.sort(key=lambda x: (1, 0.0) if math.isnan(x) else (0, 0.0 if x == 0 else x))
        if n % 2:
            return "f32", xs[(n - 1) // 2]
        lo, hi = xs[n // 2 - 1], xs[n // 2]
        with np.errstate(all="ignore"):
            return "f32", f(F32(F32(lo) * F32(0.5)) + F32(F32(hi) * F32(0.5)))
    raise NotImplementedError(op)


# ---- 15.5.5 casts ---------------------------------------------------------------------------------

_F32_RE = re.compile(r"[+-]?([0-9]+\.?[0-9]*|\.[0-9]+)([eE][+-]?[0-9]+)?")


def cast_cell(frm, to, v):
    """The converted cell, or raises ValueError (the cell does not convert)."""
    if v is None:
        return None
    if frm == to:
        return v
    if to == "str":
        if frm == "bool":
            return "true" if v else "false"
        if frm == "f32":
            return M.f32_show(v)
        return str(v)
    if frm == "bool":
        return float(v) if to == "f32" else int(v)
    if frm == "u32":
        if to == "i32":
            if v >= 2**31:
                raise ValueError
            return v
        return f(F32(v))
    if frm == "i32":
        if to == "u32":
            if v < 0:
                raise ValueError
            return v
        return f(F32(v))
    if frm == "f32":
        if math.isnan(v) or math.isinf(v):
            raise ValueError
        if to == "u32":
            if not (v > -1.0 and v < 4294967296.0):
                raise ValueError
            return int(math.trunc(v))
        if not (v >= -2147483648.0 and v < 2147483648.0):
            raise ValueError
        return int(math.trunc(v))
    if frm == "str":
        if to == "bool":
            if v in ("true", "True"):
                return True
            if v in ("false", "False"):
                return False
            raise ValueError
        if to == "u32":
            if re.fullmatch(r"[0-9]+", v) and int(v) <= M.U32_MAX:
                return int(v)
            raise ValueError
        if to == "i32":
            if re.fullmatch(r"-?[0-9]+", v) and M.I32_MIN <= int(v) <= M.I32_MAX:
                return int(v)
            raise ValueError
        if v in ("nan", "NaN"):
            return float("nan")
        if v in ("inf", "+inf"):
            return float("inf")
        if v == "-inf":
            return float("-inf")
        if _F32_RE.fullmatch(v):
            return f(F32(float(v)))
        raise ValueError
    raise NotImplementedError((frm, to))


def cast_series(s: pl.Series, frm, to, strict, name=None):
    vals = s.to_list()
    out = []
    for i, v in enumerate(vals):
        try:
            out.append(cast_cell(frm, to, v))
        except ValueError:
            if strict:
                raise RuntimeErr(f"InvalidOperation: cast {frm} to {to}: row {i} holds {M.show_lit(frm, v)}")
            out.append(None)
    return mkseries(s.name, to, out)


# ---- expression evaluation --------------------------------------------------------------------------

def ev(e: Ex, of: OF, schema):
    """(Series, kind): row-wise series have the frame height; scalar/red ones have length 1."""
    o = e.op
    if o == "col":
        return of.get(e.p[0]).clone(), KROW
    if o == "lit":
        dt, v = e.p
        return mkseries("literal", dt, [v]), KSCALAR
    if o == "alias":
        return ev(e.args[0], of, schema)
    spec = M.EXPRS[o]
    rs = [ev(a, of, schema) for a in e.args]
    ss = [r[0] for r in rs]
    ks = [r[1] for r in rs]
    ts = [dtn(s) for s in ss]
    if spec.red:
        if o == "len":
            return mkseries("literal", "u32", [of.h]), KRED
        s = ss[0]   # a scalar argument is ONE value (Polars: `pl.lit(1).sum()` is 1); len() counts rows
        dt, v = reduce_(o, ts[0], s.to_list())
        return mkseries("literal", dt, [v]), KRED
    kind = M.kjoin(*ks)
    return IMPL[o](ss, ts, e.p, of), kind


def impl_bin(fn):
    def g(ss, ts, p, of):
        a, b = bc2(ss[0], ss[1])
        return fn(a, b)
    return g


def _floordiv(a, b):
    r = a // b
    if dtn(a) == "i32":
        # contract 15.5.1: MIN // -1 is null (Polars: MIN)
        bad = (a == M.I32_MIN) & (b == -1)
        r = pl.select(pl.when(bad.fill_null(False)).then(None).otherwise(r)).to_series()
    return r.cast(a.dtype)


def _cmp(fn):
    return impl_bin(fn)


def _neg(ss, ts, p, of):
    return -ss[0]


def _abs(ss, ts, p, of):
    return ss[0].abs()


def _sqrt(ss, ts, p, of):
    return ss[0].sqrt().cast(pl.Float32)


def _fill(ss, ts, p, of):
    a, b = bc2(ss[0], ss[1])
    return a.zip_with(a.is_not_null(), b)


def _when(ss, ts, p, of):
    n = next((len(s) for s in ss if len(s) != 1), 1)
    c, a, b = (bc(s, n) for s in ss)
    return a.zip_with(c.fill_null(False), b)


def _cast(strict):
    def g(ss, ts, p, of):
        return cast_series(ss[0], ts[0], p[0], strict)
    return g


def _is_in(ss, ts, p, of):
    dt, vals = p
    keys = {M.val_key(dt, v) for v in vals}
    out = [None if v is None else (M.val_key(dt, v) in keys) for v in ss[0].to_list()]
    return mkseries("literal", "bool", out)


def _clip(ss, ts, p, of):
    dt, lo, hi = p
    out = []
    for v in ss[0].to_list():
        if v is None:
            out.append(None)
        elif v < lo:
            out.append(lo)
        elif v > hi:
            out.append(hi)
        else:
            out.append(v)
    return mkseries("literal", dt, out)


def _strmap(fn, dt):
    def g(ss, ts, p, of):
        return mkseries("literal", dt, [None if v is None else fn(v, p) for v in ss[0].to_list()])
    return g


IMPL = {
    "add": impl_bin(lambda a, b: a + b),
    "sub": impl_bin(lambda a, b: a - b),
    "mul": impl_bin(lambda a, b: a * b),
    "div": impl_bin(lambda a, b: a / b),
    "floor_div": impl_bin(_floordiv),
    "mod": impl_bin(lambda a, b: a % b),
    "eq": _cmp(lambda a, b: a == b),
    "ne": _cmp(lambda a, b: a != b),
    "lt": _cmp(lambda a, b: a < b),
    "le": _cmp(lambda a, b: a <= b),
    "gt": _cmp(lambda a, b: a > b),
    "ge": _cmp(lambda a, b: a >= b),
    "and": impl_bin(lambda a, b: a & b),
    "or": impl_bin(lambda a, b: a | b),
    "not": lambda ss, ts, p, of: ~ss[0],
    "neg": _neg,
    "abs": _abs,
    "sqrt": _sqrt,
    "is_null": lambda ss, ts, p, of: ss[0].is_null(),
    "is_not_null": lambda ss, ts, p, of: ss[0].is_not_null(),
    "fill_null": _fill,
    "cast": _cast(True),
    "try_cast": _cast(False),
    "when": _when,
    "is_in": _is_in,
    "clip": _clip,
    "len_chars": _strmap(lambda v, p: len(v), "u32"),
    "contains_literal": _strmap(lambda v, p: p[0] in v, "bool"),
    "starts_with": _strmap(lambda v, p: v.startswith(p[0]), "bool"),
    "ends_with": _strmap(lambda v, p: v.endswith(p[0]), "bool"),
}


# ---- verbs -------------------------------------------------------------------------------------------

def named(s, n):
    return s.alias(n)


def o_select(of, p, schema):
    exprs, = p
    outs = [(M.name_of(e), *ev(e, of, schema)) for e in exprs]
    if not outs:
        return OF([], 0)
    h = of.h if any(k == KROW for _, _, k in outs) else 1
    return OF([named(bc(s, h), n) for n, s, k in outs], h)


def o_with(of, p, schema):
    exprs, = p
    outs = [(M.name_of(e), *ev(e, of, schema)) for e in exprs]
    cols = list(of.cols)
    for n, s, k in outs:
        s = named(bc(s, of.h), n)
        for i, c in enumerate(cols):
            if c.name == n:
                cols[i] = s
                break
        else:
            cols.append(s)
    return OF(cols, of.h)


def o_filter(of, p, schema):
    pred, = p
    s, k = ev(pred, of, schema)
    mask = bc(s, of.h).fill_null(False)
    kept = int(mask.sum()) if of.h else 0
    return OF([c.filter(mask) for c in of.cols], kept)


def o_sort(of, p, schema):
    keys, = p
    seen, ks = set(), []
    for n, d, nl in keys:
        if n not in seen:
            seen.add(n)
            ks.append((n, d, nl))
    if not ks or of.h == 0:
        return of
    # 15.5.2: -0.0 and 0.0 are equal keys, so ties keep input order: sort by a canonical key
    # (x + 0.0 turns -0.0 into 0.0) and gather the untouched rows (Polars orders -0.0 before 0.0)
    kcols = []
    for n, d, nl in ks:
        c = of.get(n)
        kcols.append((c + 0.0).alias(n) if dtn(c) == "f32" else c)
    kdf = pl.DataFrame(kcols).with_row_index("__i")
    idx = kdf.sort([k[0] for k in ks], descending=[k[1] for k in ks], nulls_last=[k[2] for k in ks],
                   maintain_order=True).get_column("__i")
    return OF([c.gather(idx) for c in of.cols], of.h)


def o_head(of, p, schema):
    n = p[0]
    k = min(n, of.h)
    return OF([c.head(k) for c in of.cols], k)


def o_slice(of, p, schema):
    off, ln = p
    start = min(off, of.h)
    cnt = min(ln, of.h - start)
    return OF([c.slice(start, cnt) for c in of.cols], cnt)


def o_tail(of, p, schema):
    k = min(p[0], of.h)
    return OF([c.slice(of.h - k, k) for c in of.cols], k)


def o_drop(of, p, schema):
    names, = p
    return OF([c for c in of.cols if c.name not in names], of.h)


def o_rename(of, p, schema):
    pairs, = p
    m = dict(pairs)
    return OF([c.alias(m.get(c.name, c.name)) for c in of.cols], of.h)


def o_unique(of, p, schema):
    subset, = p
    if not of.cols:
        k = min(of.h, 1)
        return OF([], k)
    subset = list(subset) or [c.name for c in of.cols]
    if of.h == 0:
        return of
    df = of.df().unique(subset=subset, keep="first", maintain_order=True)
    return OF(df.get_columns(), df.height)


def o_concat(ofs, p, schema):
    h = sum(o.h for o in ofs)
    if not ofs[0].cols:
        return OF([], h)
    df = pl.concat([o.df() for o in ofs], how="vertical")
    return OF(df.get_columns(), df.height)


def peel(e):
    while e.op == "alias":
        e = e.args[0]
    return e


def o_group(of, p, schema):
    keys, aggs = p
    h = of.h
    kcols = []
    for k in keys:
        s, kind = ev(k, of, schema)
        kcols.append(named(bc(s, h), M.name_of(k)))
    # grouping: first-appearance order, one group per key tuple under the 15.5.2 relation
    if h == 0:
        groups = []
        keyout = [c.clear() for c in kcols]
    else:
        kdf = pl.DataFrame(kcols).with_row_index("__row")
        g = kdf.group_by([c.name for c in kcols], maintain_order=True).agg(pl.col("__row"))
        groups = [list(map(int, r)) for r in g.get_column("__row").to_list()]
        keyout = [g.get_column(c.name) for c in kcols]
    outs = list(keyout)
    for a in aggs:
        x = peel(a)
        n = M.name_of(a)
        if x.op == "len":
            outs.append(mkseries(n, "u32", [len(ix) for ix in groups]))
            continue
        s, kind = ev(x.args[0], of, schema)
        # a scalar argument is one value per group, not the group's rows broadcast
        s = s if kind == KSCALAR else bc(s, h)
        dt = dtn(s)
        vals = s.to_list()
        res_dt, res = None, []
        for ix in groups:
            res_dt, v = reduce_(x.op, dt, vals if kind == KSCALAR else [vals[i] for i in ix])
            res.append(v)
        if res_dt is None:
            res_dt = M.EXPRS[x.op].typ((dt,), x.p)
        outs.append(mkseries(n, res_dt, res))
    return OF(outs, len(groups))


def o_join(how):
    def g(l: OF, r: OF, p, schema_out):
        lo, ro = p
        pairs = list(dict.fromkeys(zip(lo, ro)))      # an identical pair twice is one condition
        if len({a for a, _ in pairs}) != len(pairs) or len({b for _, b in pairs}) != len(pairs):
            raise Uncertain("a key column used in two pairs (Polars refuses repeated key names)")
        lo, ro = [a for a, _ in pairs], [b for _, b in pairs]
        ldf, rdf = l.df(), r.df()
        if how in ("semi", "anti"):
            res = ldf.join(rdf, left_on=list(lo), right_on=list(ro), how=how, maintain_order="left", nulls_equal=False)
            return OF(res.get_columns(), res.height)
        res = ldf.join(rdf, left_on=list(lo), right_on=list(ro), how=how, maintain_order="left_right",
                       nulls_equal=False, coalesce=True, suffix="_right")
        want = [n for n, _ in schema_out]
        if res.columns != want:
            raise Uncertain(f"join columns {res.columns} vs contract {want}")
        return OF(res.get_columns(), res.height)
    return g


UNARY = {"select": o_select, "with_columns": o_with, "filter": o_filter, "sort": o_sort, "group_by": o_group,
         "head": o_head, "slice": o_slice, "tail": o_tail, "drop": o_drop, "rename": o_rename, "unique": o_unique}
JOINS = {"inner_join": o_join("inner"), "left_join": o_join("left"), "semi_join": o_join("semi"), "anti_join": o_join("anti")}


def run_plan(pl_: Pl, srcs: dict, sources_schema):
    """Evaluate bottom-up; returns an OF. Raises RuntimeErr (runtime) or M.TErr (static, from the
    verbs' own typing on the way up: eager semantics)."""
    if pl_.verb == "source":
        return OF([c.clone() for c in srcs[pl_.p[0]].cols], srcs[pl_.p[0]].h)
    if pl_.verb == "concat_vertical":
        # input by input: an input's own errors, then its schema against input 0's (model.concat_schema)
        kids = []
        M.concat_schema(pl_.kids, lambda k: kids.append(run_plan(k, srcs, sources_schema)) or [(c.name, dtn(c)) for c in kids[-1].cols])
        return o_concat(kids, pl_.p, None)
    kids = [run_plan(k, srcs, sources_schema) for k in pl_.kids]
    ins = [[(c.name, dtn(c)) for c in k.cols] for k in kids]
    out_schema = M.VERBS[pl_.verb].sch(pl_.p, ins)      # static check of THIS verb (eager)
    v = pl_.verb
    if v in UNARY:
        return UNARY[v](kids[0], pl_.p, ins[0])
    if v in JOINS:
        return JOINS[v](kids[0], kids[1], pl_.p, out_schema)
    raise NotImplementedError(v)


# ---- dumps ---------------------------------------------------------------------------------------------

def dump_of(of: OF) -> str:
    lines = ["frame", f"height\t{of.h}", f"width\t{len(of.cols)}"]
    cells = [DP.column_cells(c, c.name) for c in of.cols]
    for c in of.cols:
        lines.append(f"col\t{dtn(c)}\t{DP.quote(c.name)}")
    if of.cols:
        for i in range(of.h):
            lines.append("row\t" + "\t".join(col[i] for col in cells))
    return "\n".join(lines) + "\n"


def err_dump(text: str) -> str:
    return DP.dump_error(text)


def expected(case: M.Case) -> dict:
    """{'eager': dump, 'lazy': dump, 'admissible': bool}; raises Uncertain when it cannot say."""
    sources = case.sources()
    static = None
    try:
        M.plan_schema(case.plan, sources)
    except M.TErr as e:
        static = e.text
    srcs = {k: OF.of(v) for k, v in case.inputs.items()}
    # eager: verb by verb
    try:
        res = run_plan(case.plan, srcs, sources)
        eager = dump_of(res)
    except M.TErr as e:
        eager = err_dump(e.text)
    except RuntimeErr as e:
        eager = err_dump(e.text)
    if static is not None:
        lazy = err_dump(static)
    else:
        lazy = eager
    return {"eager": eager, "lazy": lazy, "admissible": eager == lazy}
