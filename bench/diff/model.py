"""The differential generator's model: dtypes, frames, expression and plan trees, the
contract's typing rules (DESIGN.md 15.3), tables of expression operators and plan verbs.

Everything the generator, the Bend emitter and the oracle need to agree on lives here, and
every operator is ONE ROW in a table (EXPRS, VERBS): adding a verb the facade grows later is
a new row plus (for the oracle) one function. A row names the facade defs it `needs`; the
generator only uses rows whose defs exist in frame.bend (see `facade_defs`), so a landed verb
switches itself on.

Typing here is the CONTRACT's (DESIGN.md 15), not today's behaviour: where main differs the
case fails, and that is the point.
"""
from __future__ import annotations

import math
import re
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
DTYPES = ("bool", "u32", "i32", "f32", "str")
NUMERIC = ("u32", "i32", "f32")
U32_MAX = 2**32 - 1
I32_MIN, I32_MAX = -(2**31), 2**31 - 1


# ---- f32 helpers --------------------------------------------------------------------------

def f32(x: float) -> float:
    """x rounded to the nearest f32, as a Python float (NaN stays NaN, -0.0 stays -0.0)."""
    return float(np.float32(x))


def f32bits(x: float) -> int:
    return struct.unpack(">I", struct.pack(">f", x))[0]


def bits_f32(b: int) -> float:
    return struct.unpack(">f", struct.pack(">I", b))[0]


def f32_text(x: float) -> str:
    """A Bend F32 literal's decimal text for a finite non-negative f32 (no exponent)."""
    t = np.format_float_positional(np.float32(x), unique=True, trim="-")
    if "." not in t:
        t += ".0"
    return t


def f32_show(x: float) -> str:
    """Bend's F32.show (JavaScript Number-to-string of the shortest f32 digits)."""
    if math.isnan(x):
        return "nan"
    if math.isinf(x):
        return "inf" if x > 0 else "-inf"
    if x == 0:
        return "-0" if math.copysign(1.0, x) < 0 else "0"
    sign = "-" if x < 0 else ""
    t = np.format_float_scientific(np.float32(abs(x)), unique=True, trim="-")
    mant, _, ex = t.partition("e")
    digits = mant.replace(".", "")
    e10 = int(ex)
    n = len(digits)
    if -7 <= e10 < 21:
        if e10 >= n - 1:
            body = digits + "0" * (e10 - n + 1)
        elif e10 >= 0:
            body = digits[: e10 + 1] + "." + digits[e10 + 1:]
        else:
            body = "0." + "0" * (-e10 - 1) + digits
    else:
        body = digits[0] + ("." + digits[1:] if n > 1 else "") + "e" + ("+" if e10 > 0 else "-") + str(abs(e10))
    return sign + body


def val_key(dt: str, v):
    """A hashable key of a cell under the contract's equality relation (15.5.2)."""
    if v is None:
        return ("null",)
    if dt == "f32":
        if math.isnan(v):
            return ("nan",)
        return ("f", 0.0 if v == 0 else v)
    return (v,)


# ---- frames -------------------------------------------------------------------------------

@dataclass
class Col:
    name: str
    dtype: str
    vals: list  # None = null; f32 values are Python floats already rounded to f32


@dataclass
class Frame:
    cols: list
    height: int

    @property
    def schema(self):
        return [(c.name, c.dtype) for c in self.cols]


# ---- expressions --------------------------------------------------------------------------

@dataclass(frozen=True)
class Ex:
    """op: col lit alias or an EXPRS key. args: child Ex tuple. p: non-expression parameters.
    col p=(name,)  lit p=(dtype, value|None)  alias p=(name,)  cast/try_cast p=(dtype,)
    is_in p=(dtype, vals)  clip p=(dtype, lo, hi)  str preds p=(pat,)."""
    op: str
    args: tuple = ()
    p: tuple = ()


def col(n):
    return Ex("col", (), (n,))


def lit(dt, v):
    return Ex("lit", (), (dt, v))


def alias(e, n):
    return Ex("alias", (e,), (n,))


class TErr(Exception):
    """A static (typing / shape) error; .text is Err.show's rendering."""

    def __init__(self, text):
        super().__init__(text)
        self.text = text


def mismatch(op, want, got):
    return TErr(f"TypeMismatch in {op}: expected {want}, got {got}")


def invalid(what):
    return TErr(f"InvalidOperation: {what}")


# ---- Expr.show (src/expr.bend + 15.2.6) ---------------------------------------------------

def show_lit(dt, v):
    if v is None:
        return "null"
    if dt == "str":
        return '"' + v + '"'
    return show_scalar(dt, v)


def show_scalar(dt, v):
    if v is None:
        return "null"
    if dt == "bool":
        return "true" if v else "false"
    if dt == "f32":
        return f32_show(v)
    if dt == "str":
        return v
    return str(v)


def show(e: Ex) -> str:
    o = e.op
    if o == "col":
        return f'col("{e.p[0]}")'
    if o == "lit":
        if e.p[1] is None:     # the typed null literal is `Cast{Lit{SNull}, t}` (DF.lit_null): Bend shows the cast
            return f"lit(null).cast({e.p[0]})"
        return f"lit({show_lit(*e.p)})"
    if o == "alias":
        return f'{show(e.args[0])}.alias("{e.p[0]}")'
    spec = EXPRS[o]
    return spec.show(e)


# ---- expression table ---------------------------------------------------------------------

@dataclass
class ExprOp:
    name: str
    arity: int
    typ: Any                    # (arg dtypes tuple, p) -> dtype, raises TErr
    sigs: Any                   # result dtype -> list of arg dtype tuples (generation)
    facade: str | None = None   # DF.<facade> builds it; None: same as name
    needs: tuple = ()           # facade defs required
    red: bool = False           # a reducer (Agg)
    infix: str | None = None    # Expr.show symbol for binary operators
    shim: str | None = None     # Bend text of a DX shim when the facade lacks it
    show_fmt: str | None = None  # method-style show: "{0}.name({p})"

    def show(self, e):
        a = [show(x) for x in e.args]
        if self.name == "len":
            return "lit(1).len()"
        if self.infix:
            return f"({a[0]} {self.infix} {a[1]})"
        if self.name == "when":
            return f"when({a[0]}).then({a[1]}).otherwise({a[2]})"
        if self.name == "is_in":
            return f"{a[0]}.is_in([{', '.join(show_lit(e.p[0], v) for v in e.p[1])}])"
        if self.name == "clip":
            return f"{a[0]}.clip({show_lit(e.p[0], e.p[1])}, {show_lit(e.p[0], e.p[2])})"
        if self.name == "len_chars":
            return f"{a[0]}.str.len_chars()"
        if self.name in ("contains_literal", "starts_with", "ends_with"):
            return f'{a[0]}.str.{self.name}("{e.p[0]}")'
        if self.name in ("cast", "try_cast"):
            return f"{a[0]}.{self.name}({e.p[0]})"
        if self.name == "fill_null":
            return f"{a[0]}.fill_null({a[1]})"
        return f"{a[0]}.{self.name}()"


EXPRS: dict[str, ExprOp] = {}


def reg(name, arity, typ, sigs, **kw):
    EXPRS[name] = ExprOp(name, arity, typ, sigs, **kw)


def _is_num(t):
    return t in NUMERIC


def _int(t):
    return t in ("u32", "i32")


def t_arith(name):
    def f(ts, p):
        a, b = ts
        if not _is_num(a):
            raise mismatch(name, "numeric", a)
        if a != b:
            raise mismatch(name, a, b)
        return a
    return f


def t_div(ts, p):
    a, b = ts
    if a != "f32":
        raise mismatch("div", "f32", a)
    if b != "f32":
        raise mismatch("div", "f32", b)
    return "f32"


def t_intop(name):
    def f(ts, p):
        a, b = ts
        if not _int(a):
            raise mismatch(name, "u32 or i32", a)
        if a != b:
            raise mismatch(name, a, b)
        return a
    return f


def t_cmp(name):
    def f(ts, p):
        a, b = ts
        if a != b:
            raise mismatch(name, a, b)
        return "bool"
    return f


def t_logic(name):
    def f(ts, p):
        for t in ts:
            if t != "bool":
                raise mismatch(name, "bool", t)
        return "bool"
    return f


def t_un(name, ok, want):
    def f(ts, p):
        if ts[0] not in ok:
            raise mismatch(name, want, ts[0])
        return ts[0]
    return f


def cast_ok(frm, to):
    if frm == "str":
        return True
    if frm == "bool":
        return True
    if to == "bool":
        return False
    return True


def t_cast(name):
    def f(ts, p):
        if not cast_ok(ts[0], p[0]):
            raise mismatch(name, f"castable to {p[0]}", ts[0])
        return p[0]
    return f


def t_fill(ts, p):
    if ts[0] != ts[1]:
        raise mismatch("fill_null", ts[0], ts[1])
    return ts[0]


def t_when(ts, p):
    c, a, b = ts
    if c != "bool":
        raise mismatch("when", "bool", c)
    if a != b:
        raise mismatch("when", a, b)
    return a


def t_is_in(ts, p):
    """15.3.1: the first offending literal, in list order (an SNull is "null"); [] is fine."""
    dt, vals = p
    for v in vals:
        if v is None:
            raise mismatch("is_in", ts[0], "null")
        if ts[0] != dt:
            raise mismatch("is_in", ts[0], dt)
    return "bool"


def t_clip(ts, p):
    if not _is_num(ts[0]):
        raise mismatch("clip", "numeric", ts[0])
    dt, lo, hi = p
    if dt != ts[0] or lo is None:
        raise mismatch("clip", ts[0], "null" if lo is None else dt)
    if hi is None:
        raise mismatch("clip", ts[0], "null")
    return ts[0]


def t_str(name, res):
    def f(ts, p):
        if ts[0] != "str":
            raise mismatch(name, "str", ts[0])
        return res
    return f


def t_agg(name, num_only):
    def f(ts, p):
        if num_only and not _is_num(ts[0]):
            raise mismatch(name, "numeric", ts[0])
        return ts[0]
    return f


def t_mean(name):
    def f(ts, p):
        if not _is_num(ts[0]):
            raise mismatch(name, "numeric", ts[0])
        return "f32"
    return f


def same_num(t):
    return [(t, t)] if _is_num(t) else []


reg("add", 2, t_arith("add"), same_num, infix="+")
reg("sub", 2, t_arith("sub"), same_num, infix="-")
reg("mul", 2, t_arith("mul"), same_num, infix="*")
reg("div", 2, t_div, lambda t: [("f32", "f32")] if t == "f32" else [], infix="/")
reg("floor_div", 2, t_intop("floor_div"), lambda t: [(t, t)] if _int(t) else [], needs=("floor_div",), infix="//")
reg("mod", 2, t_intop("mod"), lambda t: [(t, t)] if _int(t) else [], infix="%")
for _n, _s in (("eq", "=="), ("ne", "!="), ("lt", "<"), ("le", "<="), ("gt", ">"), ("ge", ">=")):
    reg(_n, 2, t_cmp(_n), (lambda t: [(d, d) for d in DTYPES] if t == "bool" else []), infix=_s)
reg("and", 2, t_logic("and"), lambda t: [("bool", "bool")] if t == "bool" else [], infix="&")
reg("or", 2, t_logic("or"), lambda t: [("bool", "bool")] if t == "bool" else [], infix="|")
reg("not", 1, t_un("not", ("bool",), "bool"), lambda t: [("bool",)] if t == "bool" else [])
reg("neg", 1, t_un("neg", ("i32", "f32"), "i32 or f32"), lambda t: [(t,)] if t in ("i32", "f32") else [])
reg("abs", 1, t_un("abs", ("i32", "f32"), "i32 or f32"), lambda t: [(t,)] if t in ("i32", "f32") else [],
    shim="def abs(e: X.Expr) -> X.Expr:\n  X.Un{X.Abs{}, e}")
reg("sqrt", 1, t_un("sqrt", ("f32",), "f32"), lambda t: [("f32",)] if t == "f32" else [],
    shim="def sqrt(e: X.Expr) -> X.Expr:\n  X.Un{X.Sqrt{}, e}")
reg("is_null", 1, lambda ts, p: "bool", lambda t: [(d,) for d in DTYPES] if t == "bool" else [])
reg("is_not_null", 1, lambda ts, p: "bool", lambda t: [(d,) for d in DTYPES] if t == "bool" else [])
reg("fill_null", 2, t_fill, lambda t: [(t, t)])
reg("cast", 1, t_cast("cast"), lambda t: [(d,) for d in DTYPES if cast_ok(d, t)])
reg("try_cast", 1, t_cast("try_cast"), lambda t: [(d,) for d in DTYPES if cast_ok(d, t)], needs=("try_cast",))
reg("when", 3, t_when, lambda t: [("bool", t, t)], needs=("when",))
reg("is_in", 1, t_is_in, lambda t: [(d,) for d in DTYPES] if t == "bool" else [], needs=("is_in",))
reg("clip", 1, t_clip, lambda t: [(t,)] if _is_num(t) else [], needs=("clip",))
reg("len_chars", 1, t_str("len_chars", "u32"), lambda t: [("str",)] if t == "u32" else [], needs=("len_chars",))
for _n in ("contains_literal", "starts_with", "ends_with"):
    reg(_n, 1, t_str(_n, "bool"), (lambda t: [("str",)] if t == "bool" else []), needs=(_n,))

# reducers: (name, result rule, which input dtypes, needs)
reg("sum", 1, t_agg("sum", True), lambda t: [(t,)] if _is_num(t) else [], red=True)
reg("mean", 1, t_mean("mean"), lambda t: [(d,) for d in NUMERIC] if t == "f32" else [], red=True)
reg("min", 1, t_agg("min", False), lambda t: [(t,)], red=True)
reg("max", 1, t_agg("max", False), lambda t: [(t,)], red=True)
reg("count", 1, lambda ts, p: "u32", lambda t: [(d,) for d in DTYPES] if t == "u32" else [], red=True)
reg("n_unique", 1, lambda ts, p: "u32", lambda t: [(d,) for d in DTYPES] if t == "u32" else [], red=True)
reg("first", 1, t_agg("first", False), lambda t: [(t,)], red=True)
reg("last", 1, t_agg("last", False), lambda t: [(t,)], red=True)
# len() is Agg{Len, lit 1}: modelled as a nullary reducer
reg("len", 0, lambda ts, p: "u32", lambda t: [()] if t == "u32" else [], red=True)
for _n in ("std", "var", "median"):
    reg(_n, 1, t_mean(_n), (lambda t: [(d,) for d in NUMERIC] if t == "f32" else []), red=True, needs=(_n,))


# ---- analysis: dtype and kind of an expression ---------------------------------------------

KROW, KSCALAR, KRED = "row", "scalar", "red"


def kjoin(*ks):
    if KROW in ks:
        return KROW
    if KRED in ks:
        return KRED
    return KSCALAR


def analyse(e: Ex, schema, nested_ok=False) -> tuple:
    """(dtype, kind) of e over schema [(name, dtype)], or raises TErr (first error, left to right)."""
    o = e.op
    if o == "col":
        for n, t in schema:
            if n == e.p[0]:
                return t, KROW
        raise TErr(f"ColumnNotFound: {e.p[0]}")
    if o == "lit":
        dt, v = e.p
        return dt, KSCALAR
    if o == "alias":
        return analyse(e.args[0], schema, nested_ok)
    spec = EXPRS[o]
    rs = [analyse(a, schema, nested_ok) for a in e.args]
    ts = tuple(r[0] for r in rs)
    ks = [r[1] for r in rs]
    if spec.red:
        if spec.arity == 1 and ks[0] == KRED and not nested_ok:
            raise invalid(f"nested aggregation: {show(e)}")
        return spec.typ(ts, e.p), KRED
    return spec.typ(ts, e.p), kjoin(*ks)


def lname(e: Ex):
    o = e.op
    if o == "col":
        return e.p[0]
    if o == "lit":
        return None
    if o == "alias":
        return e.p[0]
    if o == "len":
        return None
    if o == "when":
        return lname(e.args[1])
    for a in e.args:
        n = lname(a)
        if n is not None:
            return n
    return None


def name_of(e: Ex) -> str:
    n = lname(e)
    return "literal" if n is None else n


def is_agg(e: Ex) -> bool:
    if e.op in EXPRS and EXPRS[e.op].red:
        return True
    return any(is_agg(a) for a in e.args)


def walk(e: Ex):
    yield e
    for a in e.args:
        yield from walk(a)


def expr_ops(e: Ex) -> set:
    return {x.op for x in walk(e)}


# ---- plans ----------------------------------------------------------------------------------

@dataclass(frozen=True)
class Pl:
    """verb: 'source' or a VERBS key. p: verb parameters (hashable). kids: input plans."""
    verb: str
    p: tuple = ()
    kids: tuple = ()


def first_dup(names):
    seen = set()
    for n in names:
        if n in seen:
            return n
        seen.add(n)
    return None


def check_dups(names):
    d = first_dup(names)
    if d is not None:
        raise TErr(f"DuplicateColumn: {d}")


def find(schema, n):
    for a, t in schema:
        if a == n:
            return t
    return None


# every verb: name -> VerbSpec; `sch` computes the output schema (raises TErr) from the input
# schemas and parameters.
@dataclass
class VerbSpec:
    name: str
    nin: int                     # number of input plans (-1 = variadic)
    sch: Any                     # (p, in_schemas) -> schema
    needs: tuple = ()
    lazy: str | None = None      # facade lazy builder name, default lazy_<name>
    weight: float = 1.0


VERBS: dict[str, VerbSpec] = {}


def vreg(name, nin, sch, **kw):
    VERBS[name] = VerbSpec(name, nin, sch, **kw)


def exprs_schema(exprs, schema, nested_ok=False):
    """Type every expression in order; returns [(name, dtype, kind)] (first error wins)."""
    out = []
    for e in exprs:
        t, k = analyse(e, schema, nested_ok)
        out.append((name_of(e), t, k))
    return out


def s_select(p, ins):
    exprs, = p
    r = exprs_schema(exprs, ins[0])
    check_dups([n for n, _, _ in r])
    return [(n, t) for n, t, _ in r]


def s_with(p, ins):
    exprs, = p
    r = exprs_schema(exprs, ins[0])
    check_dups([n for n, _, _ in r])
    out = list(ins[0])
    for n, t, _ in r:
        for i, (a, _t) in enumerate(out):
            if a == n:
                out[i] = (n, t)
                break
        else:
            out.append((n, t))
    return out


def s_filter(p, ins):
    pred, = p
    t, k = analyse(pred, ins[0])
    if t != "bool":
        raise mismatch("filter", "bool", t)
    return list(ins[0])


def s_sort(p, ins):
    keys, = p
    for n, d, nl in keys:
        if find(ins[0], n) is None:
            raise TErr(f"ColumnNotFound: {n}")
    return list(ins[0])


def s_group(p, ins):
    keys, aggs = p
    sch = ins[0]
    kr = exprs_schema(keys, sch, True)
    ar = exprs_schema(aggs, sch, True)
    if not keys:
        raise invalid("group_by needs at least one key")
    for k in keys:
        if is_agg(k):
            raise invalid(f"group_by key is an aggregation: {show(k)}")
    for a in aggs:
        x = a
        while x.op == "alias":
            x = x.args[0]
        if not (x.op in EXPRS and EXPRS[x.op].red):
            raise invalid(f"agg expects an aggregation: {show(a)}")
        if any(is_agg(c) for c in x.args):
            raise invalid(f"nested aggregation in agg: {show(a)}")
    out = [(n, t) for n, t, _ in kr] + [(n, t) for n, t, _ in ar]
    check_dups([n for n, _ in out])
    return out


def s_head(p, ins):
    return list(ins[0])


def s_join(p, ins):
    how, lo, ro = p
    ls, rs = ins
    if not lo:
        raise invalid("join: no key columns")
    if len(lo) != len(ro):
        raise invalid("join: left_on and right_on must have the same length")
    for a, b in zip(lo, ro):
        ta, tb = find(ls, a), find(rs, b)
        if ta is None:
            raise TErr(f"ColumnNotFound: {a}")
        if tb is None:
            raise TErr(f"ColumnNotFound: {b}")
        if ta != tb:
            raise mismatch("join", ta, tb)
    if how in ("semi", "anti"):
        return list(ls)
    lnames = {n for n, _ in ls}
    out = list(ls)
    for n, t in rs:
        if n in ro:
            continue
        out.append((n + "_right" if n in lnames else n, t))
    check_dups([n for n, _ in out])
    return out


def s_drop(p, ins):
    names, = p
    for n in names:
        if find(ins[0], n) is None:
            raise TErr(f"ColumnNotFound: {n}")
    return [(n, t) for n, t in ins[0] if n not in names]


def s_rename(p, ins):
    pairs, = p
    for a, b in pairs:
        if find(ins[0], a) is None:
            raise TErr(f"ColumnNotFound: {a}")
    d = first_dup([a for a, _ in pairs])
    if d is not None:
        raise TErr(f"DuplicateColumn: {d}")
    m = dict(pairs)
    out = [(m.get(n, n), t) for n, t in ins[0]]
    check_dups([n for n, _ in out])
    return out


def s_unique(p, ins):
    subset, = p
    for n in subset:
        if find(ins[0], n) is None:
            raise TErr(f"ColumnNotFound: {n}")
    return list(ins[0])


def concat_differs(i, s, s0):
    return invalid(f"concat_vertical: input {i} schema [{schema_show(s)}] differs from input 0's [{schema_show(s0)}]")


def s_concat(p, ins):
    if not ins:
        raise invalid("concat_vertical: no inputs")
    for i, s in enumerate(ins[1:], 1):
        if s != ins[0]:
            raise concat_differs(i, s, ins[0])
    return list(ins[0])


def concat_schema(kids, schema_of):
    """concat_vertical's static checks input by input (DESIGN.md 14 "M3 table verbs": the lazy
    plan is a chain of binary Concat nodes): input i's own errors, then its schema against input
    0's, then input i + 1. schema_of(kid) types one input (raises TErr)."""
    if not kids:
        raise invalid("concat_vertical: no inputs")
    s0 = schema_of(kids[0])
    for i, k in enumerate(kids[1:], 1):
        s = schema_of(k)
        if s != s0:
            raise concat_differs(i, s, s0)
    return list(s0)


def schema_show(s):
    return ", ".join(f"{n}:{t}" for n, t in s)


vreg("select", 1, s_select, weight=3)
vreg("with_columns", 1, s_with, weight=3)
vreg("filter", 1, s_filter, weight=3)
vreg("sort", 1, s_sort, weight=2)
vreg("group_by", 1, s_group, weight=2)
vreg("head", 1, s_head, weight=1.5)
vreg("inner_join", 2, lambda p, ins: s_join(("inner",) + p, ins), weight=1)
vreg("left_join", 2, lambda p, ins: s_join(("left",) + p, ins), weight=1)
vreg("semi_join", 2, lambda p, ins: s_join(("semi",) + p, ins), needs=("semi_join",), weight=1)
vreg("anti_join", 2, lambda p, ins: s_join(("anti",) + p, ins), needs=("anti_join",), weight=1)
vreg("drop", 1, s_drop, needs=("drop",))
vreg("rename", 1, s_rename, needs=("rename",))
vreg("slice", 1, s_head, needs=("slice",))
vreg("tail", 1, s_head, needs=("tail",))
vreg("unique", 1, s_unique, needs=("unique",))
vreg("concat_vertical", -1, s_concat, needs=("concat_vertical",))


def plan_schema(pl: Pl, sources: dict):
    """Output schema of a plan or raises TErr. sources: name -> schema."""
    if pl.verb == "source":
        return list(sources[pl.p[0]])
    if pl.verb == "concat_vertical":
        return concat_schema(pl.kids, lambda k: plan_schema(k, sources))
    ins = [plan_schema(k, sources) for k in pl.kids]
    return VERBS[pl.verb].sch(pl.p, ins)


def plan_nodes(pl: Pl):
    yield pl
    for k in pl.kids:
        yield from plan_nodes(k)


def plan_sources(pl: Pl):
    """Source names in postfix order, with repeats."""
    if pl.verb == "source":
        return [pl.p[0]]
    out = []
    for k in pl.kids:
        out += plan_sources(k)
    return out


# ---- facade detection -----------------------------------------------------------------------

_FACADE = None


def facade_defs(path=None):
    """The set of `def name(` of frame.bend (the facade surface a generated case may use)."""
    global _FACADE
    if _FACADE is None or path:
        txt = Path(path or ROOT / "frame.bend").read_text()
        _FACADE = set(re.findall(r"^def ([A-Za-z_][A-Za-z_0-9.]*)\(", txt, re.M))
    return _FACADE


def op_available(name, all_=False):
    s = EXPRS[name]
    fac = facade_defs()
    return all_ or all(n in fac for n in s.needs)


def verb_available(name, all_=False):
    s = VERBS[name]
    fac = facade_defs()
    if all_:
        return True
    need = [s.name, s.lazy or f"lazy_{s.name}", *s.needs]
    return all(n in fac for n in need)


# ---- JSON ---------------------------------------------------------------------------------

def enc_val(dt, v):
    if v is None:
        return None
    if dt == "f32":
        return ["f", "0x%08x" % f32bits(v)]
    return v


def dec_val(dt, v):
    if v is None:
        return None
    if dt == "f32":
        return bits_f32(int(v[1], 16))
    return v


def enc_ex(e: Ex):
    if e.op == "lit":
        return ["lit", e.p[0], enc_val(e.p[0], e.p[1])]
    if e.op == "is_in":
        return ["is_in", enc_ex(e.args[0]), e.p[0], [enc_val(e.p[0], v) for v in e.p[1]]]
    if e.op == "clip":
        return ["clip", enc_ex(e.args[0]), e.p[0], enc_val(e.p[0], e.p[1]), enc_val(e.p[0], e.p[2])]
    return [e.op, [enc_ex(a) for a in e.args], list(e.p)]


def dec_ex(j) -> Ex:
    op = j[0]
    if op == "lit":
        return Ex("lit", (), (j[1], dec_val(j[1], j[2])))
    if op == "is_in":
        return Ex("is_in", (dec_ex(j[1]),), (j[2], tuple(dec_val(j[2], v) for v in j[3])))
    if op == "clip":
        return Ex("clip", (dec_ex(j[1]),), (j[2], dec_val(j[2], j[3]), dec_val(j[2], j[4])))
    return Ex(op, tuple(dec_ex(a) for a in j[1]), tuple(j[2]))


def enc_plan(pl: Pl):
    if pl.verb == "source":
        return ["source", list(pl.p)]
    return [pl.verb, enc_params(pl.verb, pl.p), [enc_plan(k) for k in pl.kids]]


def dec_plan(j) -> Pl:
    if j[0] == "source":
        return Pl("source", tuple(j[1]), ())
    return Pl(j[0], dec_params(j[0], j[1]), tuple(dec_plan(k) for k in j[2]))


EXPR_PARAMS = {"select": "E", "with_columns": "E", "filter": "e", "group_by": "EE"}


def enc_params(verb, p):
    if verb in ("select", "with_columns"):
        return [[enc_ex(e) for e in p[0]]]
    if verb == "filter":
        return [enc_ex(p[0])]
    if verb == "group_by":
        return [[enc_ex(e) for e in p[0]], [enc_ex(e) for e in p[1]]]
    return json_safe(p)


def dec_params(verb, j):
    if verb in ("select", "with_columns"):
        return (tuple(dec_ex(e) for e in j[0]),)
    if verb == "filter":
        return (dec_ex(j[0]),)
    if verb == "group_by":
        return (tuple(dec_ex(e) for e in j[0]), tuple(dec_ex(e) for e in j[1]))
    return tupleize(j)


def json_safe(x):
    if isinstance(x, tuple):
        return [json_safe(i) for i in x]
    return x


def tupleize(x):
    if isinstance(x, list):
        return tuple(tupleize(i) for i in x)
    return x


def enc_frame(f: Frame):
    return {"height": f.height, "cols": [[c.name, c.dtype, [enc_val(c.dtype, v) for v in c.vals]] for c in f.cols]}


def dec_frame(j) -> Frame:
    return Frame([Col(n, t, [dec_val(t, v) for v in vs]) for n, t, vs in j["cols"]], j["height"])


@dataclass
class Case:
    id: str
    seed: int
    inputs: dict        # source name -> Frame
    plan: Pl
    kind: str = "valid"  # valid | invalid
    notes: str = ""

    def to_json(self):
        return {"id": self.id, "seed": self.seed, "kind": self.kind, "notes": self.notes,
                "inputs": {k: enc_frame(v) for k, v in self.inputs.items()}, "plan": enc_plan(self.plan)}

    @staticmethod
    def from_json(j):
        return Case(j["id"], j["seed"], {k: dec_frame(v) for k, v in j["inputs"].items()}, dec_plan(j["plan"]),
                    j.get("kind", "valid"), j.get("notes", ""))

    def sources(self):
        return {k: v.schema for k, v in self.inputs.items()}


def case_static(case: Case):
    """('ok', schema) or ('error', text) by the contract's static rules."""
    try:
        return "ok", plan_schema(case.plan, case.sources())
    except TErr as e:
        return "error", e.text
