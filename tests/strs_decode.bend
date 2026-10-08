# M4 decode equivalence: every operation over Dictionary-encoded Str columns answers the same
# dump (DF.dump: dtype, validity, every cell) as over the Raw columns it was encoded from.
# Each line compares one operation run twice: over the Raw frames and over the same frames
# with every Str column encoded (C.Frame.encode(f, True{})); `same` means equal dump text.
# Joins also run with one side encoded and the other Raw. `repr` lines show which result
# columns stayed Dictionary-encoded (the operation worked on codes, not on decoded strings).
# The values themselves are pinned by the Raw tests (tests/sort_*, groupby_*, join_*, eval_*).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csv.bend as V
import ./../src/fmt.bend as F

def s(x: String) -> D.Scalar:
  D.SStr{x}

def nl() -> D.Scalar:
  D.SNull{}

def u(x: U32) -> D.Scalar:
  D.SU32{x}

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def enc(+e: Bool, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{x}:
      Fail{x}
    case Done{f}:
      Done{C.Frame.encode(f, e)}

# nulls, the empty string, duplicates, shared prefixes, Unicode, an upper-case letter
def t(+e: Bool) -> E.ResT(C.Frame):
  enc(e, DF.from_columns([mk("k", [s("b"), s("a"), nl(), s(""), s("ab"), s("b"), s("日本"), s("a"), s("abc"), nl(), s("b"), s("Z")], D.TStr{}), mk("v", [u(1), u(2), u(3), u(4), u(5), u(6), u(7), u(8), u(9), u(10), u(11), u(12)], D.TU32{}), mk("w", [s("a"), s("b"), s("b"), nl(), s(""), s("x"), s("日本"), s("ab"), s("a"), s("b"), s("abc"), s("z")], D.TStr{}), mk("num", [s("1"), s("x"), s("3"), nl(), s(""), s("-2"), s("7"), s("1"), s("3.5"), s("true"), s("1"), s("8")], D.TStr{})]))

# the right side: the same strings coded in another order, a duplicate key, a null key
def r(+e: Bool) -> E.ResT(C.Frame):
  enc(e, DF.from_columns([mk("key", [s("ab"), s("b"), s("q"), s("日本"), s(""), s("b"), nl()], D.TStr{}), mk("n", [u(5), u(1), u(3), u(7), u(4), u(6), u(3)], D.TU32{}), mk("cat", [s("x"), s("y"), s("z"), s("w"), s("e"), s("yy"), s("nn")], D.TStr{})]))

# every value null; and no rows at all
def z(+e: Bool) -> E.ResT(C.Frame):
  enc(e, DF.from_columns([mk("k", [nl(), nl(), nl()], D.TStr{}), mk("v", [u(3), u(1), u(2)], D.TU32{})]))

def z0(+e: Bool) -> E.ResT(C.Frame):
  enc(e, DF.from_columns([mk("k", [], D.TStr{}), mk("v", [], D.TU32{})]))

def same.t(+name: String, +x: String, +y: String) -> String:
  Bool.pick(String, String.eq(x, y), name ++ ": same", name ++ ": DIFF\n" ++ x ++ "\n" ++ y)

def same(+name: String, a: E.ResT(C.Frame), b: E.ResT(C.Frame)) -> String:
  same.t(name, DF.dump(a), DF.dump(b))

def repr.k(r: C.Column & Bool) -> String:
  (c, b) = r
  Bool.pick(String, b, "dict", "raw")

# which columns are Dictionary-encoded
def repr.cols(cs: List<&1, C.Named>) -> String:
  match cs:
    case Nil{}:
      ""
    case C.Named{n, c} <> t:
      " " ++ n ++ ":" ++ repr.k(C.Column.is_dict(c)) ++ repr.cols(t)

def repr(+name: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{x}:
      name ++ " repr: error"
    case Done{C.Frame{h, cs}}:
      name ++ " repr:" ++ repr.cols(cs)

# ---- operations ----------------------------------------------------------------------------

def o.dump(+e: Bool) -> E.ResT(C.Frame):
  t(e)

def o.clone.k(r: C.Frame & C.Frame) -> E.ResT(C.Frame):
  (a, b) = r
  Done{b}

def o.clone(+e: Bool) -> E.ResT(C.Frame):
  DF.then(t(e), f => o.clone.k(DF.clone(f)))

def o.head(+e: Bool) -> E.ResT(C.Frame):
  DF.then(t(e), f => DF.head(f, 5))

def o.slice.k(r: C.Frame & Maybe<&1, C.Column>) -> E.ResT(C.Frame):
  (f, m) = r
  match m:
    case None{}:
      Fail{E.ColumnNotFound{"k"}}
    case Some{c}:
      DF.from_columns([C.Named{"k", C.Column.slice(c, 3, 5)}])

def o.slice(+e: Bool) -> E.ResT(C.Frame):
  DF.then(t(e), f => o.slice.k(C.Frame.take(f, "k")))

def o.filter(+e: Bool, p: DF.Expr()) -> E.ResT(C.Frame):
  DF.then(t(e), f => DF.filter(f, p))

def o.sort(+e: Bool, ks: List<&2, DF.SortKey()>) -> E.ResT(C.Frame):
  DF.then(t(e), f => DF.sort(f, ks))

def o.gb(+e: Bool, ks: List<&2, DF.Expr()>, ags: List<&2, DF.Expr()>) -> E.ResT(C.Frame):
  DF.then(t(e), f => DF.group_by(f, ks, ags))

def o.sel(+e: Bool, es: List<&2, DF.Expr()>) -> E.ResT(C.Frame):
  DF.then(t(e), f => DF.select(f, es))

def o.wc(+e: Bool, es: List<&2, DF.Expr()>) -> E.ResT(C.Frame):
  DF.then(t(e), f => DF.with_columns(f, es))

def o.join3(left: Bool, a: C.Frame, b: C.Frame, lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match left:
    case True{}:
      DF.left_join(a, b, lo, ro)
    case False{}:
      DF.inner_join(a, b, lo, ro)

def o.join2(l: E.ResT(C.Frame), rr: E.ResT(C.Frame), +left: Bool, lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match l rr:
    case Done{a} Done{b}:
      o.join3(left, a, b, lo, ro)
    case Fail{x} _:
      Fail{x}
    case _ Fail{x}:
      Fail{x}

def o.join(+el: Bool, +er: Bool, +left: Bool, +lo: List<&2, String>, +ro: List<&2, String>) -> E.ResT(C.Frame):
  o.join2(t(el), r(er), left, lo, ro)

def o.render.k(+e: Bool, x: C.Frame & String) -> String:
  (f, txt) = x
  txt

def o.render.r(+e: Bool, r0: E.ResT(C.Frame)) -> String:
  match r0:
    case Fail{x}:
      "error"
    case Done{f}:
      o.render.k(e, V.Csv.render(f, None{}))

def o.render(+e: Bool) -> String:
  o.render.r(e, t(e))

def o.lazy.k(+e: Bool, x: DF.Env() & DF.Plan()) -> IO(E.ResT(C.Frame)):
  (env, p) = x
  DF.collect(DF.lazy_sort(DF.lazy_group_by(DF.lazy_filter(p, DF.ne(DF.col("k"), DF.lit_str("a"))), [DF.col("k")], [DF.alias(DF.sum(DF.col("v")), "s"), DF.alias(DF.max(DF.col("w")), "mw")]), [DF.asc("k")]), env)

def o.edge(r0: E.ResT(C.Frame), k: C.Frame -> E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.then(r0, k)

# ---- the run ---------------------------------------------------------------------------------

def k() -> DF.Expr():
  DF.col("k")

def w() -> DF.Expr():
  DF.col("w")

def ls(x: String) -> DF.Expr():
  DF.lit_str(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(same("dump", o.dump(False{}), o.dump(True{})))
    IO.print(repr("dump", o.dump(True{})))
    IO.print(same("clone", o.clone(False{}), o.clone(True{})))
    IO.print(same("head", o.head(False{}), o.head(True{})))
    IO.print(same("slice", o.slice(False{}), o.slice(True{})))
    IO.print(repr("slice", o.slice(True{})))
    IO.print(same("filter k == lit", o.filter(False{}, DF.eq(k(), ls("b"))), o.filter(True{}, DF.eq(k(), ls("b")))))
    IO.print(repr("filter k == lit", o.filter(True{}, DF.eq(k(), ls("b")))))
    IO.print(same("filter k != lit", o.filter(False{}, DF.ne(k(), ls("b"))), o.filter(True{}, DF.ne(k(), ls("b")))))
    IO.print(same("filter k == absent lit", o.filter(False{}, DF.eq(k(), ls("nope"))), o.filter(True{}, DF.eq(k(), ls("nope")))))
    IO.print(same("filter k == \"\"", o.filter(False{}, DF.eq(k(), ls(""))), o.filter(True{}, DF.eq(k(), ls("")))))
    IO.print(same("filter k < lit", o.filter(False{}, DF.lt(k(), ls("ab"))), o.filter(True{}, DF.lt(k(), ls("ab")))))
    IO.print(same("filter k >= lit", o.filter(False{}, DF.ge(k(), ls("a"))), o.filter(True{}, DF.ge(k(), ls("a")))))
    IO.print(same("filter k > absent lit", o.filter(False{}, DF.gt(k(), ls("aa"))), o.filter(True{}, DF.gt(k(), ls("aa")))))
    IO.print(same("filter lit > k", o.filter(False{}, DF.gt(ls("b"), k())), o.filter(True{}, DF.gt(ls("b"), k()))))
    IO.print(same("filter k == null", o.filter(False{}, DF.eq(k(), DF.lit_null(D.TStr{}))), o.filter(True{}, DF.eq(k(), DF.lit_null(D.TStr{})))))
    IO.print(same("filter k == w", o.filter(False{}, DF.eq(k(), w())), o.filter(True{}, DF.eq(k(), w()))))
    IO.print(same("filter k != w", o.filter(False{}, DF.ne(k(), w())), o.filter(True{}, DF.ne(k(), w()))))
    IO.print(same("filter k < w", o.filter(False{}, DF.lt(k(), w())), o.filter(True{}, DF.lt(k(), w()))))
    IO.print(same("filter k >= w", o.filter(False{}, DF.ge(k(), w())), o.filter(True{}, DF.ge(k(), w()))))
    IO.print(same("filter k == k", o.filter(False{}, DF.eq(k(), k())), o.filter(True{}, DF.eq(k(), k()))))
    IO.print(same("sort k", o.sort(False{}, [DF.asc("k")]), o.sort(True{}, [DF.asc("k")])))
    IO.print(repr("sort k", o.sort(True{}, [DF.asc("k")])))
    IO.print(same("sort k desc nulls_last", o.sort(False{}, [DF.sort_key("k", True{}, True{})]), o.sort(True{}, [DF.sort_key("k", True{}, True{})])))
    IO.print(same("sort w, k desc", o.sort(False{}, [DF.asc("w"), DF.desc("k")]), o.sort(True{}, [DF.asc("w"), DF.desc("k")])))
    IO.print(same("group_by k", o.gb(False{}, [k()], [DF.alias(DF.len(), "n"), DF.alias(DF.count(w()), "c"), DF.alias(DF.n_unique(w()), "u"), DF.alias(DF.min(w()), "lo"), DF.alias(DF.max(w()), "hi"), DF.alias(DF.first(w()), "f"), DF.alias(DF.last(w()), "l"), DF.alias(DF.sum(DF.col("v")), "s")]), o.gb(True{}, [k()], [DF.alias(DF.len(), "n"), DF.alias(DF.count(w()), "c"), DF.alias(DF.n_unique(w()), "u"), DF.alias(DF.min(w()), "lo"), DF.alias(DF.max(w()), "hi"), DF.alias(DF.first(w()), "f"), DF.alias(DF.last(w()), "l"), DF.alias(DF.sum(DF.col("v")), "s")])))
    IO.print(repr("group_by k", o.gb(True{}, [k()], [DF.alias(DF.len(), "n"), DF.alias(DF.first(w()), "f")])))
    IO.print(same("group_by k, w", o.gb(False{}, [k(), w()], [DF.alias(DF.len(), "n")]), o.gb(True{}, [k(), w()], [DF.alias(DF.len(), "n")])))
    IO.print(same("group_by w == lit", o.gb(False{}, [DF.eq(w(), ls("b"))], [DF.alias(DF.n_unique(k()), "u")]), o.gb(True{}, [DF.eq(w(), ls("b"))], [DF.alias(DF.n_unique(k()), "u")])))
    IO.print(same("select aggs", o.sel(False{}, [DF.alias(DF.min(k()), "lo"), DF.alias(DF.max(k()), "hi"), DF.alias(DF.n_unique(k()), "u"), DF.alias(DF.first(k()), "f"), DF.alias(DF.last(k()), "l"), DF.alias(DF.count(k()), "c")]), o.sel(True{}, [DF.alias(DF.min(k()), "lo"), DF.alias(DF.max(k()), "hi"), DF.alias(DF.n_unique(k()), "u"), DF.alias(DF.first(k()), "f"), DF.alias(DF.last(k()), "l"), DF.alias(DF.count(k()), "c")])))
    IO.print(same("try_cast num", o.wc(False{}, [DF.alias(DF.try_cast(DF.col("num"), D.TU32{}), "u"), DF.alias(DF.try_cast(DF.col("num"), D.TI32{}), "i"), DF.alias(DF.try_cast(DF.col("num"), D.TF32{}), "f"), DF.alias(DF.try_cast(DF.col("num"), D.TBool{}), "b"), DF.alias(DF.cast(k(), D.TStr{}), "s")]), o.wc(True{}, [DF.alias(DF.try_cast(DF.col("num"), D.TU32{}), "u"), DF.alias(DF.try_cast(DF.col("num"), D.TI32{}), "i"), DF.alias(DF.try_cast(DF.col("num"), D.TF32{}), "f"), DF.alias(DF.try_cast(DF.col("num"), D.TBool{}), "b"), DF.alias(DF.cast(k(), D.TStr{}), "s")])))
    IO.print(same("cast num u32 (strict, fails)", o.wc(False{}, [DF.cast(DF.col("num"), D.TU32{})]), o.wc(True{}, [DF.cast(DF.col("num"), D.TU32{})])))
    IO.print(same("fill_null lit, col; is_null", o.wc(False{}, [DF.alias(DF.fill_null(k(), ls("zz")), "a"), DF.alias(DF.fill_null(k(), w()), "b"), DF.alias(DF.fill_null(w(), ls("")), "c"), DF.alias(DF.is_null(k()), "d")]), o.wc(True{}, [DF.alias(DF.fill_null(k(), ls("zz")), "a"), DF.alias(DF.fill_null(k(), w()), "b"), DF.alias(DF.fill_null(w(), ls("")), "c"), DF.alias(DF.is_null(k()), "d")])))
    IO.print(repr("fill_null", o.wc(True{}, [DF.alias(DF.fill_null(k(), ls("zz")), "a"), DF.alias(DF.fill_null(k(), w()), "b")])))
    IO.print(same("inner join dict x dict", o.join(False{}, False{}, False{}, ["k"], ["key"]), o.join(True{}, True{}, False{}, ["k"], ["key"])))
    IO.print(repr("inner join dict x dict", o.join(True{}, True{}, False{}, ["k"], ["key"])))
    IO.print(same("inner join dict x raw", o.join(False{}, False{}, False{}, ["k"], ["key"]), o.join(True{}, False{}, False{}, ["k"], ["key"])))
    IO.print(same("inner join raw x dict", o.join(False{}, False{}, False{}, ["k"], ["key"]), o.join(False{}, True{}, False{}, ["k"], ["key"])))
    IO.print(same("left join dict x dict", o.join(False{}, False{}, True{}, ["k"], ["key"]), o.join(True{}, True{}, True{}, ["k"], ["key"])))
    IO.print(same("left join raw x dict", o.join(False{}, False{}, True{}, ["k"], ["key"]), o.join(False{}, True{}, True{}, ["k"], ["key"])))
    IO.print(same("left join on w (other codes)", o.join(False{}, False{}, True{}, ["w"], ["key"]), o.join(True{}, True{}, True{}, ["w"], ["key"])))
    IO.print(same("inner join two keys", o.join(False{}, False{}, False{}, ["k", "v"], ["key", "n"]), o.join(True{}, True{}, False{}, ["k", "v"], ["key", "n"])))
    IO.print(same("inner join u32, str", o.join(False{}, False{}, False{}, ["v", "w"], ["n", "key"]), o.join(True{}, True{}, False{}, ["v", "w"], ["n", "key"])))
    IO.print(same.t("render", o.render(False{}), o.render(True{})))
    IO.print(same.t("show", DF.show(t(False{})), DF.show(t(True{}))))
    IO.print(same("describe", DF.describe(t(False{})), DF.describe(t(True{}))))
    a : E.ResT(C.Frame) <- DF.then_io(t(False{}), f => o.lazy.k(False{}, DF.source("t", f)))
    b : E.ResT(C.Frame) <- DF.then_io(t(True{}), f => o.lazy.k(True{}, DF.source("t", f)))
    IO.print(same("lazy filter/group_by/sort", a, b))
    IO.print(same("all null: sort", o.edge(z(False{}), f => DF.sort(f, [DF.asc("k")])), o.edge(z(True{}), f => DF.sort(f, [DF.asc("k")]))))
    IO.print(same("all null: group_by", o.edge(z(False{}), f => DF.group_by(f, [DF.col("k")], [DF.alias(DF.max(DF.col("k")), "m"), DF.alias(DF.n_unique(DF.col("k")), "u")])), o.edge(z(True{}), f => DF.group_by(f, [DF.col("k")], [DF.alias(DF.max(DF.col("k")), "m"), DF.alias(DF.n_unique(DF.col("k")), "u")]))))
    IO.print(same("all null: filter == \"\"", o.edge(z(False{}), f => DF.filter(f, DF.eq(DF.col("k"), DF.lit_str("")))), o.edge(z(True{}), f => DF.filter(f, DF.eq(DF.col("k"), DF.lit_str(""))))))
    IO.print(same("all null: select min", o.edge(z(False{}), f => DF.select(f, [DF.min(DF.col("k")), DF.alias(DF.first(DF.col("k")), "f")])), o.edge(z(True{}), f => DF.select(f, [DF.min(DF.col("k")), DF.alias(DF.first(DF.col("k")), "f")]))))
    IO.print(same("no rows: sort, filter, min", o.edge(z0(False{}), f => DF.select(f, [DF.min(DF.col("k"))])), o.edge(z0(True{}), f => DF.select(f, [DF.min(DF.col("k"))]))))
    IO.print(same("no rows: filter", o.edge(z0(False{}), f => DF.filter(f, DF.lt(DF.col("k"), DF.lit_str("a")))), o.edge(z0(True{}), f => DF.filter(f, DF.lt(DF.col("k"), DF.lit_str("a"))))))

#|dump: same
#|dump repr: k:dict v:raw w:dict num:dict
#|clone: same
#|head: same
#|slice: same
#|slice repr: k:dict
#|filter k == lit: same
#|filter k == lit repr: k:dict v:raw w:dict num:dict
#|filter k != lit: same
#|filter k == absent lit: same
#|filter k == "": same
#|filter k < lit: same
#|filter k >= lit: same
#|filter k > absent lit: same
#|filter lit > k: same
#|filter k == null: same
#|filter k == w: same
#|filter k != w: same
#|filter k < w: same
#|filter k >= w: same
#|filter k == k: same
#|sort k: same
#|sort k repr: k:dict v:raw w:dict num:dict
#|sort k desc nulls_last: same
#|sort w, k desc: same
#|group_by k: same
#|group_by k repr: k:dict n:raw f:dict
#|group_by k, w: same
#|group_by w == lit: same
#|select aggs: same
#|try_cast num: same
#|cast num u32 (strict, fails): same
#|fill_null lit, col; is_null: same
#|fill_null repr: k:dict v:raw w:dict num:dict a:dict b:dict
#|inner join dict x dict: same
#|inner join dict x dict repr: k:dict v:raw w:dict num:dict n:raw cat:dict
#|inner join dict x raw: same
#|inner join raw x dict: same
#|left join dict x dict: same
#|left join raw x dict: same
#|left join on w (other codes): same
#|inner join two keys: same
#|inner join u32, str: same
#|render: same
#|show: same
#|describe: same
#|lazy filter/group_by/sort: same
#|all null: sort: same
#|all null: group_by: same
#|all null: filter == "": same
#|all null: select min: same
#|no rows: sort, filter, min: same
#|no rows: filter: same
