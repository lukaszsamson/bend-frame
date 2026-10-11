# T4.2 (DESIGN.md 16.3 F1-F5): the fused evaluator keeps v0.1's results exactly. Eval.fuse rewrites
# the marked postfix code into fused fragments (F1 a literal operand as a scalar, F2 the
# null-propagating zip with validity in one loop, F3 a total cast folded into the zip, F4
# fill_null with the dtype default as a validity change) that read frame columns in place
# (borrowed, or moved on a last reference); Eval.filter runs a conjunction of bool columns and
# `column op literal` comparisons as pred_count passes (F5). Every other shape runs the unfused
# code.
#
# Part 1 is hand-worked (the expectations were derived by hand before the run, and agree with
# Eval.full, the unfused evaluator). Part 2 is a differential: every expression of a long list over
# an 8-row frame with nulls, NaN, -0.0, the u32 / i32 extremes is evaluated by with_columns and by
# select (fused, borrowing / moving) and by Eval.full (the unfused stack machine, every reference
# copying), and the whole result frames are compared cell by cell, F32 by its bits; every filter
# predicate is run through Eval.filter (F5 or the fused evaluator) and through Eval.full + the v0.1
# mask path. Part 3: competing errors (strict casts in different rows, operands and expressions
# next to fused fragments) report the same first error as the unfused evaluator.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/eval.bend as V

# ---- helpers ----------------------------------------------------------------------

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def scal(xs: List<&2, D.Scalar>) -> String:
  List.show(~&2, ~D.Scalar, ~(s => D.Scalar.show(s)), xs)

# a cell with an F32 shown by its bits (NaN payloads and -0.0 are told apart)
def bits(s: D.Scalar) -> String:
  match s:
    case D.SF32{x}:
      "f#" ++ U32.show(F32.bits(x))
    case other:
      D.Scalar.show(other)

def scalb(xs: List<&2, D.Scalar>) -> String:
  List.show(~&2, ~D.Scalar, ~(s => bits(s)), xs)

def cs.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scal(xs)

def cs.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cs.b(t, C.Column.to_scalars(c))

def cs(c: C.Column) -> String:
  cs.a(C.Column.dtype(c))

def cb.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scalb(xs)

def cb.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cb.b(t, C.Column.to_scalars(c))

def cb(c: C.Column) -> String:
  cb.a(C.Column.dtype(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs(c)) <> ncols(t)

def ncolb(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cb(c)) <> ncolb(t)

def fs(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncols(cols), " | ")

def fb(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncolb(cols), " | ")

def fr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fs(f)

def frb(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fb(f)

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def li(v: U32) -> X.Expr:
  X.Lit{D.SI32{D.I32{v}}}

def lf(v: F32) -> X.Expr:
  X.Lit{D.SF32{v}}

def lb(v: Bool) -> X.Expr:
  X.Lit{D.SBool{v}}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def al(e: X.Expr, n: String) -> X.Expr:
  X.Alias{e, n}

def cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.Cast{e, t}

def fill(e: X.Expr, v: X.Expr) -> X.Expr:
  X.FillNull{e, v}

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

# ---- part 1: hand-worked ------------------------------------------------------------

# a: u32 with a null; b: u32 (row 1 does not fit i32); s: str; c: f32 with a null (row 3 does not
# fit u32); k: bool with a null
def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}], D.TU32{}), mk("b", [D.SU32{10}, D.SU32{3000000000}, D.SU32{30}, D.SU32{40}], D.TU32{}), mk("s", [D.SStr{"x"}, D.SStr{"y"}, D.SStr{"x"}, D.SStr{"7"}], D.TStr{}), mk("c", [D.SF32{0.5}, D.SNull{}, D.SF32{2.5}, D.SF32{F32.neg(2.5)}], D.TF32{}), mk("k", [D.SBool{True{}}, D.SBool{False{}}, D.SBool{True{}}, D.SNull{}], D.TBool{})])

def on(g: C.Frame -> String) -> String:
  on.k(g, base())

# ---- part 2: the differential ---------------------------------------------------------

# u: u32 masked; w: u32 dense; i: i32 masked; j: i32 dense; f: f32 masked (NaN, -0.0, inf);
# g: f32 dense (NaN, -0.0); b: bool masked; e: bool dense; s: str
def dbase() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("u", [D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}, D.SU32{0}, D.SU32{4294967295}, D.SU32{7}, D.SNull{}], D.TU32{}),
    mk("w", [D.SU32{3}, D.SU32{0}, D.SU32{5}, D.SU32{9}, D.SU32{0}, D.SU32{1}, D.SU32{7}, D.SU32{2}], D.TU32{}),
    mk("i", [D.SI32{D.I32{4294967295}}, D.SI32{D.I32{2}}, D.SNull{}, D.SI32{D.I32{2147483648}}, D.SI32{D.I32{0}}, D.SI32{D.I32{5}}, D.SI32{D.I32{4294967289}}, D.SNull{}], D.TI32{}),
    mk("j", [D.SI32{D.I32{1}}, D.SI32{D.I32{4294967294}}, D.SI32{D.I32{3}}, D.SI32{D.I32{4294967295}}, D.SI32{D.I32{0}}, D.SI32{D.I32{2147483647}}, D.SI32{D.I32{4294967289}}, D.SI32{D.I32{4}}], D.TI32{}),
    mk("f", [D.SF32{0.5}, D.SNull{}, D.SF32{nan()}, D.SF32{F32.neg(0.0)}, D.SF32{2.5}, D.SF32{F32.neg(1.5)}, D.SF32{inf()}, D.SNull{}], D.TF32{}),
    mk("g", [D.SF32{1.0}, D.SF32{2.0}, D.SF32{0.0}, D.SF32{F32.neg(0.0)}, D.SF32{nan()}, D.SF32{3.5}, D.SF32{F32.neg(2.25)}, D.SF32{10000000000.0}], D.TF32{}),
    mk("b", [D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}, D.SBool{False{}}, D.SBool{True{}}, D.SNull{}, D.SBool{False{}}], D.TBool{}),
    mk("e", [D.SBool{True{}}, D.SBool{True{}}, D.SBool{False{}}, D.SBool{False{}}, D.SBool{True{}}, D.SBool{False{}}, D.SBool{True{}}, D.SBool{False{}}], D.TBool{}),
    mk("s", [D.SStr{"1"}, D.SStr{"x"}, D.SStr{"3"}, D.SStr{"y"}, D.SStr{"5"}, D.SStr{"6"}, D.SStr{"7"}, D.SStr{"8"}], D.TStr{})])

def ops() -> List<&2, X.BinOp>:
  [X.Add{}, X.Sub{}, X.Mul{}, X.Eq{}, X.Ne{}, X.Lt{}, X.Le{}, X.Gt{}, X.Ge{}]

def fops() -> List<&2, X.BinOp>:
  [X.Add{}, X.Sub{}, X.Mul{}, X.Div{}, X.Eq{}, X.Ne{}, X.Lt{}, X.Le{}, X.Gt{}, X.Ge{}]

def arith() -> List<&2, X.BinOp>:
  [X.Add{}, X.Sub{}, X.Mul{}, X.Div{}]

# op applied to every pair (x, y) of the list
def by.ops(os: List<&2, X.BinOp>, +x: X.Expr, +y: X.Expr) -> List<&2, X.Expr>:
  match os:
    case Nil{}:
      Nil{}
    case op <> t:
      bin(op, x, y) <> by.ops(t, x, y)

def pairs(+os: List<&2, X.BinOp>, ps: List<&2, List<&2, X.Expr>>) -> List<&2, X.Expr>:
  match ps:
    case Nil{}:
      Nil{}
    case [x, y] <> t:
      List.append(&2, X.Expr, by.ops(os, x, y), pairs(os, t))
    case other <> t:
      pairs(os, t)

def wpairs() -> List<&2, List<&2, X.Expr>>:
  [[col("u"), col("w")], [col("w"), col("u")], [col("u"), col("u")], [col("w"), col("w")], [col("u"), lu(4)], [lu(4), col("u")], [col("w"), lu(0)], [lu(4294967295), col("w")], [bin(X.Add{}, col("u"), lu(1)), col("w")], [col("w"), bin(X.Mul{}, col("u"), col("w"))], [bin(X.Sub{}, col("w"), col("u")), lu(2)], [lu(3), bin(X.Add{}, col("u"), col("w"))], [fill(col("u"), lu(0)), col("w")], [col("w"), fill(col("u"), lu(0))], [fill(col("u"), lu(9)), lu(3)], [lu(1), fill(col("u"), lu(0))], [cast(col("e"), D.TU32{}), col("u")]]

def ipairs() -> List<&2, List<&2, X.Expr>>:
  [[col("i"), col("j")], [col("j"), col("i")], [col("i"), li(4294967294)], [li(2147483648), col("j")], [col("j"), li(0)], [li(7), col("i")], [bin(X.Sub{}, col("i"), col("j")), col("j")], [fill(col("i"), li(0)), col("j")], [col("j"), fill(col("i"), li(0))], [li(1), fill(col("i"), li(0))]]

def fpairs() -> List<&2, List<&2, X.Expr>>:
  [[col("f"), col("g")], [col("g"), col("f")], [col("f"), col("f")], [col("g"), lf(1.5)], [lf(1.5), col("f")], [col("f"), lf(nan())], [lf(F32.neg(0.0)), col("g")], [col("g"), lf(0.0)], [bin(X.Mul{}, col("f"), col("g")), lf(2.0)], [fill(col("f"), lf(0.0)), col("g")], [lf(1.0), fill(col("f"), lf(0.0))], [fill(col("f"), lf(F32.neg(0.0))), col("g")], [lf(1.0), fill(col("f"), lf(3.0))], [col("g"), fill(col("f"), lf(0.0))]]

# F3: a total cast folded into an f32 zip, on either side (the comparisons and the both-cast
# shapes have no kernel: they run unfused)
def cpairs() -> List<&2, List<&2, X.Expr>>:
  [[cast(col("u"), D.TF32{}), col("g")], [cast(col("w"), D.TF32{}), col("f")], [cast(col("i"), D.TF32{}), col("g")], [cast(col("j"), D.TF32{}), col("f")], [col("g"), cast(col("u"), D.TF32{})], [col("f"), cast(col("j"), D.TF32{})], [col("g"), cast(col("i"), D.TF32{})], [cast(col("b"), D.TF32{}), col("g")], [col("f"), cast(col("e"), D.TF32{})], [cast(col("u"), D.TF32{}), cast(col("w"), D.TF32{})], [cast(col("f"), D.TF32{}), col("g")]]

# shapes outside the arithmetic / comparison zips (they must run as before) and whole expressions
def others() -> List<&2, X.Expr>:
  [
    fill(col("u"), lu(0)), fill(col("u"), lu(5)), fill(col("w"), lu(0)), fill(col("i"), li(0)), fill(col("f"), lf(0.0)), fill(col("f"), lf(F32.neg(0.0))), fill(col("f"), lf(nan())), fill(col("b"), lb(False{})), fill(col("b"), lb(True{})), fill(col("s"), X.Lit{D.SStr{""}}),
    fill(bin(X.Add{}, col("u"), lu(1)), lu(0)), fill(bin(X.Mul{}, col("f"), col("g")), lf(0.0)), fill(X.Lit{D.SNull{}}, lu(0)), fill(col("u"), X.Cast{X.Lit{D.SNull{}}, D.TU32{}}),
    bin(X.And{}, col("b"), col("e")), bin(X.Or{}, col("b"), col("e")), bin(X.And{}, col("b"), lb(False{})), bin(X.Or{}, lb(True{}), col("b")),
    bin(X.FloorDiv{}, col("u"), col("w")), bin(X.Mod{}, col("i"), col("j")), bin(X.FloorDiv{}, col("j"), li(0)), bin(X.Mod{}, lu(7), col("u")),
    bin(X.Eq{}, col("s"), X.Lit{D.SStr{"x"}}), bin(X.Lt{}, col("s"), col("s")), bin(X.Eq{}, col("b"), col("e")), bin(X.Ne{}, col("e"), lb(True{})),
    bin(X.Add{}, lu(1), lu(2)), bin(X.Sub{}, col("u"), X.Agg{X.Sum{}, col("u")}), bin(X.Add{}, X.Agg{X.Sum{}, col("w")}, lu(1)), bin(X.Mul{}, X.Agg{X.Max{}, col("g")}, col("f")), bin(X.Gt{}, X.Agg{X.Mean{}, col("f")}, lf(0.0)),
    bin(X.Add{}, col("u"), X.Cast{X.Lit{D.SNull{}}, D.TU32{}}), bin(X.Mul{}, X.Cast{X.Lit{D.SNull{}}, D.TF32{}}, col("g")),
    bin(X.Mul{}, bin(X.Mul{}, cast(col("w"), D.TF32{}), col("g")), bin(X.Sub{}, lf(1.0), fill(col("f"), lf(0.0)))),
    bin(X.Mul{}, bin(X.Mul{}, cast(col("u"), D.TF32{}), col("f")), bin(X.Sub{}, lf(1.0), fill(col("f"), lf(0.0)))),
    cast(bin(X.Add{}, col("u"), col("w")), D.TF32{}), bin(X.Gt{}, bin(X.Add{}, col("u"), col("w")), lu(3)),
    X.Un{X.Neg{}, bin(X.Sub{}, col("j"), li(1))}, X.Clip{bin(X.Add{}, col("w"), lu(1)), D.SU32{2}, D.SU32{6}},
    X.When{bin(X.Gt{}, col("u"), lu(1)), bin(X.Add{}, col("w"), lu(1)), col("u")},
    X.TryCast{col("s"), D.TU32{}}, bin(X.Add{}, X.TryCast{col("s"), D.TU32{}}, col("w")), bin(X.Add{}, col("w"), X.TryCast{col("s"), D.TU32{}}),
    bin(X.Add{}, cast(col("i"), D.TI32{}), col("j")), bin(X.Add{}, cast(col("w"), D.TU32{}), lu(1)), bin(X.Mul{}, cast(col("e"), D.TI32{}), col("j"))]

def exprs() -> List<&2, X.Expr>:
  List.append(&2, X.Expr, pairs(ops(), wpairs()), List.append(&2, X.Expr, pairs(ops(), ipairs()), List.append(&2, X.Expr, pairs(fops(), fpairs()), List.append(&2, X.Expr, pairs(arith(), cpairs()), others()))))

# the unfused answer: the input frame with the column Eval.full computes appended (as with_columns
# appends `r`), or its error
def unf.k(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      frb(C.Frame.replace(f, "r", c))

def unf(+e: X.Expr, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{er}:
      "error: " ++ E.Err.show(er)
    case Done{f}:
      unf.k(V.Eval.full(f, e))

def fus(+e: X.Expr, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{er}:
      "error: " ++ E.Err.show(er)
    case Done{f}:
      frb(V.Eval.with_columns(f, [al(e, "r")]))


# select: r, then every input column (the last reads move them: the expression's earlier reads
# borrow), against r computed by Eval.full in front of the unchanged input columns
def allc() -> List<&2, X.Expr>:
  [col("u"), col("w"), col("i"), col("j"), col("f"), col("g"), col("b"), col("e"), col("s")]

def sfus(+e: X.Expr, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{er}:
      "error: " ++ E.Err.show(er)
    case Done{f}:
      frb(V.Eval.select(f, al(e, "r") <> allc()))

def sunf.c(c: C.Column, f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      frb(C.Frame.from_columns(C.Named{"r", c} <> cols))

def sunf.k(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      sunf.c(c, f)

def sunf(+e: X.Expr, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{er}:
      "error: " ++ E.Err.show(er)
    case Done{f}:
      sunf.k(V.Eval.full(f, e))

def report(same: Bool, +what: String, +a: String, +b: String) -> List<&2, String>:
  match same:
    case True{}:
      Nil{}
    case False{}:
      [what ++ "\n  fused:   " ++ a ++ "\n  unfused: " ++ b]

def diff.w(+e: X.Expr, +a: String, +b: String) -> List<&2, String>:
  report(String.eq(a, b), "with_columns " ++ X.Expr.show(e), a, b)

def diff.s(+e: X.Expr, +a: String, +b: String) -> List<&2, String>:
  report(String.eq(a, b), "select " ++ X.Expr.show(e), a, b)

def diff(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      List.append(&2, String, diff.w(e, fus(e, dbase()), unf(e, dbase())), List.append(&2, String, diff.s(e, sfus(e, dbase()), sunf(e, dbase())), diff(t)))

# filter: Eval.filter (F5 or the fused evaluator) against v0.1's path (Eval.full, then the mask of
# Eval.pred and Frame.filter_mask: Eval.filter.go)
def preds() -> List<&2, X.Expr>:
  [col("b"), col("e"), bin(X.And{}, col("b"), col("e")), bin(X.And{}, col("e"), col("b")),
   bin(X.Gt{}, col("u"), lu(2)), bin(X.And{}, bin(X.Gt{}, col("u"), lu(2)), col("e")), bin(X.And{}, col("e"), bin(X.Gt{}, col("u"), lu(2))),
   bin(X.And{}, col("b"), bin(X.Le{}, col("w"), lu(5))), bin(X.And{}, bin(X.And{}, bin(X.Lt{}, col("i"), li(0)), bin(X.Ge{}, col("j"), li(1))), col("e")),
   bin(X.And{}, bin(X.Ne{}, col("i"), li(2)), bin(X.Eq{}, col("j"), li(4294967289))),
   bin(X.Gt{}, col("f"), lf(0.0)), bin(X.Eq{}, col("g"), lf(nan())), bin(X.Le{}, col("f"), lf(F32.neg(0.0))), bin(X.Ge{}, col("g"), lf(0.0)), bin(X.Ne{}, col("f"), lf(2.5)), bin(X.Lt{}, col("g"), lf(3.0)),
   bin(X.And{}, bin(X.Gt{}, col("g"), lf(1.0)), bin(X.Lt{}, col("g"), lf(5.0))), bin(X.And{}, bin(X.And{}, bin(X.Gt{}, col("f"), lf(0.0)), bin(X.Lt{}, col("f"), lf(10.0))), col("b")),
   bin(X.And{}, col("b"), bin(X.And{}, col("e"), bin(X.Ne{}, col("u"), lu(1)))),
   bin(X.Lt{}, lu(4), col("u")), bin(X.Or{}, col("b"), col("e")), bin(X.Or{}, bin(X.Gt{}, col("u"), lu(2)), col("b")), lb(True{}), lb(False{}),
   bin(X.And{}, col("b"), lb(True{})), bin(X.And{}, bin(X.Eq{}, col("s"), X.Lit{D.SStr{"x"}}), col("e")), bin(X.Gt{}, bin(X.Add{}, col("u"), lu(1)), lu(2)),
   bin(X.And{}, bin(X.Gt{}, col("u"), col("w")), col("e")), bin(X.And{}, bin(X.Gt{}, col("u"), X.Cast{X.Lit{D.SNull{}}, D.TU32{}}), col("e")),
   bin(X.Gt{}, X.Agg{X.Sum{}, col("w")}, lu(3)), bin(X.And{}, col("e"), bin(X.Eq{}, col("b"), lb(True{}))),
   bin(X.And{}, bin(X.Gt{}, col("u"), lu(2)), bin(X.Gt{}, cast(col("s"), D.TU32{}), lu(1)))]

def pfus(+p: X.Expr, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{er}:
      "error: " ++ E.Err.show(er)
    case Done{f}:
      frb(V.Eval.filter(f, p))

def punf(+p: X.Expr, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{er}:
      "error: " ++ E.Err.show(er)
    case Done{f}:
      frb(V.Eval.filter.go(V.Eval.full(f, p)))

def diff.p(+p: X.Expr, +a: String, +b: String) -> List<&2, String>:
  report(String.eq(a, b), "filter " ++ X.Expr.show(p), a, b)

def pdiff(ps: List<&2, X.Expr>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      List.append(&2, String, diff.p(p, pfus(p, dbase()), punf(p, dbase())), pdiff(t))

# part 3: single-expression errors, fused (with_columns) and unfused (Eval.full)
def errs() -> List<&2, X.Expr>:
  [bin(X.Add{}, cast(col("s"), D.TU32{}), cast(col("u"), D.TI32{})),
   bin(X.Add{}, cast(col("u"), D.TI32{}), cast(col("s"), D.TU32{})),
   bin(X.Add{}, cast(col("g"), D.TU32{}), col("w")),
   bin(X.Add{}, col("w"), cast(col("g"), D.TU32{})),
   bin(X.Sub{}, lf(1.0), cast(col("s"), D.TF32{})),
   bin(X.Mul{}, cast(col("f"), D.TU32{}), cast(col("g"), D.TU32{})),
   bin(X.Add{}, bin(X.Mul{}, col("u"), lu(2)), cast(col("f"), D.TU32{})),
   cast(fill(col("u"), lu(0)), D.TI32{})]

def eshow.k(same: Bool, +a: String) -> String:
  match same:
    case True{}:
      a
    case False{}:
      a ++ " (UNFUSED DIFFERS)"

def eshow(+e: X.Expr) -> String:
  eshow.k(String.eq(fus(e, dbase()), unf(e, dbase())), fus(e, dbase()))

def eshows(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      eshow(e) <> eshows(t)

def nshow(+n: Nat) -> String:
  U32.show(U32.from_nat(n))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- part 1: with_columns (the input columns come back unchanged), select, filter")
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Add{}, col("a"), lu(1)), "d")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Sub{}, lf(1.0), fill(col("c"), lf(0.0))), "e")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Mul{}, cast(col("a"), D.TF32{}), col("c")), "p")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Gt{}, col("b"), col("a")), "g")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Lt{}, lu(20), col("b")), "h")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(fill(col("a"), lu(0)), "z")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Mul{}, cast(bin(X.Add{}, col("a"), lu(1)), D.TF32{}), col("c")), "q")]))))
    IO.print(on(f => fr(V.Eval.select(f, [al(bin(X.Mul{}, bin(X.Mul{}, cast(col("a"), D.TF32{}), col("c")), bin(X.Sub{}, lf(1.0), fill(col("c"), lf(0.0)))), "r")]))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.And{}, col("k"), bin(X.Gt{}, col("b"), lu(15)))))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.And{}, bin(X.Gt{}, col("b"), lu(15)), bin(X.Lt{}, col("c"), lf(0.0)))))))
    IO.print(on(f => fr(V.Eval.filter(f, col("k")))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.And{}, bin(X.And{}, bin(X.Gt{}, col("a"), lu(1)), bin(X.Lt{}, col("b"), lu(35))), col("k"))))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.Or{}, col("k"), bin(X.Gt{}, col("b"), lu(35)))))))
    IO.print("-- part 2: differential (fused vs unfused, F32 by bits)")
    IO.print(String.join(diff(exprs()), "\n"))
    IO.print("expressions: " ++ nshow(List.length(&2, X.Expr, exprs())))
    IO.print(String.join(pdiff(preds()), "\n"))
    IO.print("predicates: " ++ nshow(List.length(&2, X.Expr, preds())))
    IO.print("-- part 3: competing errors (rows, operands, expressions) next to fused fragments")
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Add{}, cast(col("s"), D.TU32{}), cast(col("b"), D.TI32{})), "x")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Add{}, cast(col("b"), D.TI32{}), cast(col("s"), D.TI32{})), "x")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Add{}, col("a"), lu(1)), "d"), al(cast(col("c"), D.TU32{}), "e"), al(cast(col("b"), D.TI32{}), "f")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Add{}, bin(X.Mul{}, col("a"), lu(2)), cast(col("c"), D.TU32{})), "x")]))))
    IO.print(on(f => fr(V.Eval.select(f, [al(bin(X.Add{}, cast(col("s"), D.TU32{}), col("b")), "y"), col("s")]))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.And{}, bin(X.Gt{}, col("b"), lu(15)), bin(X.Gt{}, cast(col("s"), D.TU32{}), lu(1)))))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Sub{}, lf(1.0), cast(col("s"), D.TF32{})), "x")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(cast(col("s"), D.TU32{}), "x"), al(bin(X.Add{}, col("a"), lf(1.0)), "y")]))))
    IO.print(String.join(eshows(errs()), "\n"))
