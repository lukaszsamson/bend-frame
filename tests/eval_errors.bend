# Eval: early (pre-evaluation) errors of select / with_columns / filter,
# duplicate output names, constant folding, degenerate frames.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/eval.bend as V
import ./../src/fmt.bend as F

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

def cs.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scal(xs)

def cs.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cs.b(t, C.Column.to_scalars(c))

# a column as `dtype=[cells]`
def cs(c: C.Column) -> String:
  cs.a(C.Column.dtype(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs(c)) <> ncols(t)

# a frame as `h=N name:dtype=[cells] | ...`
def fs(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncols(cols), " | ")

def fr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fs(f)

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def table(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def ex.k(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      cs(c)

def neg(v: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{v})}

def pos(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [D.SU32{1}, D.SU32{2}, D.SNull{}], D.TU32{}), mk("b", [D.SF32{0.5}, D.SNull{}, D.SF32{2.5}], D.TF32{})])

# Eval.expr hands the frame back unchanged
def after(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e) ++ " / " ++ fs(f)
    case Done{c}:
      cs(c) ++ " / " ++ fs(f)

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

def on(g: C.Frame -> String) -> String:
  on.k(g, base())

def ex(e: X.Expr) -> String:
  on(f => ex.k(V.Eval.expr(f, e)))

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def ls(s: String) -> X.Expr:
  X.Lit{D.SStr{s}}

def lb(b: Bool) -> X.Expr:
  X.Lit{D.SBool{b}}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def rs(r: E.Res(D.Scalar)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{v}:
      D.Scalar.show(v)

def main() -> IO(Unit):
  do IO<Unit>:
    # every expression is type checked before anything runs
    IO.print(on(f => fr(V.Eval.with_columns(f, [X.Alias{bin(X.Add{}, col("a"), col("b")), "c"}]))))
    IO.print(on(f => fr(V.Eval.select(f, [col("a"), col("nope")]))))
    IO.print(on(f => fr(V.Eval.select(f, [col("a"), X.Un{X.Not{}, col("a")}]))))
    IO.print(on(f => fr(V.Eval.filter(f, col("a")))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.Gt{}, col("nope"), lu(1))))))
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.Gt{}, col("b"), lu(1))))))
    IO.print(on(f => after(V.Eval.expr(f, X.Lit{D.SNull{}}))))
    IO.print(on(f => after(V.Eval.expr(f, X.Agg{X.Sum{}, col("b")}))))
    # output names: duplicates are errors (type errors are reported first)
    IO.print(on(f => fr(V.Eval.select(f, [col("a"), X.Agg{X.Max{}, col("a")}]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [X.Alias{lu(1), "x"}, X.Alias{lu(2), "x"}]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [X.Alias{col("nope"), "x"}, X.Alias{lu(2), "x"}]))))
    # constant folding needs no frame; a column reference fails
    IO.print(rs(V.Eval.scalar(col("a"))))
    IO.print(rs(V.Eval.scalar(X.Agg{X.Sum{}, lu(5)})))
    IO.print(rs(V.Eval.scalar(X.Agg{X.Len{}, lu(1)})))
    IO.print(rs(V.Eval.scalar(X.Cast{X.Lit{D.SNull{}}, D.TI32{}})))
    # empty selections and a frame with no columns
    IO.print(on(f => fr(V.Eval.select(f, Nil{}))))
    IO.print(on(f => fr(V.Eval.with_columns(f, Nil{}))))
    IO.print(fr(V.Eval.with_columns(C.Frame.empty(), [X.Alias{lu(1), "x"}])))
    IO.print(fr(V.Eval.select(C.Frame.empty(), [X.Alias{X.Agg{X.Len{}, lu(1)}, "n"}, X.Alias{X.Agg{X.Sum{}, lu(1)}, "s"}])))
#|error: TypeMismatch in add: expected u32, got f32
#|error: ColumnNotFound: nope
#|error: TypeMismatch in not: expected bool, got u32
#|error: TypeMismatch in filter: expected bool, got u32
#|error: ColumnNotFound: nope
#|error: TypeMismatch in gt: expected f32, got u32
#|error: TypeMismatch in lit: expected a typed literal, got null / h=3 a:u32=[1, 2, null] | b:f32=[0.5, null, 2.5]
#|f32=[3] / h=3 a:u32=[1, 2, null] | b:f32=[0.5, null, 2.5]
#|error: DuplicateColumn: a
#|error: DuplicateColumn: x
#|error: ColumnNotFound: nope
#|error: ColumnNotFound: a
#|5
#|1
#|null
#|h=0 
#|h=3 a:u32=[1, 2, null] | b:f32=[0.5, null, 2.5]
#|h=0 x:u32=[]
#|h=1 n:u32=[0] | s:u32=[0]
