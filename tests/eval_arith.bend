# Eval: with_columns / filter / select (M2 acceptance), arithmetic per dtype
# with null propagation, division by zero, U32 wrap-around, I32 negatives,
# broadcasting of literals and aggregations.
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
  C.Frame.from_columns([mk("a", [D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}, D.SU32{5}], D.TU32{}), mk("b", [D.SF32{0.5}, D.SF32{1.5}, D.SF32{2.5}, D.SNull{}, D.SF32{4.5}], D.TF32{}), mk("i", [neg(3), pos(7), neg(8), pos(0), D.SNull{}], D.TI32{})])

def strs() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("s", [D.SStr{"1.5"}, D.SStr{"x"}, D.SStr{" 3"}, D.SNull{}, D.SStr{"-2"}], D.TStr{})])

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

def on(g: C.Frame -> String) -> String:
  on.k(g, base())

# one expression over the base frame
def ex(e: X.Expr) -> String:
  on(f => ex.k(V.Eval.expr(f, e)))

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def lf(v: F32) -> X.Expr:
  X.Lit{D.SF32{v}}

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
    # M2 acceptance: with_columns(alias(add(col a, lit 1), "c")) keeps the null
    IO.print(on(f => table(V.Eval.with_columns(f, [X.Alias{bin(X.Add{}, col("a"), lu(1)), "c"}]))))
    # filter(gt(col a, lit 3)): the null row is dropped, order kept
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.Gt{}, col("a"), lu(3))))))
    # select reorders (and drops)
    IO.print(on(f => fr(V.Eval.select(f, [col("i"), col("a")]))))
    # cast(str -> f32): "x" (unparsable) becomes null, text is trimmed
    IO.print(on.k(f => fr(V.Eval.select(f, [X.Alias{X.Cast{col("s"), D.TF32{}}, "x"}])), strs()))
    # U32: + - * / % (wrap-around, division by zero answers 0, mod by zero a)
    IO.print(ex(bin(X.Sub{}, col("a"), lu(3))))
    IO.print(ex(bin(X.Mul{}, col("a"), lu(4294967295))))
    IO.print(ex(bin(X.Div{}, col("a"), lu(2))))
    IO.print(ex(bin(X.Mod{}, col("a"), lu(2))))
    IO.print(ex(bin(X.Div{}, col("a"), lu(0))))
    IO.print(ex(bin(X.Mod{}, col("a"), lu(0))))
    # I32 negatives: truncating division, remainder takes the sign of a
    IO.print(ex(bin(X.Sub{}, col("i"), X.Lit{pos(5)})))
    IO.print(ex(bin(X.Mul{}, col("i"), col("i"))))
    IO.print(ex(bin(X.Div{}, col("i"), X.Lit{pos(2)})))
    IO.print(ex(bin(X.Mod{}, col("i"), X.Lit{pos(3)})))
    IO.print(ex(bin(X.Div{}, col("i"), X.Lit{neg(2)})))
    IO.print(ex(bin(X.Div{}, col("i"), X.Lit{pos(0)})))
    IO.print(ex(X.Un{X.Neg{}, col("i")}))
    IO.print(ex(X.Un{X.Abs{}, col("i")}))
    # F32: IEEE, x / 0 = inf, -x / 0 = -inf, 0 / 0 = nan
    IO.print(ex(bin(X.Mul{}, col("b"), lf(2.0))))
    IO.print(ex(bin(X.Div{}, col("b"), lf(0.0))))
    IO.print(ex(bin(X.Div{}, X.Un{X.Neg{}, col("b")}, lf(0.0))))
    IO.print(ex(bin(X.Div{}, bin(X.Sub{}, col("b"), col("b")), lf(0.0))))
    IO.print(ex(X.Un{X.Sqrt{}, col("b")}))
    # column op column, both nullable: nulls OR together
    IO.print(ex(bin(X.Add{}, X.Cast{col("a"), D.TF32{}}, col("b"))))
    # broadcasting: an aggregation against a column, a literal-only result
    IO.print(ex(bin(X.Sub{}, X.Cast{col("a"), D.TF32{}}, X.Agg{X.Mean{}, col("a")})))
    IO.print(ex(bin(X.Add{}, X.Agg{X.Sum{}, col("a")}, lu(1))))
    IO.print(ex(bin(X.Add{}, lu(2), lu(3))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [X.Alias{X.Lit{D.SStr{"k"}}, "k"}, X.Alias{X.Agg{X.Max{}, col("i")}, "m"}]))))
    # with_columns: in place, and every expression sees the INPUT frame
    IO.print(on(f => fr(V.Eval.with_columns(f, [X.Alias{bin(X.Mul{}, col("a"), lu(10)), "a"}, X.Alias{bin(X.Add{}, col("a"), lu(1)), "z"}]))))
    # select of aggregations: one row; mixed with a column: broadcast
    IO.print(on(f => fr(V.Eval.select(f, [X.Agg{X.Sum{}, col("a")}, X.Alias{X.Agg{X.Count{}, col("b")}, "nb"}]))))
    IO.print(on(f => fr(V.Eval.select(f, [col("a"), X.Alias{X.Agg{X.Sum{}, col("a")}, "s"}]))))
    # a filter that keeps nothing: an empty frame with the same columns
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.Gt{}, col("a"), lu(100))))))
    # constant folding
    IO.print(rs(V.Eval.scalar(bin(X.Mul{}, lu(6), lu(7)))))
#|shape: (5, 4)
#|+-----+-----+-----+-----+
#|| a   | b   | i   | c   |
#|| --- | --- | --- | --- |
#|| u32 | f32 | i32 | u32 |
#|+=====+=====+=====+=====+
#|| 1   | 0.5 | -3  | 2   |
#|| 2   | 1.5 | 7   | 3   |
#||     | 2.5 | -8  |     |
#|| 4   |     | 0   | 5   |
#|| 5   | 4.5 |     | 6   |
#|+-----+-----+-----+-----+
#|h=2 a:u32=[4, 5] | b:f32=[null, 4.5] | i:i32=[0, null]
#|h=5 i:i32=[-3, 7, -8, 0, null] | a:u32=[1, 2, null, 4, 5]
#|h=5 x:f32=[1.5, null, 3, null, -2]
#|u32=[4294967294, 4294967295, null, 1, 2]
#|u32=[4294967295, 4294967294, null, 4294967292, 4294967291]
#|u32=[0, 1, null, 2, 2]
#|u32=[1, 0, null, 0, 1]
#|u32=[0, 0, null, 0, 0]
#|u32=[1, 2, null, 4, 5]
#|i32=[-8, 2, -13, -5, null]
#|i32=[9, 49, 64, 0, null]
#|i32=[-1, 3, -4, 0, null]
#|i32=[0, 1, -2, 0, null]
#|i32=[1, -3, 4, 0, null]
#|i32=[0, 0, 0, 0, null]
#|i32=[3, -7, 8, 0, null]
#|i32=[3, 7, 8, 0, null]
#|f32=[1, 3, 5, null, 9]
#|f32=[inf, inf, inf, null, inf]
#|f32=[-inf, -inf, -inf, null, -inf]
#|f32=[nan, nan, nan, null, nan]
#|f32=[0.70710677, 1.2247449, 1.5811388, null, 2.1213202]
#|f32=[1.5, 3.5, null, null, 9.5]
#|f32=[-2, -1, null, 1, 2]
#|u32=[13]
#|u32=[5, 5, 5, 5, 5]
#|h=5 a:u32=[1, 2, null, 4, 5] | b:f32=[0.5, 1.5, 2.5, null, 4.5] | i:i32=[-3, 7, -8, 0, null] | k:str=[k, k, k, k, k] | m:i32=[7, 7, 7, 7, 7]
#|h=5 a:u32=[10, 20, null, 40, 50] | b:f32=[0.5, 1.5, 2.5, null, 4.5] | i:i32=[-3, 7, -8, 0, null] | z:u32=[2, 3, null, 5, 6]
#|h=1 a:u32=[12] | nb:u32=[4]
#|h=5 a:u32=[1, 2, null, 4, 5] | s:u32=[12, 12, 12, 12, 12]
#|h=0 a:u32=[] | b:f32=[] | i:i32=[]
#|42
