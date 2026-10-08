# Eval: the cast table at runtime (DESIGN.md 15.5.5): strict cast (the first failing valid
# cell is an error), try_cast (failing cells become null), Str parses of the text as is,
# nulls through casts, the typed null literal.
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
  C.Frame.from_columns([mk("s", [D.SStr{"1.5"}, D.SStr{"x"}, D.SStr{" 3"}, D.SNull{}, D.SStr{"-2"}, D.SStr{"true"}, D.SStr{"False"}], D.TStr{}), mk("i", [neg(3), pos(7), D.SNull{}, pos(0), neg(2147483648), pos(2147483647), neg(1)], D.TI32{}), mk("f", [D.SF32{2.7}, D.SF32{F32.neg(2.7)}, D.SNull{}, D.SF32{0.5}, D.SF32{F32.neg(0.5)}, D.SF32{100.0}, D.SF32{3.0}], D.TF32{}), mk("b", [D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}, D.SBool{False{}}, D.SBool{True{}}, D.SBool{False{}}], D.TBool{}), mk("a", [D.SU32{0}, D.SU32{1}, D.SNull{}, D.SU32{4294967295}, D.SU32{7}, D.SU32{10}, D.SU32{3}], D.TU32{})])

def cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.Cast{e, t}

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

def try_cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.TryCast{e, t}

def li(v: U32) -> X.Expr:
  X.Lit{pos(v)}

def main() -> IO(Unit):
  do IO<Unit>:
    # Str -> numbers / bool with try_cast: the text as is (no trimming), a failure is null
    IO.print(ex(try_cast(col("s"), D.TF32{})))
    IO.print(ex(try_cast(col("s"), D.TU32{})))
    IO.print(ex(try_cast(col("s"), D.TI32{})))
    IO.print(ex(try_cast(col("s"), D.TBool{})))
    IO.print(ex(cast(col("s"), D.TStr{})))
    # strict cast: the first valid cell that does not read is the error
    IO.print(ex(cast(col("s"), D.TF32{})))
    IO.print(ex(cast(col("s"), D.TBool{})))
    # I32 -> U32: negatives fail (cast) or become null (try_cast); values to F32, text
    IO.print(ex(cast(col("i"), D.TU32{})))
    IO.print(ex(try_cast(col("i"), D.TU32{})))
    IO.print(ex(cast(col("i"), D.TStr{})))
    IO.print(ex(cast(try_cast(col("i"), D.TU32{}), D.TI32{})))
    IO.print(ex(cast(X.Bin{X.FloorDiv{}, col("i"), li(1000000)}, D.TF32{})))
    # F32 -> I32: truncation toward zero (in range); F32 -> U32: -2.7 fails, -0.5 is 0
    IO.print(ex(cast(col("f"), D.TI32{})))
    IO.print(ex(cast(col("f"), D.TU32{})))
    IO.print(ex(try_cast(col("f"), D.TU32{})))
    IO.print(ex(cast(col("f"), D.TStr{})))
    # Bool -> 0/1 and text
    IO.print(ex(cast(col("b"), D.TU32{})))
    IO.print(ex(cast(col("b"), D.TI32{})))
    IO.print(ex(cast(col("b"), D.TF32{})))
    IO.print(ex(cast(col("b"), D.TStr{})))
    # U32 -> I32: 2^32-1 fails (cast) or is null (try_cast); to F32 through I32, text
    IO.print(ex(cast(col("a"), D.TI32{})))
    IO.print(ex(try_cast(col("a"), D.TI32{})))
    IO.print(ex(cast(try_cast(col("a"), D.TI32{}), D.TF32{})))
    IO.print(ex(cast(col("a"), D.TStr{})))
    # round trip through text
    IO.print(ex(cast(cast(col("f"), D.TStr{}), D.TF32{})))
    # the typed null literal broadcasts as an all-null column (cast and try_cast)
    IO.print(ex(cast(X.Lit{D.SNull{}}, D.TStr{})))
    IO.print(ex(try_cast(X.Lit{D.SNull{}}, D.TI32{})))
    IO.print(ex(X.FillNull{col("a"), cast(X.Lit{D.SNull{}}, D.TU32{})}))
    # identity casts and refused ones
    IO.print(ex(cast(col("b"), D.TBool{})))
    IO.print(ex(cast(col("f"), D.TBool{})))
    IO.print(ex(try_cast(col("f"), D.TBool{})))
    # constant folding through a parse
    IO.print(rs(V.Eval.scalar(bin(X.Add{}, cast(ls("12"), D.TU32{}), lu(1)))))
    IO.print(rs(V.Eval.scalar(cast(ls("1e3"), D.TF32{}))))
    IO.print(rs(V.Eval.scalar(cast(ls("abc"), D.TI32{}))))
    IO.print(rs(V.Eval.scalar(try_cast(ls("abc"), D.TI32{}))))
#|f32=[1.5, null, null, null, -2, null, null]
#|u32=[null, null, null, null, null, null, null]
#|i32=[null, null, null, null, -2, null, null]
#|bool=[null, null, null, null, null, true, false]
#|str=[1.5, x,  3, null, -2, true, False]
#|error: InvalidOperation: cast str to f32: row 1 holds "x"
#|error: InvalidOperation: cast str to bool: row 0 holds "1.5"
#|error: InvalidOperation: cast i32 to u32: row 0 holds -3
#|u32=[null, 7, null, 0, null, 2147483647, null]
#|str=[-3, 7, null, 0, -2147483648, 2147483647, -1]
#|i32=[null, 7, null, 0, null, 2147483647, null]
#|f32=[-1, 0, null, 0, -2148, 2147, -1]
#|i32=[2, -2, null, 0, 0, 100, 3]
#|error: InvalidOperation: cast f32 to u32: row 1 holds -2.7
#|u32=[2, null, null, 0, 0, 100, 3]
#|str=[2.7, -2.7, null, 0.5, -0.5, 100, 3]
#|u32=[1, 0, null, 1, 0, 1, 0]
#|i32=[1, 0, null, 1, 0, 1, 0]
#|f32=[1, 0, null, 1, 0, 1, 0]
#|str=[true, false, null, true, false, true, false]
#|error: InvalidOperation: cast u32 to i32: row 3 holds 4294967295
#|i32=[0, 1, null, null, 7, 10, 3]
#|f32=[0, 1, null, null, 7, 10, 3]
#|str=[0, 1, null, 4294967295, 7, 10, 3]
#|f32=[2.7, -2.7, null, 0.5, -0.5, 100, 3]
#|str=[null, null, null, null, null, null, null]
#|i32=[null, null, null, null, null, null, null]
#|u32=[0, 1, null, 4294967295, 7, 10, 3]
#|bool=[true, false, null, true, false, true, false]
#|error: TypeMismatch in cast: expected castable to bool, got f32
#|error: TypeMismatch in try_cast: expected castable to bool, got f32
#|13
#|1000
#|error: InvalidOperation: cast str to i32: row 0 holds "abc"
#|null
