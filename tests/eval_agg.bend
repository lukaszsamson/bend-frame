# Eval aggregations: sum/mean/min/max/count/len/first/last/n_unique over
# columns with nulls (sum/mean/min/max/count skip nulls; first/last return the
# first/last ROW even when null; n_unique counts null as one value, all like
# Polars), an all-null column, an empty frame, aggregations of expressions and
# literals (aggregating a literal does not broadcast it), compensated F32 sums.
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
  C.Frame.from_columns([mk("a", [D.SU32{3}, D.SNull{}, D.SU32{1}, D.SU32{3}, D.SU32{5}, D.SNull{}], D.TU32{}), mk("f", [D.SF32{2.5}, D.SNull{}, D.SF32{F32.neg(1.0)}, D.SF32{2.5}, D.SF32{0.5}, D.SNull{}], D.TF32{}), mk("i", [neg(4), D.SNull{}, pos(2), neg(4), pos(9), D.SNull{}], D.TI32{}), mk("s", [D.SStr{"pear"}, D.SNull{}, D.SStr{"apple"}, D.SStr{"pear"}, D.SStr{"fig"}, D.SNull{}], D.TStr{}), mk("b", [D.SBool{True{}}, D.SNull{}, D.SBool{False{}}, D.SBool{True{}}, D.SBool{True{}}, D.SNull{}], D.TBool{}), mk("n", [D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}], D.TU32{})])

# first row null, last row valid, one distinct value twice
def edge() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("x", [D.SNull{}, D.SU32{7}, D.SU32{7}, D.SU32{9}], D.TU32{}), mk("y", [D.SU32{7}, D.SU32{7}, D.SU32{9}, D.SU32{9}], D.TU32{}), mk("z", [D.SStr{"b"}, D.SNull{}, D.SStr{"b"}, D.SNull{}], D.TStr{})])

def tenths() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("x", [D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}, D.SF32{0.1}], D.TF32{})])

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

def on(g: C.Frame -> String) -> String:
  on.k(g, base())

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def named(+op: X.AggOp, +c: String) -> X.Expr:
  X.Alias{X.Agg{op, X.Col{c}}, X.AggOp.name(op)}

def every(+c: String) -> List<&2, X.Expr>:
  [named(X.Sum{}, c), named(X.Mean{}, c), named(X.Min{}, c), named(X.Max{}, c), named(X.Count{}, c), named(X.Len{}, c), named(X.First{}, c), named(X.Last{}, c), named(X.NUnique{}, c)]

def nonnum(+c: String) -> List<&2, X.Expr>:
  [named(X.Min{}, c), named(X.Max{}, c), named(X.Count{}, c), named(X.Len{}, c), named(X.First{}, c), named(X.Last{}, c), named(X.NUnique{}, c)]

def sel(es: List<&2, X.Expr>) -> String:
  on(f => fr(V.Eval.select(f, es)))

# select after a filter
def fsel.k(es: List<&2, X.Expr>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fr(V.Eval.select(f, es))

def fsel(pred: X.Expr, es: List<&2, X.Expr>) -> String:
  on(f => fsel.k(es, V.Eval.filter(f, pred)))

def esel(es: List<&2, X.Expr>) -> String:
  on.k(f => fr(V.Eval.select(f, es)), edge())

def main() -> IO(Unit):
  do IO<Unit>:
    # every aggregation over each dtype, nulls skipped
    IO.print(sel(every("a")))
    IO.print(sel(every("f")))
    IO.print(sel(every("i")))
    IO.print(sel(nonnum("s")))
    IO.print(sel(nonnum("b")))
    # an all-null column: sum 0, count 0, n_unique 1 (null is a value), the rest null
    IO.print(sel(every("n")))
    # an empty frame (a filter that keeps nothing): same, and len 0
    IO.print(fsel(X.Bin{X.Gt{}, col("a"), lu(100)}, every("a")))
    IO.print(fsel(X.Bin{X.Gt{}, col("a"), lu(100)}, nonnum("s")))
    # strict typing: sum/mean need numbers
    IO.print(sel([named(X.Sum{}, "s")]))
    IO.print(sel([named(X.Mean{}, "b")]))
    # aggregations of expressions; literals broadcast to the height first
    IO.print(sel([X.Agg{X.Sum{}, X.Bin{X.Mul{}, col("a"), lu(2)}}, X.Agg{X.Mean{}, X.Bin{X.Add{}, X.Cast{col("a"), D.TF32{}}, col("f")}}]))
    IO.print(sel([X.Agg{X.Sum{}, X.Bin{X.Mul{}, col("a"), lu(2)}}, X.Alias{X.Agg{X.Mean{}, X.Bin{X.Add{}, X.Cast{col("a"), D.TF32{}}, col("f")}}, "m"}]))
    IO.print(sel([X.Alias{X.Agg{X.Sum{}, lu(2)}, "s2"}, X.Agg{X.Len{}, lu(1)}, X.Alias{X.Agg{X.Max{}, X.Lit{D.SStr{"z"}}}, "mz"}]))
    # an aggregation of an aggregation is a 1-row aggregation
    IO.print(sel([X.Agg{X.Count{}, X.Agg{X.Sum{}, col("a")}}]))
    # Eval.expr: a 1-row column
    IO.print(on(f => ex.k(V.Eval.expr(f, X.Agg{X.Min{}, col("f")}))))
    # compensated F32 summation: ten 0.1 sum to exactly 1
    IO.print(on.k(f => fr(V.Eval.select(f, [named(X.Sum{}, "x"), named(X.Mean{}, "x")])), tenths()))
    # first / last return the row as is, null included; n_unique counts null as a value
    IO.print(esel([named(X.First{}, "x"), named(X.Last{}, "x"), named(X.NUnique{}, "x"), named(X.Count{}, "x"), named(X.Len{}, "x")]))
    IO.print(esel([named(X.First{}, "y"), named(X.Last{}, "y"), named(X.NUnique{}, "y")]))
    IO.print(esel([named(X.First{}, "z"), named(X.Last{}, "z"), named(X.NUnique{}, "z")]))
    # literals: an aggregate of a literal is the literal's own (Polars: lit(2).sum() = 2);
    # len(lit) is the frame height (that is how pl.len() is encoded)
    IO.print(sel([X.Alias{X.Agg{X.Sum{}, lu(2)}, "s"}, X.Alias{X.Agg{X.Mean{}, lu(2)}, "m"}, X.Alias{X.Agg{X.Count{}, lu(2)}, "c"}, X.Alias{X.Agg{X.NUnique{}, lu(2)}, "u"}, X.Alias{X.Agg{X.First{}, lu(2)}, "f"}, X.Alias{X.Agg{X.Len{}, lu(1)}, "n"}]))
    # a literal-only select has 1 row; a column in the select makes literals broadcast
    IO.print(sel([X.Alias{lu(2), "two"}, X.Alias{X.Bin{X.Add{}, lu(2), lu(3)}, "five"}]))
    IO.print(sel([X.Alias{lu(2), "two"}, col("a")]))
    IO.print(sel([X.Alias{X.Agg{X.Sum{}, lu(2)}, "s"}, X.Alias{lu(3), "t"}]))
    IO.print(sel([X.Alias{X.Bin{X.Add{}, X.Agg{X.Sum{}, lu(2)}, col("a")}, "x"}]))
#|h=1 sum:u32=[12] | mean:f32=[3] | min:u32=[1] | max:u32=[5] | count:u32=[4] | len:u32=[6] | first:u32=[3] | last:u32=[null] | n_unique:u32=[4]
#|h=1 sum:f32=[4.5] | mean:f32=[1.125] | min:f32=[-1] | max:f32=[2.5] | count:u32=[4] | len:u32=[6] | first:f32=[2.5] | last:f32=[null] | n_unique:u32=[4]
#|h=1 sum:i32=[3] | mean:f32=[0.75] | min:i32=[-4] | max:i32=[9] | count:u32=[4] | len:u32=[6] | first:i32=[-4] | last:i32=[null] | n_unique:u32=[4]
#|h=1 min:str=[apple] | max:str=[pear] | count:u32=[4] | len:u32=[6] | first:str=[pear] | last:str=[null] | n_unique:u32=[4]
#|h=1 min:bool=[false] | max:bool=[true] | count:u32=[4] | len:u32=[6] | first:bool=[true] | last:bool=[null] | n_unique:u32=[3]
#|h=1 sum:u32=[0] | mean:f32=[null] | min:u32=[null] | max:u32=[null] | count:u32=[0] | len:u32=[6] | first:u32=[null] | last:u32=[null] | n_unique:u32=[1]
#|h=1 sum:u32=[0] | mean:f32=[null] | min:u32=[null] | max:u32=[null] | count:u32=[0] | len:u32=[0] | first:u32=[null] | last:u32=[null] | n_unique:u32=[0]
#|h=1 min:str=[null] | max:str=[null] | count:u32=[0] | len:u32=[0] | first:str=[null] | last:str=[null] | n_unique:u32=[0]
#|error: TypeMismatch in sum: expected numeric, got str
#|error: TypeMismatch in mean: expected numeric, got bool
#|error: DuplicateColumn: a
#|h=1 a:u32=[24] | m:f32=[4.125]
#|h=1 s2:u32=[2] | literal:u32=[6] | mz:str=[z]
#|h=1 a:u32=[1]
#|f32=[-1]
#|h=1 sum:f32=[1] | mean:f32=[0.1]
#|h=1 first:u32=[null] | last:u32=[9] | n_unique:u32=[3] | count:u32=[3] | len:u32=[4]
#|h=1 first:u32=[7] | last:u32=[9] | n_unique:u32=[2]
#|h=1 first:str=[b] | last:str=[null] | n_unique:u32=[2]
#|h=1 s:u32=[2] | m:f32=[2] | c:u32=[1] | u:u32=[1] | f:u32=[2] | n:u32=[6]
#|h=1 two:u32=[2] | five:u32=[5]
#|h=6 two:u32=[2, 2, 2, 2, 2, 2] | a:u32=[3, null, 1, 3, 5, null]
#|h=1 s:u32=[2] | t:u32=[3]
#|h=6 x:u32=[5, null, 3, 5, 7, null]
