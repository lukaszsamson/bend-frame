# GroupBy.run: p11's groups in first-appearance order (maintain_order), a null
# key group, every AggOp over f32/u32/i32/str/bool values with nulls.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/groupby.bend as G

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

def cs(c: C.Column) -> String:
  cs.a(C.Column.dtype(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs(c)) <> ncols(t)

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

def u(v: U32) -> D.Scalar:
  D.SU32{v}

def s(v: String) -> D.Scalar:
  D.SStr{v}

def f(v: F32) -> D.Scalar:
  D.SF32{v}

def ineg(v: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{v})}

def ipos(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def bo(b: Bool) -> D.Scalar:
  D.SBool{b}

def nul() -> D.Scalar:
  D.SNull{}

def col(n: String) -> X.Expr:
  X.Col{n}

def agg(+op: X.AggOp, +c: String) -> X.Expr:
  X.Alias{X.Agg{op, X.Col{c}}, c ++ "_" ++ X.AggOp.name(op)}

def every(+c: String) -> List<&2, X.Expr>:
  [agg(X.Sum{}, c), agg(X.Mean{}, c), agg(X.Min{}, c), agg(X.Max{}, c), agg(X.Count{}, c), agg(X.Len{}, c), agg(X.First{}, c), agg(X.Last{}, c), agg(X.NUnique{}, c)]

def nonnum(+c: String) -> List<&2, X.Expr>:
  [agg(X.Min{}, c), agg(X.Max{}, c), agg(X.Count{}, c), agg(X.First{}, c), agg(X.Last{}, c), agg(X.NUnique{}, c)]

def gb(keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fr0}:
      fr(G.GroupBy.run(fr0, keys, aggs, True{}))

# p11's rows (k, v) plus a null key, nullable values of every dtype
def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("b"), s("a"), s("b"), s("c"), s("a"), nul(), s("b"), nul()], D.TStr{}), mk("v", [f(1.0), f(2.0), f(3.0), f(4.0), f(5.0), f(6.0), nul(), f(8.0)], D.TF32{}), mk("u", [nul(), u(4), u(3), u(3), u(5), u(6), u(3), nul()], D.TU32{}), mk("i", [ineg(1), ipos(4), nul(), ipos(3), ineg(5), ipos(6), ineg(7), ipos(6)], D.TI32{}), mk("s", [s("x"), nul(), s("y"), s("x"), s("w"), s("z"), s("a"), nul()], D.TStr{}), mk("b", [bo(True{}), bo(False{}), nul(), bo(True{}), bo(True{}), bo(False{}), bo(False{}), nul()], D.TBool{})])

def main() -> IO(Unit):
  do IO<Unit>:
    # p11: count / sum per key, first-appearance order (b, a, c, then null)
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Count{}, col("v")}, "n"}, X.Alias{X.Agg{X.Sum{}, col("v")}, "sum"}], base()))
    # every aggregation per group, per value dtype
    IO.print(gb([col("k")], every("v"), base()))
    IO.print(gb([col("k")], every("u"), base()))
    IO.print(gb([col("k")], every("i"), base()))
    IO.print(gb([col("k")], nonnum("s"), base()))
    IO.print(gb([col("k")], nonnum("b"), base()))
    # pl.len() and a literal aggregation (sum(lit 2) = 2 per group, Polars)
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}, X.Alias{X.Agg{X.Sum{}, X.Lit{D.SU32{2}}}, "two"}], base()))
#|h=4 k:str=[b, a, c, null] | n:u32=[2, 2, 1, 2] | sum:f32=[4, 7, 4, 14]
#|h=4 k:str=[b, a, c, null] | v_sum:f32=[4, 7, 4, 14] | v_mean:f32=[2, 3.5, 4, 7] | v_min:f32=[1, 2, 4, 6] | v_max:f32=[3, 5, 4, 8] | v_count:u32=[2, 2, 1, 2] | v_len:u32=[3, 2, 1, 2] | v_first:f32=[1, 2, 4, 6] | v_last:f32=[null, 5, 4, 8] | v_n_unique:u32=[3, 2, 1, 2]
#|h=4 k:str=[b, a, c, null] | u_sum:u32=[6, 9, 3, 6] | u_mean:f32=[3, 4.5, 3, 6] | u_min:u32=[3, 4, 3, 6] | u_max:u32=[3, 5, 3, 6] | u_count:u32=[2, 2, 1, 1] | u_len:u32=[3, 2, 1, 2] | u_first:u32=[null, 4, 3, 6] | u_last:u32=[3, 5, 3, null] | u_n_unique:u32=[2, 2, 1, 2]
#|h=4 k:str=[b, a, c, null] | i_sum:i32=[-8, -1, 3, 12] | i_mean:f32=[-4, -0.5, 3, 6] | i_min:i32=[-7, -5, 3, 6] | i_max:i32=[-1, 4, 3, 6] | i_count:u32=[2, 2, 1, 2] | i_len:u32=[3, 2, 1, 2] | i_first:i32=[-1, 4, 3, 6] | i_last:i32=[-7, -5, 3, 6] | i_n_unique:u32=[3, 2, 1, 1]
#|h=4 k:str=[b, a, c, null] | s_min:str=[a, w, x, z] | s_max:str=[y, w, x, z] | s_count:u32=[3, 1, 1, 1] | s_first:str=[x, null, x, z] | s_last:str=[a, w, x, null] | s_n_unique:u32=[3, 2, 1, 2]
#|h=4 k:str=[b, a, c, null] | b_min:bool=[false, false, true, false] | b_max:bool=[true, true, true, false] | b_count:u32=[2, 2, 1, 1] | b_first:bool=[true, false, true, false] | b_last:bool=[false, true, true, null] | b_n_unique:u32=[3, 2, 1, 2]
#|h=4 k:str=[b, a, c, null] | len:u32=[3, 2, 1, 2] | two:u32=[2, 2, 2, 2]
