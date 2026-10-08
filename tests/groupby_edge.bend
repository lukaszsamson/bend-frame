# GroupBy.run edge cases: multi-key with nulls, f32 keys (NaN, -0.0), i32 and
# bool keys, wide-range keys (rank / pair-rank paths), expression keys,
# empty frame, one row, maintain_order = False, errors.
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

def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("b"), s("a"), s("b"), nul(), s("a"), nul(), s("b"), s("a")], D.TStr{}), mk("t", [bo(True{}), bo(True{}), bo(False{}), nul(), bo(True{}), nul(), bo(True{}), nul()], D.TBool{}), mk("x", [f(0.0), f(F32.div(0.0, 0.0)), f(F32.neg(0.0)), f(1.5), f(F32.div(0.0, 0.0)), nul(), f(1.5), nul()], D.TF32{}), mk("n", [ineg(3), ipos(3), ineg(3), nul(), ipos(0), ineg(2147483648), ipos(3), nul()], D.TI32{}), mk("w", [u(4000000000), u(7), u(4000000000), u(7), u(0), nul(), u(7), u(0)], D.TU32{}), mk("r", [u(1000000), u(0), u(1000000), u(0), u(0), u(5), u(1000000), u(0)], D.TU32{}), mk("v", [u(1), u(2), u(3), u(4), u(5), u(6), u(7), u(8)], D.TU32{})])

def one() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("q")], D.TStr{}), mk("v", [f(1.5)], D.TF32{})])

def empty() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [], D.TStr{}), mk("v", [], D.TF32{})])

def rows() -> List<&2, X.Expr>:
  [X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}, X.Alias{X.Agg{X.Sum{}, col("v")}, "sum"}, X.Alias{X.Agg{X.First{}, col("v")}, "first"}]

def gbu.k(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr0}:
      G.GroupBy.run(fr0, [col("k")], [X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}], False{})

def gbu(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  gbu.k(r)

def main() -> IO(Unit):
  do IO<Unit>:
    # two keys: (str, bool) with nulls in both
    IO.print(gb([col("k"), col("t")], rows(), base()))
    # f32 keys: -0.0 groups with 0.0, NaNs form one group, nulls one group
    IO.print(gb([col("x")], rows(), base()))
    # i32 keys incl. MIN, then bool alone
    IO.print(gb([col("n")], rows(), base()))
    IO.print(gb([col("t")], rows(), base()))
    # a key range wider than 2^20 (rank path), and two wide keys (pair rank)
    IO.print(gb([col("w")], rows(), base()))
    IO.print(gb([col("r"), col("w")], rows(), base()))
    # an expression key (named after its column) and an aliased one
    IO.print(gb([X.Bin{X.Mod{}, col("v"), X.Lit{D.SU32{3}}}, X.Alias{X.Bin{X.Gt{}, col("v"), X.Lit{D.SU32{4}}}, "big"}], [X.Alias{X.Agg{X.NUnique{}, col("k")}, "nk"}], base()))
    # n_unique of a multi-valued column per group (null counted once)
    IO.print(gb([col("t")], [X.Alias{X.Agg{X.NUnique{}, col("k")}, "nk"}, X.Alias{X.Agg{X.NUnique{}, col("x")}, "nx"}, X.Alias{X.Agg{X.NUnique{}, col("w")}, "nw"}], base()))
    # one row; no rows (typed empty output)
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Mean{}, col("v")}, "m"}, X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}], one()))
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Mean{}, col("v")}, "m"}, X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}], empty()))
    # maintain_order = False{} (v1: still first appearance; not part of the contract)
    IO.print(fr(gbu(base())))
    # errors: unknown column, type error, no keys, aggregated key, non-aggregation,
    # nested aggregation, duplicate output name
    IO.print(gb([col("zz")], rows(), base()))
    IO.print(gb([col("k")], [X.Agg{X.Sum{}, col("k")}], base()))
    IO.print(gb([], rows(), base()))
    IO.print(gb([X.Agg{X.Sum{}, col("v")}], rows(), base()))
    IO.print(gb([col("k")], [col("v")], base()))
    IO.print(gb([col("k")], [X.Agg{X.Sum{}, X.Agg{X.Sum{}, col("v")}}], base()))
    IO.print(gb([col("k")], [X.Agg{X.Sum{}, col("k")}], base()))
    IO.print(gb([col("k")], [X.Agg{X.Max{}, col("k")}], base()))
#|h=5 k:str=[b, a, b, null, a] | t:bool=[true, true, false, null, null] | len:u32=[2, 2, 1, 2, 1] | sum:u32=[8, 7, 3, 10, 8] | first:u32=[1, 2, 3, 4, 8]
#|h=4 x:f32=[0, nan, 1.5, null] | len:u32=[2, 2, 2, 2] | sum:u32=[4, 7, 11, 14] | first:u32=[1, 2, 4, 6]
#|h=5 n:i32=[-3, 3, null, 0, -2147483648] | len:u32=[2, 2, 2, 1, 1] | sum:u32=[4, 9, 12, 5, 6] | first:u32=[1, 2, 4, 5, 6]
#|h=3 t:bool=[true, false, null] | len:u32=[4, 1, 3] | sum:u32=[15, 3, 18] | first:u32=[1, 3, 4]
#|h=4 w:u32=[4000000000, 7, 0, null] | len:u32=[2, 3, 2, 1] | sum:u32=[4, 13, 13, 6] | first:u32=[1, 2, 5, 6]
#|h=5 r:u32=[1000000, 0, 0, 5, 1000000] | w:u32=[4000000000, 7, 0, null, 7] | len:u32=[2, 2, 2, 1, 1] | sum:u32=[4, 6, 13, 6, 7] | first:u32=[1, 2, 5, 6, 7]
#|h=6 v:u32=[1, 2, 0, 2, 0, 1] | big:bool=[false, false, false, true, true, true] | nk:u32=[2, 1, 1, 1, 1, 1]
#|h=3 t:bool=[true, false, null] | nk:u32=[2, 1, 2] | nx:u32=[3, 1, 2] | nw:u32=[3, 1, 3]
#|h=1 k:str=[q] | m:f32=[1.5] | len:u32=[1]
#|h=0 k:str=[] | m:f32=[] | len:u32=[]
#|h=3 k:str=[b, a, null] | len:u32=[3, 3, 2]
#|error: ColumnNotFound: zz
#|error: TypeMismatch in sum: expected numeric, got str
#|error: InvalidOperation: group_by needs at least one key
#|error: InvalidOperation: group_by key is an aggregation: col("v").sum()
#|error: InvalidOperation: agg expects an aggregation: col("v")
#|error: InvalidOperation: nested aggregation in agg: col("v").sum().sum()
#|error: TypeMismatch in sum: expected numeric, got str
#|error: DuplicateColumn: k
