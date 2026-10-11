# GroupBy.run ownership (T3.3): aggregation inputs and keys are moved out of the consumed frame when
# the column is referenced once among the key and aggregation expressions (cloned only before its last
# reference), Len over a column or literal reads nothing, and a single key skips the combine with the
# constant code and the second densify. Every expected line was worked out by hand before the first
# run (comments give the groups and the arithmetic).
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

def nul() -> D.Scalar:
  D.SNull{}

def inf() -> F32:
  F32.div(1.0, 0.0)

def nan() -> F32:
  F32.div(0.0, 0.0)

def col(n: String) -> X.Expr:
  X.Col{n}

def agg(+op: X.AggOp, +c: String) -> X.Expr:
  X.Alias{X.Agg{op, X.Col{c}}, c ++ "_" ++ X.AggOp.name(op)}

def len1() -> X.Expr:
  X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}

def gb(keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fr0}:
      fr(G.GroupBy.run(fr0, keys, aggs, True{}))

def enc.k(+dict: Bool, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f0}:
      Done{C.Frame.encode(f0, dict)}

# rows 0..7
#  k  u32 [5, 3, 5, null, 3, null, 5, 9]
#  p  u32 [1000, 5, null, 1000, 5, 700000, 1000, null]       (sparse, range 699995 < 2^20: direct codes)
#  w  u32 [4000000000, 7, 4000000000, 7, 0, null, 7, 0]      (range >= 2^20: rank codes)
#  x  f32 [1, 2, 3, 4, 6, 8, 5, 9]
#  v  u32 [1, 2, 3, 4, 5, 6, 7, 8]
#  s  str [b, a, b, null, a, c, null, b]
def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [u(5), u(3), u(5), nul(), u(3), nul(), u(5), u(9)], D.TU32{}), mk("p", [u(1000), u(5), nul(), u(1000), u(5), u(700000), u(1000), nul()], D.TU32{}), mk("w", [u(4000000000), u(7), u(4000000000), u(7), u(0), nul(), u(7), u(0)], D.TU32{}), mk("x", [f(1.0), f(2.0), f(3.0), f(4.0), f(6.0), f(8.0), f(5.0), f(9.0)], D.TF32{}), mk("v", [u(1), u(2), u(3), u(4), u(5), u(6), u(7), u(8)], D.TU32{}), mk("s", [s("b"), s("a"), s("b"), nul(), s("a"), s("c"), nul(), s("b")], D.TStr{})])

# a frame with only the key: after the key is moved the frame has no columns but keeps its height
def only() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [u(5), u(3), u(5), nul(), u(3), nul(), u(5), u(9)], D.TU32{})])

# f32 specials: g = [1,2,3,4,1,2,3,4,5,6,6,5,6]
def fz() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("g", [u(1), u(2), u(3), u(4), u(1), u(2), u(3), u(4), u(5), u(6), u(6), u(5), u(6)], D.TU32{}), mk("x", [f(nan()), f(inf()), f(inf()), f(F32.neg(0.0)), f(1.0), f(1.0), f(F32.neg(inf())), f(F32.neg(0.0)), f(3.0), f(16777216.0), f(1.0), nul(), f(1.0)], D.TF32{})])

# an all-null group in an f32 column
def zn() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("g", [u(1), u(2), u(1), u(2), u(3)], D.TU32{}), mk("x", [nul(), f(1.5), nul(), f(2.5), f(0.5)], D.TF32{})])

def empty() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [], D.TU32{}), mk("v", [], D.TU32{}), mk("x", [], D.TF32{})])

def main() -> IO(Unit):
  do IO<Unit>:
    # single numeric key with nulls: groups 5 (rows 0,2,6), 3 (1,4), null (3,5), 9 (7)
    # sum v = 11, 7, 10, 8; mean x = (1+3+5)/3, (2+6)/2, (4+8)/2, 9 = 3, 4, 6, 9; len v = 3, 2, 2, 1; len = same
    IO.print(gb([col("k")], [agg(X.Sum{}, "v"), agg(X.Mean{}, "x"), agg(X.Len{}, "v"), len1()], base()))
    # the same, aggregations listed in another order (the Len over v reads nothing; v is moved by the sum)
    IO.print(gb([col("k")], [agg(X.Len{}, "v"), len1(), agg(X.Mean{}, "x"), agg(X.Sum{}, "v")], base()))
    # sparse narrow key p: 1000 (rows 0,3,6), 5 (1,4), null (2,7), 700000 (5): sum v = 12, 7, 11, 6
    IO.print(gb([col("p")], [agg(X.Sum{}, "v"), agg(X.Len{}, "v")], base()))
    # wide key w (rank codes): 4e9 (0,2), 7 (1,3,6), 0 (4,7), null (5): sum v = 4, 13, 13, 6
    IO.print(gb([col("w")], [agg(X.Sum{}, "v"), len1()], base()))
    # Raw string key: b (0,2,7), a (1,4), null (3,6), c (5): sum v = 12, 7, 11, 6; len 3, 2, 2, 1
    IO.print(gb([col("s")], [agg(X.Sum{}, "v"), len1()], base()))
    # the same key as a Dictionary column
    IO.print(gb([col("s")], [agg(X.Sum{}, "v"), len1()], enc.k(True{}, base())))
    # multi-key (k, p): (5,1000) rows 0,6; (3,5) rows 1,4; (5,null) row 2; (null,1000) row 3;
    # (null,700000) row 5; (9,null) row 7; sum v = 8, 7, 3, 4, 6, 8; len = 2, 2, 1, 1, 1, 1
    IO.print(gb([col("k"), col("p")], [agg(X.Sum{}, "v"), len1()], base()))
    # keys in the other order: same groups, same order, columns swapped
    IO.print(gb([col("p"), col("k")], [agg(X.Sum{}, "v"), len1()], base()))
    # a wide key and a narrow one: (w, k): (4e9,5) rows 0,2; (7,3) row 1; (7,null) rows 3; (0,3) row 4;
    # (null,null) row 5; (7,5) row 6; (0,9) row 7; sum v = 4, 2, 4, 5, 6, 7, 8
    IO.print(gb([col("w"), col("k")], [agg(X.Sum{}, "v")], base()))
    # the key column also an aggregate input: group 5 sums 15, 3 sums 6, the null group 0 (all null),
    # 9 sums 9; mean 5, 3, null, 9; max the same; count 3, 2, 0, 1; first 5, 3, null, 9; last the same;
    # n_unique 1 each (null is a value)
    IO.print(gb([col("k")], [agg(X.Sum{}, "k"), agg(X.Mean{}, "k"), agg(X.Max{}, "k"), agg(X.Count{}, "k"), agg(X.First{}, "k"), agg(X.Last{}, "k"), agg(X.NUnique{}, "k")], base()))
    # a key expression reading k twice among the keys (col k, then k % 2): groups as for k alone
    IO.print(gb([col("k"), X.Alias{X.Bin{X.Mod{}, col("k"), X.Lit{D.SU32{2}}}, "kp"}], [agg(X.Sum{}, "v")], base()))
    # the key reused by a computed aggregate input and by a bare one: sum(k + 1) = 18, 8, 0, 10; sum k = 15, 6, 0, 9
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Sum{}, X.Bin{X.Add{}, col("k"), X.Lit{D.SU32{1}}}}, "k1"}, agg(X.Sum{}, "k")], base()))
    # the same column in several aggregates: x sums 9, 8, 12, 9; means 3, 4, 6, 9; max 5, 6, 8, 9; count 3, 2, 2, 1
    IO.print(gb([col("k")], [agg(X.Sum{}, "x"), agg(X.Mean{}, "x"), agg(X.Max{}, "x"), agg(X.Count{}, "x")], base()))
    # a computed input before / after the bare ones: sum(x * 2) = 18, 16, 24, 18
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Sum{}, X.Bin{X.Mul{}, col("x"), X.Lit{D.SF32{2.0}}}}, "x2"}, agg(X.Sum{}, "x")], base()))
    IO.print(gb([col("k")], [agg(X.Sum{}, "x"), X.Alias{X.Agg{X.Sum{}, X.Bin{X.Mul{}, col("x"), X.Lit{D.SF32{2.0}}}}, "x2"}], base()))
    # a frame holding only the key: the height survives the move; len = 3, 2, 2, 1
    IO.print(gb([col("k")], [len1(), agg(X.Len{}, "k")], only()))
    # f32 specials, per group in row order: g1 {nan, 1} -> nan; g2 {inf, 1} -> inf; g3 {inf, -inf} -> nan;
    # g4 {-0, -0} -> 0 (0.0 + -0.0 = 0.0); g5 {3, null} -> 3; g6 {2^24, 1, 1} -> 16777218 (Neumaier);
    # means: nan, inf, nan, 0, 3, 16777218 / 3 = 5592406
    IO.print(gb([col("g")], [agg(X.Sum{}, "x"), agg(X.Mean{}, "x"), agg(X.Count{}, "x")], fz()))
    # an all-null f32 group: g1 {null, null} sum 0, mean null, min null, max null, count 0;
    # g2 {1.5, 2.5} -> 4, 2, 1.5, 2.5, 2; g3 {0.5} -> 0.5, 0.5, 0.5, 0.5, 1
    IO.print(gb([col("g")], [agg(X.Sum{}, "x"), agg(X.Mean{}, "x"), agg(X.Min{}, "x"), agg(X.Max{}, "x"), agg(X.Count{}, "x")], zn()))
    # an empty frame: typed empty columns, no group
    IO.print(gb([col("k")], [agg(X.Sum{}, "v"), agg(X.Mean{}, "x"), agg(X.Len{}, "v"), len1()], empty()))
    IO.print(gb([col("k"), col("v")], [agg(X.Sum{}, "x")], empty()))
    # errors precede any move: unknown aggregate input, duplicate output name (key k, alias k)
    IO.print(gb([col("k")], [agg(X.Sum{}, "zz")], base()))
    IO.print(gb([col("k")], [X.Alias{X.Agg{X.Sum{}, col("v")}, "k"}], base()))
#|h=4 k:u32=[5, 3, null, 9] | v_sum:u32=[11, 7, 10, 8] | x_mean:f32=[3, 4, 6, 9] | v_len:u32=[3, 2, 2, 1] | len:u32=[3, 2, 2, 1]
#|h=4 k:u32=[5, 3, null, 9] | v_len:u32=[3, 2, 2, 1] | len:u32=[3, 2, 2, 1] | x_mean:f32=[3, 4, 6, 9] | v_sum:u32=[11, 7, 10, 8]
#|h=4 p:u32=[1000, 5, null, 700000] | v_sum:u32=[12, 7, 11, 6] | v_len:u32=[3, 2, 2, 1]
#|h=4 w:u32=[4000000000, 7, 0, null] | v_sum:u32=[4, 13, 13, 6] | len:u32=[2, 3, 2, 1]
#|h=4 s:str=[b, a, null, c] | v_sum:u32=[12, 7, 11, 6] | len:u32=[3, 2, 2, 1]
#|h=4 s:str=[b, a, null, c] | v_sum:u32=[12, 7, 11, 6] | len:u32=[3, 2, 2, 1]
#|h=6 k:u32=[5, 3, 5, null, null, 9] | p:u32=[1000, 5, null, 1000, 700000, null] | v_sum:u32=[8, 7, 3, 4, 6, 8] | len:u32=[2, 2, 1, 1, 1, 1]
#|h=6 p:u32=[1000, 5, null, 1000, 700000, null] | k:u32=[5, 3, 5, null, null, 9] | v_sum:u32=[8, 7, 3, 4, 6, 8] | len:u32=[2, 2, 1, 1, 1, 1]
#|h=7 w:u32=[4000000000, 7, 7, 0, null, 7, 0] | k:u32=[5, 3, null, 3, null, 5, 9] | v_sum:u32=[4, 2, 4, 5, 6, 7, 8]
#|h=4 k:u32=[5, 3, null, 9] | k_sum:u32=[15, 6, 0, 9] | k_mean:f32=[5, 3, null, 9] | k_max:u32=[5, 3, null, 9] | k_count:u32=[3, 2, 0, 1] | k_first:u32=[5, 3, null, 9] | k_last:u32=[5, 3, null, 9] | k_n_unique:u32=[1, 1, 1, 1]
#|h=4 k:u32=[5, 3, null, 9] | kp:u32=[1, 1, null, 1] | v_sum:u32=[11, 7, 10, 8]
#|h=4 k:u32=[5, 3, null, 9] | k1:u32=[18, 8, 0, 10] | k_sum:u32=[15, 6, 0, 9]
#|h=4 k:u32=[5, 3, null, 9] | x_sum:f32=[9, 8, 12, 9] | x_mean:f32=[3, 4, 6, 9] | x_max:f32=[5, 6, 8, 9] | x_count:u32=[3, 2, 2, 1]
#|h=4 k:u32=[5, 3, null, 9] | x2:f32=[18, 16, 24, 18] | x_sum:f32=[9, 8, 12, 9]
#|h=4 k:u32=[5, 3, null, 9] | x_sum:f32=[9, 8, 12, 9] | x2:f32=[18, 16, 24, 18]
#|h=4 k:u32=[5, 3, null, 9] | len:u32=[3, 2, 2, 1] | k_len:u32=[3, 2, 2, 1]
#|h=6 g:u32=[1, 2, 3, 4, 5, 6] | x_sum:f32=[nan, inf, nan, 0, 3, 16777218] | x_mean:f32=[nan, inf, nan, 0, 3, 5592406] | x_count:u32=[2, 2, 2, 2, 1, 3]
#|h=3 g:u32=[1, 2, 3] | x_sum:f32=[0, 4, 0.5] | x_mean:f32=[null, 2, 0.5] | x_min:f32=[null, 1.5, 0.5] | x_max:f32=[null, 2.5, 0.5] | x_count:u32=[0, 2, 1]
#|h=0 k:u32=[] | v_sum:u32=[] | x_mean:f32=[] | v_len:u32=[] | len:u32=[]
#|h=0 k:u32=[] | v:u32=[] | x_sum:f32=[]
#|error: ColumnNotFound: zz
#|error: DuplicateColumn: k
