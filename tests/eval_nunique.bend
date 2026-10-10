# n_unique over word / F32 / Bool columns (DESIGN.md 15.4, 15.5.2): a global reduction counts the
# distinct valid values plus one when any row is null; F32 by the single total order (every NaN one
# value, the greatest; -0.0 == 0.0). The numeric path radix-sorts the order words and counts runs
# in one flat loop (Eval.nu.words; Bool by presence bits). Each count is derived by hand from the
# generator, not from the code under test.
#   u   8192 rows, row i holds (i mod 4096) * 2654435761 (an odd multiplier: injective mod 2^32)
#       -> 4096 distinct, every value twice
#   un  the same words, null on the even rows (odd rows keep their value; 4096 is even, so the odd
#       rows carry exactly the 2048 odd residues) -> 2048 + 1 for the null = 2049
#   iv  the same words as an I32 column -> 4096
#   fv  to_f32(i mod 4096): 4096 distinct values; row 4096 is -0.0 (row 0's 0.0 is the same value),
#       row 5 is NaN (5.0 stays at row 4101), row 2 is -NaN (2.0 stays at row 4098)
#       -> 4096 + 1 (every NaN is one value) = 4097
# The small frame:
#   f1  [1, NaN, -0, 0, -NaN, 2, 1, null, inf, -inf] -> {1, NaN, 0, 2, inf, -inf} + null = 7
#   f2  [0, -0, 0] -> 1;  f3 all null -> 1
#   b1  all true -> 1;  b2 [false, null, false] -> 2;  b3 [false, true, false] -> 2
#   u1  {2^32-1, 0, 2^32-1, 2^31, 0} -> 3;  u2 one row -> 1
#   i1  {-1, 1, -1, i32 min, i32 max} -> 4
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/eval.bend as V

def nu(+c: String) -> X.Expr:
  X.Alias{X.Agg{X.NUnique{}, X.Col{c}}, c}

def odd(+i: U32) -> U32:
  U32.and(i, 1)

def word(+i: U32) -> U32:
  U32.mul(U32.mod(i, 4096), 2654435761)

# the null slot of `un` holds the dtype default (0)
def wordn(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(odd(i), 1), word(i), 0)

def nan() -> F32:
  F32.div(0.0, 0.0)

def fcell(+i: U32) -> F32:
  +v = U32.to_f32(U32.mod(i, 4096))
  Bool.pick(F32, U32.is_eq(i, 5), nan(), Bool.pick(F32, U32.is_eq(i, 2), F32.neg(nan()), Bool.pick(F32, U32.is_eq(i, 4096), F32.neg(0.0), v)))

def big() -> C.Frame:
  C.Frame{8192, [C.Named{"u", C.CU32{8192, 13n, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), 8192, 13n, K.Kernel.iota(8192, 13n), 0)}}, C.Named{"un", C.CU32{8192, 13n, C.Mask{K.Kernel.map(~U32, ~U32, ~(i => odd(i)), 8192, 13n, K.Kernel.iota(8192, 13n), 0)}, K.Kernel.map(~U32, ~U32, ~(i => wordn(i)), 8192, 13n, K.Kernel.iota(8192, 13n), 0)}}, C.Named{"iv", C.CI32{8192, 13n, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), 8192, 13n, K.Kernel.iota(8192, 13n), 0)}}, C.Named{"fv", C.CF32{8192, 13n, C.AllValid{}, K.Kernel.map(~U32, ~F32, ~(i => fcell(i)), 8192, 13n, K.Kernel.iota(8192, 13n), 0.0)}}]}

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def sf(x: F32) -> D.Scalar:
  D.SF32{x}

def si(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def su(v: U32) -> D.Scalar:
  D.SU32{v}

def sb(b: Bool) -> D.Scalar:
  D.SBool{b}

def cs.k(r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  List.show(~&2, ~D.Scalar, ~(s => D.Scalar.show(s)), xs)

def cs(c: C.Column) -> String:
  cs.k(C.Column.to_scalars(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ "=" ++ cs(c)) <> ncols(t)

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

# one column per frame (the columns have different heights)
def one.k(c: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fr(V.Eval.select(f, [nu(c)]))

def one(+c: String, xs: List<&2, D.Scalar>, +t: D.DType) -> String:
  one.k(c, C.Frame.from_columns([mk(c, xs, t)]))

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(fr(V.Eval.select(big(), [nu("u"), nu("un"), nu("iv"), nu("fv")])))
    IO.print(one("f1", [sf(1.0), sf(nan()), sf(F32.neg(0.0)), sf(0.0), sf(F32.neg(nan())), sf(2.0), sf(1.0), D.SNull{}, sf(F32.div(1.0, 0.0)), sf(F32.div(F32.neg(1.0), 0.0))], D.TF32{}))
    IO.print(one("f2", [sf(0.0), sf(F32.neg(0.0)), sf(0.0)], D.TF32{}))
    IO.print(one("f3", [D.SNull{}, D.SNull{}, D.SNull{}], D.TF32{}))
    IO.print(one("b1", [sb(True{}), sb(True{}), sb(True{})], D.TBool{}))
    IO.print(one("b2", [sb(False{}), D.SNull{}, sb(False{})], D.TBool{}))
    IO.print(one("b3", [sb(False{}), sb(True{}), sb(False{})], D.TBool{}))
    IO.print(one("u1", [su(4294967295), su(0), su(4294967295), su(2147483648), su(0)], D.TU32{}))
    IO.print(one("u2", [su(9)], D.TU32{}))
    IO.print(one("i1", [si(4294967295), si(1), si(4294967295), si(2147483648), si(2147483647)], D.TI32{}))
    # an empty frame (a filter keeping nothing): n_unique is 0 for every dtype
    IO.print(on.k(f => fr(V.Eval.select(f, [nu("u"), nu("un"), nu("iv"), nu("fv")])), V.Eval.filter(big(), X.Bin{X.Gt{}, X.Col{"u"}, X.Lit{D.SU32{4294967295}}})))
#|h=1 u=[4096] | un=[2049] | iv=[4096] | fv=[4097]
#|h=1 f1=[7]
#|h=1 f2=[1]
#|h=1 f3=[1]
#|h=1 b1=[1]
#|h=1 b2=[2]
#|h=1 b3=[2]
#|h=1 u1=[3]
#|h=1 u2=[1]
#|h=1 i1=[4]
#|h=1 u=[0] | un=[0] | iv=[0] | fv=[0]
