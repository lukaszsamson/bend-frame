# Sort.frame edge cases: f32 NaN/-0.0/inf ordering (Polars: NaN largest),
# i32 signs, bools, string order, one row, no rows.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/sort.bend as SO

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

def nul() -> D.Scalar:
  D.SNull{}

def f(v: F32) -> D.Scalar:
  D.SF32{v}

def ineg(v: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{v})}

def ipos(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def bo(b: Bool) -> D.Scalar:
  D.SBool{b}

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

# f32 with NaN, -0.0, +-inf and a null; i32 negatives; bools; strings with
# prefixes, the empty string and non-ASCII
def edge() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("x", [f(1.0), f(nan()), f(F32.neg(0.0)), f(0.0), nul(), f(F32.neg(inf())), f(F32.neg(2.5)), f(inf())], D.TF32{}), mk("n", [ipos(5), ineg(7), ipos(0), ineg(2147483648), ipos(2147483647), ineg(1), nul(), ipos(5)], D.TI32{}), mk("b", [bo(True{}), bo(False{}), nul(), bo(True{}), bo(False{}), bo(True{}), bo(False{}), nul()], D.TBool{}), mk("s", [s("ab"), s(""), s("abc"), s("b"), s("\u{e9}"), s("a"), nul(), s("ab")], D.TStr{}), mk("i", [u(0), u(1), u(2), u(3), u(4), u(5), u(6), u(7)], D.TU32{})])

def one() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("x", [f(1.5)], D.TF32{}), mk("s", [s("q")], D.TStr{})])

def empty() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("x", [], D.TF32{}), mk("s", [], D.TStr{})])

def key(n: String, desc: Bool, nl: Bool) -> SO.SortKey:
  SO.SortKey{n, desc, nl}

def sorted(ks: List<&2, SO.SortKey>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fr(SO.Sort.frame(f, ks))

def main() -> IO(Unit):
  do IO<Unit>:
    # f32: null first, NaN largest, -0.0 ties with 0.0 (input order kept)
    IO.print(sorted([key("x", False{}, False{})], edge()))
    IO.print(sorted([key("x", True{}, False{})], edge()))
    # i32 signed order, nulls last
    IO.print(sorted([key("n", False{}, True{})], edge()))
    # bool descending then i32 descending
    IO.print(sorted([key("b", True{}, False{}), key("n", True{}, False{})], edge()))
    # strings in code-point order: "" < a < ab < abc < b < e-acute
    IO.print(sorted([key("s", False{}, True{})], edge()))
    IO.print(sorted([key("s", True{}, False{}), key("i", True{}, False{})], edge()))
    # one row, no rows
    IO.print(sorted([key("x", True{}, False{}), key("s", False{}, False{})], one()))
    IO.print(sorted([key("x", False{}, False{}), key("s", True{}, True{})], empty()))
#|h=8 x:f32=[null, -inf, -2.5, -0, 0, 1, inf, nan] | n:i32=[2147483647, -1, null, 0, -2147483648, 5, 5, -7] | b:bool=[false, true, false, null, true, true, null, false] | s:str=[é, a, null, abc, b, ab, ab, ] | i:u32=[4, 5, 6, 2, 3, 0, 7, 1]
#|h=8 x:f32=[null, nan, inf, 1, -0, 0, -2.5, -inf] | n:i32=[2147483647, -7, 5, 5, 0, -2147483648, null, -1] | b:bool=[false, false, null, true, null, true, false, true] | s:str=[é, , ab, ab, abc, b, null, a] | i:u32=[4, 1, 7, 0, 2, 3, 6, 5]
#|h=8 x:f32=[0, nan, -inf, -0, 1, inf, null, -2.5] | n:i32=[-2147483648, -7, -1, 0, 5, 5, 2147483647, null] | b:bool=[true, false, true, null, true, null, false, false] | s:str=[b, , a, abc, ab, ab, é, null] | i:u32=[3, 1, 5, 2, 0, 7, 4, 6]
#|h=8 x:f32=[inf, -0, 1, -inf, 0, -2.5, null, nan] | n:i32=[5, 0, 5, -1, -2147483648, null, 2147483647, -7] | b:bool=[null, null, true, true, true, false, false, false] | s:str=[ab, abc, ab, a, b, null, é, ] | i:u32=[7, 2, 0, 5, 3, 6, 4, 1]
#|h=8 x:f32=[nan, -inf, 1, inf, -0, 0, null, -2.5] | n:i32=[-7, -1, 5, 5, 0, -2147483648, 2147483647, null] | b:bool=[false, true, true, null, null, true, false, false] | s:str=[, a, ab, ab, abc, b, é, null] | i:u32=[1, 5, 0, 7, 2, 3, 4, 6]
#|h=8 x:f32=[-2.5, null, 0, -0, inf, 1, -inf, nan] | n:i32=[null, 2147483647, -2147483648, 0, 5, 5, -1, -7] | b:bool=[false, false, true, null, null, true, true, false] | s:str=[null, é, b, abc, ab, ab, a, ] | i:u32=[6, 4, 3, 2, 7, 0, 5, 1]
#|h=1 x:f32=[1.5] | s:str=[q]
#|h=0 x:f32=[] | s:str=[]
