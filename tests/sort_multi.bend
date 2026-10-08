# Sort.frame: two keys (one descending), nulls first by default, stability
# witnessed by the row-id column `i`; nulls_last; Sort.argsort; errors.
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

def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [u(2), nul(), u(1), u(2), nul(), u(1), u(3), u(2)], D.TU32{}), mk("b", [s("x"), s("y"), s("x"), s("w"), s("y"), s("z"), s("x"), s("x")], D.TStr{}), mk("i", [u(0), u(1), u(2), u(3), u(4), u(5), u(6), u(7)], D.TU32{})])

def key(n: String, desc: Bool, nl: Bool) -> SO.SortKey:
  SO.SortKey{n, desc, nl}

def sorted(ks: List<&2, SO.SortKey>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fr(SO.Sort.frame(f, ks))

def perm.k(r: C.Frame & E.ResT(Array<U32>)) -> String:
  (f, rp) = r
  match rp:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{p}:
      List.show(~&1, ~U32, ~(x => U32.show(x)), Array.to_list(~U32, p))

def perm(ks: List<&2, SO.SortKey>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      perm.k(SO.Sort.argsort(f, ks))

def main() -> IO(Unit):
  do IO<Unit>:
    # a descending (nulls still first), then b ascending; ties keep input order
    IO.print(sorted([key("a", True{}, False{}), key("b", False{}, False{})], base()))
    # b ascending, then a ascending with nulls last
    IO.print(sorted([key("b", False{}, False{}), key("a", False{}, True{})], base()))
    # one key: equal keys keep input order (i increases within each a)
    IO.print(sorted([key("a", False{}, False{})], base()))
    IO.print(sorted([key("a", False{}, True{})], base()))
    # the permutation itself (2^3 slots)
    IO.print(perm([key("a", True{}, True{})], base()))
    # no keys: unchanged; an unknown key: ColumnNotFound
    IO.print(sorted([], base()))
    IO.print(sorted([key("a", False{}, False{}), key("zz", False{}, False{})], base()))
#|h=8 a:u32=[null, null, 3, 2, 2, 2, 1, 1] | b:str=[y, y, x, w, x, x, x, z] | i:u32=[1, 4, 6, 3, 0, 7, 2, 5]
#|h=8 a:u32=[2, 1, 2, 2, 3, null, null, 1] | b:str=[w, x, x, x, x, y, y, z] | i:u32=[3, 2, 0, 7, 6, 1, 4, 5]
#|h=8 a:u32=[null, null, 1, 1, 2, 2, 2, 3] | b:str=[y, y, x, z, x, w, x, x] | i:u32=[1, 4, 2, 5, 0, 3, 7, 6]
#|h=8 a:u32=[1, 1, 2, 2, 2, 3, null, null] | b:str=[x, z, x, w, x, x, y, y] | i:u32=[2, 5, 0, 3, 7, 6, 1, 4]
#|[6, 0, 3, 7, 2, 5, 1, 4]
#|h=8 a:u32=[2, null, 1, 2, null, 1, 3, 2] | b:str=[x, y, x, w, y, z, x, x] | i:u32=[0, 1, 2, 3, 4, 5, 6, 7]
#|error: ColumnNotFound: zz
