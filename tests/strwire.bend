# W2.3: group_by / unique / sort / n_unique / min / max over Raw string keys, now coded by the flat
# coder (src/hcode.bend) and ranked by the rank stage (src/ranks.bend), and over the same column as a
# Dictionary. Real FNV-1a 32-bit collisions (k32004 / k261338: ST.Str.hash is equal, tests/hcode_unit),
# "" as a value, null rows (whose slot holds "", the v0.1 invariant), "" only on null rows, an all-null
# column and an empty frame. Every expected line was worked out by hand before the first run (comments).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C

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

def enc(+dict: Bool, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f0}:
      Done{DF.encode_strings(f0, dict)}

def then(r: E.ResT(C.Frame), k: C.Frame -> E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f0}:
      k(f0)

# rows 0..9
#  s  str [k32004, k261338, null, "", k32004, null, k261338, b, "", ab]   (k32004 / k261338 collide)
#  v  u32 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def base(+dict: Bool) -> E.ResT(C.Frame):
  enc(dict, DF.from_columns([mk("s", [s("k32004"), s("k261338"), nul(), s(""), s("k32004"), nul(), s("k261338"), s("b"), s(""), s("ab")], D.TStr{}), mk("v", [u(1), u(2), u(3), u(4), u(5), u(6), u(7), u(8), u(9), u(10)], D.TU32{})]))

# "" only on null rows: t [null, x, null, y, x]
def onlynull(+dict: Bool) -> E.ResT(C.Frame):
  enc(dict, DF.from_columns([mk("t", [nul(), s("x"), nul(), s("y"), s("x")], D.TStr{}), mk("v", [u(1), u(2), u(3), u(4), u(5)], D.TU32{})]))

def allnull(+dict: Bool) -> E.ResT(C.Frame):
  enc(dict, DF.from_columns([mk("t", [nul(), nul(), nul()], D.TStr{}), mk("v", [u(1), u(2), u(3)], D.TU32{})]))

def empty(+dict: Bool) -> E.ResT(C.Frame):
  enc(dict, DF.from_columns([mk("t", [], D.TStr{}), mk("v", [], D.TU32{})]))

def gb(+k: String, r: E.ResT(C.Frame)) -> String:
  fr(then(r, f => DF.group_by(f, [DF.col(k)], [DF.alias(DF.sum(DF.col("v")), "v_sum"), DF.alias(DF.len(), "len")])))

def un(+k: String, r: E.ResT(C.Frame)) -> String:
  fr(then(r, f => DF.unique(f, [k])))

def so(+k: String, +desc: Bool, +nl: Bool, r: E.ResT(C.Frame)) -> String:
  fr(then(r, f => DF.sort(f, [DF.sort_key(k, desc, nl)])))

def nu(+k: String, r: E.ResT(C.Frame)) -> String:
  fr(then(r, f => DF.select(f, [DF.n_unique(DF.col(k)), DF.alias(DF.min(DF.col(k)), "mn"), DF.alias(DF.max(DF.col(k)), "mx")])))

def cases(+dict: Bool) -> List<&2, String>:
  [gb("s", base(dict)), un("s", base(dict)), so("s", False{}, False{}, base(dict)), so("s", True{}, True{}, base(dict)), nu("s", base(dict)),
   gb("t", onlynull(dict)), un("t", onlynull(dict)), nu("t", onlynull(dict)), so("t", False{}, True{}, onlynull(dict)),
   gb("t", allnull(dict)), nu("t", allnull(dict)), so("t", True{}, False{}, allnull(dict)),
   gb("t", empty(dict)), un("t", empty(dict)), nu("t", empty(dict)), so("t", False{}, False{}, empty(dict))]

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(String.join(cases(False{}), "\n"))
    IO.print("-- dictionary")
    IO.print(String.join(cases(True{}), "\n"))
# base, group_by s: codes by first appearance (null rows hold "", coded at row 2, then zeroed):
#   k32004 rows 0,4 (sum 6), k261338 1,6 (9), null 2,5 (9), "" 3,8 (13), b 7 (8), ab 9 (10)
# unique s: rows 0, 1, 2, 3, 7, 9
# sort s asc, nulls first: nulls 2,5; "" 3,8; ab 9; b 7; k261338 1,6 (2 < 3); k32004 0,4
# sort s desc, nulls last: k32004 0,4; k261338 1,6; b 7; ab 9; "" 3,8; nulls 2,5 (ties stable)
# n_unique: 5 valid distinct (k32004, k261338, "", b, ab) + 1 null = 6; min "", max k32004
# onlynull: groups null (0,2: sum 4, len 2), x (1,4: 7, 2), y (3: 4, 1); unique rows 0, 1, 3;
#   n_unique 2 + 1 = 3 (the "" of the null slots is not a value); min x, max y;
#   sort asc nulls last: x 1,4; y 3; nulls 0,2
# allnull: one null group (sum 6, len 3); n_unique 1, min / max null; sort: rows as they are
# empty: no rows; n_unique 0, min / max null
#|h=6 s:str=[k32004, k261338, null, , b, ab] | v_sum:u32=[6, 9, 9, 13, 8, 10] | len:u32=[2, 2, 2, 2, 1, 1]
#|h=6 s:str=[k32004, k261338, null, , b, ab] | v:u32=[1, 2, 3, 4, 8, 10]
#|h=10 s:str=[null, null, , , ab, b, k261338, k261338, k32004, k32004] | v:u32=[3, 6, 4, 9, 10, 8, 2, 7, 1, 5]
#|h=10 s:str=[k32004, k32004, k261338, k261338, b, ab, , , null, null] | v:u32=[1, 5, 2, 7, 8, 10, 4, 9, 3, 6]
#|h=1 s:u32=[6] | mn:str=[] | mx:str=[k32004]
#|h=3 t:str=[null, x, y] | v_sum:u32=[4, 7, 4] | len:u32=[2, 2, 1]
#|h=3 t:str=[null, x, y] | v:u32=[1, 2, 4]
#|h=1 t:u32=[3] | mn:str=[x] | mx:str=[y]
#|h=5 t:str=[x, x, y, null, null] | v:u32=[2, 5, 4, 1, 3]
#|h=1 t:str=[null] | v_sum:u32=[6] | len:u32=[3]
#|h=1 t:u32=[1] | mn:str=[null] | mx:str=[null]
#|h=3 t:str=[null, null, null] | v:u32=[1, 2, 3]
#|h=0 t:str=[] | v_sum:u32=[] | len:u32=[]
#|h=0 t:str=[] | v:u32=[]
#|h=1 t:u32=[0] | mn:str=[null] | mx:str=[null]
#|h=0 t:str=[] | v:u32=[]
#|-- dictionary
#|h=6 s:str=[k32004, k261338, null, , b, ab] | v_sum:u32=[6, 9, 9, 13, 8, 10] | len:u32=[2, 2, 2, 2, 1, 1]
#|h=6 s:str=[k32004, k261338, null, , b, ab] | v:u32=[1, 2, 3, 4, 8, 10]
#|h=10 s:str=[null, null, , , ab, b, k261338, k261338, k32004, k32004] | v:u32=[3, 6, 4, 9, 10, 8, 2, 7, 1, 5]
#|h=10 s:str=[k32004, k32004, k261338, k261338, b, ab, , , null, null] | v:u32=[1, 5, 2, 7, 8, 10, 4, 9, 3, 6]
#|h=1 s:u32=[6] | mn:str=[] | mx:str=[k32004]
#|h=3 t:str=[null, x, y] | v_sum:u32=[4, 7, 4] | len:u32=[2, 2, 1]
#|h=3 t:str=[null, x, y] | v:u32=[1, 2, 4]
#|h=1 t:u32=[3] | mn:str=[x] | mx:str=[y]
#|h=5 t:str=[x, x, y, null, null] | v:u32=[2, 5, 4, 1, 3]
#|h=1 t:str=[null] | v_sum:u32=[6] | len:u32=[3]
#|h=1 t:u32=[1] | mn:str=[null] | mx:str=[null]
#|h=3 t:str=[null, null, null] | v:u32=[1, 2, 3]
#|h=0 t:str=[] | v_sum:u32=[] | len:u32=[]
#|h=0 t:str=[] | v:u32=[]
#|h=1 t:u32=[0] | mn:str=[null] | mx:str=[null]
#|h=0 t:str=[] | v:u32=[]
