# Join (M5 acceptance): inner and left join on a str key with a duplicate key
# on the right, a miss and a null key on the left (null right columns), and a
# clashing non-key name (`x` -> `x_right`). Expectations checked against
# Polars 2.0 `join(.., maintain_order="left_right")` (bend-frame's order).
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/fmt.bend as F
import ./../src/join.bend as J

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

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def table(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def jn.b(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rf}:
      J.Join.run(how, l, rf, lo, ro)

def jn(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{lf}:
      jn.b(how, lo, ro, lf, r)

def u(x: U32) -> D.Scalar:
  D.SU32{x}

def s(x: String) -> D.Scalar:
  D.SStr{x}

def nul() -> D.Scalar:
  D.SNull{}

def lf() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("a"), s("b"), s("c"), nul(), s("b")], D.TStr{}), mk("v", [u(1), u(2), u(3), u(4), u(5)], D.TU32{}), mk("x", [u(10), u(20), u(30), u(40), u(50)], D.TU32{})])

def rf() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("b"), s("a"), s("b"), nul(), s("d")], D.TStr{}), mk("x", [u(100), u(200), u(300), u(400), u(500)], D.TU32{}), mk("w", [D.SF32{1.5}, D.SF32{2.5}, D.SF32{3.5}, D.SF32{4.5}, D.SF32{5.5}], D.TF32{})])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], lf(), rf())))
    IO.print(fr(jn(J.Left{}, ["k"], ["k"], lf(), rf())))
    IO.print(table(jn(J.Left{}, ["k"], ["k"], lf(), rf())))

#|h=5 k:str=[a, b, b, b, b] | v:u32=[1, 2, 2, 5, 5] | x:u32=[10, 20, 20, 50, 50] | x_right:u32=[200, 100, 300, 100, 300] | w:f32=[2.5, 1.5, 3.5, 1.5, 3.5]
#|h=7 k:str=[a, b, b, c, null, b, b] | v:u32=[1, 2, 2, 3, 4, 5, 5] | x:u32=[10, 20, 20, 30, 40, 50, 50] | x_right:u32=[200, 100, 300, null, null, 100, 300] | w:f32=[2.5, 1.5, 3.5, null, null, 1.5, 3.5]
#|shape: (7, 5)
#|+-----+-----+-----+---------+-----+
#|| k   | v   | x   | x_right | w   |
#|| --- | --- | --- | ---     | --- |
#|| str | u32 | u32 | u32     | f32 |
#|+=====+=====+=====+=========+=====+
#|| a   | 1   | 10  | 200     | 2.5 |
#|| b   | 2   | 20  | 100     | 1.5 |
#|| b   | 2   | 20  | 300     | 3.5 |
#|| c   | 3   | 30  |         |     |
#||     | 4   | 40  |         |     |
#|| b   | 5   | 50  | 100     | 1.5 |
#|| b   | 5   | 50  | 300     | 3.5 |
#|+-----+-----+-----+---------+-----+
