# M1: Fmt.show -- the Polars-style ASCII table of DESIGN.md 4.12.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/fmt.bend as F

# a named column; a build error becomes a column named after the error
def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def show(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

# 1..n as scalars
def seq(f: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match f:
    case 0n:
      List.reverse(&2, D.Scalar, acc)
    case 1n+p:
      seq(p, U32.inc(i), D.SU32{i} <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(C.Frame.from_columns([mk("name", [D.SStr{"ann"}, D.SStr{"bob"}, D.SStr{"cy"}], D.TStr{}), mk("age", [D.SU32{31}, D.SU32{42}, D.SNull{}], D.TU32{})])))
    IO.print(show(C.Frame.from_columns([mk("x", [D.SF32{1.5}, D.SNull{}], D.TF32{}), mk("flag", [D.SBool{True{}}, D.SBool{False{}}], D.TBool{}), mk("a_much_longer_name", [D.SI32{D.I32{4294967293}}, D.SNull{}], D.TI32{})])))
    IO.print(show(C.Frame.from_columns([mk("n", seq(12n, 1, Nil{}), D.TU32{})])))
    IO.print(show(C.Frame.from_columns([mk("n", seq(10n, 1, Nil{}), D.TU32{}), mk("s", [D.SStr{"a"}, D.SNull{}, D.SStr{"c"}, D.SStr{"d"}, D.SStr{"e"}, D.SStr{"f"}, D.SStr{"g"}, D.SStr{"h"}, D.SStr{"i"}, D.SStr{"jj"}], D.TStr{})])))
    IO.print(show(C.Frame.from_columns([mk("e", [], D.TStr{})])))
    IO.print(show(C.Frame.from_columns([])))
#|shape: (3, 2)
#|+------+-----+
#|| name | age |
#|| ---  | --- |
#|| str  | u32 |
#|+======+=====+
#|| ann  | 31  |
#|| bob  | 42  |
#|| cy   |     |
#|+------+-----+
#|shape: (2, 3)
#|+-----+-------+--------------------+
#|| x   | flag  | a_much_longer_name |
#|| --- | ---   | ---                |
#|| f32 | bool  | i32                |
#|+=====+=======+====================+
#|| 1.5 | true  | -3                 |
#||     | false |                    |
#|+-----+-------+--------------------+
#|shape: (12, 1)
#|+-----+
#|| n   |
#|| --- |
#|| u32 |
#|+=====+
#|| 1   |
#|| 2   |
#|| 3   |
#|| 4   |
#|| 5   |
#|| ... |
#|| 8   |
#|| 9   |
#|| 10  |
#|| 11  |
#|| 12  |
#|+-----+
#|shape: (10, 2)
#|+-----+-----+
#|| n   | s   |
#|| --- | --- |
#|| u32 | str |
#|+=====+=====+
#|| 1   | a   |
#|| 2   |     |
#|| 3   | c   |
#|| 4   | d   |
#|| 5   | e   |
#|| 6   | f   |
#|| 7   | g   |
#|| 8   | h   |
#|| 9   | i   |
#|| 10  | jj  |
#|+-----+-----+
#|shape: (0, 1)
#|+-----+
#|| e   |
#|| --- |
#|| str |
#|+=====+
#|+-----+
#|shape: (0, 0)
