# Fmt.describe beyond the q6 golden: a u32 with nulls, an i32 (negatives), a str and a bool
# column with nulls, an all-null f32 column, one-row std (null), and nearest-rank quantiles
# (n = 6 valid rows: idx round(0.25*5)=1, round(0.5*5)=3 (2.5 away from zero), round(0.75*5)=4).
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/fmt.bend as F

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

def desc.k(r: C.Frame & E.ResT(C.Frame)) -> String:
  (f, res) = r
  show(res)

def desc(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      desc.k(F.Fmt.describe(f))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(desc(C.Frame.from_columns([
      mk("u", [D.SU32{7}, D.SNull{}, D.SU32{1}, D.SU32{4}, D.SU32{10}, D.SU32{2}, D.SU32{5}, D.SNull{}], D.TU32{}),
      mk("i", [D.SI32{D.I32.neg(D.I32{3})}, D.SI32{D.I32.neg(D.I32{1})}, D.SI32{D.I32{0}}, D.SI32{D.I32{2}}, D.SI32{D.I32{4}}, D.SI32{D.I32{6}}, D.SI32{D.I32{8}}, D.SI32{D.I32{9}}], D.TI32{}),
      mk("s", [D.SStr{"pear"}, D.SNull{}, D.SStr{"apple"}, D.SStr{"fig"}, D.SNull{}, D.SStr{"kiwi"}, D.SStr{"fig"}, D.SStr{"zed"}], D.TStr{}),
      mk("b", [D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}], D.TBool{}),
      mk("n", [D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}], D.TF32{})
    ])))
    IO.print(desc(C.Frame.from_columns([
      mk("x", [D.SF32{2.5}], D.TF32{})
    ])))
#|shape: (9, 6)
#|+------------+-----------+---------+-------+-------+-----+
#|| statistic  | u         | i       | s     | b     | n   |
#|| ---        | ---       | ---     | ---   | ---   | --- |
#|| str        | f32       | f32     | str   | str   | f32 |
#|+============+===========+=========+=======+=======+=====+
#|| count      | 6         | 8       | 6     | 3     | 0   |
#|| null_count | 2         | 0       | 2     | 5     | 8   |
#|| mean       | 4.8333335 | 3.125   |       |       |     |
#|| std        | 3.3115957 | 4.35685 |       |       |     |
#|| min        | 1         | -3      | apple | false |     |
#|| 25%        | 2         | 0       |       |       |     |
#|| 50%        | 5         | 4       |       |       |     |
#|| 75%        | 7         | 6       |       |       |     |
#|| max        | 10        | 9       | zed   | true  |     |
#|+------------+-----------+---------+-------+-------+-----+
#|shape: (9, 2)
#|+------------+-----+
#|| statistic  | x   |
#|| ---        | --- |
#|| str        | f32 |
#|+============+=====+
#|| count      | 1   |
#|| null_count | 0   |
#|| mean       | 2.5 |
#|| std        |     |
#|| min        | 2.5 |
#|| 25%        | 2.5 |
#|| 50%        | 2.5 |
#|| 75%        | 2.5 |
#|| max        | 2.5 |
#|+------------+-----+
