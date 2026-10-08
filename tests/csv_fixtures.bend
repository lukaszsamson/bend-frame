# M3: bench/fixtures parse with the schema DESIGN.md states (sales: id u32, region str,
# product str, qty u32, price f32, discount f32 nullable, ok bool). Run from the repo root.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/fmt.bend as F
import ./../src/csv.bend as V

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def show(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

# the first n lines of the rendering with 4 decimals
def head(r: E.ResT(C.Frame), +n: Nat) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      String.join(List.take(&2, String, String.lines(snd(V.Csv.render(f, Some{4}))), n), "\n")

def text(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(V.Csv.render(f, None{}))

# render(parse(text)) is a fixed point: parsing the rendering renders the same text
def again(+t1: String) -> String:
  Bool.show(String.eq(t1, text(V.Csv.parse(t1, V.Csv.default()))))

def roundtrip(r: E.ResT(C.Frame)) -> String:
  again(text(r))

def main() -> IO(Unit):
  do IO<Unit>:
    t : E.ResT(C.Frame) <- V.Csv.read("bench/fixtures/tiny.csv", V.Csv.default())
    IO.print(show(t))
    t2 : E.ResT(C.Frame) <- V.Csv.read("bench/fixtures/tiny.csv", V.Csv.default())
    IO.print(head(t2, 4n))
    t3 : E.ResT(C.Frame) <- V.Csv.read("bench/fixtures/tiny.csv", V.Csv.default())
    IO.print(roundtrip(t3))
    p : E.ResT(C.Frame) <- V.Csv.read("bench/fixtures/products.csv", V.Csv.default())
    IO.print(show(p))
    p2 : E.ResT(C.Frame) <- V.Csv.read("bench/fixtures/products.csv", V.Csv.default())
    IO.print(roundtrip(p2))
#|shape: (20, 7)
#|+-----+---------+---------+-----+--------+----------+-------+
#|| id  | region  | product | qty | price  | discount | ok    |
#|| --- | ---     | ---     | --- | ---    | ---      | ---   |
#|| u32 | str     | str     | u32 | f32    | f32      | bool  |
#|+=====+=========+=========+=====+========+==========+=======+
#|| 0   | inland  | prod_60 | 49  | 42.84  | 0.13     | false |
#|| 1   | inland  | prod_61 | 78  | 333.37 |          | true  |
#|| 2   | inland  | prod_40 | 97  | 446.7  | 0.17     | false |
#|| 3   | inland  | prod_17 | 47  | 409.68 |          | true  |
#|| 4   | west    | prod_08 | 57  | 60.76  | 0.24     | false |
#|| ... | ...     | ...     | ... | ...    | ...      | ...   |
#|| 15  | central | prod_20 | 91  | 146.07 | 0.27     | false |
#|| 16  | island  | prod_31 | 87  | 14.41  |          | false |
#|| 17  | north   | prod_58 | 33  | 421.68 | 0.25     | true  |
#|| 18  | coastal | prod_33 | 88  | 190.93 | 0.14     | true  |
#|| 19  | south   | prod_23 | 11  | 167.94 | 0.07     | true  |
#|+-----+---------+---------+-----+--------+----------+-------+
#|id,region,product,qty,price,discount,ok
#|0,inland,prod_60,49,42.8400,0.1300,false
#|1,inland,prod_61,78,333.3700,,true
#|2,inland,prod_40,97,446.7000,0.1700,false
#|True
#|shape: (64, 3)
#|+---------+----------+--------+
#|| product | category | weight |
#|| ---     | ---      | ---    |
#|| str     | str      | f32    |
#|+=========+==========+========+
#|| prod_00 | tools    | 4.55   |
#|| prod_01 | toys     | 38.72  |
#|| prod_02 | food     | 32.76  |
#|| prod_03 | books    | 22     |
#|| prod_04 | garden   | 21.7   |
#|| ...     | ...      | ...    |
#|| prod_59 | sports   | 34.18  |
#|| prod_60 | tools    | 46.13  |
#|| prod_61 | toys     | 37.26  |
#|| prod_62 | food     | 18.39  |
#|| prod_63 | books    | 48.37  |
#|+---------+----------+--------+
#|True
