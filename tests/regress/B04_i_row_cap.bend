# B04-i (DESIGN 14 M1.7, Fable 2): the 2^23 row cap existed only as a comment. DESIGN.md
# 15.8: Kernel.max_rows() = 8388608; check_rows(n) is Some{InvalidOperation{"too many
# rows: <n> exceeds 8388608"}} iff n > 8388608. Every allocation path that exists today calls
# it before allocating: Column.from_scalars (list length), Csv.rows (data records), Join.run
# (output rows from the CSR counts; the sum saturates at 2^32 - 1 instead of wrapping),
# GroupBy.run (input height, which bounds the group count). No test allocates 8M rows:
#  - the real cap is exercised through a 2900 x 2900 equal-key join (8.41M output rows),
#    a 65536 x 65536 one (2^32 rows: a wrapped sum would read 0), and a zero-column frame of
#    8388609 rows under group_by (Frame{h, []} holds no data);
#  - the other paths are exercised through their `.cap` entry points with a lowered cap
#    (K.Kernel.check_rows.cap, C.Column.from_scalars.cap, V.Csv.rows.cap / V.Csv.parse_with.cap);
#    the error text then names the lowered cap.
# concat_vertical does not exist yet (M3): its cases wait in pending/B04_i_concat_cap.bend.txt.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./../../src/kernels.bend as K
import ./../../src/csv.bend as V
import ./lib/rx.bend as R

def chk(m: Maybe<&2, E.Err>) -> String:
  match m:
    case None{}:
      "none"
    case Some{e}:
      "some " ++ E.Err.show(e)

def res.f(r: E.ResT(C.Column)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      DF.from_columns([C.Named{"x", c}])

def res(+tag: String, r: E.ResT(C.Column)) -> String:
  "-- " ++ tag ++ "\n" ++ DF.dump(res.f(r))


# n equal u32 keys
def keys.go(n: Nat) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      R.u(1) <> keys.go(p)

def side(n: Nat) -> E.ResT(C.Frame):
  R.frame([R.mk("k", keys.go(n), D.TU32{})])

# 65536 equal keys, built without a 65536-element list (its recursion overflows the stack)
def side16() -> E.ResT(C.Frame):
  DF.from_columns([C.Named{"k", C.CU32{65536, 16n, C.AllValid{}, Array.new(U32, 16n, 1)}}])

def us(n: Nat) -> List<&2, D.Scalar>:
  keys.go(n)

def hdr() -> V.CsvOpts:
  V.CsvOpts{',', True{}, 100}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- B04-i guard")
    IO.print(U32.show(K.Kernel.max_rows()))
    IO.print(chk(K.Kernel.check_rows(8388608)))
    IO.print(chk(K.Kernel.check_rows(8388609)))
    IO.print(chk(K.Kernel.check_rows(4294967295)))
    IO.print(chk(K.Kernel.check_rows.cap(5, 5)))
    IO.print(chk(K.Kernel.check_rows.cap(5, 6)))
    IO.print("")
    IO.print(R.show("B04-i join", "eager", R.e_inner(side(2900n), side(2900n), ["k"], ["k"])))
    IO.print(R.show("B04-i left-join", "eager", R.e_left(side(2900n), side(2900n), ["k"], ["k"])))
    IO.print(R.show("B04-i join-wrap", "eager", R.e_inner(side16(), side16(), ["k"], ["k"])))
    IO.print(R.show("B04-i join-under", "eager", R.e_inner(side(3n), side(2n), ["k"], ["k"])))
    IO.print(R.show("B04-i group-by", "eager", R.e_group(R.zcols(8388609), [DF.lit_u32(1)], [DF.alias(DF.len(), "n")])))
    IO.print(R.show("B04-i group-by-under", "eager", R.e_group(side(3n), [DF.col("k")], [DF.alias(DF.len(), "n")])))
    IO.print(res("B04-i from_scalars over", C.Column.from_scalars.cap(3, us(4n), D.TU32{})))
    IO.print(res("B04-i from_scalars at-cap", C.Column.from_scalars.cap(4, us(4n), D.TU32{})))
    IO.print(res("B04-i from_scalars over-bad-dtype", C.Column.from_scalars.cap(3, us(4n), D.TStr{})))
    IO.print(res("B04-i from_scalars default-cap", C.Column.from_scalars(us(4n), D.TU32{})))
    IO.print(R.show("B04-i csv over", "eager", V.Csv.parse_with.cap(3, "a\n1\n2\n3\n4\n", hdr(), Nil{})))
    IO.print(R.show("B04-i csv at-cap", "eager", V.Csv.parse_with.cap(4, "a\n1\n2\n3\n4\n", hdr(), Nil{})))
    IO.print(R.show("B04-i csv over-explicit-dtypes", "eager", V.Csv.parse_with.cap(3, "a\n1\n2\n3\n4\n", hdr(), [D.TU32{}])))
    IO.print(R.show("B04-i csv no-header", "eager", V.Csv.parse_with.cap(2, "1\n2\n3\n", V.CsvOpts{',', False{}, 100}, Nil{})))
    IO.print(R.show("B04-i csv blank-lines-not-counted", "eager", V.Csv.parse_with.cap(2, "a,b\n1,2\n\n\n3,4\n", hdr(), Nil{})))
    IO.print(R.show("B04-i csv header-only", "eager", V.Csv.parse_with.cap(0, "a,b\n", hdr(), Nil{})))
    IO.print(R.show("B04-i csv ragged-before-cap", "eager", V.Csv.parse_with.cap(1, "a,b\n1,2\n3\n", hdr(), Nil{})))
    IO.print(R.show("B04-i csv default-cap", "eager", V.Csv.parse_with("a\n1\n2\n", hdr(), Nil{})))
#|-- B04-i guard
#|8388608
#|none
#|some InvalidOperation: too many rows: 8388609 exceeds 8388608
#|some InvalidOperation: too many rows: 4294967295 exceeds 8388608
#|none
#|some InvalidOperation: too many rows: 6 exceeds 5
#|
#|-- B04-i join eager
#|error	InvalidOperation: too many rows: 8410000 exceeds 8388608
#|
#|-- B04-i left-join eager
#|error	InvalidOperation: too many rows: 8410000 exceeds 8388608
#|
#|-- B04-i join-wrap eager
#|error	InvalidOperation: too many rows: 4294967295 exceeds 8388608
#|
#|-- B04-i join-under eager
#|frame
#|height	6
#|width	1
#|col	u32	"k"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B04-i group-by eager
#|error	InvalidOperation: too many rows: 8388609 exceeds 8388608
#|
#|-- B04-i group-by-under eager
#|frame
#|height	1
#|width	2
#|col	u32	"k"
#|col	u32	"n"
#|row	1	3
#|
#|-- B04-i from_scalars over
#|error	InvalidOperation: too many rows: 4 exceeds 3
#|
#|-- B04-i from_scalars at-cap
#|frame
#|height	4
#|width	1
#|col	u32	"x"
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B04-i from_scalars over-bad-dtype
#|error	InvalidOperation: too many rows: 4 exceeds 3
#|
#|-- B04-i from_scalars default-cap
#|frame
#|height	4
#|width	1
#|col	u32	"x"
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B04-i csv over eager
#|error	InvalidOperation: too many rows: 4 exceeds 3
#|
#|-- B04-i csv at-cap eager
#|frame
#|height	4
#|width	1
#|col	u32	"a"
#|row	1
#|row	2
#|row	3
#|row	4
#|
#|-- B04-i csv over-explicit-dtypes eager
#|error	InvalidOperation: too many rows: 4 exceeds 3
#|
#|-- B04-i csv no-header eager
#|error	InvalidOperation: too many rows: 3 exceeds 2
#|
#|-- B04-i csv blank-lines-not-counted eager
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
#|-- B04-i csv header-only eager
#|frame
#|height	0
#|width	2
#|col	str	"a"
#|col	str	"b"
#|
#|-- B04-i csv ragged-before-cap eager
#|error	ParseError at line 3: expected 2 fields, got 1
#|
#|-- B04-i csv default-cap eager
#|frame
#|height	2
#|width	1
#|col	u32	"a"
#|row	1
#|row	2
#|
