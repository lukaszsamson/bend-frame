# M1: columns of every dtype built from scalar lists (SNull -> invalid row),
# cells read back, len / dtype / null_count, and the TypeMismatch error.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C

def cells(r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  List.show(~&2, ~D.Scalar, ~(x => D.Scalar.show(x)), xs)

def d4(+n: U32, +t: D.DType, k: U32, r: C.Column & List<&2, D.Scalar>) -> String:
  "len=" ++ U32.show(n) ++ " " ++ D.DType.show(t) ++ " nulls=" ++ U32.show(k) ++ " " ++ cells(r)

def d3(+n: U32, +t: D.DType, r: C.Column & U32) -> String:
  (c, k) = r
  d4(n, t, k, C.Column.to_scalars(c))

def d2(+n: U32, r: C.Column & D.DType) -> String:
  (c, t) = r
  d3(n, t, C.Column.null_count(c))

def d1(r: C.Column & U32) -> String:
  (c, +n) = r
  d2(n, C.Column.dtype(c))

def describe(r: E.ResT(C.Column)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      d1(C.Column.len(c))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(describe(C.Column.from_scalars([D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}], D.TU32{})))
    IO.print(describe(C.Column.from_scalars([D.SF32{1.5}, D.SNull{}, D.SF32{F32.neg(2.0)}], D.TF32{})))
    IO.print(describe(C.Column.from_scalars([D.SStr{"ann"}, D.SStr{"bob"}, D.SNull{}], D.TStr{})))
    IO.print(describe(C.Column.from_scalars([D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SNull{}], D.TBool{})))
    IO.print(describe(C.Column.from_scalars([D.SI32{D.I32{4294967295}}, D.SNull{}, D.SI32{D.I32{7}}], D.TI32{})))
    IO.print(describe(C.Column.from_scalars([D.SU32{5}, D.SU32{6}], D.TU32{})))
    IO.print(describe(C.Column.from_scalars([], D.TU32{})))
    IO.print(describe(C.Column.from_scalars([D.SNull{}, D.SNull{}], D.TStr{})))
    IO.print(describe(C.Column.from_scalars([D.SU32{1}, D.SStr{"x"}], D.TU32{})))
    IO.print(describe(C.Column.from_scalars([D.SF32{1.0}, D.SU32{2}], D.TF32{})))

#|len=4 u32 nulls=1 [1, 2, null, 4]
#|len=3 f32 nulls=1 [1.5, null, -2]
#|len=3 str nulls=1 [ann, bob, null]
#|len=4 bool nulls=2 [true, false, null, null]
#|len=3 i32 nulls=1 [-1, null, 7]
#|len=2 u32 nulls=0 [5, 6]
#|len=0 u32 nulls=0 []
#|len=2 str nulls=2 [null, null]
#|error: TypeMismatch in from_scalars: expected u32, got str
#|error: TypeMismatch in from_scalars: expected f32, got u32
