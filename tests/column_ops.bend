# Column ops on small columns with nulls: head, slice, clone, gather, compact. Slice is one range
# copy per buffer (W1f): every dtype, both string storages, empty and past-the-end slices.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C

def cells(r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  List.show(~&2, ~D.Scalar, ~(x => D.Scalar.show(x)), xs)

# len and cells of a column
def sh2(+n: U32, r: C.Column & List<&2, D.Scalar>) -> String:
  "len=" ++ U32.show(n) ++ " " ++ cells(r)

def sh1(r: C.Column & U32) -> String:
  (c, +n) = r
  sh2(n, C.Column.to_scalars(c))

def sh(c: C.Column) -> String:
  sh1(C.Column.len(c))

# a column that failed to build prints its error
def shr(r: E.ResT(C.Column)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      sh(c)

def mk(+xs: List<&2, D.Scalar>, +t: D.DType) -> E.ResT(C.Column):
  C.Column.from_scalars(xs, t)

def on(f: C.Column -> String, r: E.ResT(C.Column)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      f(c)

# clone: both copies print the same, and the copy is independent
def two(r: C.Column & C.Column) -> String:
  (a, b) = r
  sh(a) ++ " | " ++ sh(b)

# gather answers (column, perm)
def gat(r: C.Column & Array<U32>) -> String:
  (c, perm) = r
  sh(c)

def arr(r: U32 & Array<U32>) -> Array<U32>:
  (n, a) = r
  a

def ints() -> List<&2, D.Scalar>:
  [D.SU32{10}, D.SNull{}, D.SU32{30}, D.SU32{40}, D.SNull{}]

def strs() -> List<&2, D.Scalar>:
  [D.SStr{"a"}, D.SNull{}, D.SStr{"c"}, D.SStr{"d"}]

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(on(c => sh(C.Column.head(c, 3)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.head(c, 99)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.slice(c, 1, 3)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.slice(c, 3, 99)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.slice(c, 5, 1)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.slice(c, 99, 1)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.slice(c, 0, 0)), mk(ints(), D.TU32{})))
    IO.print(on(c => sh(C.Column.slice(c, 1, 2)), mk(strs(), D.TStr{})))
    IO.print(on(c => sh(C.Column.slice(C.Column.encode(c), 1, 3)), mk(strs(), D.TStr{})))
    IO.print(on(c => sh(C.Column.slice(c, 1, 2)), mk([D.SF32{0.5}, D.SNull{}, D.SF32{2.5}, D.SF32{3.5}], D.TF32{})))
    IO.print(on(c => sh(C.Column.slice(c, 1, 2)), mk([D.SI32{D.I32{7}}, D.SI32{D.I32{8}}, D.SI32{D.I32{9}}], D.TI32{})))
    IO.print(on(c => two(C.Column.clone(c)), mk(strs(), D.TStr{})))
    IO.print(on(c => gat(C.Column.gather(c, arr(K.Kernel.from_list(~U32, [3, 1, 0, 0], 0)), 4)), mk(strs(), D.TStr{})))
    IO.print(on(c => gat(C.Column.gather(c, arr(K.Kernel.from_list(~U32, [2, 4, 0], 0)), 3)), mk(ints(), D.TU32{})))
    IO.print(on(c => gat(C.Column.compact(c, arr(K.Kernel.from_list(~U32, [1, 1, 0, 1, 0], 0)), 3)), mk(ints(), D.TU32{})))
    IO.print(on(c => gat(C.Column.compact(c, arr(K.Kernel.from_list(~U32, [0, 0, 0, 0, 0], 0)), 0)), mk(ints(), D.TU32{})))
    IO.print(on(c => gat(C.Column.compact(c, arr(K.Kernel.from_list(~U32, [1, 0, 1, 1], 0)), 3)), mk(strs(), D.TStr{})))
    IO.print(on(c => gat(C.Column.compact(c, arr(K.Kernel.from_list(~U32, [1, 0, 1], 0)), 2)), mk([D.SF32{0.5}, D.SF32{1.5}, D.SF32{2.5}], D.TF32{})))
#|len=3 [10, null, 30]
#|len=5 [10, null, 30, 40, null]
#|len=3 [null, 30, 40]
#|len=2 [40, null]
#|len=0 []
#|len=0 []
#|len=0 []
#|len=2 [null, c]
#|len=3 [null, c, d]
#|len=2 [null, 2.5]
#|len=2 [8, 9]
#|len=4 [a, null, c, d] | len=4 [a, null, c, d]
#|len=4 [d, null, a, a]
#|len=3 [30, null, 10]
#|len=3 [10, null, 40]
#|len=0 []
#|len=3 [a, c, d]
#|len=2 [0.5, 2.5]
