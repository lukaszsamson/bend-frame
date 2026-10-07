# DType / Scalar helpers and the exact Err.show formats (DESIGN.md 4.1, 4.2).
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E

def md(m: Maybe<&2, D.DType>) -> String:
  match m:
    case None{}:
      "none"
    case Some{t}:
      D.DType.show(t)

def dd(t: D.DType) -> String:
  D.Scalar.show(D.DType.default(t))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(D.DType.show(D.TBool{}) ++ " " ++ D.DType.show(D.TU32{}) ++ " " ++ D.DType.show(D.TI32{}) ++ " " ++ D.DType.show(D.TF32{}) ++ " " ++ D.DType.show(D.TStr{}))
    IO.print(Bool.show(D.DType.eq(D.TU32{}, D.TU32{})) ++ " " ++ Bool.show(D.DType.eq(D.TU32{}, D.TI32{})) ++ " " ++ Bool.show(D.DType.eq(D.TStr{}, D.TStr{})))
    IO.print(dd(D.TBool{}) ++ " " ++ dd(D.TU32{}) ++ " " ++ dd(D.TI32{}) ++ " " ++ dd(D.TF32{}) ++ " [" ++ dd(D.TStr{}) ++ "]")
    IO.print(md(D.Scalar.dtype(D.SNull{})) ++ " " ++ md(D.Scalar.dtype(D.SBool{True{}})) ++ " " ++ md(D.Scalar.dtype(D.SU32{1})) ++ " " ++ md(D.Scalar.dtype(D.SI32{D.I32{1}})) ++ " " ++ md(D.Scalar.dtype(D.SF32{1.0})) ++ " " ++ md(D.Scalar.dtype(D.SStr{"x"})))
    IO.print(D.Scalar.show(D.SNull{}) ++ " " ++ D.Scalar.show(D.SBool{True{}}) ++ " " ++ D.Scalar.show(D.SBool{False{}}) ++ " " ++ D.Scalar.show(D.SU32{42}) ++ " " ++ D.Scalar.show(D.SI32{D.I32{4294967294}}) ++ " " ++ D.Scalar.show(D.SF32{2.5}) ++ " " ++ D.Scalar.show(D.SStr{"hi"}))
    IO.print(E.Err.show(E.ColumnNotFound{"a"}))
    IO.print(E.Err.show(E.DuplicateColumn{"a"}))
    IO.print(E.Err.show(E.TypeMismatch{"add", "u32", "str"}))
    IO.print(E.Err.show(E.ShapeMismatch{3, 2}))
    IO.print(E.Err.show(E.ParseError{7, "bad field"}))
    IO.print(E.Err.show(E.InvalidOperation{"self join"}))
    IO.print(E.Err.show(E.IoError{2, "No such file or directory"}))
#|bool u32 i32 f32 str
#|True False True
#|false 0 0 0 []
#|none bool u32 i32 f32 str
#|null true false 42 -2 2.5 hi
#|ColumnNotFound: a
#|DuplicateColumn: a
#|TypeMismatch in add: expected u32, got str
#|ShapeMismatch: expected 3 rows, got 2
#|ParseError at line 7: bad field
#|InvalidOperation: self join
#|IoError 2: No such file or directory
