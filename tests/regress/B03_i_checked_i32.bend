# M1 API test (was tests/regress/pending/; activated with the B03 numerics work).
# B03-i: DESIGN.md 15.2.1: DF.i32(v) is D.I32.checked(v): v < 2^31 else
# InvalidOperation{"i32 out of range: <v>"}; DF.i32_neg(v) accepts v <= 2^31;
# D.I32.from_bits(w) is the explicit unchecked reinterpretation.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def sh(r: E.Res(D.I32)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{v}:
      D.Scalar.show(D.SI32{v})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- B03-i checked")
    IO.print(sh(DF.i32(5)))
    IO.print(sh(DF.i32(2147483647)))
    IO.print(sh(DF.i32(2147483648)))
    IO.print(sh(DF.i32_neg(2147483648)))
    IO.print(sh(DF.i32_neg(2147483649)))
    IO.print(D.Scalar.show(D.SI32{D.I32.from_bits(4294967295)}))
#|-- B03-i checked
#|5
#|2147483647
#|error: InvalidOperation: i32 out of range: 2147483648
#|-2147483648
#|error: InvalidOperation: i32 out of range: 2147483649
#|-1
#|
