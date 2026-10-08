# B03-i (Fable minor, plan 2.2d): DF.lit_i32(v) with v >= 2^31 is silently negative.
# DESIGN.md 15.2.1 (D:): lit_i32 / lit_i32_neg stay total builders; out of range they
# build Cast{Lit{SU32{v}}, TI32} (resp. its Neg), a strict cast that fails when evaluated:
# InvalidOperation{"cast u32 to i32: row 0 holds <v>"}; collect_schema accepts (i32).
# In range: lit_i32(2147483647) and lit_i32_neg(2147483648) = MIN are plain literals.
# The checked DF.i32 / DF.i32_neg are M1 API (tests/regress/B03_i_checked_i32.bend).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.u(3)], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def go(+tag: String, +e: X.Expr) -> IO(Unit):
  do IO<Unit>:
    R.three(tag, R.e_select(t(), [e]), DF.lazy_select(src(), [e]), env(), env())
    IO.print(R.schema(tag, DF.lazy_select(src(), [e])))

def main() -> IO(Unit):
  do IO<Unit>:
    go("B03-i max", DF.alias(DF.lit_i32(2147483647), "x"))
    go("B03-i min", DF.alias(DF.lit_i32_neg(2147483648), "x"))
    go("B03-i too-big", DF.alias(DF.lit_i32(3000000000), "x"))
    go("B03-i two-pow-31", DF.alias(DF.lit_i32(2147483648), "x"))
    go("B03-i neg-too-big", DF.alias(DF.lit_i32_neg(2147483649), "x"))
#|-- B03-i max eager
#|frame
#|height	1
#|width	1
#|col	i32	"x"
#|row	2147483647
#|
#|-- B03-i max raw
#|frame
#|height	1
#|width	1
#|col	i32	"x"
#|row	2147483647
#|
#|-- B03-i max opt
#|frame
#|height	1
#|width	1
#|col	i32	"x"
#|row	2147483647
#|
#|-- B03-i max schema
#|x:i32
#|
#|-- B03-i min eager
#|frame
#|height	1
#|width	1
#|col	i32	"x"
#|row	-2147483648
#|
#|-- B03-i min raw
#|frame
#|height	1
#|width	1
#|col	i32	"x"
#|row	-2147483648
#|
#|-- B03-i min opt
#|frame
#|height	1
#|width	1
#|col	i32	"x"
#|row	-2147483648
#|
#|-- B03-i min schema
#|x:i32
#|
#|-- B03-i too-big eager
#|error	InvalidOperation: cast u32 to i32: row 0 holds 3000000000
#|
#|-- B03-i too-big raw
#|error	InvalidOperation: cast u32 to i32: row 0 holds 3000000000
#|
#|-- B03-i too-big opt
#|error	InvalidOperation: cast u32 to i32: row 0 holds 3000000000
#|
#|-- B03-i too-big schema
#|x:i32
#|
#|-- B03-i two-pow-31 eager
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483648
#|
#|-- B03-i two-pow-31 raw
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483648
#|
#|-- B03-i two-pow-31 opt
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483648
#|
#|-- B03-i two-pow-31 schema
#|x:i32
#|
#|-- B03-i neg-too-big eager
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483649
#|
#|-- B03-i neg-too-big raw
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483649
#|
#|-- B03-i neg-too-big opt
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483649
#|
#|-- B03-i neg-too-big schema
#|x:i32
#|
