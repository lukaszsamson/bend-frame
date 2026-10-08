# B03-p: str -> number cast nulls failures silently under the name cast. DESIGN.md 15.5.5:
# cast is strict: the first valid cell that does not read is
# InvalidOperation{"cast str to <t>: row <i> holds \"<text>\""} (strings quoted); str ->
# bool accepts exactly true/false/True/False. Nulls pass. Polars 2.0.0 strict cast raises
# on the same cells. try_cast (the null-ing variant) is M1 API
# (tests/regress/B03_e_try_cast.bend).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def fr(xs: List<&2, D.Scalar>) -> E.ResT(C.Frame):
  R.frame([R.mk("s", xs, D.TStr{})])

def go(+tag: String, +to: D.DType, +xs: List<&2, D.Scalar>) -> IO(Unit):
  R.three(tag, R.e_select(fr(xs), [DF.alias(DF.cast(DF.col("s"), to), "y")]), DF.lazy_select(R.src("t", fr(xs)), [DF.alias(DF.cast(DF.col("s"), to), "y")]), R.env1("t", fr(xs)), R.env1("t", fr(xs)))

def main() -> IO(Unit):
  do IO<Unit>:
    go("B03-p str-u32", D.TU32{}, [R.s("1"), R.null(), R.s("x")])
    go("B03-p str-i32-empty", D.TI32{}, [R.s("-3"), R.s("")])
    go("B03-p str-f32", D.TF32{}, [R.s("1.5"), R.s("abc")])
    go("B03-p str-bool", D.TBool{}, [R.s("true"), R.s("False"), R.s("yes")])
    go("B03-p str-u32-valid", D.TU32{}, [R.s("1"), R.null(), R.s("4294967295")])
#|-- B03-p str-u32 eager
#|error	InvalidOperation: cast str to u32: row 2 holds "x"
#|
#|-- B03-p str-u32 raw
#|error	InvalidOperation: cast str to u32: row 2 holds "x"
#|
#|-- B03-p str-u32 opt
#|error	InvalidOperation: cast str to u32: row 2 holds "x"
#|
#|-- B03-p str-i32-empty eager
#|error	InvalidOperation: cast str to i32: row 1 holds ""
#|
#|-- B03-p str-i32-empty raw
#|error	InvalidOperation: cast str to i32: row 1 holds ""
#|
#|-- B03-p str-i32-empty opt
#|error	InvalidOperation: cast str to i32: row 1 holds ""
#|
#|-- B03-p str-f32 eager
#|error	InvalidOperation: cast str to f32: row 1 holds "abc"
#|
#|-- B03-p str-f32 raw
#|error	InvalidOperation: cast str to f32: row 1 holds "abc"
#|
#|-- B03-p str-f32 opt
#|error	InvalidOperation: cast str to f32: row 1 holds "abc"
#|
#|-- B03-p str-bool eager
#|error	InvalidOperation: cast str to bool: row 2 holds "yes"
#|
#|-- B03-p str-bool raw
#|error	InvalidOperation: cast str to bool: row 2 holds "yes"
#|
#|-- B03-p str-bool opt
#|error	InvalidOperation: cast str to bool: row 2 holds "yes"
#|
#|-- B03-p str-u32-valid eager
#|frame
#|height	3
#|width	1
#|col	u32	"y"
#|row	1
#|row	null
#|row	4294967295
#|
#|-- B03-p str-u32-valid raw
#|frame
#|height	3
#|width	1
#|col	u32	"y"
#|row	1
#|row	null
#|row	4294967295
#|
#|-- B03-p str-u32-valid opt
#|frame
#|height	3
#|width	1
#|col	u32	"y"
#|row	1
#|row	null
#|row	4294967295
#|
