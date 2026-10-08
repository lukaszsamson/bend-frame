#! xfail B03-m
# B03-m (Astra G5): f32 -> i32 out of range is garbage; u32 <-> i32 casts retag silently.
# DESIGN.md 15.5.5: f32 -> i32 = trunc toward zero, failing for NaN, +-inf,
# x < -2147483648.0 and x >= 2147483648.0; u32 -> i32 fails for v >= 2^31; i32 -> u32
# fails for negatives. Error InvalidOperation{"cast <from> to <to>: row <i> holds <cell>"}
# (cells by Scalar.show / F32.show: 2^31 shows as 2147483600). Polars 2.0.0 strict cast
# raises on the same cells and agrees on the valid cases (regress_expect.py).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def fr(+t: D.DType, xs: List<&2, D.Scalar>) -> E.ResT(C.Frame):
  R.frame([R.mk("x", xs, t)])

def go(+tag: String, +t: D.DType, +to: D.DType, +xs: List<&2, D.Scalar>) -> IO(Unit):
  R.three(tag, R.e_select(fr(t, xs), [DF.alias(DF.cast(DF.col("x"), to), "y")]), DF.lazy_select(R.src("t", fr(t, xs)), [DF.alias(DF.cast(DF.col("x"), to), "y")]), R.env1("t", fr(t, xs)), R.env1("t", fr(t, xs)))

def main() -> IO(Unit):
  do IO<Unit>:
    go("B03-m f32-i32-two-pow-31", D.TF32{}, D.TI32{}, [R.f(1.0), R.f(2147483648.0)])
    go("B03-m f32-i32-below-min", D.TF32{}, D.TI32{}, [R.f(F32.neg(2147483904.0))])
    go("B03-m f32-i32-nan", D.TF32{}, D.TI32{}, [R.f(R.nan())])
    go("B03-m f32-i32-inf", D.TF32{}, D.TI32{}, [R.f(R.ninf())])
    go("B03-m f32-i32-valid", D.TF32{}, D.TI32{}, [R.f(F32.neg(2147483648.0)), R.f(2147483520.0), R.f(F32.neg(1.9)), R.null()])
    go("B03-m u32-i32", D.TU32{}, D.TI32{}, [R.u(5), R.u(2147483648)])
    go("B03-m u32-i32-valid", D.TU32{}, D.TI32{}, [R.u(0), R.u(2147483647), R.null()])
    go("B03-m i32-u32", D.TI32{}, D.TU32{}, [R.i(5), R.ineg(1)])
    go("B03-m i32-u32-valid", D.TI32{}, D.TU32{}, [R.i(0), R.i(2147483647), R.null()])
#|-- B03-m f32-i32-two-pow-31 eager
#|error	InvalidOperation: cast f32 to i32: row 1 holds 2147483600
#|
#|-- B03-m f32-i32-two-pow-31 raw
#|error	InvalidOperation: cast f32 to i32: row 1 holds 2147483600
#|
#|-- B03-m f32-i32-two-pow-31 opt
#|error	InvalidOperation: cast f32 to i32: row 1 holds 2147483600
#|
#|-- B03-m f32-i32-below-min eager
#|error	InvalidOperation: cast f32 to i32: row 0 holds -2147484000
#|
#|-- B03-m f32-i32-below-min raw
#|error	InvalidOperation: cast f32 to i32: row 0 holds -2147484000
#|
#|-- B03-m f32-i32-below-min opt
#|error	InvalidOperation: cast f32 to i32: row 0 holds -2147484000
#|
#|-- B03-m f32-i32-nan eager
#|error	InvalidOperation: cast f32 to i32: row 0 holds nan
#|
#|-- B03-m f32-i32-nan raw
#|error	InvalidOperation: cast f32 to i32: row 0 holds nan
#|
#|-- B03-m f32-i32-nan opt
#|error	InvalidOperation: cast f32 to i32: row 0 holds nan
#|
#|-- B03-m f32-i32-inf eager
#|error	InvalidOperation: cast f32 to i32: row 0 holds -inf
#|
#|-- B03-m f32-i32-inf raw
#|error	InvalidOperation: cast f32 to i32: row 0 holds -inf
#|
#|-- B03-m f32-i32-inf opt
#|error	InvalidOperation: cast f32 to i32: row 0 holds -inf
#|
#|-- B03-m f32-i32-valid eager
#|frame
#|height	4
#|width	1
#|col	i32	"y"
#|row	-2147483648
#|row	2147483520
#|row	-1
#|row	null
#|
#|-- B03-m f32-i32-valid raw
#|frame
#|height	4
#|width	1
#|col	i32	"y"
#|row	-2147483648
#|row	2147483520
#|row	-1
#|row	null
#|
#|-- B03-m f32-i32-valid opt
#|frame
#|height	4
#|width	1
#|col	i32	"y"
#|row	-2147483648
#|row	2147483520
#|row	-1
#|row	null
#|
#|-- B03-m u32-i32 eager
#|error	InvalidOperation: cast u32 to i32: row 1 holds 2147483648
#|
#|-- B03-m u32-i32 raw
#|error	InvalidOperation: cast u32 to i32: row 1 holds 2147483648
#|
#|-- B03-m u32-i32 opt
#|error	InvalidOperation: cast u32 to i32: row 1 holds 2147483648
#|
#|-- B03-m u32-i32-valid eager
#|frame
#|height	3
#|width	1
#|col	i32	"y"
#|row	0
#|row	2147483647
#|row	null
#|
#|-- B03-m u32-i32-valid raw
#|frame
#|height	3
#|width	1
#|col	i32	"y"
#|row	0
#|row	2147483647
#|row	null
#|
#|-- B03-m u32-i32-valid opt
#|frame
#|height	3
#|width	1
#|col	i32	"y"
#|row	0
#|row	2147483647
#|row	null
#|
#|-- B03-m i32-u32 eager
#|error	InvalidOperation: cast i32 to u32: row 1 holds -1
#|
#|-- B03-m i32-u32 raw
#|error	InvalidOperation: cast i32 to u32: row 1 holds -1
#|
#|-- B03-m i32-u32 opt
#|error	InvalidOperation: cast i32 to u32: row 1 holds -1
#|
#|-- B03-m i32-u32-valid eager
#|frame
#|height	3
#|width	1
#|col	u32	"y"
#|row	0
#|row	2147483647
#|row	null
#|
#|-- B03-m i32-u32-valid raw
#|frame
#|height	3
#|width	1
#|col	u32	"y"
#|row	0
#|row	2147483647
#|row	null
#|
#|-- B03-m i32-u32-valid opt
#|frame
#|height	3
#|width	1
#|col	u32	"y"
#|row	0
#|row	2147483647
#|row	null
#|
