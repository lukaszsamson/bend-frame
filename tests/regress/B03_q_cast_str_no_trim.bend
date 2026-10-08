# B03-q: str -> number cast trims; Polars does not. DESIGN.md 15.5.5 (D:): U32.read /
# I32.read / F32.read of the cell AS IS: " 2 " and "+5" fail for u32, " -3" for i32;
# F32.read accepts nan, inf, -inf, 1e3, .5, 5., +5 (the valid case). Polars 2.0.0 strict
# cast fails on the padded cells too (regress_expect.py).
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
    go("B03-q u32-padded", D.TU32{}, [R.s("1"), R.s(" 2 ")])
    go("B03-q u32-plus", D.TU32{}, [R.s("+5")])
    go("B03-q i32-padded", D.TI32{}, [R.s(" -3")])
    go("B03-q f32-padded", D.TF32{}, [R.s("2.5 ")])
    go("B03-q f32-spellings", D.TF32{}, [R.s("nan"), R.s("inf"), R.s("-inf"), R.s("1e3"), R.s(".5"), R.s("5."), R.s("+5")])
#|-- B03-q u32-padded eager
#|error	InvalidOperation: cast str to u32: row 1 holds " 2 "
#|
#|-- B03-q u32-padded raw
#|error	InvalidOperation: cast str to u32: row 1 holds " 2 "
#|
#|-- B03-q u32-padded opt
#|error	InvalidOperation: cast str to u32: row 1 holds " 2 "
#|
#|-- B03-q u32-plus eager
#|error	InvalidOperation: cast str to u32: row 0 holds "+5"
#|
#|-- B03-q u32-plus raw
#|error	InvalidOperation: cast str to u32: row 0 holds "+5"
#|
#|-- B03-q u32-plus opt
#|error	InvalidOperation: cast str to u32: row 0 holds "+5"
#|
#|-- B03-q i32-padded eager
#|error	InvalidOperation: cast str to i32: row 0 holds " -3"
#|
#|-- B03-q i32-padded raw
#|error	InvalidOperation: cast str to i32: row 0 holds " -3"
#|
#|-- B03-q i32-padded opt
#|error	InvalidOperation: cast str to i32: row 0 holds " -3"
#|
#|-- B03-q f32-padded eager
#|error	InvalidOperation: cast str to f32: row 0 holds "2.5 "
#|
#|-- B03-q f32-padded raw
#|error	InvalidOperation: cast str to f32: row 0 holds "2.5 "
#|
#|-- B03-q f32-padded opt
#|error	InvalidOperation: cast str to f32: row 0 holds "2.5 "
#|
#|-- B03-q f32-spellings eager
#|frame
#|height	7
#|width	1
#|col	f32	"y"
#|row	0x7fc00000
#|row	0x7f800000
#|row	0xff800000
#|row	0x447a0000
#|row	0x3f000000
#|row	0x40a00000
#|row	0x40a00000
#|
#|-- B03-q f32-spellings raw
#|frame
#|height	7
#|width	1
#|col	f32	"y"
#|row	0x7fc00000
#|row	0x7f800000
#|row	0xff800000
#|row	0x447a0000
#|row	0x3f000000
#|row	0x40a00000
#|row	0x40a00000
#|
#|-- B03-q f32-spellings opt
#|frame
#|height	7
#|width	1
#|col	f32	"y"
#|row	0x7fc00000
#|row	0x7f800000
#|row	0xff800000
#|row	0x447a0000
#|row	0x3f000000
#|row	0x40a00000
#|row	0x40a00000
#|
