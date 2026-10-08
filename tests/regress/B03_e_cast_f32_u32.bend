#! xfail B03-e
# B03-e (Fable B2, Astra G5): cast f32 -> u32 of a negative, huge or NaN value answers 0.
# DESIGN.md 15.5.5: cast is strict; f32 -> u32 is trunc(x), failing for NaN, +-inf,
# x <= -1.0 and x >= 4294967296.0; the first failing valid cell is
# InvalidOperation{"cast f32 to u32: row <i> holds <F32.show cell>"} in every API (a
# runtime error: collect_schema accepts). Polars 2.0.0 strict cast raises on the same
# cells and gives [0, 4294967040, 2, null] for the valid case. try_cast (the null-ing
# variant) is M1 API: tests/regress/pending/B03_e_try_cast.bend.txt.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def fx(xs: List<&2, D.Scalar>) -> E.ResT(C.Frame):
  R.frame([R.mk("x", xs, D.TF32{})])

def y() -> List<&2, X.Expr>:
  [DF.alias(DF.cast_u32(DF.col("x")), "y")]

def go(+tag: String, +xs: List<&2, D.Scalar>) -> IO(Unit):
  R.three(tag, R.e_select(fx(xs), y()), DF.lazy_select(R.src("t", fx(xs)), y()), R.env1("t", fx(xs)), R.env1("t", fx(xs)))

def main() -> IO(Unit):
  do IO<Unit>:
    go("B03-e negative", [R.f(1.5), R.f(F32.neg(1.5))])
    go("B03-e minus-one", [R.f(F32.neg(1.0))])
    go("B03-e huge", [R.f(1000000000000.0)])
    go("B03-e two-pow-32", [R.f(4294967296.0)])
    go("B03-e nan", [R.f(R.nan())])
    go("B03-e inf", [R.f(R.inf())])
    go("B03-e neg-inf", [R.f(R.ninf())])
    go("B03-e valid", [R.f(F32.neg(0.5)), R.f(4294967040.0), R.f(2.9), R.null()])
    IO.print(R.schema("B03-e negative", DF.lazy_select(R.src("t", fx([R.f(F32.neg(1.5))])), y())))
#|-- B03-e negative eager
#|error	InvalidOperation: cast f32 to u32: row 1 holds -1.5
#|
#|-- B03-e negative raw
#|error	InvalidOperation: cast f32 to u32: row 1 holds -1.5
#|
#|-- B03-e negative opt
#|error	InvalidOperation: cast f32 to u32: row 1 holds -1.5
#|
#|-- B03-e minus-one eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds -1
#|
#|-- B03-e minus-one raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds -1
#|
#|-- B03-e minus-one opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds -1
#|
#|-- B03-e huge eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds 1000000000000
#|
#|-- B03-e huge raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds 1000000000000
#|
#|-- B03-e huge opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds 1000000000000
#|
#|-- B03-e two-pow-32 eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds 4294967300
#|
#|-- B03-e two-pow-32 raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds 4294967300
#|
#|-- B03-e two-pow-32 opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds 4294967300
#|
#|-- B03-e nan eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds nan
#|
#|-- B03-e nan raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds nan
#|
#|-- B03-e nan opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds nan
#|
#|-- B03-e inf eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds inf
#|
#|-- B03-e inf raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds inf
#|
#|-- B03-e inf opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds inf
#|
#|-- B03-e neg-inf eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds -inf
#|
#|-- B03-e neg-inf raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds -inf
#|
#|-- B03-e neg-inf opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds -inf
#|
#|-- B03-e valid eager
#|frame
#|height	4
#|width	1
#|col	u32	"y"
#|row	0
#|row	4294967040
#|row	2
#|row	null
#|
#|-- B03-e valid raw
#|frame
#|height	4
#|width	1
#|col	u32	"y"
#|row	0
#|row	4294967040
#|row	2
#|row	null
#|
#|-- B03-e valid opt
#|frame
#|height	4
#|width	1
#|col	u32	"y"
#|row	0
#|row	4294967040
#|row	2
#|row	null
#|
#|-- B03-e negative schema
#|y:u32
#|
