# B03-g (Fable B4): mean of integers is f32, documented in DESIGN but missing from the
# README differences (M1 README). DESIGN.md 15.2.5: Mean of u32/i32 is f32 (Polars f64:
# documented departure). Pinned through group_by (eager and lazy accept it today);
# 16777217 is not an f32, so the mean of [16777217, 16777219] shows the f32 rounding:
# each cell converts to f32 first (16777216, 16777220), mean 16777218. Passes today.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("g", [R.u(1), R.u(1), R.u(2), R.u(2)], D.TU32{}),
    R.mk("a", [R.u(1), R.u(2), R.u(16777217), R.u(16777219)], D.TU32{}),
    R.mk("ai", [R.ineg(1), R.ineg(2), R.i(3), R.i(4)], D.TI32{})])

def env() -> P.Env:
  R.env1("t", t())

def aggs() -> List<&2, X.Expr>:
  [DF.alias(DF.mean(DF.col("a")), "ma"), DF.alias(DF.mean(DF.col("ai")), "mai")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-g int-mean", R.e_group(t(), [DF.col("g")], aggs()), DF.lazy_group_by(R.src("t", t()), [DF.col("g")], aggs()), env(), env())
#|-- B03-g int-mean eager
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"ma"
#|col	f32	"mai"
#|row	1	0x3fc00000	0xbfc00000
#|row	2	0x4b800001	0x40600000
#|
#|-- B03-g int-mean raw
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"ma"
#|col	f32	"mai"
#|row	1	0x3fc00000	0xbfc00000
#|row	2	0x4b800001	0x40600000
#|
#|-- B03-g int-mean opt
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"ma"
#|col	f32	"mai"
#|row	1	0x3fc00000	0xbfc00000
#|row	2	0x4b800001	0x40600000
#|
