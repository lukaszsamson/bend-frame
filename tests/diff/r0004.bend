# T2.3 regression (bench/diff/reduce_regress.py, minimised by reduce.py --shrink): expectation = the contract
# (reduce_ref.py step model, DESIGN.md 15.5.3 / 15.5.4), never Bend's output. Kind: pin sel+grp sum
# non-finite data per 15.5.3: [inf, 1] and [1, inf] -> inf, [inf, -inf] -> NaN, [NaN, 1] -> NaN; the guard makes an overflowing partial
# sum final ([3e38, 3e38, -3e38] -> inf although the exact sum is finite); sums of -0.0 are +0.0 (the accumulator starts at +0.0).
#
import Base
import ./../../frame.bend as DF
import ./lib/dx.bend as DX
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P

def lz_raw(+tag: String, +how: String, +p: P.Plan, e: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- DF.collect_raw(p, e)
    IO.print(DX.show(tag, how, r))

def lz_full(+tag: String, +how: String, +p: P.Plan, e: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- DF.collect_full(p, e)
    IO.print(DX.show(tag, how, r))

def c00000_g0() -> List<&2, D.Scalar>:
  [DX.u(0), DX.u(0), DX.u(1), DX.u(1), DX.u(2), DX.u(2), DX.u(3), DX.u(3), DX.u(4), DX.u(4), DX.u(4), DX.u(5), DX.u(5), DX.u(6), DX.u(6)]

def c00000_x0() -> List<&2, D.Scalar>:
  [DX.f(DX.inf()), DX.f(1.0), DX.f(1.0), DX.f(DX.inf()), DX.f(DX.inf()), DX.f(DX.ninf()), DX.f(DX.nan()), DX.f(1.0), DX.f(300000000000000000000000000000000000000.0), DX.f(300000000000000000000000000000000000000.0), DX.f(F32.neg(300000000000000000000000000000000000000.0)), DX.f(DX.nzero()), DX.f(DX.nzero()), DX.f(5.0), DX.f(DX.nzero())]

def c00000_f() -> DF.ResT(DF.Frame()):
  DX.frame([DX.cu32("g", c00000_g0()), DX.cf32("x", c00000_x0())])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(DX.show("c00000", "sel_e", DX.e_select(c00000_f(), [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")])))
    lz_raw("c00000", "sel_r", DF.lazy_select(DX.src("t", c00000_f()), [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")]), DX.env1("t", c00000_f()))
    lz_full("c00000", "sel_f", DF.lazy_select(DX.src("t", c00000_f()), [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")]), DX.env1("t", c00000_f()))
    IO.print(DX.show("c00000", "grp_e", DX.e_group_by(c00000_f(), [DF.col("g")], [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")])))
    lz_raw("c00000", "grp_r", DF.lazy_group_by(DX.src("t", c00000_f()), [DF.col("g")], [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")]), DX.env1("t", c00000_f()))
    lz_full("c00000", "grp_f", DF.lazy_group_by(DX.src("t", c00000_f()), [DF.col("g")], [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")]), DX.env1("t", c00000_f()))

#|-- c00000 sel_e
#|frame
#|height	1
#|width	2
#|col	f32	"s"
#|col	f32	"m"
#|row	0x7fc00000	0x7fc00000
#|
#|-- c00000 sel_r
#|frame
#|height	1
#|width	2
#|col	f32	"s"
#|col	f32	"m"
#|row	0x7fc00000	0x7fc00000
#|
#|-- c00000 sel_f
#|frame
#|height	1
#|width	2
#|col	f32	"s"
#|col	f32	"m"
#|row	0x7fc00000	0x7fc00000
#|
#|-- c00000 grp_e
#|frame
#|height	7
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x7f800000	0x7f800000
#|row	1	0x7f800000	0x7f800000
#|row	2	0x7fc00000	0x7fc00000
#|row	3	0x7fc00000	0x7fc00000
#|row	4	0x7f800000	0x7f800000
#|row	5	0x00000000	0x00000000
#|row	6	0x40a00000	0x40200000
#|
#|-- c00000 grp_r
#|frame
#|height	7
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x7f800000	0x7f800000
#|row	1	0x7f800000	0x7f800000
#|row	2	0x7fc00000	0x7fc00000
#|row	3	0x7fc00000	0x7fc00000
#|row	4	0x7f800000	0x7f800000
#|row	5	0x00000000	0x00000000
#|row	6	0x40a00000	0x40200000
#|
#|-- c00000 grp_f
#|frame
#|height	7
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x7f800000	0x7f800000
#|row	1	0x7f800000	0x7f800000
#|row	2	0x7fc00000	0x7fc00000
#|row	3	0x7fc00000	0x7fc00000
#|row	4	0x7f800000	0x7f800000
#|row	5	0x00000000	0x00000000
#|row	6	0x40a00000	0x40200000
