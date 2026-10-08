# T2.3 regression (bench/diff/reduce_regress.py, minimised by reduce.py --shrink): expectation = the contract
# (reduce_ref.py step model, DESIGN.md 15.5.3 / 15.5.4), never Bend's output. Kind: pin sel+grp sum
# cancellation: group 0 = [1e8, 1, -1e8, 0.25] sums to 1.25 and group 1 = [1e16, 0.5, -1e16] to 0.5 (a naive f32 sum answers 0.25 / 0);
# the null row is skipped; eager, raw lazy and optimised lazy agree. The select sums all seven valid rows to 0.25, not the exact 1.75: c is itself
# an f32, and bound (1) (gamma^2 * sum|x| ~ 2.6e3 here) allows it; the step model, not the exact sum, is the contract.
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
  [DX.u(0), DX.u(1), DX.u(0), DX.u(1), DX.u(0), DX.u(1), DX.u(0), DX.u(1)]

def c00000_x0() -> List<&2, D.Scalar>:
  [DX.f(100000000.0), DX.f(10000000000000000.0), DX.f(1.0), DX.f(0.5), DX.f(F32.neg(100000000.0)), DX.f(F32.neg(10000000000000000.0)), DX.f(0.25), DX.n()]

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
#|row	0x3e800000	0x3d124925
#|
#|-- c00000 sel_r
#|frame
#|height	1
#|width	2
#|col	f32	"s"
#|col	f32	"m"
#|row	0x3e800000	0x3d124925
#|
#|-- c00000 sel_f
#|frame
#|height	1
#|width	2
#|col	f32	"s"
#|col	f32	"m"
#|row	0x3e800000	0x3d124925
#|
#|-- c00000 grp_e
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x3fa00000	0x3ea00000
#|row	1	0x3f000000	0x3e2aaaab
#|
#|-- c00000 grp_r
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x3fa00000	0x3ea00000
#|row	1	0x3f000000	0x3e2aaaab
#|
#|-- c00000 grp_f
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x3fa00000	0x3ea00000
#|row	1	0x3f000000	0x3e2aaaab
