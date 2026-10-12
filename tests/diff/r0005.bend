# T2.3 regression (bench/diff/reduce_regress.py, minimised by reduce.py --shrink): expectation = the contract
# (reduce_ref.py step model, DESIGN.md 15.5.3 / 15.5.4), never Bend's output. Kind: pin sel+grp sum
# ten 0.1: Neumaier gives 1.0 (0x3f800000; Polars' eager sum 0x3f800001); groups of 3 and 7 -> 0.3 and 0.7 correctly rounded.
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
  [DX.u(0), DX.u(0), DX.u(0), DX.u(1), DX.u(1), DX.u(1), DX.u(1), DX.u(1), DX.u(1), DX.u(1)]

def c00000_x0() -> List<&2, D.Scalar>:
  [DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1), DX.f(0.1)]

def c00000_f() -> DF.ResT(DF.Frame()):
  DX.frame([DX.cu32("g", c00000_g0()), DX.cf32("x", c00000_x0())])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(DX.show("c00000", "sel_e", DX.e_select(c00000_f(), [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")])))
    IO.print(DX.show("c00000", "grp_e", DX.e_group_by(c00000_f(), [DF.col("g")], [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")])))
    lz_full("c00000", "grp_f", DF.lazy_group_by(DX.src("t", c00000_f()), [DF.col("g")], [DF.alias(DF.sum(DF.col("x")), "s"), DF.alias(DF.mean(DF.col("x")), "m")]), DX.env1("t", c00000_f()))

#|-- c00000 sel_e
#|frame
#|height	1
#|width	2
#|col	f32	"s"
#|col	f32	"m"
#|row	0x3f800000	0x3dcccccd
#|p0 ok
#|
#|-- c00000 grp_e
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x3e99999a	0x3dcccccd
#|row	1	0x3f333333	0x3dcccccd
#|p0 ok
#|
#|-- c00000 grp_f
#|frame
#|height	2
#|width	3
#|col	u32	"g"
#|col	f32	"s"
#|col	f32	"m"
#|row	0	0x3e99999a	0x3dcccccd
#|row	1	0x3f333333	0x3dcccccd
#|p0 ok
