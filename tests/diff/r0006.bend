# T2.3 regression (bench/diff/reduce_regress.py, minimised by reduce.py --shrink): expectation = the contract
# (reduce_ref.py step model, DESIGN.md 15.5.3 / 15.5.4), never Bend's output. Kind: pin desc std
# describe of [1, null, 2, 4, null]: mean 7/3, std by the two-pass step model (15.5.4). Note DESIGN.md 15.5.4 quotes the correctly rounded
# std 1.5275252 / var 2.3333333; the specified algorithm (squares rounded to f32) gives 1.5275253 (0x3fc385f3), one ulp above, inside bound (3).
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
  [DX.u(0), DX.u(0), DX.u(0), DX.u(0), DX.u(0)]

def c00000_x0() -> List<&2, D.Scalar>:
  [DX.f(1.0), DX.n(), DX.f(2.0), DX.f(4.0), DX.n()]

def c00000_f() -> DF.ResT(DF.Frame()):
  DX.frame([DX.cu32("g", c00000_g0()), DX.cf32("x", c00000_x0())])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(DX.show("c00000", "desc", DF.describe(DX.e_select(c00000_f(), [DF.col("x")]))))

#|-- c00000 desc
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"x"
#|row	"count"	0x40400000
#|row	"null_count"	0x40000000
#|row	"mean"	0x40155555
#|row	"std"	0x3fc385f3
#|row	"min"	0x3f800000
#|row	"25%"	0x40000000
#|row	"50%"	0x40000000
#|row	"75%"	0x40800000
#|row	"max"	0x40800000
