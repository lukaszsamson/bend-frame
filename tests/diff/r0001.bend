# T2.3 regression (bench/diff/reduce_regress.py, minimised by reduce.py --shrink): expectation = the contract
# (reduce_ref.py step model, DESIGN.md 15.5.3 / 15.5.4), never Bend's output. Kind: minmax desc max
# describe max of [NaN, 1, 2] must be 2 (and min 1): the min/max rule of 15.5.2 skips NaN; Polars 2.0.0 describe agrees.
# Fixed (NEW-T23-1): describe takes min/max from Eval.agg Min/Max (K.Kernel.fmin/fmax), not from the NaN-greatest sort.
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
  [DX.u(0), DX.u(0), DX.u(0)]

def c00000_x0() -> List<&2, D.Scalar>:
  [DX.f(DX.nan()), DX.f(1.0), DX.f(2.0)]

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
#|row	"null_count"	0x00000000
#|row	"mean"	0x7fc00000
#|row	"std"	0x7fc00000
#|row	"min"	0x3f800000
#|row	"25%"	0x40000000
#|row	"50%"	0x40000000
#|row	"75%"	0x7fc00000
#|row	"max"	0x40000000
