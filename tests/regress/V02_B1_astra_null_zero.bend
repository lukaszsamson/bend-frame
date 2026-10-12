# V02-B1: plans/REVIEW_V02_ASTRA.txt section 1, the reproduction plans/review_v02_astra/null_zero.bend kept as a
# passing regression: the default (fused) evaluator against the unfused Eval.full over x = [null, +0.0,
# -0.0, 2.0]. Before the fix the fused run's first row was 0x80000000 (-0.0) / 0xff800000 (-inf); both
# runs must now print the unfused answer (v0.1's and Polars').
import Base
import ./../../frame.bend as DF
import ./../../src/eval.bend as V
import ./../../src/dtype.bend as D
import ./../../src/column.bend as C
import ./../../src/err.bend as E
import ./../../tests/regress/lib/rx.bend as R

def base() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("x", [R.null(), R.f(0.0), R.f(F32.neg(0.0)), R.f(2.0)], D.TF32{})])

def expr() -> DF.Expr():
  DF.fill_null(DF.neg(DF.col("x")), DF.lit_f32(0.0))

def old(r: C.Frame & E.ResT(C.Column)) -> E.ResT(C.Frame):
  (f, c) = r
  match c:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      DF.from_columns([DF.named("x", x)])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("fused:\n" ++ DF.dump(DF.then(base(), f => DF.select(f, [expr()]))))
    IO.print("unfused:\n" ++ DF.dump(DF.then(base(), f => old(V.Eval.full(f, expr())))))
#|fused:
#|frame
#|height	4
#|width	1
#|col	f32	"x"
#|row	0x00000000
#|row	0x80000000
#|row	0x00000000
#|row	0xc0000000
#|
#|unfused:
#|frame
#|height	4
#|width	1
#|col	f32	"x"
#|row	0x00000000
#|row	0x80000000
#|row	0x00000000
#|row	0xc0000000
#|
