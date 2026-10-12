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
