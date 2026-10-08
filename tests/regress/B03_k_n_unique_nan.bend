#! xfail B03-k
# B03-k (DESIGN 14 M5.5): top-level n_unique counts each NaN apart; grouped counts NaN
# once. DESIGN.md 15.2.5 NUnique: distinct values under the 15.5.2 relation (every NaN one
# value, -0.0 = 0.0), plus one if any null, both eager and grouped.
# x = [NaN, -NaN, -0.0, 0.0, 1, null] -> {NaN, 0, 1} + null = 4. Polars 2.0.0: 4
# (regress_expect.py). The lazy select also needs B04-a.
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
    R.mk("g", [R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(1)], D.TU32{}),
    R.mk("x", [R.f(R.nan()), R.f(F32.neg(R.nan())), R.f(R.nzero()), R.f(0.0), R.f(1.0), R.null()], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def nu() -> List<&2, X.Expr>:
  [DF.alias(DF.n_unique(DF.col("x")), "n")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-k select", R.e_select(t(), nu()), DF.lazy_select(src(), nu()), env(), env())
    R.three("B03-k group", R.e_group(t(), [DF.col("g")], nu()), DF.lazy_group_by(src(), [DF.col("g")], nu()), env(), env())
#|-- B03-k select eager
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	4
#|
#|-- B03-k select raw
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	4
#|
#|-- B03-k select opt
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	4
#|
#|-- B03-k group eager
#|frame
#|height	1
#|width	2
#|col	u32	"g"
#|col	u32	"n"
#|row	1	4
#|
#|-- B03-k group raw
#|frame
#|height	1
#|width	2
#|col	u32	"g"
#|col	u32	"n"
#|row	1	4
#|
#|-- B03-k group opt
#|frame
#|height	1
#|width	2
#|col	u32	"g"
#|col	u32	"n"
#|row	1	4
#|
