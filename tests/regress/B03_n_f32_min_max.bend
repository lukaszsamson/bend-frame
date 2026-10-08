#! xfail B03-n
# B03-n: f32 min/max depend on NaN position (F32.min(NaN, 1) = 1, F32.min(1, NaN) = NaN)
# and on the sign of zero. DESIGN.md 15.5.2 exceptions: min/max skip NaN (all-NaN -> NaN);
# on a -0.0 / 0.0 tie min answers -0.0 and max 0.0, in both input orders.
#   p [NaN, 2, 1] -> 1, 2   q [NaN, NaN] -> NaN, NaN   v [1, NaN] -> 1, 1
#   r [-0.0, 0.0] -> -0.0, 0.0   w [0.0, -0.0] -> -0.0, 0.0
# Polars 2.0.0 agrees (regress_expect.py). Eager select, lazy select (needs B04-a too),
# and grouped (one group).
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
    R.mk("g", [R.u(1), R.u(1), R.u(1)], D.TU32{}),
    R.mk("p", [R.f(R.nan()), R.f(2.0), R.f(1.0)], D.TF32{}),
    R.mk("q", [R.f(R.nan()), R.f(R.nan()), R.null()], D.TF32{}),
    R.mk("v", [R.f(1.0), R.f(R.nan()), R.null()], D.TF32{}),
    R.mk("r", [R.f(R.nzero()), R.f(0.0), R.null()], D.TF32{}),
    R.mk("w", [R.f(0.0), R.f(R.nzero()), R.null()], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def mm(+n: String) -> List<&2, X.Expr>:
  [DF.alias(DF.min(DF.col(n)), "min_" ++ n), DF.alias(DF.max(DF.col(n)), "max_" ++ n)]

def es() -> List<&2, X.Expr>:
  List.concat(&2, X.Expr, [mm("p"), mm("q"), mm("v"), mm("r"), mm("w")])

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-n select", R.e_select(t(), es()), DF.lazy_select(src(), es()), env(), env())
    R.three("B03-n group", R.e_group(t(), [DF.col("g")], es()), DF.lazy_group_by(src(), [DF.col("g")], es()), env(), env())
#|-- B03-n select eager
#|frame
#|height	1
#|width	10
#|col	f32	"min_p"
#|col	f32	"max_p"
#|col	f32	"min_q"
#|col	f32	"max_q"
#|col	f32	"min_v"
#|col	f32	"max_v"
#|col	f32	"min_r"
#|col	f32	"max_r"
#|col	f32	"min_w"
#|col	f32	"max_w"
#|row	0x3f800000	0x40000000	0x7fc00000	0x7fc00000	0x3f800000	0x3f800000	0x80000000	0x00000000	0x80000000	0x00000000
#|
#|-- B03-n select raw
#|frame
#|height	1
#|width	10
#|col	f32	"min_p"
#|col	f32	"max_p"
#|col	f32	"min_q"
#|col	f32	"max_q"
#|col	f32	"min_v"
#|col	f32	"max_v"
#|col	f32	"min_r"
#|col	f32	"max_r"
#|col	f32	"min_w"
#|col	f32	"max_w"
#|row	0x3f800000	0x40000000	0x7fc00000	0x7fc00000	0x3f800000	0x3f800000	0x80000000	0x00000000	0x80000000	0x00000000
#|
#|-- B03-n select opt
#|frame
#|height	1
#|width	10
#|col	f32	"min_p"
#|col	f32	"max_p"
#|col	f32	"min_q"
#|col	f32	"max_q"
#|col	f32	"min_v"
#|col	f32	"max_v"
#|col	f32	"min_r"
#|col	f32	"max_r"
#|col	f32	"min_w"
#|col	f32	"max_w"
#|row	0x3f800000	0x40000000	0x7fc00000	0x7fc00000	0x3f800000	0x3f800000	0x80000000	0x00000000	0x80000000	0x00000000
#|
#|-- B03-n group eager
#|frame
#|height	1
#|width	11
#|col	u32	"g"
#|col	f32	"min_p"
#|col	f32	"max_p"
#|col	f32	"min_q"
#|col	f32	"max_q"
#|col	f32	"min_v"
#|col	f32	"max_v"
#|col	f32	"min_r"
#|col	f32	"max_r"
#|col	f32	"min_w"
#|col	f32	"max_w"
#|row	1	0x3f800000	0x40000000	0x7fc00000	0x7fc00000	0x3f800000	0x3f800000	0x80000000	0x00000000	0x80000000	0x00000000
#|
#|-- B03-n group raw
#|frame
#|height	1
#|width	11
#|col	u32	"g"
#|col	f32	"min_p"
#|col	f32	"max_p"
#|col	f32	"min_q"
#|col	f32	"max_q"
#|col	f32	"min_v"
#|col	f32	"max_v"
#|col	f32	"min_r"
#|col	f32	"max_r"
#|col	f32	"min_w"
#|col	f32	"max_w"
#|row	1	0x3f800000	0x40000000	0x7fc00000	0x7fc00000	0x3f800000	0x3f800000	0x80000000	0x00000000	0x80000000	0x00000000
#|
#|-- B03-n group opt
#|frame
#|height	1
#|width	11
#|col	u32	"g"
#|col	f32	"min_p"
#|col	f32	"max_p"
#|col	f32	"min_q"
#|col	f32	"max_q"
#|col	f32	"min_v"
#|col	f32	"max_v"
#|col	f32	"min_r"
#|col	f32	"max_r"
#|col	f32	"min_w"
#|col	f32	"max_w"
#|row	1	0x3f800000	0x40000000	0x7fc00000	0x7fc00000	0x3f800000	0x3f800000	0x80000000	0x00000000	0x80000000	0x00000000
#|
