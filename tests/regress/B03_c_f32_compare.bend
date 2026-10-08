# B03-c (Astra D): f32 == and > use raw IEEE predicates (NaN == NaN false, NaN > 0
# false) while sort/group/join keys use a total order. DESIGN.md 15.5.2: every f32
# comparison is U32.cmp of Sort.fword: -inf < .. < -0.0 = 0.0 < .. < inf < NaN, all NaNs
# equal; null stays null. x = [NaN, 1, -0.0, 0.0, inf, -inf, null]; the contract lists
# x == x, x > 0.0, x < NaN, x >= NaN; Polars 2.0.0 agrees on all eight columns below
# (regress_expect.py).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("x", [R.f(R.nan()), R.f(1.0), R.f(R.nzero()), R.f(0.0), R.f(R.inf()), R.f(R.ninf()), R.null()], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def x() -> X.Expr:
  DF.col("x")

def nan() -> X.Expr:
  DF.lit_f32(R.nan())

def cmps() -> List<&2, X.Expr>:
  [DF.alias(DF.eq(x(), x()), "eq"), DF.alias(DF.ne(x(), x()), "ne"), DF.alias(DF.gt(x(), DF.lit_f32(0.0)), "gt0"), DF.alias(DF.eq(x(), DF.lit_f32(0.0)), "eq0"), DF.alias(DF.lt(x(), nan()), "ltnan"), DF.alias(DF.ge(x(), nan()), "genan"), DF.alias(DF.le(x(), DF.lit_f32(R.nzero())), "lenz"), DF.alias(DF.lt(x(), DF.lit_f32(R.inf())), "ltinf")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-c compare", R.e_with(t(), cmps()), DF.lazy_with_columns(src(), cmps()), env(), env())
    # the relation also decides filter
    R.three("B03-c filter-ge-nan", R.e_filter(t(), DF.ge(x(), nan())), DF.lazy_filter(src(), DF.ge(x(), nan())), env(), env())
#|-- B03-c compare eager
#|frame
#|height	7
#|width	9
#|col	f32	"x"
#|col	bool	"eq"
#|col	bool	"ne"
#|col	bool	"gt0"
#|col	bool	"eq0"
#|col	bool	"ltnan"
#|col	bool	"genan"
#|col	bool	"lenz"
#|col	bool	"ltinf"
#|row	0x7fc00000	true	false	true	false	false	true	false	false
#|row	0x3f800000	true	false	true	false	true	false	false	true
#|row	0x80000000	true	false	false	true	true	false	true	true
#|row	0x00000000	true	false	false	true	true	false	true	true
#|row	0x7f800000	true	false	true	false	true	false	false	false
#|row	0xff800000	true	false	false	false	true	false	true	true
#|row	null	null	null	null	null	null	null	null	null
#|
#|-- B03-c compare raw
#|frame
#|height	7
#|width	9
#|col	f32	"x"
#|col	bool	"eq"
#|col	bool	"ne"
#|col	bool	"gt0"
#|col	bool	"eq0"
#|col	bool	"ltnan"
#|col	bool	"genan"
#|col	bool	"lenz"
#|col	bool	"ltinf"
#|row	0x7fc00000	true	false	true	false	false	true	false	false
#|row	0x3f800000	true	false	true	false	true	false	false	true
#|row	0x80000000	true	false	false	true	true	false	true	true
#|row	0x00000000	true	false	false	true	true	false	true	true
#|row	0x7f800000	true	false	true	false	true	false	false	false
#|row	0xff800000	true	false	false	false	true	false	true	true
#|row	null	null	null	null	null	null	null	null	null
#|
#|-- B03-c compare opt
#|frame
#|height	7
#|width	9
#|col	f32	"x"
#|col	bool	"eq"
#|col	bool	"ne"
#|col	bool	"gt0"
#|col	bool	"eq0"
#|col	bool	"ltnan"
#|col	bool	"genan"
#|col	bool	"lenz"
#|col	bool	"ltinf"
#|row	0x7fc00000	true	false	true	false	false	true	false	false
#|row	0x3f800000	true	false	true	false	true	false	false	true
#|row	0x80000000	true	false	false	true	true	false	true	true
#|row	0x00000000	true	false	false	true	true	false	true	true
#|row	0x7f800000	true	false	true	false	true	false	false	false
#|row	0xff800000	true	false	false	false	true	false	true	true
#|row	null	null	null	null	null	null	null	null	null
#|
#|-- B03-c filter-ge-nan eager
#|frame
#|height	1
#|width	1
#|col	f32	"x"
#|row	0x7fc00000
#|
#|-- B03-c filter-ge-nan raw
#|frame
#|height	1
#|width	1
#|col	f32	"x"
#|row	0x7fc00000
#|
#|-- B03-c filter-ge-nan opt
#|frame
#|height	1
#|width	1
#|col	f32	"x"
#|row	0x7fc00000
#|
