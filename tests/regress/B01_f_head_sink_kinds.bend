#! xfail B01-f
# B01-f: Opt.head sinks below every Select/WithColumns whatever its expressions are. It
# may only sink below a node whose expressions are all KRow and total, with a non-empty
# list (DESIGN.md 15.3.2 design note ii, 15.4 rule): a reduction computed over the full
# input must not be recomputed over the first n rows. Polars 2.0.0: same programs in
# bench/contract/regress_expect.py. Needs B04-a (lazy accepts reductions) as well.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

# t: a u32 1..6, x f32 1..6
def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{}), R.mk("x", [R.f(1.0), R.f(2.0), R.f(3.0), R.f(4.0), R.f(5.0), R.f(6.0)], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def s() -> X.Expr:
  DF.alias(DF.sum(DF.col("a")), "s")

def d() -> X.Expr:
  DF.alias(DF.sub(DF.col("x"), DF.mean(DF.col("x"))), "d")

def main() -> IO(Unit):
  do IO<Unit>:
    # head(2) over with_columns([sum(a) as s]): s is the sum of all six rows (21)
    R.three("B01-f head2-over-with-sum", R.e_head(R.e_with(t(), [s()]), 2), DF.lazy_head(DF.lazy_with_columns(src(), [s()]), 2), env(), env())
    # head(1) over select([a, sum(a) as s]) (mixed: height preserving, s still 21)
    R.three("B01-f head1-over-mixed-select", R.e_head(R.e_select(t(), [DF.col("a"), s()]), 1), DF.lazy_head(DF.lazy_select(src(), [DF.col("a"), s()]), 1), env(), env())
    # head(0) over select([sum(a)]) (KRed only: a height barrier) -> (0, 1)
    R.three("B01-f head0-over-reduction-select", R.e_head(R.e_select(t(), [s()]), 0), DF.lazy_head(DF.lazy_select(src(), [s()]), 0), env(), env())
    # head(2) over select([x - mean(x) as d]): mean over all six rows (3.5)
    R.three("B01-f head2-over-centered", R.e_head(R.e_select(t(), [d()]), 2), DF.lazy_head(DF.lazy_select(src(), [d()]), 2), env(), env())
    # head(2) over select([a, a * 2 as b]) (KRow, total): sinking is allowed and harmless
    R.three("B01-f head2-over-row-select", R.e_head(R.e_select(t(), [DF.col("a"), DF.alias(DF.mul(DF.col("a"), DF.lit_u32(2)), "b")]), 2), DF.lazy_head(DF.lazy_select(src(), [DF.col("a"), DF.alias(DF.mul(DF.col("a"), DF.lit_u32(2)), "b")]), 2), env(), env())
#|-- B01-f head2-over-with-sum eager
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|row	1	0x3f800000	21
#|row	2	0x40000000	21
#|
#|-- B01-f head2-over-with-sum raw
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|row	1	0x3f800000	21
#|row	2	0x40000000	21
#|
#|-- B01-f head2-over-with-sum opt
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|row	1	0x3f800000	21
#|row	2	0x40000000	21
#|
#|-- B01-f head1-over-mixed-select eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|row	1	21
#|
#|-- B01-f head1-over-mixed-select raw
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|row	1	21
#|
#|-- B01-f head1-over-mixed-select opt
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|row	1	21
#|
#|-- B01-f head0-over-reduction-select eager
#|frame
#|height	0
#|width	1
#|col	u32	"s"
#|
#|-- B01-f head0-over-reduction-select raw
#|frame
#|height	0
#|width	1
#|col	u32	"s"
#|
#|-- B01-f head0-over-reduction-select opt
#|frame
#|height	0
#|width	1
#|col	u32	"s"
#|
#|-- B01-f head2-over-centered eager
#|frame
#|height	2
#|width	1
#|col	f32	"d"
#|row	0xc0200000
#|row	0xbfc00000
#|
#|-- B01-f head2-over-centered raw
#|frame
#|height	2
#|width	1
#|col	f32	"d"
#|row	0xc0200000
#|row	0xbfc00000
#|
#|-- B01-f head2-over-centered opt
#|frame
#|height	2
#|width	1
#|col	f32	"d"
#|row	0xc0200000
#|row	0xbfc00000
#|
#|-- B01-f head2-over-row-select eager
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	2	4
#|
#|-- B01-f head2-over-row-select raw
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	2	4
#|
#|-- B01-f head2-over-row-select opt
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	2	4
#|
