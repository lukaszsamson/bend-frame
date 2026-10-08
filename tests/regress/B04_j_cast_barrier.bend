# B04-j: once cast is strict, a filter merge / pushdown or a head sink across a fallible
# cast changes which rows reach it, hence whether (and at which row) it fails. DESIGN.md
# 15.3.2 design note i: Cast of a fallible pair is a barrier for every rewrite that can
# change which rows reach it; eager, raw lazy and optimised lazy must give the same dump,
# errors included (15.1 rule 7). x = [1.0, -5.0, 3.0]: cast(x, u32) fails at row 1.
# (Today cast is lenient, -5 -> 0: every case differs from the contract.)
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../../src/expr.bend as X
import ./../../src/join.bend as J
import ./../../src/groupby.bend as G
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.u(3)], D.TU32{}), R.mk("x", [R.f(1.0), R.f(F32.neg(5.0)), R.f(3.0)], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def y() -> X.Expr:
  DF.alias(DF.cast_u32(DF.col("x")), "y")

def not2() -> X.Expr:
  DF.ne(DF.col("a"), DF.lit_u32(2))

def ypos() -> X.Expr:
  DF.ge(DF.cast_u32(DF.col("x")), DF.lit_u32(1))

def main() -> IO(Unit):
  do IO<Unit>:
    # the select casts all rows first: error at row 1 (a pushdown of a != 2 would hide it)
    R.three("B04-j filter-over-cast-select", R.e_filter(R.e_select(t(), [DF.col("a"), y()]), not2()), DF.lazy_filter(DF.lazy_select(src(), [DF.col("a"), y()]), not2()), env(), env())
    # head(1) over the cast: the cast still sees row 1 (a head sink would hide it)
    R.three("B04-j head-over-cast-select", R.e_head(R.e_select(t(), [y()]), 1), DF.lazy_head(DF.lazy_select(src(), [y()]), 1), env(), env())
    R.three("B04-j head-over-cast-with", R.e_head(R.e_with(t(), [y()]), 1), DF.lazy_head(DF.lazy_with_columns(src(), [y()]), 1), env(), env())
    # the inner filter removes row 1 before the cast runs: success (merging the two
    # filters into one And would evaluate the cast on row 1)
    R.three("B04-j cast-filter-over-filter", R.e_filter(R.e_filter(t(), not2()), ypos()), DF.lazy_filter(DF.lazy_filter(src(), not2()), ypos()), env(), env())
    # a filter below the cast: the failing cell is row 0 of the filtered column
    R.three("B04-j cast-after-filter-row-index", R.e_select(R.e_filter(t(), DF.ne(DF.col("a"), DF.lit_u32(1))), [y()]), DF.lazy_select(DF.lazy_filter(src(), DF.ne(DF.col("a"), DF.lit_u32(1))), [y()]), env(), env())
#|-- B04-j filter-over-cast-select eager
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j filter-over-cast-select raw
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j filter-over-cast-select opt
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j head-over-cast-select eager
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j head-over-cast-select raw
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j head-over-cast-select opt
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j head-over-cast-with eager
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j head-over-cast-with raw
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j head-over-cast-with opt
#|error	InvalidOperation: cast f32 to u32: row 1 holds -5
#|
#|-- B04-j cast-filter-over-filter eager
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	1	0x3f800000
#|row	3	0x40400000
#|
#|-- B04-j cast-filter-over-filter raw
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	1	0x3f800000
#|row	3	0x40400000
#|
#|-- B04-j cast-filter-over-filter opt
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	1	0x3f800000
#|row	3	0x40400000
#|
#|-- B04-j cast-after-filter-row-index eager
#|error	InvalidOperation: cast f32 to u32: row 0 holds -5
#|
#|-- B04-j cast-after-filter-row-index raw
#|error	InvalidOperation: cast f32 to u32: row 0 holds -5
#|
#|-- B04-j cast-after-filter-row-index opt
#|error	InvalidOperation: cast f32 to u32: row 0 holds -5
#|
