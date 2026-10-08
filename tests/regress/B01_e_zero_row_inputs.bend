#! xfail B01-e
# B01-e: zero-row inputs through literal-only, reduction and mixed selects, with_columns,
# filter and group_by. DESIGN.md 15.4 C3, C7, C10, C13, C14, C21, C26: a select of only
# literals / only reductions is one row even on h = 0; sum/count/len/n_unique of nothing
# are 0, mean/min/max/first/last are null; with_columns and filter keep h = 0; group_by
# gives (0, keys + aggs). Polars 2.0.0: bench/contract/cardinality.py (mean is f64 there,
# f32 here: 15.2.5). The reduction cases also need B04-a (lazy accepts reductions).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

# t0: a u32, x f32, no rows
def t0() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [], D.TU32{}), R.mk("x", [], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t0())

def src() -> P.Plan:
  R.src("t", t0())

def a() -> X.Expr:
  DF.col("a")

def one() -> X.Expr:
  DF.alias(DF.lit_u32(1), "one")

# every reducer over the empty column, one row
def reds() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(a()), "sum"), DF.alias(DF.mean(a()), "mean"), DF.alias(DF.min(a()), "min"), DF.alias(DF.max(a()), "max"), DF.alias(DF.first(a()), "first"), DF.alias(DF.last(a()), "last"), DF.alias(DF.count(a()), "count"), DF.alias(DF.len(), "len"), DF.alias(DF.n_unique(a()), "n_unique")]

def mixed() -> List<&2, X.Expr>:
  [a(), DF.alias(DF.sum(a()), "s")]

def main() -> IO(Unit):
  do IO<Unit>:
    # C3: select([lit 1]) on h = 0 -> (1, 1)
    R.three("B01-e C3 literal-select", R.e_select(t0(), [one()]), DF.lazy_select(src(), [one()]), env(), env())
    # C7: every reducer on h = 0 -> one row
    R.three("B01-e C7 reductions", R.e_select(t0(), reds()), DF.lazy_select(src(), reds()), env(), env())
    # C10: select([a, sum(a) as s]) on h = 0 -> (0, 2)
    R.three("B01-e C10 mixed-select", R.e_select(t0(), mixed()), DF.lazy_select(src(), mixed()), env(), env())
    # C13: with_columns([sum(a) as s]) on h = 0 -> (0, 3)
    R.three("B01-e C13 with-reduction", R.e_with(t0(), [DF.alias(DF.sum(a()), "s")]), DF.lazy_with_columns(src(), [DF.alias(DF.sum(a()), "s")]), env(), env())
    # C14: with_columns([lit 1 as one]) on h = 0 -> (0, 3)
    R.three("B01-e C14 with-literal", R.e_with(t0(), [one()]), DF.lazy_with_columns(src(), [one()]), env(), env())
    # C21: filter(a > 1) on h = 0 -> (0, 2)
    R.three("B01-e C21 filter", R.e_filter(t0(), DF.gt(a(), DF.lit_u32(1))), DF.lazy_filter(src(), DF.gt(a(), DF.lit_u32(1))), env(), env())
    # C26: group_by on h = 0 -> (0, 2)
    R.three("B01-e C26 group-by", R.e_group(t0(), [a()], [DF.alias(DF.count(DF.col("x")), "n")]), DF.lazy_group_by(src(), [a()], [DF.alias(DF.count(DF.col("x")), "n")]), env(), env())
#|-- B01-e C3 literal-select eager
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-e C3 literal-select raw
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-e C3 literal-select opt
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-e C7 reductions eager
#|frame
#|height	1
#|width	9
#|col	u32	"sum"
#|col	f32	"mean"
#|col	u32	"min"
#|col	u32	"max"
#|col	u32	"first"
#|col	u32	"last"
#|col	u32	"count"
#|col	u32	"len"
#|col	u32	"n_unique"
#|row	0	null	null	null	null	null	0	0	0
#|
#|-- B01-e C7 reductions raw
#|frame
#|height	1
#|width	9
#|col	u32	"sum"
#|col	f32	"mean"
#|col	u32	"min"
#|col	u32	"max"
#|col	u32	"first"
#|col	u32	"last"
#|col	u32	"count"
#|col	u32	"len"
#|col	u32	"n_unique"
#|row	0	null	null	null	null	null	0	0	0
#|
#|-- B01-e C7 reductions opt
#|frame
#|height	1
#|width	9
#|col	u32	"sum"
#|col	f32	"mean"
#|col	u32	"min"
#|col	u32	"max"
#|col	u32	"first"
#|col	u32	"last"
#|col	u32	"count"
#|col	u32	"len"
#|col	u32	"n_unique"
#|row	0	null	null	null	null	null	0	0	0
#|
#|-- B01-e C10 mixed-select eager
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|
#|-- B01-e C10 mixed-select raw
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|
#|-- B01-e C10 mixed-select opt
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|
#|-- B01-e C13 with-reduction eager
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|
#|-- B01-e C13 with-reduction raw
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|
#|-- B01-e C13 with-reduction opt
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|
#|-- B01-e C14 with-literal eager
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"one"
#|
#|-- B01-e C14 with-literal raw
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"one"
#|
#|-- B01-e C14 with-literal opt
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"one"
#|
#|-- B01-e C21 filter eager
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|
#|-- B01-e C21 filter raw
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|
#|-- B01-e C21 filter opt
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|
#|-- B01-e C26 group-by eager
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"n"
#|
#|-- B01-e C26 group-by raw
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"n"
#|
#|-- B01-e C26 group-by opt
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"n"
#|
