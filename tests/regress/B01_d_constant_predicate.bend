#! xfail B01-d
# B01-d: a constant (KScalar) predicate over a literal projection. DESIGN.md 15.4 C18-C20:
# a scalar predicate broadcasts to the input height in every API. Polars' LAZY engine
# answers (1, 1) for select(lit 1).filter(lit false) (it does not apply a 1-row scalar
# predicate); eager Polars answers (0, 1). The contract follows the eager answer: an
# intended departure (README). The `one == 2` case is Astra's probe (all APIs (0, 1)).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.u(3)], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def one() -> X.Expr:
  DF.alias(DF.lit_u32(1), "one")

def tr() -> X.Expr:
  DF.lit_bool(True{})

def fa() -> X.Expr:
  DF.lit_bool(False{})

# the typed null literal (DF.lit_null is M1 API; this is its definition, 15.2.1)
def nb() -> X.Expr:
  DF.cast(X.Lit{D.SNull{}}, D.TBool{})

def two() -> X.Expr:
  DF.eq(DF.col("one"), DF.lit_u32(2))

def main() -> IO(Unit):
  do IO<Unit>:
    # C19: select([lit 1]).filter(lit false) -> (0, 1) (Polars lazy: (1, 1), departure)
    R.three("B01-d C19 literal-select-filter-false", R.e_filter(R.e_select(t(), [one()]), fa()), DF.lazy_filter(DF.lazy_select(src(), [one()]), fa()), env(), env())
    R.three("B01-d C19 literal-select-filter-true", R.e_filter(R.e_select(t(), [one()]), tr()), DF.lazy_filter(DF.lazy_select(src(), [one()]), tr()), env(), env())
    # Astra's probe: select([lit 1 as one]).filter(one == 2) -> (0, 1)
    R.three("B01-d literal-select-filter-one-eq-2", R.e_filter(R.e_select(t(), [one()]), two()), DF.lazy_filter(DF.lazy_select(src(), [one()]), two()), env(), env())
    # C18: filter(lit true) / filter(lit false) over a 3-row frame
    R.three("B01-d C18 filter-true", R.e_filter(t(), tr()), DF.lazy_filter(src(), tr()), env(), env())
    R.three("B01-d C18 filter-false", R.e_filter(t(), fa()), DF.lazy_filter(src(), fa()), env(), env())
    # C20: filter(lit null::bool) -> (0, w)
    R.three("B01-d C20 filter-null", R.e_filter(t(), nb()), DF.lazy_filter(src(), nb()), env(), env())
#|-- B01-d C19 literal-select-filter-false eager
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-d C19 literal-select-filter-false raw
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-d C19 literal-select-filter-false opt
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-d C19 literal-select-filter-true eager
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-d C19 literal-select-filter-true raw
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-d C19 literal-select-filter-true opt
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-d literal-select-filter-one-eq-2 eager
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-d literal-select-filter-one-eq-2 raw
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-d literal-select-filter-one-eq-2 opt
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-d C18 filter-true eager
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	2
#|row	3
#|
#|-- B01-d C18 filter-true raw
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	2
#|row	3
#|
#|-- B01-d C18 filter-true opt
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	2
#|row	3
#|
#|-- B01-d C18 filter-false eager
#|frame
#|height	0
#|width	1
#|col	u32	"a"
#|
#|-- B01-d C18 filter-false raw
#|frame
#|height	0
#|width	1
#|col	u32	"a"
#|
#|-- B01-d C18 filter-false opt
#|frame
#|height	0
#|width	1
#|col	u32	"a"
#|
#|-- B01-d C20 filter-null eager
#|frame
#|height	0
#|width	1
#|col	u32	"a"
#|
#|-- B01-d C20 filter-null raw
#|frame
#|height	0
#|width	1
#|col	u32	"a"
#|
#|-- B01-d C20 filter-null opt
#|frame
#|height	0
#|width	1
#|col	u32	"a"
#|
