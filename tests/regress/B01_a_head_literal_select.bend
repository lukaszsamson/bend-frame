# B01-a (Astra A): Head{0} sunk below a literal-only Select gives one row.
# Contract DESIGN.md 15.4 C4/C5 and 15.2.8 (a Select all of whose expressions are
# KScalar/KRed is a height barrier for Opt.head). Polars 2.0.0
# (bench/contract/cardinality.py C4, C5): select(lit(1)).head(0) is (0, 1);
# head(0).select(lit(1)) is (1, 1), both APIs.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

# t: three rows
def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.u(3)], D.TU32{}), R.mk("b", [R.s("x"), R.s("y"), R.s("z")], D.TStr{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def one() -> X.Expr:
  DF.alias(DF.lit_u32(1), "one")

def main() -> IO(Unit):
  do IO<Unit>:
    # C5, Astra A: select(lit 1).head(0) -> (0, 1)
    R.three("B01-a C5 head0-over-literal-select", R.e_head(R.e_select(t(), [one()]), 0), DF.lazy_head(DF.lazy_select(src(), [one()]), 0), env(), env())
    # C4: head(0).select(lit 1) -> (1, 1)
    R.three("B01-a C4 literal-select-over-head0", R.e_select(R.e_head(t(), 0), [one()]), DF.lazy_select(DF.lazy_head(src(), 0), [one()]), env(), env())
    # head(2) over a literal select: still one row
    R.three("B01-a head2-over-literal-select", R.e_head(R.e_select(t(), [one()]), 2), DF.lazy_head(DF.lazy_select(src(), [one()]), 2), env(), env())
#|-- B01-a C5 head0-over-literal-select eager
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-a C5 head0-over-literal-select raw
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-a C5 head0-over-literal-select opt
#|frame
#|height	0
#|width	1
#|col	u32	"one"
#|
#|-- B01-a C4 literal-select-over-head0 eager
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-a C4 literal-select-over-head0 raw
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-a C4 literal-select-over-head0 opt
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-a head2-over-literal-select eager
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-a head2-over-literal-select raw
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B01-a head2-over-literal-select opt
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
