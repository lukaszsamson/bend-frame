#! xfail B01-c
# B01-c (Astra E): the height of a zero-column frame must stay what the contract says and
# become visible only as the contract says. DESIGN.md 15.4 C1, C22-C24 and the rule below
# the table: select([]) answers Frame{0, []}; a zero-column frame of height h (what `drop`
# of every column gives; built here as Frame{6, []} since drop is M3) keeps h through every
# verb. Polars 2.0.0: bench/contract/cardinality.py C22-C24 and regress_expect.py.
# C24's unique([]) and concat are M3 API: tests/regress/pending/B01_c_zero_column_m3.bend.txt.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

# z: no columns, height 6
def z() -> E.ResT(C.Frame):
  R.zcols(6)

def zenv() -> P.Env:
  R.env1("z", z())

def zsrc() -> P.Plan:
  R.src("z", z())

def o() -> X.Expr:
  DF.alias(DF.lit_u32(1), "o")

def n() -> X.Expr:
  DF.alias(DF.len(), "n")

def main() -> IO(Unit):
  do IO<Unit>:
    # the hidden height of select([]) must not reappear: (0, 0) then a literal column -> (0, 1)
    R.three("B01-c C1 select-empty-then-with-literal", R.e_with(R.e_select(t(), []), [o()]), DF.lazy_with_columns(DF.lazy_select(src(), []), [o()]), env(), env())
    # ... and len() over it counts 0 rows
    R.three("B01-c C1 select-empty-then-len", R.e_select(R.e_select(t(), []), [n()]), DF.lazy_select(DF.lazy_select(src(), []), [n()]), env(), env())
    # C22: z.with_columns([lit 1 as o]) -> (6, 1)
    R.three("B01-c C22 zero-col-with-literal", R.e_with(z(), [o()]), DF.lazy_with_columns(zsrc(), [o()]), zenv(), zenv())
    # C23: z.select([len()]) -> [6]; z.select([lit 1]) -> [1]
    R.three("B01-c C23 zero-col-select-len", R.e_select(z(), [n()]), DF.lazy_select(zsrc(), [n()]), zenv(), zenv())
    R.three("B01-c C23 zero-col-select-literal", R.e_select(z(), [DF.lit_u32(1)]), DF.lazy_select(zsrc(), [DF.lit_u32(1)]), zenv(), zenv())
    # C24: z.head(2) -> (2, 0); z.filter(lit true) -> (6, 0)
    R.three("B01-c C24 zero-col-head2", R.e_head(z(), 2), DF.lazy_head(zsrc(), 2), zenv(), zenv())
    R.three("B01-c C24 zero-col-filter-true", R.e_filter(z(), DF.lit_bool(True{})), DF.lazy_filter(zsrc(), DF.lit_bool(True{})), zenv(), zenv())
#|-- B01-c C1 select-empty-then-with-literal eager
#|frame
#|height	0
#|width	1
#|col	u32	"o"
#|
#|-- B01-c C1 select-empty-then-with-literal raw
#|frame
#|height	0
#|width	1
#|col	u32	"o"
#|
#|-- B01-c C1 select-empty-then-with-literal opt
#|frame
#|height	0
#|width	1
#|col	u32	"o"
#|
#|-- B01-c C1 select-empty-then-len eager
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	0
#|
#|-- B01-c C1 select-empty-then-len raw
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	0
#|
#|-- B01-c C1 select-empty-then-len opt
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	0
#|
#|-- B01-c C22 zero-col-with-literal eager
#|frame
#|height	6
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B01-c C22 zero-col-with-literal raw
#|frame
#|height	6
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B01-c C22 zero-col-with-literal opt
#|frame
#|height	6
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B01-c C23 zero-col-select-len eager
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	6
#|
#|-- B01-c C23 zero-col-select-len raw
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	6
#|
#|-- B01-c C23 zero-col-select-len opt
#|frame
#|height	1
#|width	1
#|col	u32	"n"
#|row	6
#|
#|-- B01-c C23 zero-col-select-literal eager
#|frame
#|height	1
#|width	1
#|col	u32	"literal"
#|row	1
#|
#|-- B01-c C23 zero-col-select-literal raw
#|frame
#|height	1
#|width	1
#|col	u32	"literal"
#|row	1
#|
#|-- B01-c C23 zero-col-select-literal opt
#|frame
#|height	1
#|width	1
#|col	u32	"literal"
#|row	1
#|
#|-- B01-c C24 zero-col-head2 eager
#|frame
#|height	2
#|width	0
#|
#|-- B01-c C24 zero-col-head2 raw
#|frame
#|height	2
#|width	0
#|
#|-- B01-c C24 zero-col-head2 opt
#|frame
#|height	2
#|width	0
#|
#|-- B01-c C24 zero-col-filter-true eager
#|frame
#|height	6
#|width	0
#|
#|-- B01-c C24 zero-col-filter-true raw
#|frame
#|height	6
#|width	0
#|
#|-- B01-c C24 zero-col-filter-true opt
#|frame
#|height	6
#|width	0
#|
