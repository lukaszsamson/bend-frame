#! xfail B01-b
# B01-b (Astra E): lazy Select{[]} keeps the input height; eager select([]) gives (0, 0).
# Contract DESIGN.md 15.4 C1 and 15.2.3: select([]) is (0, 0) in both APIs (Polars 2.0.0
# eager and lazy: (0, 0), bench/contract/cardinality.py C1).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

# Astra's frame: six rows, nulls in a, c and d
def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a", [R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.u(6)], D.TU32{}),
    R.mk("b", [R.s("x"), R.s("y"), R.s("z"), R.s("x"), R.s("y"), R.s("x")], D.TStr{}),
    R.mk("c", [R.f(0.5), R.f(1.5), R.f(2.5), R.null(), R.f(4.5), R.f(5.5)], D.TF32{}),
    R.mk("d", [R.b(True{}), R.b(False{}), R.b(True{}), R.b(True{}), R.null(), R.b(True{})], D.TBool{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B01-b C1 select-empty", R.e_select(t(), []), DF.lazy_select(src(), []), env(), env())
    # under a head: still (0, 0)
    R.three("B01-b C1 head3-over-select-empty", R.e_head(R.e_select(t(), []), 3), DF.lazy_head(DF.lazy_select(src(), []), 3), env(), env())
#|-- B01-b C1 select-empty eager
#|frame
#|height	0
#|width	0
#|
#|-- B01-b C1 select-empty raw
#|frame
#|height	0
#|width	0
#|
#|-- B01-b C1 select-empty opt
#|frame
#|height	0
#|width	0
#|
#|-- B01-b C1 head3-over-select-empty eager
#|frame
#|height	0
#|width	0
#|
#|-- B01-b C1 head3-over-select-empty raw
#|frame
#|height	0
#|width	0
#|
#|-- B01-b C1 head3-over-select-empty opt
#|frame
#|height	0
#|width	0
#|
