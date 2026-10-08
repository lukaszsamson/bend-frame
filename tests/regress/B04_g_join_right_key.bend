# B04-g (Fable B7): a join drops the right key even when left_on and right_on differ;
# the README did not say so (M1 README). DESIGN.md 15.2.4: output = left fields, then
# right fields minus right_on. Polars 2.0.0 does the same (coalesce default;
# regress_expect.py). Pinned here; passes today.
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

def l() -> E.ResT(C.Frame):
  R.frame([R.mk("id", [R.u(1), R.u(2), R.u(3)], D.TU32{}), R.mk("x", [R.s("a"), R.s("b"), R.s("c")], D.TStr{})])

def r() -> E.ResT(C.Frame):
  R.frame([R.mk("rid", [R.u(2), R.u(1)], D.TU32{}), R.mk("y", [R.s("two"), R.s("one")], D.TStr{})])

def env() -> P.Env:
  R.env_add(R.env1("l", l()), "r", r())

def lo() -> List<&2, String>:
  ["id"]

def ro() -> List<&2, String>:
  ["rid"]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B04-g inner", R.e_inner(l(), r(), lo(), ro()), DF.lazy_inner_join(R.src("l", l()), R.src("r", r()), lo(), ro()), env(), env())
    R.three("B04-g left", R.e_left(l(), r(), lo(), ro()), DF.lazy_left_join(R.src("l", l()), R.src("r", r()), lo(), ro()), env(), env())
#|-- B04-g inner eager
#|frame
#|height	2
#|width	3
#|col	u32	"id"
#|col	str	"x"
#|col	str	"y"
#|row	1	"a"	"one"
#|row	2	"b"	"two"
#|
#|-- B04-g inner raw
#|frame
#|height	2
#|width	3
#|col	u32	"id"
#|col	str	"x"
#|col	str	"y"
#|row	1	"a"	"one"
#|row	2	"b"	"two"
#|
#|-- B04-g inner opt
#|frame
#|height	2
#|width	3
#|col	u32	"id"
#|col	str	"x"
#|col	str	"y"
#|row	1	"a"	"one"
#|row	2	"b"	"two"
#|
#|-- B04-g left eager
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"x"
#|col	str	"y"
#|row	1	"a"	"one"
#|row	2	"b"	"two"
#|row	3	"c"	null
#|
#|-- B04-g left raw
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"x"
#|col	str	"y"
#|row	1	"a"	"one"
#|row	2	"b"	"two"
#|row	3	"c"	null
#|
#|-- B04-g left opt
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"x"
#|col	str	"y"
#|row	1	"a"	"one"
#|row	2	"b"	"two"
#|row	3	"c"	null
#|
