# B04-k: maintain_order=False{} is silently ignored (M1 README). DESIGN.md 15.2 shared
# rules: accepted and ignored, the output is first-appearance order anyway. Pinned (eager
# through G.GroupBy.run with False{}, lazy through a GroupBy node with False{}, since
# DF.group_by / DF.lazy_group_by always pass True{}); passes today. Polars 2.0.0 with
# maintain_order=True gives this order (regress_expect.py).
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
  R.frame([R.mk("k", [R.s("b"), R.s("a"), R.s("b"), R.s("c")], D.TStr{}), R.mk("v", [R.u(1), R.u(2), R.u(3), R.u(4)], D.TU32{})])

def eager(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      G.GroupBy.run(f, [DF.col("k")], [DF.alias(DF.sum(DF.col("v")), "s")], False{})

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B04-k group-unordered", eager(t()), P.GroupBy{[DF.col("k")], [DF.alias(DF.sum(DF.col("v")), "s")], False{}, R.src("t", t())}, R.env1("t", t()), R.env1("t", t()))
#|-- B04-k group-unordered eager
#|frame
#|height	3
#|width	2
#|col	str	"k"
#|col	u32	"s"
#|row	"b"	4
#|row	"a"	2
#|row	"c"	4
#|
#|-- B04-k group-unordered raw
#|frame
#|height	3
#|width	2
#|col	str	"k"
#|col	u32	"s"
#|row	"b"	4
#|row	"a"	2
#|row	"c"	4
#|
#|-- B04-k group-unordered opt
#|frame
#|height	3
#|width	2
#|col	str	"k"
#|col	u32	"s"
#|row	"b"	4
#|row	"a"	2
#|row	"c"	4
#|
