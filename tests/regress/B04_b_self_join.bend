# B04-b (Fable B8, Astra G4): a Source used twice (self-join) passes collect_schema and
# fails collect ("source not in env (or used twice)"). DESIGN.md 15.7 use counting: Exec
# clones the frame at every use but the last, so a self-join sees two identical frames.
# Output per 15.2.4: left fields, right fields minus the key, clashes get _right; left row
# order, matches in right row order. Polars 2.0.0 df.join(df, on="k",
# maintain_order="left_right") gives the same rows (regress_expect.py).
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
  R.frame([R.mk("k", [R.u(1), R.u(2), R.u(2)], D.TU32{}), R.mk("v", [R.s("a"), R.s("b"), R.s("c")], D.TStr{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def ks() -> List<&2, String>:
  ["k"]

def flt() -> X.Expr:
  DF.ne(DF.col("v"), DF.lit_str("a"))

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B04-b self-inner-join", R.e_inner(t(), t(), ks(), ks()), DF.lazy_inner_join(src(), src(), ks(), ks()), env(), env())
    IO.print(R.schema("B04-b self-inner-join", DF.lazy_inner_join(src(), src(), ks(), ks())))
    R.three("B04-b self-left-join-filtered", R.e_left(R.e_filter(t(), flt()), t(), ks(), ks()), DF.lazy_left_join(DF.lazy_filter(src(), flt()), src(), ks(), ks()), env(), env())
#|-- B04-b self-inner-join eager
#|frame
#|height	5
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	1	"a"	"a"
#|row	2	"b"	"b"
#|row	2	"b"	"c"
#|row	2	"c"	"b"
#|row	2	"c"	"c"
#|
#|-- B04-b self-inner-join raw
#|frame
#|height	5
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	1	"a"	"a"
#|row	2	"b"	"b"
#|row	2	"b"	"c"
#|row	2	"c"	"b"
#|row	2	"c"	"c"
#|
#|-- B04-b self-inner-join opt
#|frame
#|height	5
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	1	"a"	"a"
#|row	2	"b"	"b"
#|row	2	"b"	"c"
#|row	2	"c"	"b"
#|row	2	"c"	"c"
#|
#|-- B04-b self-inner-join schema
#|k:u32, v:str, v_right:str
#|
#|-- B04-b self-left-join-filtered eager
#|frame
#|height	4
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	2	"b"	"b"
#|row	2	"b"	"c"
#|row	2	"c"	"b"
#|row	2	"c"	"c"
#|
#|-- B04-b self-left-join-filtered raw
#|frame
#|height	4
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	2	"b"	"b"
#|row	2	"b"	"c"
#|row	2	"c"	"b"
#|row	2	"c"	"c"
#|
#|-- B04-b self-left-join-filtered opt
#|frame
#|height	4
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	2	"b"	"b"
#|row	2	"b"	"c"
#|row	2	"c"	"b"
#|row	2	"c"	"c"
#|
