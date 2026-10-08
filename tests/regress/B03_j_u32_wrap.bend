# B03-j (Fable minor): u32 + - * and sum wrap silently; the README did not say so (M1
# README). DESIGN.md 15.5.1: u32 wraps mod 2^32, i32 is two's complement (MIN - 1 = MAX),
# sum wraps too. Pinned here (passes today); Polars 2.0.0 agrees (regress_expect.py). The
# reduction is a group_by sum so that the lazy runs do not depend on B04-a.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("g", [R.u(1), R.u(1)], D.TU32{}),
    R.mk("a", [R.u(4294967295), R.u(1)], D.TU32{}),
    R.mk("ai", [R.ineg(2147483648), R.i(2147483647)], D.TI32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def es() -> List<&2, X.Expr>:
  [DF.alias(DF.add(DF.col("a"), DF.lit_u32(1)), "a_plus_1"), DF.alias(DF.sub(DF.lit_u32(0), DF.col("a")), "zero_minus_a"), DF.alias(DF.mul(DF.col("a"), DF.lit_u32(2)), "a_times_2"), DF.alias(DF.sub(DF.col("ai"), DF.lit_i32(1)), "ai_minus_1"), DF.alias(DF.add(DF.col("ai"), DF.lit_i32(1)), "ai_plus_1")]

def aggs() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.col("a")), "sa"), DF.alias(DF.sum(DF.col("ai")), "sai")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-j arith", R.e_with(t(), es()), DF.lazy_with_columns(src(), es()), env(), env())
    R.three("B03-j group-sum", R.e_group(t(), [DF.col("g")], aggs()), DF.lazy_group_by(src(), [DF.col("g")], aggs()), env(), env())
#|-- B03-j arith eager
#|frame
#|height	2
#|width	8
#|col	u32	"g"
#|col	u32	"a"
#|col	i32	"ai"
#|col	u32	"a_plus_1"
#|col	u32	"zero_minus_a"
#|col	u32	"a_times_2"
#|col	i32	"ai_minus_1"
#|col	i32	"ai_plus_1"
#|row	1	4294967295	-2147483648	0	1	4294967294	2147483647	-2147483647
#|row	1	1	2147483647	2	4294967295	2	2147483646	-2147483648
#|
#|-- B03-j arith raw
#|frame
#|height	2
#|width	8
#|col	u32	"g"
#|col	u32	"a"
#|col	i32	"ai"
#|col	u32	"a_plus_1"
#|col	u32	"zero_minus_a"
#|col	u32	"a_times_2"
#|col	i32	"ai_minus_1"
#|col	i32	"ai_plus_1"
#|row	1	4294967295	-2147483648	0	1	4294967294	2147483647	-2147483647
#|row	1	1	2147483647	2	4294967295	2	2147483646	-2147483648
#|
#|-- B03-j arith opt
#|frame
#|height	2
#|width	8
#|col	u32	"g"
#|col	u32	"a"
#|col	i32	"ai"
#|col	u32	"a_plus_1"
#|col	u32	"zero_minus_a"
#|col	u32	"a_times_2"
#|col	i32	"ai_minus_1"
#|col	i32	"ai_plus_1"
#|row	1	4294967295	-2147483648	0	1	4294967294	2147483647	-2147483647
#|row	1	1	2147483647	2	4294967295	2	2147483646	-2147483648
#|
#|-- B03-j group-sum eager
#|frame
#|height	1
#|width	3
#|col	u32	"g"
#|col	u32	"sa"
#|col	i32	"sai"
#|row	1	0	-1
#|
#|-- B03-j group-sum raw
#|frame
#|height	1
#|width	3
#|col	u32	"g"
#|col	u32	"sa"
#|col	i32	"sai"
#|row	1	0	-1
#|
#|-- B03-j group-sum opt
#|frame
#|height	1
#|width	3
#|col	u32	"g"
#|col	u32	"sa"
#|col	i32	"sai"
#|row	1	0	-1
#|
