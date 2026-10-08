# M3 when(cond).then(a).otherwise(b) (DESIGN.md 15.2.6, 15.3): a null cond picks b, the result
# is null iff the chosen branch is; the name is the then-branch's; literals broadcast, an
# all-literal when is one row; it may sit under a reduction, in a filter and in group_by aggs.
# Every case: the eager dump, then raw / opt / full agreement (R.agree).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/plan.bend as P
import ./regress/lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("c", [R.b(True{}), R.b(False{}), R.null(), R.b(True{}), R.b(False{})], D.TBool{}),
    R.mk("a", [R.i(1), R.ineg(2), R.i(3), R.null(), R.i(5)], D.TI32{}),
    R.mk("b", [R.i(10), R.i(20), R.i(30), R.i(40), R.null()], D.TI32{}),
    R.mk("s", [R.s("x"), R.s("y"), R.null(), R.s("z"), R.s("w")], D.TStr{}),
    R.mk("f", [R.f(1.5), R.f(R.nan()), R.f(R.nzero()), R.null(), R.f(2.0)], D.TF32{})])

def t0() -> E.ResT(C.Frame):
  R.frame([R.mk("c", [], D.TBool{}), R.mk("a", [], D.TI32{}), R.mk("b", [], D.TI32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def env0() -> P.Env:
  R.env1("t", t0())

def src0() -> P.Plan:
  R.src("t", t0())

def c() -> X.Expr:
  DF.col("c")

def a() -> X.Expr:
  DF.col("a")

def cols() -> List<&2, X.Expr>:
  [DF.alias(DF.when(c(), a(), DF.col("b")), "w"), DF.alias(DF.when(c(), DF.col("s"), DF.lit_str("-")), "ws"), DF.alias(DF.when(c(), DF.col("f"), DF.lit_null(DF.t_f32())), "wf")]

def names() -> List<&2, X.Expr>:
  [DF.when(c(), a(), DF.col("b")), DF.when(c(), DF.lit_i32(1), a())]

def scalars() -> List<&2, X.Expr>:
  [DF.alias(DF.when(DF.lit_bool(True{}), DF.lit_u32(1), DF.lit_u32(2)), "k"), DF.alias(DF.when(DF.lit_null(DF.t_bool()), DF.lit_u32(1), DF.lit_u32(2)), "k2")]

def size() -> List<&2, X.Expr>:
  [DF.alias(DF.when(DF.gt(a(), DF.lit_i32(2)), DF.lit_str("big"), DF.lit_str("small")), "size")]

def pred() -> X.Expr:
  DF.when(c(), DF.gt(a(), DF.lit_i32(0)), DF.lit_bool(False{}))

def pos() -> X.Expr:
  DF.when(DF.gt(a(), DF.lit_i32(0)), a(), DF.lit_i32(0))

def red() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.when(c(), a(), DF.lit_i32(0))), "s")]

def gaggs() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(pos()), "pos")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.agree("when cols", R.e_select(t(), cols()), DF.lazy_select(src(), cols()), env(), env(), env())
    R.agree("when names", R.e_select(t(), names()), DF.lazy_select(src(), names()), env(), env(), env())
    R.agree("when scalar", R.e_select(t(), scalars()), DF.lazy_select(src(), scalars()), env(), env(), env())
    R.agree("when with_columns", R.e_select(R.e_with(t(), size()), [DF.col("a"), DF.col("size")]), DF.lazy_select(DF.lazy_with_columns(src(), size()), [DF.col("a"), DF.col("size")]), env(), env(), env())
    R.agree("when filter", R.e_filter(t(), pred()), DF.lazy_filter(src(), pred()), env(), env(), env())
    R.agree("when under sum", R.e_select(t(), red()), DF.lazy_select(src(), red()), env(), env(), env())
    R.agree("when group_by", R.e_group(t(), [c()], gaggs()), DF.lazy_group_by(src(), [c()], gaggs()), env(), env(), env())
    R.agree("when h0", R.e_select(t0(), [DF.alias(DF.when(c(), a(), DF.col("b")), "w")]), DF.lazy_select(src0(), [DF.alias(DF.when(c(), a(), DF.col("b")), "w")]), env0(), env0(), env0())
    R.agree("when cond not bool", R.e_select(t(), [DF.when(a(), a(), DF.col("b"))]), DF.lazy_select(src(), [DF.when(a(), a(), DF.col("b"))]), env(), env(), env())
    R.agree("when branches differ", R.e_select(t(), [DF.when(c(), a(), DF.col("s"))]), DF.lazy_select(src(), [DF.when(c(), a(), DF.col("s"))]), env(), env(), env())
    R.agree("when operand error first", R.e_select(t(), [DF.when(a(), DF.col("nope"), DF.col("s"))]), DF.lazy_select(src(), [DF.when(a(), DF.col("nope"), DF.col("s"))]), env(), env(), env())
    IO.print(R.schema("when", DF.lazy_select(src(), cols())))
    IO.print(DF.explain(DF.lazy_select(src(), names())) ++ "\n")
    IO.print(DF.explain(DF.optimize_full(DF.lazy_filter(DF.lazy_with_columns(src(), size()), DF.gt(a(), DF.lit_i32(0))))) ++ "\n")
#|-- when cols
#|frame
#|height	5
#|width	3
#|col	i32	"w"
#|col	str	"ws"
#|col	f32	"wf"
#|row	1	"x"	0x3fc00000
#|row	20	"-"	null
#|row	30	"-"	null
#|row	null	"z"	null
#|row	null	"-"	null
#|raw=eager opt=eager full=eager
#|
#|-- when names
#|frame
#|height	5
#|width	2
#|col	i32	"a"
#|col	i32	"literal"
#|row	1	1
#|row	20	-2
#|row	30	3
#|row	null	1
#|row	null	5
#|raw=eager opt=eager full=eager
#|
#|-- when scalar
#|frame
#|height	1
#|width	2
#|col	u32	"k"
#|col	u32	"k2"
#|row	1	2
#|raw=eager opt=eager full=eager
#|
#|-- when with_columns
#|frame
#|height	5
#|width	2
#|col	i32	"a"
#|col	str	"size"
#|row	1	"small"
#|row	-2	"small"
#|row	3	"big"
#|row	null	"small"
#|row	5	"big"
#|raw=eager opt=eager full=eager
#|
#|-- when filter
#|frame
#|height	1
#|width	5
#|col	bool	"c"
#|col	i32	"a"
#|col	i32	"b"
#|col	str	"s"
#|col	f32	"f"
#|row	true	1	10	"x"	0x3fc00000
#|raw=eager opt=eager full=eager
#|
#|-- when under sum
#|frame
#|height	1
#|width	1
#|col	i32	"s"
#|row	1
#|raw=eager opt=eager full=eager
#|
#|-- when group_by
#|frame
#|height	3
#|width	2
#|col	bool	"c"
#|col	i32	"pos"
#|row	true	1
#|row	false	5
#|row	null	3
#|raw=eager opt=eager full=eager
#|
#|-- when h0
#|frame
#|height	0
#|width	1
#|col	i32	"w"
#|raw=eager opt=eager full=eager
#|
#|-- when cond not bool
#|error	TypeMismatch in when: expected bool, got i32
#|raw=eager opt=eager full=eager
#|
#|-- when branches differ
#|error	TypeMismatch in when: expected i32, got str
#|raw=eager opt=eager full=eager
#|
#|-- when operand error first
#|error	ColumnNotFound: nope
#|raw=eager opt=eager full=eager
#|
#|-- when schema
#|w:i32, ws:str, wf:f32
#|
#|SELECT [when(col("c")).then(col("a")).otherwise(col("b")), when(col("c")).then(lit(1)).otherwise(col("a"))]
#|  SOURCE t [c:bool, a:i32, b:i32, s:str, f:f32]
#|
#|WITH_COLUMNS [when((col("a") > lit(2))).then(lit("big")).otherwise(lit("small")).alias("size")]
#|  FILTER (col("a") > lit(0))
#|    SOURCE t [c:bool, a:i32, b:i32, s:str, f:f32]
