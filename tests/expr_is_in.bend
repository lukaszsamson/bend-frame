# M3 is_in(e, [literals]) (DESIGN.md 15.2.6, 15.5.2): true iff some literal equals the cell under
# the one relation of 15.5.2 (f32: NaN == NaN, -0.0 == 0.0; the contract's own example below);
# a null cell gives null; [] gives false; every literal must have e's dtype (an SNull is refused).
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
    R.mk("x", [R.f(R.nan()), R.f(1.0), R.f(R.nzero()), R.f(0.0), R.f(R.inf()), R.f(R.ninf()), R.null()], D.TF32{}),
    R.mk("u", [R.u(1), R.u(2), R.u(3), R.null(), R.u(4294967295), R.u(0), R.u(7)], D.TU32{}),
    R.mk("i", [R.ineg(1), R.i(0), R.i(5), R.ineg(2147483648), R.null(), R.ineg(1), R.i(2)], D.TI32{}),
    R.mk("s", [R.s("a"), R.s(""), R.s("ab"), R.null(), R.s("A"), R.s("é"), R.s("a")], D.TStr{}),
    R.mk("b", [R.b(True{}), R.b(False{}), R.null(), R.b(True{}), R.b(False{}), R.b(True{}), R.b(False{})], D.TBool{})])

def t0() -> E.ResT(C.Frame):
  R.frame([R.mk("u", [], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def ins() -> List<&2, X.Expr>:
  [DF.alias(DF.is_in(DF.col("x"), [DF.s_f32(R.nan()), DF.s_f32(0.0)]), "x"), DF.is_in(DF.col("u"), [DF.s_u32(3), DF.s_u32(4294967295), DF.s_u32(0)]), DF.is_in(DF.col("i"), [R.ineg(1), R.i(2)]), DF.is_in(DF.col("s"), [DF.s_str("a"), DF.s_str(""), DF.s_str("é")]), DF.is_in(DF.col("b"), [DF.s_bool(True{})]), DF.alias(DF.is_in(DF.col("x"), []), "none")]

def sa() -> X.Expr:
  DF.is_in(DF.col("s"), [DF.s_str("a")])

def main() -> IO(Unit):
  do IO<Unit>:
    R.agree("is_in dtypes", R.e_select(t(), ins()), DF.lazy_select(src(), ins()), env(), env(), env())
    R.agree("is_in filter", R.e_filter(t(), sa()), DF.lazy_filter(src(), sa()), env(), env(), env())
    R.agree("is_in group key", R.e_group(t(), [sa()], [DF.alias(DF.len(), "n")]), DF.lazy_group_by(src(), [sa()], [DF.alias(DF.len(), "n")]), env(), env(), env())
    R.agree("is_in h0", R.e_select(t0(), [DF.is_in(DF.col("u"), [DF.s_u32(1)])]), DF.lazy_select(R.src("t", t0()), [DF.is_in(DF.col("u"), [DF.s_u32(1)])]), R.env1("t", t0()), R.env1("t", t0()), R.env1("t", t0()))
    R.agree("is_in wrong dtype", R.e_select(t(), [DF.is_in(DF.col("u"), [DF.s_u32(1), R.i(1)])]), DF.lazy_select(src(), [DF.is_in(DF.col("u"), [DF.s_u32(1), R.i(1)])]), env(), env(), env())
    R.agree("is_in null literal", R.e_select(t(), [DF.is_in(DF.col("s"), [DF.s_null(), DF.s_u32(1)])]), DF.lazy_select(src(), [DF.is_in(DF.col("s"), [DF.s_null(), DF.s_u32(1)])]), env(), env(), env())
    R.agree("is_in unknown column", R.e_select(t(), [DF.is_in(DF.col("nope"), [DF.s_u32(1)])]), DF.lazy_select(src(), [DF.is_in(DF.col("nope"), [DF.s_u32(1)])]), env(), env(), env())
    IO.print(R.schema("is_in", DF.lazy_select(src(), ins())))
    IO.print(DF.explain(DF.lazy_select(src(), ins())) ++ "\n")
#|-- is_in dtypes
#|frame
#|height	7
#|width	6
#|col	bool	"x"
#|col	bool	"u"
#|col	bool	"i"
#|col	bool	"s"
#|col	bool	"b"
#|col	bool	"none"
#|row	true	false	true	true	true	false
#|row	false	false	false	true	false	false
#|row	true	true	false	false	null	false
#|row	true	null	false	null	true	false
#|row	false	true	null	false	false	false
#|row	false	true	true	true	true	false
#|row	null	false	true	true	false	null
#|raw=eager opt=eager full=eager
#|
#|-- is_in filter
#|frame
#|height	2
#|width	5
#|col	f32	"x"
#|col	u32	"u"
#|col	i32	"i"
#|col	str	"s"
#|col	bool	"b"
#|row	0x7fc00000	1	-1	"a"	true
#|row	null	7	2	"a"	false
#|raw=eager opt=eager full=eager
#|
#|-- is_in group key
#|frame
#|height	3
#|width	2
#|col	bool	"s"
#|col	u32	"n"
#|row	true	2
#|row	false	4
#|row	null	1
#|raw=eager opt=eager full=eager
#|
#|-- is_in h0
#|frame
#|height	0
#|width	1
#|col	bool	"u"
#|raw=eager opt=eager full=eager
#|
#|-- is_in wrong dtype
#|error	TypeMismatch in is_in: expected u32, got i32
#|raw=eager opt=eager full=eager
#|
#|-- is_in null literal
#|error	TypeMismatch in is_in: expected str, got null
#|raw=eager opt=eager full=eager
#|
#|-- is_in unknown column
#|error	ColumnNotFound: nope
#|raw=eager opt=eager full=eager
#|
#|-- is_in schema
#|x:bool, u:bool, i:bool, s:bool, b:bool, none:bool
#|
#|SELECT [col("x").is_in([nan, 0]).alias("x"), col("u").is_in([3, 4294967295, 0]), col("i").is_in([-1, 2]), col("s").is_in(["a", "", "é"]), col("b").is_in([true]), col("x").is_in([]).alias("none")]
#|  SOURCE t [x:f32, u:u32, i:i32, s:str, b:bool]
