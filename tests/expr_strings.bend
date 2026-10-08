# M3 string functions (DESIGN.md 15.2.6): len_chars counts code points ("é" is one); the literal
# predicates contains_literal / starts_with / ends_with are case-sensitive, compare code points,
# and an empty pattern is true; a null cell gives null; a non-str operand is a TypeMismatch.
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
    R.mk("s", [R.s("apple"), R.s(""), R.s("Apple"), R.null(), R.s("éclair"), R.s("pineapple"), R.s("a\tb")], D.TStr{}),
    R.mk("u", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def s() -> X.Expr:
  DF.col("s")

def fns() -> List<&2, X.Expr>:
  [DF.alias(DF.len_chars(s()), "n"), DF.alias(DF.contains_literal(s(), "app"), "c_app"), DF.alias(DF.contains_literal(s(), ""), "c_empty"), DF.alias(DF.starts_with(s(), "app"), "sw_app"), DF.alias(DF.ends_with(s(), "le"), "ew_le"), DF.alias(DF.starts_with(s(), "é"), "sw_e"), DF.alias(DF.contains_literal(s(), "\t"), "c_tab"), DF.alias(DF.ends_with(s(), ""), "ew_empty")]

def bad(+e: X.Expr) -> IO(Unit):
  R.agree("string error", R.e_select(t(), [e]), DF.lazy_select(src(), [e]), env(), env(), env())

def main() -> IO(Unit):
  do IO<Unit>:
    R.agree("strings", R.e_select(t(), fns()), DF.lazy_select(src(), fns()), env(), env(), env())
    R.agree("strings filter", R.e_filter(t(), DF.contains_literal(s(), "pp")), DF.lazy_filter(src(), DF.contains_literal(s(), "pp")), env(), env(), env())
    R.agree("strings sum len", R.e_select(t(), [DF.sum(DF.len_chars(s()))]), DF.lazy_select(src(), [DF.sum(DF.len_chars(s()))]), env(), env(), env())
    R.agree("strings group key", R.e_group(t(), [DF.ends_with(s(), "le")], [DF.alias(DF.sum(DF.col("u")), "su")]), DF.lazy_group_by(src(), [DF.ends_with(s(), "le")], [DF.alias(DF.sum(DF.col("u")), "su")]), env(), env(), env())
    bad(DF.len_chars(DF.col("u")))
    bad(DF.starts_with(DF.col("u"), "a"))
    bad(DF.contains_literal(DF.col("u"), "a"))
    bad(DF.ends_with(DF.col("nope"), "a"))
    IO.print(DF.explain(DF.lazy_select(src(), fns())) ++ "\n")
#|-- strings
#|frame
#|height	7
#|width	8
#|col	u32	"n"
#|col	bool	"c_app"
#|col	bool	"c_empty"
#|col	bool	"sw_app"
#|col	bool	"ew_le"
#|col	bool	"sw_e"
#|col	bool	"c_tab"
#|col	bool	"ew_empty"
#|row	5	true	true	true	true	false	false	true
#|row	0	false	true	false	false	false	false	true
#|row	5	false	true	false	true	false	false	true
#|row	null	null	null	null	null	null	null	null
#|row	6	false	true	false	false	true	false	true
#|row	9	true	true	false	true	false	false	true
#|row	3	false	true	false	false	false	true	true
#|raw=eager opt=eager full=eager
#|
#|-- strings filter
#|frame
#|height	3
#|width	2
#|col	str	"s"
#|col	u32	"u"
#|row	"apple"	1
#|row	"Apple"	3
#|row	"pineapple"	6
#|raw=eager opt=eager full=eager
#|
#|-- strings sum len
#|frame
#|height	1
#|width	1
#|col	u32	"s"
#|row	28
#|raw=eager opt=eager full=eager
#|
#|-- strings group key
#|frame
#|height	3
#|width	2
#|col	bool	"s"
#|col	u32	"su"
#|row	true	10
#|row	false	14
#|row	null	4
#|raw=eager opt=eager full=eager
#|
#|-- string error
#|error	TypeMismatch in len_chars: expected str, got u32
#|raw=eager opt=eager full=eager
#|
#|-- string error
#|error	TypeMismatch in starts_with: expected str, got u32
#|raw=eager opt=eager full=eager
#|
#|-- string error
#|error	TypeMismatch in contains_literal: expected str, got u32
#|raw=eager opt=eager full=eager
#|
#|-- string error
#|error	ColumnNotFound: nope
#|raw=eager opt=eager full=eager
#|
#|SELECT [col("s").str.len_chars().alias("n"), col("s").str.contains_literal("app").alias("c_app"), col("s").str.contains_literal("").alias("c_empty"), col("s").str.starts_with("app").alias("sw_app"), col("s").str.ends_with("le").alias("ew_le"), col("s").str.starts_with("é").alias("sw_e"), col("s").str.contains_literal("	").alias("c_tab"), col("s").str.ends_with("").alias("ew_empty")]
#|  SOURCE t [s:str, u:u32]
