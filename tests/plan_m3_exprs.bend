# M3 expressions under the optimizers (DESIGN.md 15.2.8, 15.3.2): when / is_in / clip / the string
# functions are row-wise, total and local, so optimize_full's head pass may sink a Head below a
# Select of them (the release optimizer merges Heads only since M5 part 2: the Head stays above the
# Select); std / var / median are reductions (KRed, not local), so a Select or WithColumns holding
# one is a barrier in both (head2-over-centered, B01-f). The plans' results agree in every mode.
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
    R.mk("a", [R.u(4), R.u(1), R.null(), R.u(9), R.u(2)], D.TU32{}),
    R.mk("s", [R.s("ab"), R.s("b"), R.s("abc"), R.null(), R.s("")], D.TStr{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def a() -> X.Expr:
  DF.col("a")

def rowwise() -> List<&2, X.Expr>:
  [DF.alias(DF.when(DF.is_in(a(), [DF.s_u32(1), DF.s_u32(9)]), DF.clip(a(), DF.s_u32(2), DF.s_u32(5)), DF.lit_u32(0)), "w"), DF.alias(DF.len_chars(DF.col("s")), "n"), DF.alias(DF.starts_with(DF.col("s"), "a"), "sa")]

def centred() -> List<&2, X.Expr>:
  [DF.alias(DF.sub(DF.cast_f32(a()), DF.median(a())), "c")]

def p1() -> P.Plan:
  DF.lazy_head(DF.lazy_select(src(), rowwise()), 2)

def p2() -> P.Plan:
  DF.lazy_head(DF.lazy_with_columns(src(), centred()), 2)

def p3() -> P.Plan:
  DF.lazy_filter(DF.lazy_with_columns(src(), rowwise()), DF.contains_literal(DF.col("s"), "b"))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(DF.explain(DF.optimize(p1())) ++ "\n")
    IO.print(DF.explain(DF.optimize_full(p1())) ++ "\n")
    R.agree("head over row-wise", R.e_head(R.e_select(t(), rowwise()), 2), p1(), env(), env(), env())
    IO.print(DF.explain(DF.optimize(p2())) ++ "\n")
    IO.print(DF.explain(DF.optimize_full(p2())) ++ "\n")
    R.agree("head over median-centred", R.e_head(R.e_with(t(), centred()), 2), p2(), env(), env(), env())
    IO.print(DF.explain(DF.optimize_full(p3())) ++ "\n")
    R.agree("filter over row-wise", R.e_filter(R.e_with(t(), rowwise()), DF.contains_literal(DF.col("s"), "b")), p3(), env(), env(), env())
#|HEAD 2
#|  SELECT [when(col("a").is_in([1, 9])).then(col("a").clip(2, 5)).otherwise(lit(0)).alias("w"), col("s").str.len_chars().alias("n"), col("s").str.starts_with("a").alias("sa")]
#|    SOURCE t [a:u32, s:str]
#|
#|SELECT [when(col("a").is_in([1, 9])).then(col("a").clip(2, 5)).otherwise(lit(0)).alias("w"), col("s").str.len_chars().alias("n"), col("s").str.starts_with("a").alias("sa")]
#|  HEAD 2
#|    SOURCE t [a:u32, s:str]
#|
#|-- head over row-wise
#|frame
#|height	2
#|width	3
#|col	u32	"w"
#|col	u32	"n"
#|col	bool	"sa"
#|row	0	2	true
#|row	2	1	false
#|raw=eager opt=eager full=eager
#|
#|HEAD 2
#|  WITH_COLUMNS [(col("a").cast(f32) - col("a").median()).alias("c")]
#|    SOURCE t [a:u32, s:str]
#|
#|HEAD 2
#|  WITH_COLUMNS [(col("a").cast(f32) - col("a").median()).alias("c")]
#|    SOURCE t [a:u32, s:str]
#|
#|-- head over median-centred
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	str	"s"
#|col	f32	"c"
#|row	4	"ab"	0x3f800000
#|row	1	"b"	0xc0000000
#|raw=eager opt=eager full=eager
#|
#|WITH_COLUMNS [when(col("a").is_in([1, 9])).then(col("a").clip(2, 5)).otherwise(lit(0)).alias("w"), col("s").str.len_chars().alias("n"), col("s").str.starts_with("a").alias("sa")]
#|  FILTER col("s").str.contains_literal("b")
#|    SOURCE t [a:u32, s:str]
#|
#|-- filter over row-wise
#|frame
#|height	3
#|width	5
#|col	u32	"a"
#|col	str	"s"
#|col	u32	"w"
#|col	u32	"n"
#|col	bool	"sa"
#|row	4	"ab"	0	2	true
#|row	1	"b"	2	1	false
#|row	null	"abc"	0	3	true
#|raw=eager opt=eager full=eager
