#! xfail B04-a
# (B03 fixed in M1: eager and grouped runs pass; the lazy select runs still refuse the
# reduction until B04-a lands. Remove the marker with B04-a.)
# B03-b (Astra C audit): the eager reduction (Kernel.fsum, Kahan) has the same inf - inf
# contamination as B03-a. DESIGN.md 15.5.3 (same accumulation for every f32 sum/mean):
#   p [inf, 1] sum inf mean inf; q [1, inf] inf, inf; r [inf, -inf] NaN, NaN;
#   w [NaN, 1] NaN, NaN; c [1e8, 1, -1e8] sum 1, mean 1/3.
# Polars 2.0.0 agrees (regress_expect.py). The lazy runs also need B04-a.
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
    R.mk("p", [R.f(R.inf()), R.f(1.0), R.null()], D.TF32{}),
    R.mk("q", [R.f(1.0), R.f(R.inf()), R.null()], D.TF32{}),
    R.mk("r", [R.f(R.inf()), R.f(R.ninf()), R.null()], D.TF32{}),
    R.mk("w", [R.f(R.nan()), R.f(1.0), R.null()], D.TF32{}),
    R.mk("c", [R.f(100000000.0), R.f(1.0), R.f(F32.neg(100000000.0))], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def sums() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.col("p")), "sp"), DF.alias(DF.sum(DF.col("q")), "sq"), DF.alias(DF.sum(DF.col("r")), "sr"), DF.alias(DF.sum(DF.col("w")), "sw"), DF.alias(DF.sum(DF.col("c")), "sc")]

def means() -> List<&2, X.Expr>:
  [DF.alias(DF.mean(DF.col("p")), "mp"), DF.alias(DF.mean(DF.col("q")), "mq"), DF.alias(DF.mean(DF.col("r")), "mr"), DF.alias(DF.mean(DF.col("w")), "mw"), DF.alias(DF.mean(DF.col("c")), "mc")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-b sums", R.e_select(t(), sums()), DF.lazy_select(src(), sums()), env(), env())
    R.three("B03-b means", R.e_select(t(), means()), DF.lazy_select(src(), means()), env(), env())
#|-- B03-b sums eager
#|frame
#|height	1
#|width	5
#|col	f32	"sp"
#|col	f32	"sq"
#|col	f32	"sr"
#|col	f32	"sw"
#|col	f32	"sc"
#|row	0x7f800000	0x7f800000	0x7fc00000	0x7fc00000	0x3f800000
#|
#|-- B03-b sums raw
#|frame
#|height	1
#|width	5
#|col	f32	"sp"
#|col	f32	"sq"
#|col	f32	"sr"
#|col	f32	"sw"
#|col	f32	"sc"
#|row	0x7f800000	0x7f800000	0x7fc00000	0x7fc00000	0x3f800000
#|
#|-- B03-b sums opt
#|frame
#|height	1
#|width	5
#|col	f32	"sp"
#|col	f32	"sq"
#|col	f32	"sr"
#|col	f32	"sw"
#|col	f32	"sc"
#|row	0x7f800000	0x7f800000	0x7fc00000	0x7fc00000	0x3f800000
#|
#|-- B03-b means eager
#|frame
#|height	1
#|width	5
#|col	f32	"mp"
#|col	f32	"mq"
#|col	f32	"mr"
#|col	f32	"mw"
#|col	f32	"mc"
#|row	0x7f800000	0x7f800000	0x7fc00000	0x7fc00000	0x3eaaaaab
#|
#|-- B03-b means raw
#|frame
#|height	1
#|width	5
#|col	f32	"mp"
#|col	f32	"mq"
#|col	f32	"mr"
#|col	f32	"mw"
#|col	f32	"mc"
#|row	0x7f800000	0x7f800000	0x7fc00000	0x7fc00000	0x3eaaaaab
#|
#|-- B03-b means opt
#|frame
#|height	1
#|width	5
#|col	f32	"mp"
#|col	f32	"mq"
#|col	f32	"mr"
#|col	f32	"mw"
#|col	f32	"mc"
#|row	0x7f800000	0x7f800000	0x7fc00000	0x7fc00000	0x3eaaaaab
#|
