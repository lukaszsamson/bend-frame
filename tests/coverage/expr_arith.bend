# T6 coverage: arithmetic expression operators (add, sub, mul, div, floor_div, mod, neg, abs, sqrt)
# over the nullable fixture t (tests/coverage/lib/fx.bend; header there): success + null rows (one
# select per operator family), a zero-row frame (empty), and the refusals (invalid). Every case runs
# eager (DX.e_select) and lazy (DF.lazy_select: raw / DF.collect / DF.collect_full), R.four printing
# the eager dump and whether the three lazy runs dump the same.
# Expectations: reasoned from DESIGN.md 15.5.1 and confirmed by bench/coverage/expr_arith.py
# (Polars 2.0.0) with the departures applied there: no implicit coercion (a mixed-dtype operand pair
# is a TypeMismatch; Polars supertypes), `/` only f32, i32 MIN // -1 is null (Polars MIN), `neg`/`abs`
# only i32/f32, `sqrt` only f32.
#@ cover add,sub,mul,div,floor_div,mod,neg,abs,sqrt success null empty invalid eager lazy
#@ cover col,alias success null empty eager lazy
#@ cover lazy_select success null empty invalid eager lazy
#@ cover select success null empty invalid eager lazy
#@ cover lit_f32 success null eager lazy
#@ cover lit_u32 success null eager lazy
#@ na add,sub,mul,div,floor_div,mod,neg,abs,sqrt zerocol -- every operand is a column, a zero-column frame has none (literals only: tests/coverage/expr_lit.bend)
import Base
import ./../../frame.bend as DF
import ./../diff/lib/dx.bend as DX
import ./../regress/lib/rx.bend as R
import ./lib/fx.bend as FX

def a() -> DF.Expr():
  DF.col("a")

def b() -> DF.Expr():
  DF.col("b")

def p() -> DF.Expr():
  DF.col("p")

def q() -> DF.Expr():
  DF.col("q")

def x() -> DF.Expr():
  DF.col("x")

def y() -> DF.Expr():
  DF.col("y")

def al(e: DF.Expr(), +n: String) -> DF.Expr():
  DF.alias(e, n)

def sel(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.t(), es), DF.lazy_select(FX.srct(), es), FX.envt(), FX.envt(), FX.envt())

def selz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.z(), es), DF.lazy_select(FX.srcz(), es), FX.envz(), FX.envz(), FX.envz())

# every operator, every dtype it accepts: also the zero-row case
def all() -> List<&2, DF.Expr()>:
  [al(DF.add(a(), b()), "add_u"), al(DF.add(p(), q()), "add_i"), al(DF.add(x(), y()), "add_f"),
   al(DF.sub(a(), b()), "sub_u"), al(DF.sub(p(), q()), "sub_i"), al(DF.sub(x(), y()), "sub_f"),
   al(DF.mul(a(), b()), "mul_u"), al(DF.mul(p(), q()), "mul_i"), al(DF.mul(x(), y()), "mul_f"),
   al(DF.div(x(), y()), "div_f"), al(DF.floor_div(a(), b()), "fdiv_u"), al(DF.floor_div(p(), q()), "fdiv_i"),
   al(DF.mod(a(), b()), "mod_u"), al(DF.mod(p(), q()), "mod_i"),
   al(DF.neg(p()), "neg_i"), al(DF.neg(x()), "neg_f"), al(DF.abs(p()), "abs_i"), al(DF.abs(x()), "abs_f"),
   al(DF.sqrt(x()), "sqrt_f")]

def main() -> IO(Unit):
  do IO<Unit>:
    sel("add sub mul u32 i32 f32 with nulls", [a(), al(DF.add(a(), b()), "add_u"), al(DF.add(p(), q()), "add_i"), al(DF.add(x(), y()), "add_f"), al(DF.sub(a(), b()), "sub_u"), al(DF.sub(p(), q()), "sub_i"), al(DF.sub(x(), y()), "sub_f"), al(DF.mul(a(), b()), "mul_u"), al(DF.mul(p(), q()), "mul_i"), al(DF.mul(x(), y()), "mul_f")])
    sel("add with a literal", [al(DF.add(a(), DF.lit_u32(1)), "a1"), al(DF.add(x(), DF.lit_f32(0.5)), "x5")])
    sel("div f32", [al(DF.div(x(), y()), "div_f"), al(DF.div(x(), DF.lit_f32(0.0)), "div_zero")])
    sel("floor_div u32 i32", [al(DF.floor_div(a(), b()), "fdiv_u"), al(DF.floor_div(p(), q()), "fdiv_i")])
    sel("mod u32 i32", [al(DF.mod(a(), b()), "mod_u"), al(DF.mod(p(), q()), "mod_i")])
    sel("neg abs sqrt", [al(DF.neg(p()), "neg_i"), al(DF.neg(x()), "neg_f"), al(DF.abs(p()), "abs_i"), al(DF.abs(x()), "abs_f"), al(DF.sqrt(x()), "sqrt_f")])
    selz("all operators, zero rows", all())
    sel("invalid add u32 + i32", [DF.add(a(), p())])
    sel("invalid add bool", [DF.add(DF.col("k"), DF.col("k"))])
    sel("invalid sub u32 - f32", [DF.sub(a(), x())])
    sel("invalid mul str", [DF.mul(DF.col("s"), DF.col("s"))])
    sel("invalid add missing column", [DF.add(DF.col("nope"), a())])
    sel("invalid div u32", [DF.div(a(), b())])
    sel("invalid div f32 by u32", [DF.div(x(), b())])
    sel("invalid floor_div f32", [DF.floor_div(x(), y())])
    sel("invalid floor_div u32 i32", [DF.floor_div(a(), p())])
    sel("invalid mod f32", [DF.mod(x(), y())])
    sel("invalid mod u32 i32", [DF.mod(a(), p())])
    sel("invalid neg u32", [DF.neg(a())])
    sel("invalid neg str", [DF.neg(DF.col("s"))])
    sel("invalid abs u32", [DF.abs(a())])
    sel("invalid abs bool", [DF.abs(DF.col("k"))])
    sel("invalid sqrt i32", [DF.sqrt(p())])
    sel("invalid sqrt u32", [DF.sqrt(a())])
#|-- add sub mul u32 i32 f32 with nulls
#|frame
#|height	7
#|width	10
#|col	u32	"a"
#|col	u32	"add_u"
#|col	i32	"add_i"
#|col	f32	"add_f"
#|col	u32	"sub_u"
#|col	i32	"sub_i"
#|col	f32	"sub_f"
#|col	u32	"mul_u"
#|col	i32	"mul_i"
#|col	f32	"mul_f"
#|row	7	9	9	0x40600000	5	5	0xbf000000	14	14	0x40400000
#|row	0	3	-5	0xbfc00000	4294967293	-9	0xc0200000	0	-14	0xbf800000
#|row	4294967295	0	5	null	4294967294	9	null	4294967295	-14	null
#|row	null	null	-9	0x7fc00000	null	-5	0x7fc00000	null	14	0x7fc00000
#|row	5	null	2147483647	0x7f800000	null	-2147483647	0x7fc00000	null	-2147483648	0x7f800000
#|row	1	1	null	0x00000000	1	null	0x00000000	0	null	0x00000000
#|row	2	2	0	null	2	0	null	0	0	null
#|raw same, opt same, full same
#|
#|-- add with a literal
#|frame
#|height	7
#|width	2
#|col	u32	"a1"
#|col	f32	"x5"
#|row	8	0x40000000
#|row	1	0xbfc00000
#|row	0	null
#|row	null	0x7fc00000
#|row	6	0x7f800000
#|row	2	0x3f000000
#|row	3	0x3f000000
#|raw same, opt same, full same
#|
#|-- div f32
#|frame
#|height	7
#|width	2
#|col	f32	"div_f"
#|col	f32	"div_zero"
#|row	0x3f400000	0x7f800000
#|row	0xc0800000	0xff800000
#|row	null	null
#|row	0x7fc00000	0x7fc00000
#|row	0x7fc00000	0x7f800000
#|row	0x7fc00000	0x7fc00000
#|row	null	0x7fc00000
#|raw same, opt same, full same
#|
#|-- floor_div u32 i32
#|frame
#|height	7
#|width	2
#|col	u32	"fdiv_u"
#|col	i32	"fdiv_i"
#|row	3	3
#|row	0	-4
#|row	4294967295	-4
#|row	null	3
#|row	null	null
#|row	null	null
#|row	null	null
#|raw same, opt same, full same
#|
#|-- mod u32 i32
#|frame
#|height	7
#|width	2
#|col	u32	"mod_u"
#|col	i32	"mod_i"
#|row	1	1
#|row	0	1
#|row	0	-1
#|row	null	-1
#|row	null	0
#|row	null	null
#|row	null	null
#|raw same, opt same, full same
#|
#|-- neg abs sqrt
#|frame
#|height	7
#|width	5
#|col	i32	"neg_i"
#|col	f32	"neg_f"
#|col	i32	"abs_i"
#|col	f32	"abs_f"
#|col	f32	"sqrt_f"
#|row	-7	0xbfc00000	7	0x3fc00000	0x3f9cc471
#|row	7	0x40000000	7	0x40000000	0x7fc00000
#|row	-7	null	7	null	null
#|row	7	0x7fc00000	7	0x7fc00000	0x7fc00000
#|row	-2147483648	0xff800000	-2147483648	0x7f800000	0x7f800000
#|row	null	0x80000000	null	0x00000000	0x00000000
#|row	0	0x00000000	0	0x00000000	0x80000000
#|raw same, opt same, full same
#|
#|-- all operators, zero rows
#|frame
#|height	0
#|width	19
#|col	u32	"add_u"
#|col	i32	"add_i"
#|col	f32	"add_f"
#|col	u32	"sub_u"
#|col	i32	"sub_i"
#|col	f32	"sub_f"
#|col	u32	"mul_u"
#|col	i32	"mul_i"
#|col	f32	"mul_f"
#|col	f32	"div_f"
#|col	u32	"fdiv_u"
#|col	i32	"fdiv_i"
#|col	u32	"mod_u"
#|col	i32	"mod_i"
#|col	i32	"neg_i"
#|col	f32	"neg_f"
#|col	i32	"abs_i"
#|col	f32	"abs_f"
#|col	f32	"sqrt_f"
#|raw same, opt same, full same
#|
#|-- invalid add u32 + i32
#|error	TypeMismatch in add: expected u32, got i32
#|raw same, opt same, full same
#|
#|-- invalid add bool
#|error	TypeMismatch in add: expected numeric, got bool
#|raw same, opt same, full same
#|
#|-- invalid sub u32 - f32
#|error	TypeMismatch in sub: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid mul str
#|error	TypeMismatch in mul: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- invalid add missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid div u32
#|error	TypeMismatch in div: expected f32, got u32
#|raw same, opt same, full same
#|
#|-- invalid div f32 by u32
#|error	TypeMismatch in div: expected f32, got u32
#|raw same, opt same, full same
#|
#|-- invalid floor_div f32
#|error	TypeMismatch in floor_div: expected u32 or i32, got f32
#|raw same, opt same, full same
#|
#|-- invalid floor_div u32 i32
#|error	TypeMismatch in floor_div: expected u32, got i32
#|raw same, opt same, full same
#|
#|-- invalid mod f32
#|error	TypeMismatch in mod: expected u32 or i32, got f32
#|raw same, opt same, full same
#|
#|-- invalid mod u32 i32
#|error	TypeMismatch in mod: expected u32, got i32
#|raw same, opt same, full same
#|
#|-- invalid neg u32
#|error	TypeMismatch in neg: expected i32 or f32, got u32
#|raw same, opt same, full same
#|
#|-- invalid neg str
#|error	TypeMismatch in neg: expected i32 or f32, got str
#|raw same, opt same, full same
#|
#|-- invalid abs u32
#|error	TypeMismatch in abs: expected i32 or f32, got u32
#|raw same, opt same, full same
#|
#|-- invalid abs bool
#|error	TypeMismatch in abs: expected i32 or f32, got bool
#|raw same, opt same, full same
#|
#|-- invalid sqrt i32
#|error	TypeMismatch in sqrt: expected f32, got i32
#|raw same, opt same, full same
#|
#|-- invalid sqrt u32
#|error	TypeMismatch in sqrt: expected f32, got u32
#|raw same, opt same, full same
#|
