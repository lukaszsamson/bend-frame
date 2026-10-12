# V02-B1, the input boundary (DESIGN.md 14 "v0.2 post-review: the null-slot invariant"). The facade
# exports the Column type, so a caller can build a column from raw buffers whose null slots hold
# anything. Two consumers read null slots as stored: F4's fill side inside Z1 / Z2 and the chunked
# engine's u32 / i32 tree sum (cexec CX.tsum). DF.from_columns therefore resets every null slot to the
# dtype default (V.Eval.fix; the cells do not change), and F4 alone (Z0) resets the slots itself.
#
# The dirty columns: x f32 = [null (slot -0.0), 1.0, -0.0, null (slot 7.0)], u u32 = [null (slot 5),
# 1, 2, null (slot 9)], s str = [null (slot "junk"), "a", "b", null (slot "z")], mask [0, 1, 1, 0].
#  1. C.Frame.from_columns (no reset): the P0 report names all three columns, 2 bad slots each, the
#     first at row 0 (x: 0x80000000, u: 0x00000005, s: 1 = a non-empty string).
#  2. DF.from_columns: the same dump, "p0 ok".
#  3. on the dirty frame, F4 alone: fill_null(x, 0.0) / fill_null(u, 0) moved and borrowed give
#     x [0x00000000, 0x3f800000, 0x80000000 (a VALID -0.0 is kept), 0x00000000], u [0, 1, 2, 0].
#  4. through DF.from_columns, with_columns(w = u) then select(sum(u)): the reference and the chunked
#     engine at grains 2^0 and 2^2 answer 3. v0.2 before the fix answered 17 at grain 2^0: after the
#     first walk the frame is chunked and sum(u) is the tree sum (cexec CX.tsum.k), which adds the
#     null slots 5 and 9 (a real wrong result reachable through the facade).
# Item 3's borrowed run also passes the dirty x and u through unchanged (a select moves columns, it
# does not normalise them): its report is BAD for them, as the input's is.
#@ cover from_columns null eager
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./../../src/p0.bend as Z
import ./lib/rx.bend as R

def snd.f(r: U32 & Array<F32>) -> Array<F32>:
  (n, a) = r
  a

def snd.w(r: U32 & Array<U32>) -> Array<U32>:
  (n, a) = r
  a

def snd.s(r: U32 & Array<String>) -> Array<String>:
  (n, a) = r
  a

def mask() -> C.Valid:
  C.Mask{snd.w(K.Kernel.from_list(~U32, [0, 1, 1, 0], 0))}

def cols() -> List<&1, C.Named>:
  [C.Named{"x", C.CF32{4, 2n, mask(), snd.f(K.Kernel.from_list(~F32, [F32.neg(0.0), 1.0, F32.neg(0.0), 7.0], 0.0))}}, C.Named{"u", C.CU32{4, 2n, mask(), snd.w(K.Kernel.from_list(~U32, [5, 1, 2, 9], 0))}}, C.Named{"s", C.CStr{4, 2n, mask(), ST.SRaw{snd.s(K.Kernel.from_list(~String, ["junk", "a", "b", "z"], ""))}}}]

# no reset: what a caller gets by going around the facade
def dirty() -> E.ResT(C.Frame):
  C.Frame.from_columns(cols())

def clean() -> E.ResT(C.Frame):
  DF.from_columns(cols())

def fills() -> List<&2, X.Expr>:
  [DF.alias(DF.fill_null(DF.col("x"), DF.lit_f32(0.0)), "fx"), DF.alias(DF.fill_null(DF.col("u"), DF.lit_u32(0)), "fu")]

def fills_b() -> List<&2, X.Expr>:
  [DF.alias(DF.fill_null(DF.col("x"), DF.lit_f32(0.0)), "fx"), DF.alias(DF.fill_null(DF.col("u"), DF.lit_u32(0)), "fu"), DF.col("x"), DF.col("u")]

def sums() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.col("u")), "su")]

def lz(+how: String, r: E.ResT(C.Frame)) -> String:
  "-- B1 raw " ++ how ++ "\n" ++ Z.P0.dump(r)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- B1 raw dirty\n" ++ Z.P0.dump(dirty()))
    IO.print("-- B1 raw from_columns\n" ++ Z.P0.dump(clean()))
    IO.print("-- B1 raw F4 moved\n" ++ Z.P0.dump(R.e_select(dirty(), fills())))
    IO.print("-- B1 raw F4 borrowed\n" ++ Z.P0.dump(R.e_select(dirty(), fills_b())))
    r0 : E.ResT(C.Frame) <- DF.collect_raw(DF.lazy_select(DF.lazy_with_columns(R.src("t", clean()), [DF.alias(DF.col("u"), "w")]), sums()), R.env1("t", clean()))
    r1 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(0n), DF.lazy_select(DF.lazy_with_columns(R.src("t", clean()), [DF.alias(DF.col("u"), "w")]), sums()), R.env1("t", clean()))
    r2 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(2n), DF.lazy_select(DF.lazy_with_columns(R.src("t", clean()), [DF.alias(DF.col("u"), "w")]), sums()), R.env1("t", clean()))
    IO.print(lz("sum reference", r0) ++ lz("sum c0", r1) ++ lz("sum c2", r2))
#|-- B1 raw dirty
#|frame
#|height	4
#|width	3
#|col	f32	"x"
#|col	u32	"u"
#|col	str	"s"
#|row	null	null	null
#|row	0x3f800000	1	"a"
#|row	0x80000000	2	"b"
#|row	null	null	null
#|p0 BAD [col "x": 2 null slot(s) not the default, first row 0 holds 0x80000000; 0 validity word(s) not 0/1; 0 bool word(s) not 0/1] [col "u": 2 null slot(s) not the default, first row 0 holds 0x00000005; 0 validity word(s) not 0/1; 0 bool word(s) not 0/1] [col "s": 2 null slot(s) not the default, first row 0 holds 0x00000001; 0 validity word(s) not 0/1; 0 bool word(s) not 0/1]
#|
#|-- B1 raw from_columns
#|frame
#|height	4
#|width	3
#|col	f32	"x"
#|col	u32	"u"
#|col	str	"s"
#|row	null	null	null
#|row	0x3f800000	1	"a"
#|row	0x80000000	2	"b"
#|row	null	null	null
#|p0 ok
#|
#|-- B1 raw F4 moved
#|frame
#|height	4
#|width	2
#|col	f32	"fx"
#|col	u32	"fu"
#|row	0x00000000	0
#|row	0x3f800000	1
#|row	0x80000000	2
#|row	0x00000000	0
#|p0 ok
#|
#|-- B1 raw F4 borrowed
#|frame
#|height	4
#|width	4
#|col	f32	"fx"
#|col	u32	"fu"
#|col	f32	"x"
#|col	u32	"u"
#|row	0x00000000	0	null	null
#|row	0x3f800000	1	0x3f800000	1
#|row	0x80000000	2	0x80000000	2
#|row	0x00000000	0	null	null
#|p0 BAD [col "x": 2 null slot(s) not the default, first row 0 holds 0x80000000; 0 validity word(s) not 0/1; 0 bool word(s) not 0/1] [col "u": 2 null slot(s) not the default, first row 0 holds 0x00000005; 0 validity word(s) not 0/1; 0 bool word(s) not 0/1]
#|
#|-- B1 raw sum reference
#|frame
#|height	1
#|width	1
#|col	u32	"su"
#|row	3
#|p0 ok
#|-- B1 raw sum c0
#|frame
#|height	1
#|width	1
#|col	u32	"su"
#|row	3
#|p0 ok
#|-- B1 raw sum c2
#|frame
#|height	1
#|width	1
#|col	u32	"su"
#|row	3
#|p0 ok
#|
