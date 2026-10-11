# v0.2 T5.5: the chunked runner's compile-once leaf entry and the one-walk filter (src/cexec.bend CX.pc /
# CX.cel / CX.erun, CX.p3) against the reference runner, at SMALL grains (2^0: one row per leaf, 2^1, 2^2)
# so that every leaf boundary sits between competing rows. Each line: the reference's height or error,
# [same] when DF.dump of the two answers is equal, and the chunked runner's counters (tests/lib/cxgen.bend).
# Frame t(37): num is "<3 i>" but "bad" at row 13 and "worse" at row 22 (null at i % 10 = 9); n = (i % 9)
# - 4 (row 0 holds -4; null at i % 8 = 6); d a Dictionary ("k<i % 3>"); qty (37 i + 11) mod 100 (max 99
# at row 32); price i / 4 (NaN at i % 13 = 5, -0.0 at 6, +inf at 7); ok null at i % 7 = 3, else i % 3 != 0.
#  - errors through the compiled entry (the expressions typed and compiled ONCE per walk, the code run per
#    leaf, a failing leaf sends the operator to the flat rerun): competing strict casts in two expressions
#    (both orders), in two operands of one expression (instruction order), in a filter predicate (general
#    path: not F5), a Filter + plain Select root, a select, and a cast of a Dictionary column (the leaf
#    wraps its codes back into the Dict) against a cast of a Raw column, in both orders;
#  - the one-walk filter (an F5 predicate: mask and compaction in one walk per leaf, walks=1): bool and
#    u32 / i32 / f32 comparisons (NaN > x, nulls dropped), the leaf plans (one comparison, one bool column,
#    a bool column and a comparison in both orders, two passes), a hoisted tree aggregation (`qty >= max(qty)`),
#    a Filter + plain Select root that keeps a predicate column and a Dictionary column, mostly-empty
#    leaves, and a chain filter -> with_columns -> Filter + Select;
#  - with_columns through the compiled entry reading a Dictionary column (wrapped) and none (not wrapped);
#  - the entry itself: CX.erun(CX.code(e), f) against CX.efull(f, e) (Eval.slot.mv: typed and compiled on
#    the leaf) on the whole frame t(37) and on a leaf-sized slice (rows 10..15, a strict cast failing at
#    its local row 3), for a failing cast, q2's revenue (fused fragments, a fill_null), a literal (the
#    broadcast), a when and an is_in over the Dictionary column: the same column (DF.dump) or error.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/plan.bend as P
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/cexec.bend as QC
import ./lib/cxgen.bend as T

def c(+tag: String, +g: Nat, +p: P.Plan) -> String:
  T.cmp(tag, g, p, T.envt(37), T.envt(37))

def cu(e: DF.Expr()) -> DF.Expr():
  DF.cast(e, D.TU32{})

def wc(+es: List<&2, DF.Expr()>) -> P.Plan:
  DF.lazy_with_columns(T.srct(37), es)

def flt(+e: DF.Expr()) -> P.Plan:
  DF.lazy_filter(T.srct(37), e)

def chain() -> P.Plan:
  DF.lazy_select(DF.lazy_filter(DF.lazy_with_columns(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(20))), [DF.alias(DF.add(DF.col("qty"), DF.col("id")), "qi")]), DF.lt(DF.col("qi"), DF.lit_u32(90))), [DF.col("qi"), DF.col("d")])

def one.d(r: C.Column & U32) -> String:
  (c, +n) = r
  DF.dump(Done{C.Frame{n, C.Named{"x", c} <> Nil{}}})

def one.k(rc: E.ResT(C.Column)) -> String:
  match rc:
    case Fail{e}:
      DF.dump(Fail{e})
    case Done{c}:
      one.d(C.Column.len(c))

def one(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  one.k(rc)

# the compiled leaf entry against Eval.slot.mv's (CX.efull) on two copies of a frame
def entry(+tag: String, +e: DF.Expr(), f1: C.Frame, f2: C.Frame) -> String:
  tag ++ ": " ++ Bool.pick(String, String.eq(one(QC.CX.efull(f1, e)), one(QC.CX.erun(QC.CX.code(e), f2))), "[same]", "[DIFF]")

def ent(+tag: String, +e: DF.Expr()) -> String:
  entry(tag ++ " (37 rows)", e, T.t(37), T.t(37)) ++ ", " ++ entry("leaf 10..15", e, T.tr(10, 6), T.tr(10, 6))

def rev() -> DF.Expr():
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("disc"), DF.lit_f32(0.0))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(c("2^0 expr 1 rows 13 / 22 vs expr 2 row 0", 0n, wc([DF.alias(cu(DF.col("num")), "a"), DF.alias(cu(DF.col("n")), "b")])))
    IO.print(c("2^0 expr 1 row 0 vs expr 2 rows 13 / 22", 0n, wc([DF.alias(cu(DF.col("n")), "b"), DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("2^0 operand 1 row 0 vs operand 2 row 13", 0n, wc([DF.alias(DF.add(cu(DF.col("n")), cu(DF.col("num"))), "a")])))
    IO.print(c("2^0 operand 1 row 13 vs operand 2 row 0", 0n, wc([DF.alias(DF.add(cu(DF.col("num")), cu(DF.col("n"))), "a")])))
    IO.print(c("2^1 filter: cast predicate (general path)", 1n, flt(DF.and(DF.col("ok"), DF.gt(cu(DF.col("num")), DF.lit_u32(5))))))
    IO.print(c("2^0 filter: conjunct 1 row 0 vs conjunct 2 row 13", 0n, flt(DF.and(DF.gt(cu(DF.col("n")), DF.lit_u32(0)), DF.gt(cu(DF.col("num")), DF.lit_u32(5))))))
    IO.print(c("2^1 Filter + Select root: cast predicate", 1n, DF.lazy_select(flt(DF.gt(cu(DF.col("num")), DF.lit_u32(5))), [DF.col("id"), DF.col("d")])))
    IO.print(c("2^0 select: expr 1 row 13 vs expr 2 row 0", 0n, DF.lazy_select(T.srct(37), [DF.alias(DF.mul(cu(DF.col("num")), DF.lit_u32(2)), "a"), DF.alias(cu(DF.col("n")), "b")])))
    IO.print(c("2^1 Dictionary cast row 0 vs Raw cast row 13", 1n, wc([DF.alias(cu(DF.col("d")), "b"), DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("2^1 Raw cast row 13 vs Dictionary cast row 0", 1n, wc([DF.alias(cu(DF.col("num")), "a"), DF.alias(cu(DF.col("d")), "b")])))
    IO.print(c("2^0 one walk: ok & qty > 50", 0n, flt(DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))))
    IO.print(c("2^1 one walk: ok & qty > 50", 1n, flt(DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))))
    IO.print(c("2^2 one walk: ok & qty > 50", 2n, flt(DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))))
    IO.print(c("2^1 one walk: price > 2.0 (NaN, inf, -0.0)", 1n, flt(DF.gt(DF.col("price"), DF.lit_f32(2.0)))))
    IO.print(c("2^1 one walk: n < 0 (i32, nulls)", 1n, flt(DF.lt(DF.col("n"), DF.lit_i32(0)))))
    IO.print(c("2^1 one walk: qty >= max(qty) (hoisted)", 1n, flt(DF.ge(DF.col("qty"), DF.max(DF.col("qty"))))))
    IO.print(c("2^0 one walk: qty > 98 (empty leaves)", 0n, flt(DF.gt(DF.col("qty"), DF.lit_u32(98)))))
    IO.print(c("2^1 one walk: (qty > 20) & ok (bool column second)", 1n, flt(DF.and(DF.gt(DF.col("qty"), DF.lit_u32(20)), DF.col("ok")))))
    IO.print(c("2^0 one walk: ok (a bool column)", 0n, flt(DF.col("ok"))))
    IO.print(c("2^1 one walk: ok & qty > 20 & price < 5.0 (two passes)", 1n, flt(DF.and(DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(20))), DF.lt(DF.col("price"), DF.lit_f32(5.0))))))
    IO.print(c("2^1 one walk Filter + Select: qty, d, id", 1n, DF.lazy_select(flt(DF.and(DF.gt(DF.col("qty"), DF.lit_u32(20)), DF.col("ok"))), [DF.col("qty"), DF.col("d"), DF.col("id")])))
    IO.print(c("2^1 chain: filter, with_columns, Filter + Select", 1n, chain()))
    IO.print(c("2^1 with_columns reading a Dictionary column", 1n, wc([DF.alias(DF.is_in(DF.col("d"), [D.SStr{"k1"}]), "k1"), DF.alias(DF.starts_with(DF.col("s"), "r1"), "s1")])))
    IO.print(ent("entry: cast(num)", cu(DF.col("num"))))
    IO.print(ent("entry: revenue", rev()))
    IO.print(ent("entry: literal", DF.lit_u32(7)))
    IO.print(ent("entry: when", DF.when(DF.lt(DF.col("id"), DF.lit_u32(12)), DF.col("qty"), DF.add(DF.col("qty"), DF.lit_u32(1)))))
    IO.print(ent("entry: is_in over a Dictionary column", DF.is_in(DF.col("d"), [D.SStr{"k1"}, D.SStr{"k2"}])))
    IO.print(c("2^0 with_columns reading no Dictionary column", 0n, wc([DF.alias(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), "r")])))
#|2^0 expr 1 rows 13 / 22 vs expr 2 row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|2^0 expr 1 row 0 vs expr 2 rows 13 / 22: error: InvalidOperation: cast i32 to u32: row 0 holds -4 [same] walks=1 flat=1 cin=1 cout=1
#|2^0 operand 1 row 0 vs operand 2 row 13: error: InvalidOperation: cast i32 to u32: row 0 holds -4 [same] walks=1 flat=1 cin=1 cout=1
#|2^0 operand 1 row 13 vs operand 2 row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|2^1 filter: cast predicate (general path): error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|2^0 filter: conjunct 1 row 0 vs conjunct 2 row 13: error: InvalidOperation: cast i32 to u32: row 0 holds -4 [same] walks=1 flat=1 cin=1 cout=1
#|2^1 Filter + Select root: cast predicate: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|2^0 select: expr 1 row 13 vs expr 2 row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|2^1 Dictionary cast row 0 vs Raw cast row 13: error: InvalidOperation: cast str to u32: row 0 holds "k0" [same] walks=1 flat=1 cin=1 cout=1
#|2^1 Raw cast row 13 vs Dictionary cast row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|2^0 one walk: ok & qty > 50: h=11 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk: ok & qty > 50: h=11 [same] walks=1 flat=0 cin=1 cout=1
#|2^2 one walk: ok & qty > 50: h=11 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk: price > 2.0 (NaN, inf, -0.0): h=28 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk: n < 0 (i32, nulls): h=16 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk: qty >= max(qty) (hoisted): h=1 [same] walks=1 flat=0 cin=1 cout=1
#|2^0 one walk: qty > 98 (empty leaves): h=1 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk: (qty > 20) & ok (bool column second): h=16 [same] walks=1 flat=0 cin=1 cout=1
#|2^0 one walk: ok (a bool column): h=21 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk: ok & qty > 20 & price < 5.0 (two passes): h=6 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 one walk Filter + Select: qty, d, id: h=16 [same] walks=1 flat=0 cin=1 cout=1
#|2^1 chain: filter, with_columns, Filter + Select: h=20 [same] walks=3 flat=0 cin=1 cout=1
#|2^1 with_columns reading a Dictionary column: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|entry: cast(num) (37 rows): [same], leaf 10..15: [same]
#|entry: revenue (37 rows): [same], leaf 10..15: [same]
#|entry: literal (37 rows): [same], leaf 10..15: [same]
#|entry: when (37 rows): [same], leaf 10..15: [same]
#|entry: is_in over a Dictionary column (37 rows): [same], leaf 10..15: [same]
#|2^0 with_columns reading no Dictionary column: h=37 [same] walks=1 flat=0 cin=1 cout=1
