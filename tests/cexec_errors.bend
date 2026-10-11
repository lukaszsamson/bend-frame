# v0.2 T5.3: error texts and error PRECEDENCE of the chunked runner (src/cexec.bend) against the
# reference runner. v0.1 evaluates expression-major: every row of expression 1, then expression 2;
# inside an expression, instruction order (postfix), then the lowest row; static errors (typing, names,
# duplicate outputs) before any data. A per-leaf walk sees a later expression's error in an earlier leaf
# first, and a leaf's strict-cast text names a LOCAL row: the runner borrows its input through the walk
# and, when any leaf failed, runs the reference operator on the flattened input, so the error is v0.1's.
# Frame t(37) (tests/lib/cxgen.bend): num is "<3 i>" except "bad" at row 13 and "worse" at row 22 (null at
# i % 10 = 9); n = (i % 9) - 4 (row 0 holds -4; null at i % 8 = 6). At grain 2^2 rows 13 and 22 sit in
# leaves 3 and 5, row 0 in leaf 0; at 2^1 in leaves 6 / 11 / 0.
#  - competing strict casts in different expressions (both orders), operands of one expression (both
#    orders: instruction order wins over the row), rows of one expression in different leaves, inside a
#    filter predicate, a select and a when branch; at grains 2^1, 2^2, 2^3;
#  - rows renumbered by an earlier filter / concat (the error names the row of the operator's input);
#  - static before data: an unknown column, a duplicate output, a type mismatch next to a failing cast;
#    a failing literal cast (the ghost fails: flat);
#  - the Filter + plain Select root: the predicate's data error before the select's missing column;
#  - try_cast never fails.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/plan.bend as P
import ./lib/cxgen.bend as T

def c(+tag: String, +g: Nat, +p: P.Plan) -> String:
  T.cmp(tag, g, p, T.envt(37), T.envt(37))

def cu(e: DF.Expr()) -> DF.Expr():
  DF.cast(e, D.TU32{})

def wc(+es: List<&2, DF.Expr()>) -> P.Plan:
  DF.lazy_with_columns(T.srct(37), es)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(c("expr 1 row 13 vs expr 2 row 0", 2n, wc([DF.alias(cu(DF.col("num")), "a"), DF.alias(cu(DF.col("n")), "b")])))
    IO.print(c("expr 1 row 0 vs expr 2 row 13", 2n, wc([DF.alias(cu(DF.col("n")), "b"), DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("operand 1 row 13 vs operand 2 row 0", 2n, wc([DF.alias(DF.add(cu(DF.col("num")), cu(DF.col("n"))), "a")])))
    IO.print(c("operand 1 row 0 vs operand 2 row 13", 2n, wc([DF.alias(DF.add(cu(DF.col("n")), cu(DF.col("num"))), "a")])))
    IO.print(c("one expr, rows 13 and 22 (leaves 3, 5)", 2n, wc([DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("one expr, rows 13 and 22 at 2^1", 1n, wc([DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("expr 1 row 13 vs expr 2 row 0 at 2^1", 1n, wc([DF.alias(cu(DF.col("num")), "a"), DF.alias(cu(DF.col("n")), "b")])))
    IO.print(c("expr 1 row 13 vs expr 2 row 0 at 2^3", 3n, wc([DF.alias(cu(DF.col("num")), "a"), DF.alias(cu(DF.col("n")), "b")])))
    IO.print(c("filter predicate cast", 2n, DF.lazy_filter(T.srct(37), DF.gt(cu(DF.col("num")), DF.lit_u32(5)))))
    IO.print(c("select: expr 1 row 13 vs expr 2 row 0", 2n, DF.lazy_select(T.srct(37), [DF.alias(DF.mul(cu(DF.col("num")), DF.lit_u32(2)), "a"), DF.alias(cu(DF.col("n")), "b")])))
    IO.print(c("when branch cast", 2n, wc([DF.alias(DF.when(DF.lt(DF.col("id"), DF.lit_u32(20)), cu(DF.col("num")), DF.lit_u32(0)), "w")])))
    IO.print(c("after filter id>10: row 2", 2n, DF.lazy_with_columns(DF.lazy_filter(T.srct(37), DF.gt(DF.col("id"), DF.lit_u32(10))), [DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("after filter id>13: row 8", 2n, DF.lazy_with_columns(DF.lazy_filter(T.srct(37), DF.gt(DF.col("id"), DF.lit_u32(13))), [DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("after concat + filter id>20: row 1", 2n, DF.lazy_with_columns(DF.lazy_filter(DF.lazy_concat_vertical([T.srct(37), T.srct(37)]), DF.gt(DF.col("id"), DF.lit_u32(20))), [DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("static: unknown column after a failing cast", 2n, wc([DF.alias(cu(DF.col("num")), "a"), DF.col("nope")])))
    IO.print(c("static: duplicate output after a failing cast", 2n, wc([DF.alias(cu(DF.col("num")), "x"), DF.alias(DF.col("id"), "x")])))
    IO.print(c("static: type mismatch after a failing cast", 2n, wc([DF.alias(cu(DF.col("num")), "a"), DF.add(DF.col("qty"), DF.col("price"))])))
    IO.print(c("literal cast (ghost fails: flat)", 2n, wc([DF.alias(DF.lit_i32(3000000000), "big"), DF.alias(cu(DF.col("num")), "a")])))
    IO.print(c("Filter + Select root: predicate error first", 2n, DF.lazy_select(DF.lazy_filter(T.srct(37), DF.gt(cu(DF.col("num")), DF.lit_u32(5))), [DF.col("id"), DF.col("nope")])))
    IO.print(c("Filter + Select root: select error", 2n, DF.lazy_select(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(5))), [DF.col("id"), DF.col("nope")])))
    IO.print(c("try_cast never fails", 2n, wc([DF.alias(DF.try_cast(DF.col("num"), D.TU32{}), "a"), DF.alias(DF.try_cast(DF.col("n"), D.TU32{}), "b")])))
#|expr 1 row 13 vs expr 2 row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|expr 1 row 0 vs expr 2 row 13: error: InvalidOperation: cast i32 to u32: row 0 holds -4 [same] walks=1 flat=1 cin=1 cout=1
#|operand 1 row 13 vs operand 2 row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|operand 1 row 0 vs operand 2 row 13: error: InvalidOperation: cast i32 to u32: row 0 holds -4 [same] walks=1 flat=1 cin=1 cout=1
#|one expr, rows 13 and 22 (leaves 3, 5): error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|one expr, rows 13 and 22 at 2^1: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|expr 1 row 13 vs expr 2 row 0 at 2^1: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|expr 1 row 13 vs expr 2 row 0 at 2^3: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|filter predicate cast: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|select: expr 1 row 13 vs expr 2 row 0: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|when branch cast: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=1 flat=1 cin=1 cout=1
#|after filter id>10: row 2: error: InvalidOperation: cast str to u32: row 2 holds "bad" [same] walks=3 flat=1 cin=1 cout=1
#|after filter id>13: row 8: error: InvalidOperation: cast str to u32: row 8 holds "worse" [same] walks=3 flat=1 cin=1 cout=1
#|after concat + filter id>20: row 1: error: InvalidOperation: cast str to u32: row 1 holds "worse" [same] walks=3 flat=2 cin=1 cout=1
#|static: unknown column after a failing cast: error: ColumnNotFound: nope [same] walks=0 flat=1 cin=0 cout=0
#|static: duplicate output after a failing cast: error: DuplicateColumn: x [same] walks=0 flat=1 cin=0 cout=0
#|static: type mismatch after a failing cast: error: TypeMismatch in add: expected u32, got f32 [same] walks=0 flat=1 cin=0 cout=0
#|literal cast (ghost fails: flat): error: InvalidOperation: cast u32 to i32: row 0 holds 3000000000 [same] walks=0 flat=1 cin=0 cout=0
#|Filter + Select root: predicate error first: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same] walks=0 flat=1 cin=0 cout=0
#|Filter + Select root: select error: error: ColumnNotFound: nope [same] walks=0 flat=1 cin=0 cout=0
#|try_cast never fails: h=37 [same] walks=1 flat=0 cin=1 cout=1
