# NEW-2 (bench/diff): the interpreter (`bend file.bend`, the JS lane) crashed with "memory
# fault (machine stack overflow?)" on a result of ~2^15 rows or more (a self inner join of 200
# equal-key rows, 40,000 output rows); the native binary was fine. The JS lane runs every
# non-tail call on the host stack, so ANY recursion once per row overflows past ~2^15 rows,
# a cons-guarded one (`f(h) <> go(t)`) included. The culprits on the result path were
# DF.dump (Dump.cell_list, Base String.concat over the row lines, and `++` with the whole
# body as its LEFT operand) and Column.from_scalars (Base List.length, the per-row map
# lists). They are tail calls now.
#
# The checks print a summary of each dump instead of the dump itself: its length in chars,
# its number of lines and its FNV-1a hash over the code points (bench/contract/
# regress_expect.py builds the same dump text in Python and hashes it).
#  - from-scalars: a 70,000-row column built from a list (every 7th row null);
#  - self-join: t (780 rows; k = i % 3, s = "s<i>", x = i / 4) joined with itself on k:
#    3 * 260^2 = 202,800 rows x 5 columns (~8.5M dump chars); eager, raw lazy and optimised
#    lazy (the Source is used twice) must agree;
#  - the join output grouped by k and sorted then cut to 3 rows: printed in full.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/exec.bend as Q
import ./lib/rx.bend as R

# rows 0 .. n-1 (built from the last row down: a tail call)
def ks(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ks(p, R.u(U32.mod(U32.from_nat(p), 3)) <> acc)

def ss(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ss(p, R.s("s" ++ U32.show(U32.from_nat(p))) <> acc)

def xs(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      xs(p, R.f(F32.div(U32.to_f32(U32.from_nat(p)), 4.0)) <> acc)

# row i holds i, or null when i % 7 = 3
def nv(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 7), 3), R.null(), R.u(i))

def ns(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ns(p, nv(U32.from_nat(p)) <> acc)

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("k", ks(780n, Nil{}), D.TU32{}), R.mk("s", ss(780n, Nil{}), D.TStr{}), R.mk("x", xs(780n, Nil{}), D.TF32{})])

def big() -> E.ResT(C.Frame):
  R.frame([R.mk("v", ns(70000n, Nil{}), D.TU32{})])

# ---- the summary of a dump: chars, lines, FNV-1a (32 bit, over code points) ------------------

def sum.go(s: String, +n: U32, +l: U32, +h: U32) -> String:
  match s:
    case SNil{}:
      "chars " ++ U32.show(n) ++ " lines " ++ U32.show(l) ++ " fnv " ++ U32.show(h) ++ "\n"
    case SCon{Chr{+c}, t}:
      sum.go(t, U32.inc(n), U32.add(l, Bool.to_u32(U32.is_eq(c, 10))), U32.mul(U32.xor(h, c), 16777619))

def summary(+tag: String, how: String, r: E.ResT(C.Frame)) -> String:
  "-- " ++ tag ++ " " ++ how ++ "\n" ++ sum.go(DF.dump(r), 0, 0, 2166136261)

def src() -> P.Plan:
  R.src("t", t())

def env() -> P.Env:
  R.env1("t", t())

def selfj() -> P.Plan:
  DF.lazy_inner_join(src(), src(), ["k"], ["k"])

def aggs() -> List<&2, DF.Expr()>:
  [DF.alias(DF.len(), "n"), DF.alias(DF.sum(DF.col("x")), "sx"), DF.alias(DF.n_unique(DF.col("s_right")), "u"), DF.alias(DF.max(DF.col("s")), "ms")]

def keys() -> List<&2, DF.SortKey()>:
  [DF.desc("x"), DF.asc("s_right")]

# eager, raw lazy and optimised lazy one after the other: each 202,800-row frame is dumped and
# dropped before the next is built (three alive at once made the run ~4x slower)
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(summary("NEW-2 from-scalars-70000", "eager", big()))
    IO.print(summary("NEW-2 self-join-202800", "eager", R.e_inner(t(), t(), ["k"], ["k"])))
    r1 : E.ResT(C.Frame) <- Q.Exec.run(selfj(), env())
    IO.print(summary("NEW-2 self-join-202800", "raw", r1))
    r2 : E.ResT(C.Frame) <- DF.collect(selfj(), env())
    IO.print(summary("NEW-2 self-join-202800", "opt", r2))
    R.three("NEW-2 self-join-group-by", R.e_group(R.e_inner(t(), t(), ["k"], ["k"]), [DF.col("k")], aggs()), DF.lazy_group_by(selfj(), [DF.col("k")], aggs()), env(), env())
    R.three("NEW-2 self-join-sort-head", R.e_head(R.e_sort(R.e_inner(t(), t(), ["k"], ["k"]), keys()), 3), DF.lazy_head(DF.lazy_sort(selfj(), keys()), 3), env(), env())
#|-- NEW-2 from-scalars-70000 eager
#|chars 680516 lines 70004 fnv 2704248339
#|
#|-- NEW-2 self-join-202800 eager
#|chars 8460500 lines 202808 fnv 3998022251
#|
#|-- NEW-2 self-join-202800 raw
#|chars 8460500 lines 202808 fnv 3998022251
#|
#|-- NEW-2 self-join-202800 opt
#|chars 8460500 lines 202808 fnv 3998022251
#|
#|-- NEW-2 self-join-group-by eager
#|frame
#|height	3
#|width	5
#|col	u32	"k"
#|col	u32	"n"
#|col	f32	"sx"
#|col	u32	"u"
#|col	str	"ms"
#|row	0	67600	0x4ac85e24	260	"s99"
#|row	1	67600	0x4ac8e22c	260	"s97"
#|row	2	67600	0x4ac96634	260	"s98"
#|
#|-- NEW-2 self-join-group-by raw
#|frame
#|height	3
#|width	5
#|col	u32	"k"
#|col	u32	"n"
#|col	f32	"sx"
#|col	u32	"u"
#|col	str	"ms"
#|row	0	67600	0x4ac85e24	260	"s99"
#|row	1	67600	0x4ac8e22c	260	"s97"
#|row	2	67600	0x4ac96634	260	"s98"
#|
#|-- NEW-2 self-join-group-by opt
#|frame
#|height	3
#|width	5
#|col	u32	"k"
#|col	u32	"n"
#|col	f32	"sx"
#|col	u32	"u"
#|col	str	"ms"
#|row	0	67600	0x4ac85e24	260	"s99"
#|row	1	67600	0x4ac8e22c	260	"s97"
#|row	2	67600	0x4ac96634	260	"s98"
#|
#|-- NEW-2 self-join-sort-head eager
#|frame
#|height	3
#|width	5
#|col	u32	"k"
#|col	str	"s"
#|col	f32	"x"
#|col	str	"s_right"
#|col	f32	"x_right"
#|row	2	"s779"	0x4342c000	"s101"	0x41ca0000
#|row	2	"s779"	0x4342c000	"s104"	0x41d00000
#|row	2	"s779"	0x4342c000	"s107"	0x41d60000
#|
#|-- NEW-2 self-join-sort-head raw
#|frame
#|height	3
#|width	5
#|col	u32	"k"
#|col	str	"s"
#|col	f32	"x"
#|col	str	"s_right"
#|col	f32	"x_right"
#|row	2	"s779"	0x4342c000	"s101"	0x41ca0000
#|row	2	"s779"	0x4342c000	"s104"	0x41d00000
#|row	2	"s779"	0x4342c000	"s107"	0x41d60000
#|
#|-- NEW-2 self-join-sort-head opt
#|frame
#|height	3
#|width	5
#|col	u32	"k"
#|col	str	"s"
#|col	f32	"x"
#|col	str	"s_right"
#|col	f32	"x_right"
#|row	2	"s779"	0x4342c000	"s101"	0x41ca0000
#|row	2	"s779"	0x4342c000	"s104"	0x41d00000
#|row	2	"s779"	0x4342c000	"s107"	0x41d60000
#|
