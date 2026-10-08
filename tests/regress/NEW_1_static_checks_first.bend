# NEW-1 (bench/diff, seed 1; tests/diff/d0001, d0002): eager select and group_by evaluated the
# data before their static DuplicateColumn check, so a data error (a failing strict cast)
# shadowed it, while lazy (Plan.schema) and the contract (DESIGN.md 15.9 "order of errors")
# report the static error first. Every eager verb now makes ALL its static checks (typing
# through the shared analysis, output names, keys) before it evaluates any data, in
# Plan.schema's order. Audit, one scenario per verb (b = ["café"] does not cast to f32):
#  - select / group_by: DuplicateColumn before the cast error (the defect);
#  - group_by: DuplicateColumn before the row cap (a zero-column frame of 2^23 + 1 rows;
#    before the fix eager reported "too many rows");
#  - sort: ColumnNotFound for the FIRST missing key (Sort.argsort walks the keys last first,
#    so eager reported the last missing key);
#  - with_columns, filter, join: already static-first (guards). A join whose right non-key
#    column clashes after the `_right` suffix is DuplicateColumn before the row cap.
#  - the 15.9 admissibility rule: a static error in a LATER verb and a data error in an
#    earlier one differ by design (eager runs verb by verb, lazy types the whole plan).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def cafe() -> String:
  "caf" ++ SCon{Chr{233}, SNil{}}

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1)], D.TU32{}), R.mk("b", [R.s(cafe())], D.TStr{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

# the failing cast
def bad() -> X.Expr:
  DF.cast(DF.col("b"), D.TF32{})

# 2^23 + 1 rows, no columns (no data allocated)
def z() -> E.ResT(C.Frame):
  R.zcols(8388609)

# 2900 rows of 1 in each of the named u32 columns (8.41M join rows: over the cap)
def ones.go(ns: List<&2, String>) -> List<&1, C.Named>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      C.Named{n, C.CU32{2900, 12n, C.AllValid{}, Array.new(U32, 12n, 1)}} <> ones.go(rest)

def ones(ns: List<&2, String>) -> E.ResT(C.Frame):
  DF.from_columns(ones.go(ns))

def jl() -> E.ResT(C.Frame):
  ones(["k", "v", "v_right"])

def jr() -> E.ResT(C.Frame):
  ones(["k", "v"])

def jplan() -> P.Plan:
  DF.lazy_inner_join(R.src("l", jl()), R.src("r", jr()), ["k"], ["k"])

def jenv() -> P.Env:
  R.env_add(R.env1("l", jl()), "r", jr())

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("NEW-1 select-dup-after-cast", R.e_select(t(), [DF.alias(bad(), "x"), DF.alias(DF.col("b"), "x")]), DF.lazy_select(src(), [DF.alias(bad(), "x"), DF.alias(DF.col("b"), "x")]), env(), env())
    R.three("NEW-1 select-cast-is-the-dup", R.e_select(t(), [DF.col("a"), DF.alias(bad(), "a")]), DF.lazy_select(src(), [DF.col("a"), DF.alias(bad(), "a")]), env(), env())
    R.three("NEW-1 group-by-agg-dup", R.e_group(t(), [DF.col("b")], [DF.sum(bad())]), DF.lazy_group_by(src(), [DF.col("b")], [DF.sum(bad())]), env(), env())
    R.three("NEW-1 group-by-key-cast-dup", R.e_group(t(), [DF.alias(bad(), "k")], [DF.alias(DF.len(), "k")]), DF.lazy_group_by(src(), [DF.alias(bad(), "k")], [DF.alias(DF.len(), "k")]), env(), env())
    R.three("NEW-1 group-by-dup-before-cap", R.e_group(z(), [DF.alias(DF.lit_u32(1), "k")], [DF.alias(DF.len(), "k")]), DF.lazy_group_by(R.src("t", z()), [DF.alias(DF.lit_u32(1), "k")], [DF.alias(DF.len(), "k")]), R.env1("t", z()), R.env1("t", z()))
    R.three("NEW-1 sort-first-missing-key", R.e_sort(t(), [DF.asc("a"), DF.asc("p"), DF.desc("q")]), DF.lazy_sort(src(), [DF.asc("a"), DF.asc("p"), DF.desc("q")]), env(), env())
    R.three("NEW-1 with-columns-dup-after-cast", R.e_with(t(), [DF.alias(bad(), "x"), DF.alias(DF.col("a"), "x")]), DF.lazy_with_columns(src(), [DF.alias(bad(), "x"), DF.alias(DF.col("a"), "x")]), env(), env())
    R.three("NEW-1 filter-type-before-cast", R.e_filter(t(), bad()), DF.lazy_filter(src(), bad()), env(), env())
    R.three("NEW-1 join-clash-before-cap", R.e_inner(jl(), jr(), ["k"], ["k"]), jplan(), jenv(), jenv())
    R.three("NEW-1 15.9-inadmissible", R.e_sort(R.e_select(t(), [DF.alias(bad(), "x")]), [DF.asc("p")]), DF.lazy_sort(DF.lazy_select(src(), [DF.alias(bad(), "x")]), [DF.asc("p")]), env(), env())
#|-- NEW-1 select-dup-after-cast eager
#|error	DuplicateColumn: x
#|
#|-- NEW-1 select-dup-after-cast raw
#|error	DuplicateColumn: x
#|
#|-- NEW-1 select-dup-after-cast opt
#|error	DuplicateColumn: x
#|
#|-- NEW-1 select-cast-is-the-dup eager
#|error	DuplicateColumn: a
#|
#|-- NEW-1 select-cast-is-the-dup raw
#|error	DuplicateColumn: a
#|
#|-- NEW-1 select-cast-is-the-dup opt
#|error	DuplicateColumn: a
#|
#|-- NEW-1 group-by-agg-dup eager
#|error	DuplicateColumn: b
#|
#|-- NEW-1 group-by-agg-dup raw
#|error	DuplicateColumn: b
#|
#|-- NEW-1 group-by-agg-dup opt
#|error	DuplicateColumn: b
#|
#|-- NEW-1 group-by-key-cast-dup eager
#|error	DuplicateColumn: k
#|
#|-- NEW-1 group-by-key-cast-dup raw
#|error	DuplicateColumn: k
#|
#|-- NEW-1 group-by-key-cast-dup opt
#|error	DuplicateColumn: k
#|
#|-- NEW-1 group-by-dup-before-cap eager
#|error	DuplicateColumn: k
#|
#|-- NEW-1 group-by-dup-before-cap raw
#|error	DuplicateColumn: k
#|
#|-- NEW-1 group-by-dup-before-cap opt
#|error	DuplicateColumn: k
#|
#|-- NEW-1 sort-first-missing-key eager
#|error	ColumnNotFound: p
#|
#|-- NEW-1 sort-first-missing-key raw
#|error	ColumnNotFound: p
#|
#|-- NEW-1 sort-first-missing-key opt
#|error	ColumnNotFound: p
#|
#|-- NEW-1 with-columns-dup-after-cast eager
#|error	DuplicateColumn: x
#|
#|-- NEW-1 with-columns-dup-after-cast raw
#|error	DuplicateColumn: x
#|
#|-- NEW-1 with-columns-dup-after-cast opt
#|error	DuplicateColumn: x
#|
#|-- NEW-1 filter-type-before-cast eager
#|error	TypeMismatch in filter: expected bool, got f32
#|
#|-- NEW-1 filter-type-before-cast raw
#|error	TypeMismatch in filter: expected bool, got f32
#|
#|-- NEW-1 filter-type-before-cast opt
#|error	TypeMismatch in filter: expected bool, got f32
#|
#|-- NEW-1 join-clash-before-cap eager
#|error	DuplicateColumn: v_right
#|
#|-- NEW-1 join-clash-before-cap raw
#|error	DuplicateColumn: v_right
#|
#|-- NEW-1 join-clash-before-cap opt
#|error	DuplicateColumn: v_right
#|
#|-- NEW-1 15.9-inadmissible eager
#|error	InvalidOperation: cast str to f32: row 0 holds "café"
#|
#|-- NEW-1 15.9-inadmissible raw
#|error	ColumnNotFound: p
#|
#|-- NEW-1 15.9-inadmissible opt
#|error	ColumnNotFound: p
#|
