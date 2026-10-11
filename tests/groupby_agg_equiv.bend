# group_by with several aggregates over 2^14 rows and more (v0.2 T5.4, DESIGN.md 16.4 D4 / 14 T5.4).
# The T5.4 fork of the aggregate scatters (2x2, each lane owning a clone of the group ids) was built,
# measured and REMOVED: it did not pay on q3 (bench/w5/t54_groupby_fork.patch is the exact patch). The T5.4b
# fused single-pass scatter (one read of the group ids for every aggregate; bench/w5/t54b_groupby_fused.patch)
# passed this test, was measured and REMOVED too (DESIGN.md 14 T5.4b). This test keeps the contract those
# had to meet, so any later fork of the aggregates (or a fused scatter) is held to it:
#   * for 2, 3, 4, 7 and 8 aggregates over 20000 rows (nulls, F32 NaN / -0.0 / inf, str min, a literal,
#     Len, First / Last, NUnique, Median) every result column equals (dump, F32 bits) the same
#     aggregate run ALONE
#   * the absolute values of a few columns, derived by hand from the generator below
#   * 16383 and 16384 rows (the old fork threshold) give the same columns too
#   * errors: the first failing aggregate INPUT in aggregate order wins, whatever the later ones are
#     (cast errors at different rows), also behind aggregates that succeed; std over a str column is a
#     static TypeMismatch, found before any data is evaluated, whatever else the aggregate list holds
# Generator (n = 20000 rows, d = 15):
#   k  u32  i mod 5                                     5 groups, first appearance 0 1 2 3 4, 4000 rows each
#   x  u32  i * 2654435761 (mod 2^32)
#   y  i32  the same words
#   f  f32  null when i mod 4 = 3 (the slot holds 0.0); else (i * 37 mod 1009) / 8, except i = 12345: +inf,
#           i mod 997 = 5: NaN, i mod 991 = 3 (and valid): -0.0
#   g  f32  (i * 13 mod 997) / 3
#   s  str  show(i mod 13)  ("0".."12", numeric text)
#   b1 str  show(i), row 9000 holds "bad1";  b2 str  show(i), row 5 holds "bad2"
# Hand-derived: every group holds 4000 rows (i = g + 5j, j < 4000); of them rows with i mod 4 = 3 are
# null in f: (g + j) mod 4 runs over each residue 1000 times, so 1000 null, count(f) = 3000.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/expr.bend as X
import ./../src/groupby.bend as G

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def is_null(+i: U32) -> Bool:
  U32.is_eq(U32.mod(i, 4), 3)

def vf(+i: U32) -> U32:
  Bool.pick(U32, is_null(i), 0, 1)

def fv(+i: U32) -> F32:
  +v = F32.div(U32.to_f32(U32.mod(U32.mul(i, 37), 1009)), 8.0)
  Bool.pick(F32, is_null(i), 0.0, Bool.pick(F32, U32.is_eq(i, 12345), inf(), Bool.pick(F32, U32.is_eq(U32.mod(i, 997), 5), nan(), Bool.pick(F32, U32.is_eq(U32.mod(i, 991), 3), F32.neg(0.0), v))))

def gv(+i: U32) -> F32:
  F32.div(U32.to_f32(U32.mod(U32.mul(i, 13), 997)), 3.0)

def word(+i: U32) -> U32:
  U32.mul(i, 2654435761)

def sv(+i: U32) -> String:
  U32.show(U32.mod(i, 13))

def bv1(+i: U32) -> String:
  Bool.pick(String, U32.is_eq(i, 9000), "bad1", U32.show(i))

def bv2(+i: U32) -> String:
  Bool.pick(String, U32.is_eq(i, 5), "bad2", U32.show(i))

def d_of(+n: U32) -> Nat:
  K.Kernel.depth_for(n)

def kcol(+n: U32, +d: Nat) -> C.Column:
  C.CU32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => U32.mod(i, 5)), n, d, K.Kernel.iota(n, d), 0)}

def xcol(+n: U32, +d: Nat) -> C.Column:
  C.CU32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), n, d, K.Kernel.iota(n, d), 0)}

def ycol(+n: U32, +d: Nat) -> C.Column:
  C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), n, d, K.Kernel.iota(n, d), 0)}

def fcol(+n: U32, +d: Nat) -> C.Column:
  C.CF32{n, d, C.Mask{K.Kernel.map(~U32, ~U32, ~(i => vf(i)), n, d, K.Kernel.iota(n, d), 0)}, K.Kernel.map(~U32, ~F32, ~(i => fv(i)), n, d, K.Kernel.iota(n, d), 0.0)}

def gcol(+n: U32, +d: Nat) -> C.Column:
  C.CF32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~F32, ~(i => gv(i)), n, d, K.Kernel.iota(n, d), 0.0)}

def scol(+n: U32, +d: Nat) -> C.Column:
  C.CStr{n, d, C.AllValid{}, ST.SRaw{K.Kernel.map(~U32, ~String, ~(i => sv(i)), n, d, K.Kernel.iota(n, d), "")}}

def b1col(+n: U32, +d: Nat) -> C.Column:
  C.CStr{n, d, C.AllValid{}, ST.SRaw{K.Kernel.map(~U32, ~String, ~(i => bv1(i)), n, d, K.Kernel.iota(n, d), "")}}

def b2col(+n: U32, +d: Nat) -> C.Column:
  C.CStr{n, d, C.AllValid{}, ST.SRaw{K.Kernel.map(~U32, ~String, ~(i => bv2(i)), n, d, K.Kernel.iota(n, d), "")}}

def frame(+n: U32) -> C.Frame:
  C.Frame{n, [C.Named{"k", kcol(n, d_of(n))}, C.Named{"x", xcol(n, d_of(n))}, C.Named{"y", ycol(n, d_of(n))}, C.Named{"f", fcol(n, d_of(n))}, C.Named{"g", gcol(n, d_of(n))}, C.Named{"s", scol(n, d_of(n))}, C.Named{"b1", b1col(n, d_of(n))}, C.Named{"b2", b2col(n, d_of(n))}]}

def col(n: String) -> X.Expr:
  X.Col{n}

def agg(+op: X.AggOp, +c: String) -> X.Expr:
  X.Alias{X.Agg{op, X.Col{c}}, c ++ "_" ++ X.AggOp.name(op)}

def len1() -> X.Expr:
  X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}

def lit2() -> X.Expr:
  X.Alias{X.Agg{X.Sum{}, X.Lit{D.SU32{2}}}, "lit"}

def csum(+c: String) -> X.Expr:
  X.Alias{X.Agg{X.Sum{}, X.Cast{X.Col{c}, D.TU32{}}}, c ++ "_csum"}

def run(+n: U32, aggs: List<&2, X.Expr>) -> E.ResT(C.Frame):
  G.GroupBy.run(frame(n), [col("k")], aggs, True{})

# the column `name` of a result, as a one-column frame's dump (the key column kept for the group order)
def pick.k(+name: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      DF.dump(C.Frame.select_names(f, ["k", name]))

def pick(+name: String, f: C.Frame) -> String:
  pick.k(name, Done{f})

# per aggregate: the forked result's column equals the lone run's column (dump text compared)
def one.b(+name: String, r: C.Frame & C.Frame, lone: E.ResT(C.Frame)) -> C.Frame & String:
  (keep, copy) = r
  (keep, Bool.pick(String, String.eq(pick(name, copy), pick.k(name, lone)), "ok", "DIFF " ++ name))

def one(+n: U32, full: C.Frame, +a: X.Expr) -> C.Frame & String:
  one.b(X.Expr.name(a), C.Frame.clone(full), run(n, [a]))

def step.k(acc: List<&2, String>, r: C.Frame & String) -> C.Frame & List<&2, String>:
  (full, s) = r
  (full, s <> acc)

def step(+n: U32, a: X.Expr, st: C.Frame & List<&2, String>) -> C.Frame & List<&2, String>:
  (full, acc) = st
  step.k(acc, one(n, full, a))

def go(+n: U32, as: List<&2, X.Expr>, st: C.Frame & List<&2, String>) -> C.Frame & List<&2, String>:
  match as:
    case Nil{}:
      st
    case a <> t:
      go(n, t, step(n, a, st))

def verdict.k(r: C.Frame & List<&2, String>) -> String:
  (f, acc) = r
  String.join(List.reverse(&2, String, acc), " ")

def verdict.f(+n: U32, +as: List<&2, X.Expr>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{full}:
      verdict.k(go(n, as, (full, Nil{})))

# the aggregates run together against each one alone
def check(+n: U32, +as: List<&2, X.Expr>) -> String:
  verdict.f(n, as, run(n, as))

def show(r: E.ResT(C.Frame)) -> String:
  DF.dump(r)

def main() -> IO(Unit):
  do IO<Unit>:
    # 2, 3, 4 aggregates: sum u32, mean f32 (nulls, NaN, inf, -0.0), len, max i32
    IO.print(check(20000, [agg(X.Sum{}, "x"), agg(X.Mean{}, "f")]))
    IO.print(check(20000, [agg(X.Mean{}, "f"), len1(), agg(X.Sum{}, "x")]))
    IO.print(check(20000, [agg(X.Sum{}, "x"), agg(X.Mean{}, "f"), len1(), agg(X.Max{}, "y")]))
    # 7 aggregates: f32 sum, str min, count, median, n_unique, last, std
    IO.print(check(20000, [agg(X.Sum{}, "f"), agg(X.Min{}, "s"), agg(X.Count{}, "f"), agg(X.Median{}, "g"), agg(X.NUnique{}, "y"), agg(X.Last{}, "f"), agg(X.Std{}, "g")]))
    # 8: the same column twice (x: sum then first: the first reference is a clone), a literal, var, a Len, max str
    IO.print(check(20000, [agg(X.Sum{}, "x"), agg(X.First{}, "x"), lit2(), len1(), agg(X.Var{}, "g"), agg(X.Max{}, "s"), agg(X.Min{}, "y"), agg(X.Sum{}, "g")]))
    # the 2^14 boundary: 16383 rows run sequentially, 16384 forks; both match the lone runs
    IO.print(check(16383, [agg(X.Sum{}, "x"), agg(X.Mean{}, "g"), len1()]))
    IO.print(check(16384, [agg(X.Sum{}, "x"), agg(X.Mean{}, "g"), len1()]))
    # absolute: 5 groups of 4000 rows, count(f) = 3000 per group, the literal 2 per group
    IO.print(show(run(20000, [len1(), agg(X.Count{}, "f"), lit2()])))
    # std over a str column: a static type error (before any data is touched), also next to a good aggregate
    IO.print(show(G.GroupBy.run(frame(20000), [col("k")], [agg(X.Count{}, "s"), agg(X.Std{}, "s")], True{})))
    # errors: the first failing aggregate input in aggregate order
    IO.print(show(run(20000, [csum("b1"), csum("b2")])))
    IO.print(show(run(20000, [csum("b2"), csum("b1")])))
    IO.print(show(run(20000, [agg(X.Sum{}, "x"), agg(X.Mean{}, "f"), csum("b2"), csum("b1")])))
    IO.print(show(run(20000, [csum("b1"), agg(X.Sum{}, "x"), len1()])))
    # the static type error (std of a str column) wins over failing inputs, before and after it
    IO.print(show(run(20000, [agg(X.Std{}, "b1"), csum("b2")])))
    IO.print(show(run(20000, [csum("b2"), agg(X.Std{}, "b1")])))
    # one aggregate, or a smaller frame: the same errors
    IO.print(show(run(20000, [csum("b1")])))
    IO.print(show(run(9500, [csum("b2"), csum("b1")])))
#|ok ok
#|ok ok ok
#|ok ok ok ok
#|ok ok ok ok ok ok ok
#|ok ok ok ok ok ok ok ok
#|ok ok ok
#|ok ok ok
#|frame
#|height	5
#|width	4
#|col	u32	"k"
#|col	u32	"len"
#|col	u32	"f_count"
#|col	u32	"lit"
#|row	0	4000	3000	2
#|row	1	4000	3000	2
#|row	2	4000	3000	2
#|row	3	4000	3000	2
#|row	4	4000	3000	2
#|
#|error	TypeMismatch in std: expected numeric, got str
#|
#|error	InvalidOperation: cast str to u32: row 9000 holds "bad1"
#|
#|error	InvalidOperation: cast str to u32: row 5 holds "bad2"
#|
#|error	InvalidOperation: cast str to u32: row 5 holds "bad2"
#|
#|error	InvalidOperation: cast str to u32: row 9000 holds "bad1"
#|
#|error	TypeMismatch in std: expected numeric, got str
#|
#|error	TypeMismatch in std: expected numeric, got str
#|
#|error	InvalidOperation: cast str to u32: row 9000 holds "bad1"
#|
#|error	InvalidOperation: cast str to u32: row 5 holds "bad2"
