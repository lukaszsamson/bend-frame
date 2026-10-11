# v0.2 T3.2 / T3.4: the sort pipeline (borrowed key words, fused read pass, sorted skip,
# ping-pong radix) and the Sort + Head bounded gather (Sort.frame_head, Exec.run_phys).
#  - Sort.frame_head(f, ks, k) dumps exactly like Frame.head(Sort.frame(f, ks), k) (DF.dump
#    text), for k = 0, 1, mid, height, > height, on NaN / -0.0 / inf / nulls first and last /
#    strings (Raw and Dictionary) / multi-key asc+desc / empty frames;
#  - errors: a missing key is ColumnNotFound even for k = 0, the first missing in list order;
#  - Exec.run_phys (what collect runs) against Exec.run_pure (the proofs' runner) on
#    Head{k, Sort{..}} plans, including an error inside the sorted input with k = 0;
#  - 3000-row inputs (both 16-bit digits vary): sorted, reverse-sorted, constant, many ties,
#    hashed, masked; checked as a lexicographic (null rank, key, row id) order, which is the
#    stable order because row ids are distinct, plus a permutation check of the ids.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/sort.bend as SO
import ./../src/dump.bend as DP
import ./../src/plan.bend as P
import ./../src/exec.bend as Q

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def u(v: U32) -> D.Scalar:
  D.SU32{v}

def s(v: String) -> D.Scalar:
  D.SStr{v}

def nul() -> D.Scalar:
  D.SNull{}

def f(v: F32) -> D.Scalar:
  D.SF32{v}

def ineg(v: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{v})}

def ipos(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def bo(b: Bool) -> D.Scalar:
  D.SBool{b}

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def frame(r: E.ResT(C.Frame)) -> C.Frame:
  match r:
    case Fail{e}:
      C.Frame.empty()
    case Done{fr}:
      fr

# the sort_edge frame: f32 NaN / -0.0 / +-inf / null, i32 signs, bools, strings
def edge() -> C.Frame:
  frame(C.Frame.from_columns([mk("x", [f(1.0), f(nan()), f(F32.neg(0.0)), f(0.0), nul(), f(F32.neg(inf())), f(F32.neg(2.5)), f(inf())], D.TF32{}), mk("n", [ipos(5), ineg(7), ipos(0), ineg(2147483648), ipos(2147483647), ineg(1), nul(), ipos(5)], D.TI32{}), mk("b", [bo(True{}), bo(False{}), nul(), bo(True{}), bo(False{}), bo(True{}), bo(False{}), nul()], D.TBool{}), mk("s", [s("ab"), s(""), s("abc"), s("b"), s("\u{e9}"), s("a"), nul(), s("ab")], D.TStr{}), mk("i", [u(0), u(1), u(2), u(3), u(4), u(5), u(6), u(7)], D.TU32{})]))

# the same with the string column as a Dictionary
def edge_dict() -> C.Frame:
  C.Frame.encode(edge(), True{})

def empty() -> C.Frame:
  frame(C.Frame.from_columns([mk("x", [], D.TF32{}), mk("s", [], D.TStr{})]))

def key(n: String, desc: Bool, nl: Bool) -> SO.SortKey:
  SO.SortKey{n, desc, nl}

def asc(n: String) -> SO.SortKey:
  SO.SortKey{n, False{}, False{}}

def hres(r: E.ResT(C.Frame), +k: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      Done{C.Frame.head(fr, k)}

# compact text of a result (dtype=[cells] per column)
def scal(xs: List<&2, D.Scalar>) -> String:
  List.show(~&2, ~D.Scalar, ~(x => D.Scalar.show(x)), xs)

def cs.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scal(xs)

def cs.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cs.b(t, C.Column.to_scalars(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs.a(C.Column.dtype(c))) <> ncols(t)

def fr.f(fm: C.Frame) -> String:
  match fm:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncols(cols), " | ")

def fr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fm}:
      fr.f(fm)

def pick(+dict: Bool) -> C.Frame:
  Bool.pick(C.Frame, dict, edge_dict(), edge())

# string equality as a tail loop (String.eq recurses once per char: 60 KB dumps overflow it)
def seq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{Chr{+x}, at} SCon{Chr{+y}, bt}:
      seq.go(at, bt, Bool.and(ok, U32.is_eq(x, y)))
    case _ _:
      False{}

def seq(a: String, b: String) -> Bool:
  seq.go(a, b, True{})

# "same <k>" when the shortcut dumps like sort-then-head, else both dumps
def same.k(+k: U32, +a: String, +b: String) -> String:
  Bool.pick(String, seq(a, b), "same " ++ U32.show(k), "DIFFERENT " ++ U32.show(k) ++ "\n" ++ a ++ "---\n" ++ b)

def same(+mkf: Bool, +ks: List<&2, SO.SortKey>, +k: U32) -> String:
  same.k(k, DP.Dump.result(SO.Sort.frame_head(pick(mkf), ks, k)), DP.Dump.result(hres(SO.Sort.frame(pick(mkf), ks), k)))

def sames(+mkf: Bool, +ks: List<&2, SO.SortKey>) -> String:
  String.join([same(mkf, ks, 0), same(mkf, ks, 1), same(mkf, ks, 3), same(mkf, ks, 8), same(mkf, ks, 100)], ", ")

# ---- 3000-row inputs -----------------------------------------------------------------------------

def big() -> U32:
  3000

# kind 0 sorted, 1 reverse, 2 constant, 3 ties (i*7919 mod 5), 4 hashed, 5 hashed with every
# 7th row null, 6 ties with every 5th row null; 7 the row id; 8 i mod 3
def val(+kind: U32, +i: U32) -> D.Scalar:
  match kind:
    case 0:
      D.SU32{U32.mul(i, 65537)}
    case 1:
      D.SU32{U32.mul(U32.sub(3000, i), 65537)}
    case 2:
      D.SU32{7}
    case 3:
      D.SU32{U32.mod(U32.mul(i, 7919), 5)}
    case 4:
      D.SU32{U32.mul(i, 2654435761)}
    case 5:
      Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 7), 3), D.SNull{}, D.SU32{U32.mul(i, 2654435761)})
    case 6:
      Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 5), 0), D.SNull{}, D.SU32{U32.mod(U32.mul(i, 7919), 3)})
    case 7:
      D.SU32{i}
    case _:
      D.SU32{U32.mod(i, 3)}

def gen.go(n: Nat, +i: U32, +kind: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      gen.go(p, U32.sub(i, 1), kind, val(kind, U32.sub(i, 1)) <> acc)

# [val(kind, 0), .., val(kind, n-1)]
def gen(+n: U32, +kind: U32) -> List<&2, D.Scalar>:
  gen.go(U32.to_nat(n), n, kind, Nil{})

def bigf(+kind: U32) -> C.Frame:
  frame(C.Frame.from_columns([mk("x", gen(big(), kind), D.TU32{}), mk("y", gen(big(), 8), D.TU32{}), mk("id", gen(big(), 7), D.TU32{})]))

# (null rank, word, id) of a row, compared lexicographically: the stable order of one key
type Row is Data:
  Row{r: U32, w: U32, id: U32}

def rlt(a: Row, b: Row) -> Bool:
  match a b:
    case Row{+r1, +w1, +i1} Row{+r2, +w2, +i2}:
      Bool.or(U32.is_lt(r1, r2), Bool.and(U32.is_eq(r1, r2), Bool.or(U32.is_lt(w1, w2), Bool.and(U32.is_eq(w1, w2), U32.is_lt(i1, i2)))))

def row(+desc: Bool, +nl: Bool, x: D.Scalar, +id: U32) -> Row:
  match x:
    case D.SU32{+v}:
      Row{Bool.pick(U32, nl, 0, 1), Bool.pick(U32, desc, U32.xor(v, 4294967295), v), id}
    case _:
      Row{Bool.pick(U32, nl, 1, 0), 0, id}

def idv(x: D.Scalar) -> U32:
  match x:
    case D.SU32{v}:
      v
    case _:
      4294967295

def rows.go(+desc: Bool, +nl: Bool, xs: List<&2, D.Scalar>, js: List<&2, D.Scalar>, acc: List<&2, Row>) -> List<&2, Row>:
  match xs js:
    case x <> xt i <> it:
      rows.go(desc, nl, xt, it, row(desc, nl, x, idv(i)) <> acc)
    case _ _:
      List.reverse(&2, Row, acc)

def rows(+desc: Bool, +nl: Bool, xs: List<&2, D.Scalar>, js: List<&2, D.Scalar>) -> List<&2, Row>:
  rows.go(desc, nl, xs, js, Nil{})

# every adjacent pair strictly increasing (tail recursive: the previous row is carried)
def ordered.go(xs: List<&2, Row>, +prev: Row, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case +b <> t:
      ordered.go(t, b, Bool.and(ok, rlt(prev, b)))

def ordered(xs: List<&2, Row>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +a <> t:
      ordered.go(t, a, True{})

def idsum(xs: List<&2, Row>, +acc: U32, +sq: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (acc, sq)
    case Row{r, w, +i} <> t:
      idsum(t, U32.add(acc, i), U32.add(sq, U32.mul(i, i)))

def cells.s(r: C.Column & List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  (c, xs) = r
  xs

def scal.r(r: E.ResT(C.Column)) -> List<&2, D.Scalar>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{c}:
      cells.s(C.Column.to_scalars(c))

def getc.k(r: C.Frame & E.ResT(C.Column)) -> C.Frame & List<&2, D.Scalar>:
  (fm, rc) = r
  (fm, scal.r(rc))

# the cells of column n (a copy); the frame comes back
def getc(fm: C.Frame, +n: String) -> C.Frame & List<&2, D.Scalar>:
  getc.k(C.Frame.get_cloned(fm, n))

def fh(fm: C.Frame) -> U32:
  match fm:
    case C.Frame{h, cols}:
      h

def check.s(+h: U32, ok: Bool, r: U32 & U32) -> String:
  (a, b) = r
  "h=" ++ U32.show(h) ++ " ordered=" ++ Bool.pick(String, ok, "yes", "NO") ++ " ids=" ++ U32.show(a) ++ "/" ++ U32.show(b)

def check.r(+h: U32, +rs: List<&2, Row>) -> String:
  check.s(h, ordered(rs), idsum(rs, 0, 0))

def check.b(+desc: Bool, +nl: Bool, xs: List<&2, D.Scalar>, r: C.Frame & List<&2, D.Scalar>) -> String:
  (fm, js) = r
  check.r(fh(fm), rows(desc, nl, xs, js))

def check.a(+desc: Bool, +nl: Bool, r: C.Frame & List<&2, D.Scalar>) -> String:
  (fm, xs) = r
  check.b(desc, nl, xs, getc(fm, "id"))

def check(+desc: Bool, +nl: Bool, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fm}:
      check.a(desc, nl, getc(fm, "x"))

def big_one(+kind: U32, +desc: Bool, +nl: Bool) -> String:
  "kind " ++ U32.show(kind) ++ ": " ++ check(desc, nl, SO.Sort.frame(bigf(kind), [key("x", desc, nl)])) ++ "; " ++ same.k(10, DP.Dump.result(SO.Sort.frame_head(bigf(kind), [key("x", desc, nl)], 10)), DP.Dump.result(hres(SO.Sort.frame(bigf(kind), [key("x", desc, nl)]), 10))) ++ " " ++ same.k(3000, DP.Dump.result(SO.Sort.frame_head(bigf(kind), [key("x", desc, nl)], 3000)), DP.Dump.result(hres(SO.Sort.frame(bigf(kind), [key("x", desc, nl)]), 3000)))

# two keys: y (i mod 3) ascending, then x descending: (y, not x, id) lexicographic
def two.go(ys: List<&2, D.Scalar>, xs: List<&2, D.Scalar>, js: List<&2, D.Scalar>, acc: List<&2, Row>) -> List<&2, Row>:
  match ys xs js:
    case y <> yt x <> xt i <> it:
      two.go(yt, xt, it, Row{idv(y), U32.xor(idv(x), 4294967295), idv(i)} <> acc)
    case _ _ _:
      List.reverse(&2, Row, acc)

def two.rows(ys: List<&2, D.Scalar>, xs: List<&2, D.Scalar>, js: List<&2, D.Scalar>) -> List<&2, Row>:
  two.go(ys, xs, js, Nil{})

def two.c(ys: List<&2, D.Scalar>, xs: List<&2, D.Scalar>, r: C.Frame & List<&2, D.Scalar>) -> String:
  (fm, js) = r
  check.r(fh(fm), two.rows(ys, xs, js))

def two.b(ys: List<&2, D.Scalar>, r: C.Frame & List<&2, D.Scalar>) -> String:
  (fm, xs) = r
  two.c(ys, xs, getc(fm, "id"))

def two.a(r: C.Frame & List<&2, D.Scalar>) -> String:
  (fm, ys) = r
  two.b(ys, getc(fm, "x"))

def two(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fm}:
      two.a(getc(fm, "y"))

# ---- the runner: Exec.run_phys (collect's runner) against Exec.run_pure -------------------------

def src(+dict: Bool) -> P.Env & P.Plan:
  P.Env.add(P.Env.empty(), "t", pick(dict))

def runs.e(+k: U32, +ks: List<&2, SO.SortKey>, +p: P.Plan, r: P.Env & P.Plan) -> String:
  (env, q) = r
  DP.Dump.result(Q.Exec.run_pure(P.Head{k, P.Sort{ks, p}}, env))

def runs.d(+k: U32, a: E.ResT(C.Frame), +ks: List<&2, SO.SortKey>, +p: P.Plan) -> String:
  same.k(k, DP.Dump.result(a), runs.e(k, ks, p, src(False{})))

def runs.c(+k: U32, +ks: List<&2, SO.SortKey>, +p: P.Plan, env: P.Env) -> String:
  runs.d(k, Q.Exec.run_phys(P.Head{k, P.Sort{ks, p}}, env), ks, p)

def runs.k(+k: U32, +ks: List<&2, SO.SortKey>, r: P.Env & P.Plan) -> String:
  (env, +p) = r
  runs.c(k, ks, p, env)

# run_phys (collect's runner) and run_pure (the proofs' runner) on Head{k, Sort{ks, t}}
def runs(+k: U32, +ks: List<&2, SO.SortKey>) -> String:
  runs.k(k, ks, src(False{}))

# an input whose evaluation fails (a strict cast of the strings to u32) under Head{k, Sort}
def badp(+k: U32, +p: P.Plan) -> P.Plan:
  P.Head{k, P.Sort{[asc("c")], P.WithColumns{[X.Alias{X.Cast{X.Col{"s"}, D.TU32{}}, "c"}], p}}}

def bad.d(+a: String, +b: String) -> String:
  Bool.pick(String, seq(a, b), "same: " ++ String.join(String.split(a, '\n'), " "), "DIFFERENT\n" ++ a ++ "---\n" ++ b)

def bad.e(+k: U32, r: P.Env & P.Plan) -> String:
  (env, +p) = r
  DP.Dump.result(Q.Exec.run_pure(badp(k, p), env))

def bad.c(+k: U32, +p: P.Plan, env: P.Env) -> String:
  bad.d(DP.Dump.result(Q.Exec.run_phys(badp(k, p), env)), bad.e(k, src(False{})))

def bad.k(+k: U32, r: P.Env & P.Plan) -> String:
  (env, +p) = r
  bad.c(k, p, env)

def bad(+k: U32) -> String:
  bad.k(k, src(False{}))

def main() -> IO(Unit):
  do IO<Unit>:
    # pinned values: f32 nulls first, NaN largest, -0.0 == 0.0 (input order kept); i32 nulls last
    IO.print(fr(SO.Sort.frame_head(edge(), [asc("x")], 5)))
    IO.print(fr(SO.Sort.frame_head(edge(), [key("n", False{}, True{})], 3)))
    IO.print(fr(SO.Sort.frame_head(edge(), [key("b", True{}, False{}), key("n", True{}, False{})], 4)))
    IO.print(fr(SO.Sort.frame_head(edge_dict(), [key("s", True{}, False{}), key("i", True{}, False{})], 8)))
    IO.print(fr(SO.Sort.frame_head(edge(), [asc("x")], 0)))
    IO.print(fr(SO.Sort.frame_head(edge(), Nil{}, 2)))
    IO.print(fr(SO.Sort.frame_head(empty(), [asc("x"), key("s", True{}, True{})], 5)))
    # missing keys: ColumnNotFound even for k = 0, the first missing key in list order
    IO.print(fr(SO.Sort.frame_head(edge(), [asc("x"), asc("nope"), asc("zz")], 0)))
    IO.print(fr(SO.Sort.frame_head(empty(), [asc("zz")], 0)))
    # the shortcut dumps exactly like Sort.frame then Frame.head (k = 0, 1, 3, 8, 100)
    IO.print(sames(False{}, [asc("x")]))
    IO.print(sames(False{}, [key("x", True{}, True{})]))
    IO.print(sames(False{}, [key("n", False{}, True{}), key("x", True{}, False{})]))
    IO.print(sames(False{}, [key("b", True{}, False{}), key("s", False{}, True{}), asc("i")]))
    IO.print(sames(True{}, [key("s", True{}, True{}), asc("x")]))
    IO.print(sames(True{}, [asc("s")]))
    IO.print(sames(False{}, [asc("nope")]))
    # the runner: run_phys == run_pure (k = 0, 2, 100; an error in the sorted input with k = 0)
    IO.print(runs(0, [asc("x")]))
    IO.print(runs(2, [key("s", True{}, True{}), asc("n")]))
    IO.print(runs(100, [key("b", False{}, True{})]))
    IO.print(runs(0, [asc("missing")]))
    IO.print(bad(0))
    IO.print(bad(3))
    # 3000 rows: sorted, reverse, constant, ties, hashed, masked (nulls first / last), desc
    # the checker itself rejects an unsorted input
    IO.print(check(False{}, False{}, Done{bigf(4)}))
    IO.print(big_one(0, False{}, False{}))
    IO.print(big_one(1, False{}, False{}))
    IO.print(big_one(2, False{}, False{}))
    IO.print(big_one(3, False{}, False{}))
    IO.print(big_one(3, True{}, False{}))
    IO.print(big_one(4, False{}, False{}))
    IO.print(big_one(4, True{}, False{}))
    IO.print(big_one(5, False{}, False{}))
    IO.print(big_one(5, True{}, True{}))
    IO.print(big_one(6, False{}, True{}))
    IO.print(big_one(6, True{}, False{}))
    IO.print(two(SO.Sort.frame(bigf(4), [asc("y"), key("x", True{}, False{})])))
    IO.print(two(SO.Sort.frame_head(bigf(4), [asc("y"), key("x", True{}, False{})], 2999)))
#|h=5 x:f32=[null, -inf, -2.5, -0, 0] | n:i32=[2147483647, -1, null, 0, -2147483648] | b:bool=[false, true, false, null, true] | s:str=[é, a, null, abc, b] | i:u32=[4, 5, 6, 2, 3]
#|h=3 x:f32=[0, nan, -inf] | n:i32=[-2147483648, -7, -1] | b:bool=[true, false, true] | s:str=[b, , a] | i:u32=[3, 1, 5]
#|h=4 x:f32=[inf, -0, 1, -inf] | n:i32=[5, 0, 5, -1] | b:bool=[null, null, true, true] | s:str=[ab, abc, ab, a] | i:u32=[7, 2, 0, 5]
#|h=8 x:f32=[-2.5, null, 0, -0, inf, 1, -inf, nan] | n:i32=[null, 2147483647, -2147483648, 0, 5, 5, -1, -7] | b:bool=[false, false, true, null, null, true, true, false] | s:str=[null, é, b, abc, ab, ab, a, ] | i:u32=[6, 4, 3, 2, 7, 0, 5, 1]
#|h=0 x:f32=[] | n:i32=[] | b:bool=[] | s:str=[] | i:u32=[]
#|h=2 x:f32=[1, nan] | n:i32=[5, -7] | b:bool=[true, false] | s:str=[ab, ] | i:u32=[0, 1]
#|h=0 x:f32=[] | s:str=[]
#|error: ColumnNotFound: nope
#|error: ColumnNotFound: zz
#|same 0, same 1, same 3, same 8, same 100
#|same 0, same 1, same 3, same 8, same 100
#|same 0, same 1, same 3, same 8, same 100
#|same 0, same 1, same 3, same 8, same 100
#|same 0, same 1, same 3, same 8, same 100
#|same 0, same 1, same 3, same 8, same 100
#|same 0, same 1, same 3, same 8, same 100
#|same 0
#|same 2
#|same 100
#|same 0
#|same: error	InvalidOperation: cast str to u32: row 0 holds "ab" 
#|same: error	InvalidOperation: cast str to u32: row 0 holds "ab" 
#|h=3000 ordered=NO ids=4498500/405565908
#|kind 0: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 1: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 2: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 3: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 3: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 4: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 4: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 5: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 5: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 6: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|kind 6: h=3000 ordered=yes ids=4498500/405565908; same 10 same 3000
#|h=3000 ordered=yes ids=4498500/405565908
#|h=2999 ordered=yes ids=4496293/400695059
