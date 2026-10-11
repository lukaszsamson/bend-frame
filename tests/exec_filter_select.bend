# v0.2 T4.3: the Filter + plain Select physical step (Exec.run_phys on Select{cols, Filter{p, x}},
# DESIGN.md 16.3 F8). Every case prints the run_phys result (what collect runs) and checks it
# dumps exactly like Exec.run_pure (the proofs' runner: IFilter then ISelect), DF.dump text:
#  - q1's shape (filter ok & qty > 50, select id, region, price), the predicate with nulls;
#  - aliases (the general path: Eval.select), select([]) (the general path), all seven columns
#    (one compact4 group and one compact3 group), 1, 2, 4, 5, 6 columns (single steps and groups);
#  - errors: duplicate selected names, a selected column missing, a predicate column missing, a
#    non-bool predicate, a strict cast failing inside the predicate, and the precedence between a
#    predicate error and a select error (the predicate's first);
#  - masked columns in a group (one by one), columns of different lengths in a malformed frame
#    (the group needs one length), the empty frame, 0 / 1 / 50 / 100 % selectivity on 100 rows,
#    Raw and Dictionary strings, F32 NaN / -0.0 / inf;
#  - Filter + Select under Head / Sort / WithColumns and a Select over a Head (the general path);
#  - T4.4 (the step's mask is Eval.filter.mask's): i32 / f32 / three-conjunct / masked-column F5
#    predicates, and a Kleene-or predicate F5 does not plan (the general path inside the step).
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

def col.k(nc: C.Named) -> C.Column:
  match nc:
    case C.Named{n, c}:
      c

def col(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Column:
  col.k(mk(name, xs, t))

def u(v: U32) -> D.Scalar:
  D.SU32{v}

def s(v: String) -> D.Scalar:
  D.SStr{v}

def nul() -> D.Scalar:
  D.SNull{}

def f(v: F32) -> D.Scalar:
  D.SF32{v}

def ipos(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def ineg(v: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{v})}

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

# 8 rows: id u32, region str, price f32 (NaN, -0, inf), ok bool (a null), qty u32,
# disc f32 (nulls: a validity mask), n i32
def t8() -> C.Frame:
  frame(C.Frame.from_columns([mk("id", [u(0), u(1), u(2), u(3), u(4), u(5), u(6), u(7)], D.TU32{}), mk("region", [s("north"), s("south"), s(""), s("east"), s("north"), s("\u{e9}st"), s("south"), s("west")], D.TStr{}), mk("price", [f(1.5), f(nan()), f(F32.neg(0.0)), f(inf()), f(2.0), f(F32.neg(3.25)), f(0.0), f(7.0)], D.TF32{}), mk("ok", [bo(True{}), bo(True{}), nul(), bo(False{}), bo(True{}), bo(True{}), bo(False{}), bo(True{})], D.TBool{}), mk("qty", [u(10), u(60), u(70), u(80), u(51), u(50), u(99), u(100)], D.TU32{}), mk("disc", [f(0.5), nul(), f(0.25), nul(), f(1.0), f(0.0), nul(), f(0.75)], D.TF32{}), mk("n", [ipos(5), ineg(7), ipos(0), ineg(2147483648), ipos(2147483647), ineg(1), nul(), ipos(3)], D.TI32{})]))

def t8d() -> C.Frame:
  C.Frame.encode(t8(), True{})

def empty() -> C.Frame:
  frame(C.Frame.from_columns([mk("id", [], D.TU32{}), mk("region", [], D.TStr{}), mk("price", [], D.TF32{}), mk("ok", [], D.TBool{}), mk("qty", [], D.TU32{})]))

# a malformed frame (built directly): "b" has 2 rows in a frame of 3, so the fused group must not
# take it with "a" and "c" (one length per loop); run_pure compacts it as it is
def odd() -> C.Frame:
  C.Frame{3, [C.Named{"a", col("a", [u(1), u(2), u(3)], D.TU32{})}, C.Named{"b", col("b", [u(7), u(8)], D.TU32{})}, C.Named{"c", col("c", [f(0.5), f(1.5), f(2.5)], D.TF32{})}, C.Named{"k", col("k", [bo(True{}), bo(False{}), bo(True{})], D.TBool{})}]}

def r100.go(n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      r100.go(p, U32.sub(i, 1), u(i) <> acc)

# 100 rows: q = 1..100 (so q > K keeps 100 - K rows), w = 3 * q, g = q as f32, str labels
def w100.go(n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      w100.go(p, U32.sub(i, 1), u(U32.mul(i, 3)) <> acc)

def g100.go(n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      g100.go(p, U32.sub(i, 1), f(U32.to_f32(i)) <> acc)

def l100.go(n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      l100.go(p, U32.sub(i, 1), s("r" ++ U32.show(U32.mod(i, 7))) <> acc)

def t100() -> C.Frame:
  frame(C.Frame.from_columns([mk("q", r100.go(100n, 100, Nil{}), D.TU32{}), mk("w", w100.go(100n, 100, Nil{}), D.TU32{}), mk("g", g100.go(100n, 100, Nil{}), D.TF32{}), mk("l", l100.go(100n, 100, Nil{}), D.TStr{})]))

# ---- plans ---------------------------------------------------------------------------------------

def c(n: String) -> X.Expr:
  X.Col{n}

def gt(a: X.Expr, +k: U32) -> X.Expr:
  X.Bin{X.Gt{}, a, X.Lit{u(k)}}

def q1p() -> X.Expr:
  X.Bin{X.And{}, c("ok"), gt(c("qty"), 50)}

def sel(es: List<&2, X.Expr>, p: X.Expr, x: P.Plan) -> P.Plan:
  P.Select{es, P.Filter{p, x}}

# ---- result text ---------------------------------------------------------------------------------

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

# string equality as a tail loop
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

def same(+a: String, +b: String) -> String:
  Bool.pick(String, seq(a, b), "same", "DIFFERENT\n" ++ a ++ "---\n" ++ b)

# (text, dump) of a result
def fr.d(r: C.Frame & C.Frame) -> String & String:
  (a, b) = r
  (fr.f(a), DP.Dump.result(Done{b}))

def fr.c(r: E.ResT(C.Frame)) -> String & String:
  match r:
    case Fail{+e}:
      ("error: " ++ E.Err.show(e), DP.Dump.result(Fail{e}))
    case Done{fm}:
      fr.d(C.Frame.clone(fm))

def run.u(r: String & String, +b: String) -> String:
  (txt, +da) = r
  txt ++ " [" ++ same(da, b) ++ "]"

def run.t(r: E.ResT(C.Frame), +b: String) -> String:
  run.u(fr.c(r), b)

def run.r(+p: P.Plan, ea: P.Env, eb: P.Env) -> String:
  run.t(Q.Exec.run_phys(p, ea), DP.Dump.result(Q.Exec.run_pure(p, eb)))

def run.e(+p: P.Plan, ra: P.Env & P.Plan, rb: P.Env & P.Plan) -> String:
  (ea, sa) = ra
  (eb, sb) = rb
  run.r(p, ea, eb)

# run_phys's result text, then whether it dumps like run_pure on a fresh copy of the frame
def run.k(+p: P.Plan, fa: C.Frame, fb: C.Frame) -> String:
  run.e(p, P.Env.add(P.Env.empty(), "t", fa), P.Env.add(P.Env.empty(), "t", fb))

# the plan over Source "t" of the frame (built twice: one for each runner)
def src.k(r: P.Env & P.Plan) -> P.Plan:
  (e, p) = r
  p

def src(f: C.Frame) -> P.Plan:
  src.k(P.Env.add(P.Env.empty(), "t", f))

# 0 = t8, 1 = t8 dictionary, 2 = empty, 3 = odd, 4 = t100
def frm(+which: U32) -> C.Frame:
  Bool.pick(C.Frame, U32.is_eq(which, 0), t8(), Bool.pick(C.Frame, U32.is_eq(which, 1), t8d(), Bool.pick(C.Frame, U32.is_eq(which, 2), empty(), Bool.pick(C.Frame, U32.is_eq(which, 3), odd(), t100()))))

def run_on(+p: P.Plan, +which: U32) -> String:
  run.k(p, frm(which), frm(which))

def srcw(+which: U32) -> P.Plan:
  src(frm(which))

def cols(ns: List<&2, String>) -> List<&2, X.Expr>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      X.Col{n} <> cols(t)

def fs(+which: U32, +ns: List<&2, String>, +p: X.Expr) -> String:
  run_on(sel(cols(ns), p, srcw(which)), which)

def main() -> IO(Unit):
  do IO<Unit>:
    # q1's shape (ok has a null: dropped), Raw and Dictionary strings
    IO.print(fs(0, ["id", "region", "price"], q1p()))
    IO.print(fs(1, ["id", "region", "price"], q1p()))
    # one, two, four, five, six, seven columns (single steps, a compact4 group, 4 + 3)
    IO.print(fs(0, ["price"], q1p()))
    IO.print(fs(0, ["region", "id"], q1p()))
    IO.print(fs(0, ["n", "qty", "price", "region"], q1p()))
    IO.print(fs(1, ["n", "qty", "price", "region", "id"], q1p()))
    IO.print(fs(0, ["id", "region", "price", "ok", "qty", "n"], q1p()))
    IO.print(fs(1, ["id", "region", "price", "ok", "qty", "disc", "n"], q1p()))
    # a masked column inside a group (disc), a group of three with a masked one
    IO.print(fs(0, ["id", "disc", "price"], q1p()))
    IO.print(fs(0, ["disc", "n", "ok", "id"], q1p()))
    # aliases and select([]): the general path
    IO.print(run_on(sel([X.Alias{c("id"), "k"}, c("price")], q1p(), srcw(0)), 0))
    IO.print(run_on(sel([c("id"), X.Alias{c("price"), "id2"}, c("region")], q1p(), srcw(1)), 1))
    IO.print(run_on(sel([], q1p(), srcw(0)), 0))
    # a computed expression selected: the general path
    IO.print(run_on(sel([c("id"), X.Bin{X.Add{}, c("qty"), X.Lit{u(1)}}], q1p(), srcw(0)), 0))
    # errors: duplicate names, a missing selected column, a missing predicate column, a non-bool
    # predicate, a strict cast failing in the predicate (and it wins over a select error)
    IO.print(fs(0, ["id", "price", "id"], q1p()))
    IO.print(fs(0, ["id", "nope"], q1p()))
    IO.print(fs(0, ["id"], X.Bin{X.And{}, c("missing"), c("ok")}))
    IO.print(fs(0, ["id"], c("qty")))
    IO.print(fs(0, ["id", "nope"], X.Bin{X.Gt{}, X.Cast{c("region"), D.TU32{}}, X.Lit{u(1)}}))
    IO.print(fs(0, ["id", "id"], c("missing")))
    # the empty frame; a malformed frame (one column shorter than the height)
    IO.print(fs(2, ["id", "region", "price"], q1p()))
    IO.print(fs(2, ["qty", "ok", "price", "region", "id"], q1p()))
    IO.print(fs(3, ["a", "b", "c"], c("k")))
    IO.print(fs(3, ["c", "a", "k"], c("k")))
    # selectivity on 100 rows: q > 100 (0 %), q > 99 (1 %), q > 50 (50 %), q > 0 (100 %)
    IO.print(fs(4, ["q", "w", "g"], gt(c("q"), 100)))
    IO.print(fs(4, ["q", "w", "g"], gt(c("q"), 99)))
    IO.print(fs(4, ["l", "g", "q", "w"], gt(c("q"), 95)))
    IO.print(fs(4, ["g", "q"], gt(c("q"), 0)))
    IO.print(run_on(P.Head{3, sel(cols(["w", "l", "q"]), gt(c("q"), 50), srcw(4))}, 4))
    # nested: under Head, Sort, WithColumns; a Select over a Head over a Filter
    IO.print(run_on(P.Head{2, sel(cols(["id", "region", "price"]), q1p(), srcw(0))}, 0))
    IO.print(run_on(P.Sort{[SO.SortKey{"price", True{}, False{}}], sel(cols(["id", "price"]), q1p(), srcw(1))}, 1))
    IO.print(run_on(P.WithColumns{[X.Alias{X.Bin{X.Add{}, c("id"), X.Lit{u(10)}}, "id10"}], sel(cols(["id", "region"]), q1p(), srcw(0))}, 0))
    IO.print(run_on(P.Select{cols(["id", "region"]), P.Head{3, P.Filter{q1p(), srcw(0)}}}, 0))
    # T4.4: Exec.fs takes its mask from Eval.filter.mask, so every F5 shape runs inside the step:
    # an i32 comparison, an f32 comparison (NaN sorts above every number, as in Polars: kept), three conjuncts (one pass merged, two more), a
    # comparison over a masked column; and a predicate F5 does not plan (Kleene or: the general path)
    IO.print(fs(0, ["id", "n"], X.Bin{X.Lt{}, c("n"), X.Lit{ipos(0)}}))
    IO.print(fs(1, ["id", "price"], X.Bin{X.Gt{}, c("price"), X.Lit{f(1.0)}}))
    IO.print(fs(0, ["id", "region", "price"], X.Bin{X.And{}, q1p(), X.Bin{X.Gt{}, c("price"), X.Lit{f(0.0)}}}))
    IO.print(fs(0, ["id", "disc"], X.Bin{X.Gt{}, c("disc"), X.Lit{f(0.3)}}))
    IO.print(fs(1, ["id", "qty"], X.Bin{X.Or{}, c("ok"), gt(c("qty"), 90)}))
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] | price:f32=[nan, 2, 7] [same]
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] | price:f32=[nan, 2, 7] [same]
#|h=3 price:f32=[nan, 2, 7] [same]
#|h=3 region:str=[south, north, west] | id:u32=[1, 4, 7] [same]
#|h=3 n:i32=[-7, 2147483647, 3] | qty:u32=[60, 51, 100] | price:f32=[nan, 2, 7] | region:str=[south, north, west] [same]
#|h=3 n:i32=[-7, 2147483647, 3] | qty:u32=[60, 51, 100] | price:f32=[nan, 2, 7] | region:str=[south, north, west] | id:u32=[1, 4, 7] [same]
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] | price:f32=[nan, 2, 7] | ok:bool=[true, true, true] | qty:u32=[60, 51, 100] | n:i32=[-7, 2147483647, 3] [same]
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] | price:f32=[nan, 2, 7] | ok:bool=[true, true, true] | qty:u32=[60, 51, 100] | disc:f32=[null, 1, 0.75] | n:i32=[-7, 2147483647, 3] [same]
#|h=3 id:u32=[1, 4, 7] | disc:f32=[null, 1, 0.75] | price:f32=[nan, 2, 7] [same]
#|h=3 disc:f32=[null, 1, 0.75] | n:i32=[-7, 2147483647, 3] | ok:bool=[true, true, true] | id:u32=[1, 4, 7] [same]
#|h=3 k:u32=[1, 4, 7] | price:f32=[nan, 2, 7] [same]
#|h=3 id:u32=[1, 4, 7] | id2:f32=[nan, 2, 7] | region:str=[south, north, west] [same]
#|h=0  [same]
#|h=3 id:u32=[1, 4, 7] | qty:u32=[61, 52, 101] [same]
#|error: DuplicateColumn: id [same]
#|error: ColumnNotFound: nope [same]
#|error: ColumnNotFound: missing [same]
#|error: TypeMismatch in filter: expected bool, got u32 [same]
#|error: InvalidOperation: cast str to u32: row 0 holds "north" [same]
#|error: ColumnNotFound: missing [same]
#|h=0 id:u32=[] | region:str=[] | price:f32=[] [same]
#|h=0 qty:u32=[] | ok:bool=[] | price:f32=[] | region:str=[] | id:u32=[] [same]
#|h=2 a:u32=[1, 3] | b:u32=[7, 8] | c:f32=[0.5, 2.5] [same]
#|h=2 c:f32=[0.5, 2.5] | a:u32=[1, 3] | k:bool=[true, true] [same]
#|h=0 q:u32=[] | w:u32=[] | g:f32=[] [same]
#|h=1 q:u32=[100] | w:u32=[300] | g:f32=[100] [same]
#|h=5 l:str=[r5, r6, r0, r1, r2] | g:f32=[96, 97, 98, 99, 100] | q:u32=[96, 97, 98, 99, 100] | w:u32=[288, 291, 294, 297, 300] [same]
#|h=100 g:f32=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100] | q:u32=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100] [same]
#|h=3 w:u32=[153, 156, 159] | l:str=[r2, r3, r4] | q:u32=[51, 52, 53] [same]
#|h=2 id:u32=[1, 4] | region:str=[south, north] | price:f32=[nan, 2] [same]
#|h=3 id:u32=[1, 7, 4] | price:f32=[nan, 7, 2] [same]
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] | id10:u32=[11, 14, 17] [same]
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] [same]
#|h=3 id:u32=[1, 3, 5] | n:i32=[-7, -2147483648, -1] [same]
#|h=5 id:u32=[0, 1, 3, 4, 7] | price:f32=[1.5, nan, inf, 2, 7] [same]
#|h=3 id:u32=[1, 4, 7] | region:str=[south, north, west] | price:f32=[nan, 2, 7] [same]
#|h=3 id:u32=[0, 4, 7] | disc:f32=[0.5, 1, 0.75] [same]
#|h=6 id:u32=[0, 1, 4, 5, 6, 7] | qty:u32=[10, 60, 51, 50, 99, 100] [same]
