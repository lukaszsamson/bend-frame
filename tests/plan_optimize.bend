# M4: Plan.optimize. For each plan: explain before / after, then the plan is
# collected as written (Exec.run) and optimised (Lazy.collect); the two
# results and the two schemas must be identical. Covers filter merging,
# predicate pushdown through Select (renamed through an alias), WithColumns
# and Sort with the unmovable conjuncts left in place, no pushdown through
# Head, Head merging/pushdown, and projection pushdown to the sources
# (through a Join and a GroupBy: explain only).
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/expr.bend as X
import ./../src/sort.bend as O
import ./../src/join.bend as J
import ./../src/plan.bend as P
import ./../src/exec.bend as Q

# ---- frames ----------------------------------------------------------------------

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def env.k(r: P.Env & P.Plan) -> P.Env:
  (env, p) = r
  env

def env.r(r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      P.Env.empty()
    case Done{f}:
      env.k(P.Env.add(P.Env.empty(), "t", f))

def ca() -> C.Named:
  mk("a", [D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}, D.SU32{5}, D.SU32{6}], D.TU32{})

def cb() -> C.Named:
  mk("b", [D.SStr{"x"}, D.SStr{"y"}, D.SStr{"z"}, D.SStr{"x"}, D.SStr{"y"}, D.SStr{"x"}], D.TStr{})

def cc() -> C.Named:
  mk("c", [D.SF32{0.5}, D.SF32{1.5}, D.SF32{2.5}, D.SNull{}, D.SF32{4.5}, D.SF32{5.5}], D.TF32{})

def cd() -> C.Named:
  mk("d", [D.SBool{True{}}, D.SBool{False{}}, D.SBool{True{}}, D.SBool{True{}}, D.SNull{}, D.SBool{True{}}], D.TBool{})

def ce() -> C.Named:
  mk("e", [D.SU32{0}, D.SU32{0}, D.SU32{0}, D.SU32{0}, D.SU32{0}, D.SU32{0}], D.TU32{})

# t: a u32 (a null), b str, c f32 (a null), d bool (a null), e u32 (never used)
def env() -> P.Env:
  env.r(C.Frame.from_columns([ca(), cb(), cc(), cd(), ce()]))

def ub() -> C.Named:
  mk("b", [D.SStr{"x"}, D.SStr{"y"}, D.SStr{"w"}, D.SStr{"x"}], D.TStr{})

def ulabel() -> C.Named:
  mk("label", [D.SStr{"x1"}, D.SStr{"y1"}, D.SStr{"w1"}, D.SStr{"x2"}], D.TStr{})

def uc() -> C.Named:
  mk("c", [D.SF32{10.0}, D.SF32{20.0}, D.SF32{30.0}, D.SF32{40.0}], D.TF32{})

def env2.k(r: E.ResT(C.Frame), env: P.Env) -> P.Env:
  match r:
    case Fail{e}:
      env
    case Done{f}:
      env.k(P.Env.add(env, "u", f))

# t and u: b str (join key), label str, c f32 (clashes with t.c)
def env2() -> P.Env:
  env2.k(C.Frame.from_columns([ub(), ulabel(), uc()]), env())

def src() -> P.Plan:
  P.Source{"t", [S.Field{"a", D.TU32{}}, S.Field{"b", D.TStr{}}, S.Field{"c", D.TF32{}}, S.Field{"d", D.TBool{}}, S.Field{"e", D.TU32{}}]}

# ---- printing (eval_arith's compact form) -------------------------------------------

def scal(xs: List<&2, D.Scalar>) -> String:
  List.show(~&2, ~D.Scalar, ~(s => D.Scalar.show(s)), xs)

def cs.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scal(xs)

def cs.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cs.b(t, C.Column.to_scalars(c))

def cs(c: C.Column) -> String:
  cs.a(C.Column.dtype(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs(c)) <> ncols(t)

def fr.f(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncols(cols), " | ")

def fr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fr.f(f)

def sch(r: E.Res(List<&2, S.Field>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{s}:
      S.Schema.show(s)

def verdict(+t1: String, +t2: String, +s1: String, +s2: String) -> String:
  Bool.pick(String, Bool.and(String.eq(t1, t2), String.eq(s1, s2)), "same: " ++ t1, "DIFFERENT:\n  " ++ s1 ++ "\n  " ++ s2 ++ "\n  " ++ t1 ++ "\n  " ++ t2)

def explain2(+p: P.Plan) -> String:
  P.Plan.explain(p) ++ "\n=>\n" ++ P.Plan.explain(P.Plan.optimize(p))

def check(+name: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- " ++ name)
    IO.print(explain2(p))
    r1 : E.ResT(C.Frame) <- Q.Exec.run(p, env())
    r2 : E.ResT(C.Frame) <- Q.Lazy.collect(p, env())
    IO.print(verdict(fr(r1), fr(r2), sch(P.Plan.schema(p)), sch(P.Plan.schema(P.Plan.optimize(p)))))

def check2(+name: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- " ++ name)
    IO.print(explain2(p))
    r1 : E.ResT(C.Frame) <- Q.Exec.run(p, env2())
    r2 : E.ResT(C.Frame) <- Q.Lazy.collect(p, env2())
    IO.print(verdict(fr(r1), fr(r2), sch(P.Plan.schema(p)), sch(P.Plan.schema(P.Plan.optimize(p)))))

# ---- plans ----------------------------------------------------------------------------

def col(n: String) -> X.Expr:
  X.Col{n}

def u32(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def al(e: X.Expr, n: String) -> X.Expr:
  X.Alias{e, n}

# k > 2 moves below the Select (as a > 2); s > 12 reads a computed column: stays
def p_select() -> P.Plan:
  P.Filter{bin(X.And{}, bin(X.Gt{}, col("k"), u32(2)), bin(X.Gt{}, col("s"), u32(12))), P.Select{[al(col("a"), "k"), col("b"), al(bin(X.Add{}, col("a"), u32(10)), "s")], src()}}

# two filters merge (inner first) and sink below the Select
def p_merge() -> P.Plan:
  P.Select{[col("b"), col("a")], P.Filter{col("d"), P.Filter{bin(X.Lt{}, col("a"), u32(6)), src()}}}

# n > 4 reads the new column: stays; b == "x" moves below the WithColumns
def p_with() -> P.Plan:
  P.Filter{bin(X.And{}, bin(X.Gt{}, col("n"), u32(4)), bin(X.Eq{}, col("b"), X.Lit{D.SStr{"x"}})), P.WithColumns{[al(bin(X.Mul{}, col("a"), u32(2)), "n")], src()}}

# Head{5, Head{2, ..}} = Head{2, ..}, and it sinks below the Select
def p_head() -> P.Plan:
  P.Head{5, P.Head{2, P.Select{[col("a"), col("c")], src()}}}

# a filter does not move below a Head
def p_nohead() -> P.Plan:
  P.Filter{col("d"), P.Head{4, P.Select{[col("d"), col("b")], src()}}}

# a filter moves below a Sort
def p_sort() -> P.Plan:
  P.Filter{bin(X.Gt{}, col("c"), X.Lit{D.SF32{1.0}}), P.Sort{[O.SortKey{"a", True{}, False{}}], P.Select{[col("a"), col("c"), col("b")], src()}}}

# a filter above a GroupBy stays there; the one below sinks to the source and
# the projection keeps only b, a, d
def p_group() -> P.Plan:
  P.Filter{bin(X.Gt{}, col("s"), u32(3)), P.GroupBy{[col("b")], [al(X.Agg{X.Sum{}, col("a")}, "s"), al(X.Agg{X.Len{}, u32(1)}, "n")], True{}, P.Select{[col("b"), col("a")], P.Filter{bin(X.Ne{}, col("d"), X.Lit{D.SBool{False{}}}), src()}}}}

def usrc() -> P.Plan:
  P.Source{"u", [S.Field{"b", D.TStr{}}, S.Field{"label", D.TStr{}}, S.Field{"c", D.TF32{}}]}

# no pushdown into a Join (v1); projection keeps the keys and t.c (it makes u.c
# the clashing c_right) and drops d, e
def p_tjoin() -> P.Plan:
  P.Select{[col("a"), col("label"), col("c_right")], P.Filter{bin(X.Gt{}, col("a"), u32(1)), P.Join{J.Inner{}, ["b"], ["b"], src(), usrc()}}}

# projection through a Join (the clashing `price` is kept on the left) and a GroupBy
def p_join() -> P.Plan:
  P.Filter{bin(X.Gt{}, col("qty_sum"), u32(10)), P.GroupBy{[col("category")], [al(X.Agg{X.Sum{}, col("qty")}, "qty_sum"), X.Agg{X.Max{}, col("price_right")}], True{}, P.Join{J.Inner{}, ["product"], ["product"], P.Source{"sales", [S.Field{"id", D.TU32{}}, S.Field{"product", D.TStr{}}, S.Field{"qty", D.TU32{}}, S.Field{"price", D.TF32{}}, S.Field{"ok", D.TBool{}}]}, P.Source{"products", [S.Field{"product", D.TStr{}}, S.Field{"category", D.TStr{}}, S.Field{"price", D.TF32{}}, S.Field{"weight", D.TF32{}}]}}}}

def main() -> IO(Unit):
  do IO<Unit>:
    check("select", p_select())
    check("merge", p_merge())
    check("with_columns", p_with())
    check("head", p_head())
    check("no pushdown through head", p_nohead())
    check("sort", p_sort())
    check("group_by", p_group())
    check2("join", p_tjoin())
    IO.print("-- join + group_by")
    IO.print(explain2(p_join()))
    IO.print("-- exec errors")
    j : E.ResT(C.Frame) <- Q.Lazy.collect(P.Join{J.Inner{}, ["b"], ["b"], src(), src()}, env())
    IO.print(fr(j))
    w : E.ResT(C.Frame) <- Q.Lazy.collect(P.Source{"t", [S.Field{"a", D.TU32{}}, S.Field{"b", D.TU32{}}]}, env())
    IO.print(fr(w))
    m : E.ResT(C.Frame) <- Q.Lazy.collect(P.Source{"nope", [S.Field{"a", D.TU32{}}]}, env())
    IO.print(fr(m))
    IO.print("-- an ill-typed plan comes back unchanged")
    IO.print(explain2(P.Filter{col("a"), P.Filter{col("d"), src()}}))

#|-- select
#|FILTER ((col("k") > lit(2)) & (col("s") > lit(12)))
#|  SELECT [col("a").alias("k"), col("b"), (col("a") + lit(10)).alias("s")]
#|    SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|FILTER (col("s") > lit(12))
#|  SELECT [col("a").alias("k"), col("b"), (col("a") + lit(10)).alias("s")]
#|    FILTER (col("a") > lit(2))
#|      SELECT [col("a"), col("b")]
#|        SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=3 k:u32=[4, 5, 6] | b:str=[x, y, x] | s:u32=[14, 15, 16]
#|-- merge
#|SELECT [col("b"), col("a")]
#|  FILTER col("d")
#|    FILTER (col("a") < lit(6))
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|SELECT [col("b"), col("a")]
#|  FILTER ((col("a") < lit(6)) & col("d"))
#|    SELECT [col("a"), col("b"), col("d")]
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=2 b:str=[x, x] | a:u32=[1, 4]
#|-- with_columns
#|FILTER ((col("n") > lit(4)) & (col("b") == lit("x")))
#|  WITH_COLUMNS [(col("a") * lit(2)).alias("n")]
#|    SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|FILTER (col("n") > lit(4))
#|  WITH_COLUMNS [(col("a") * lit(2)).alias("n")]
#|    FILTER (col("b") == lit("x"))
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=2 a:u32=[4, 6] | b:str=[x, x] | c:f32=[null, 5.5] | d:bool=[true, true] | e:u32=[0, 0] | n:u32=[8, 12]
#|-- head
#|HEAD 5
#|  HEAD 2
#|    SELECT [col("a"), col("c")]
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|SELECT [col("a"), col("c")]
#|  HEAD 2
#|    SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=2 a:u32=[1, 2] | c:f32=[0.5, 1.5]
#|-- no pushdown through head
#|FILTER col("d")
#|  HEAD 4
#|    SELECT [col("d"), col("b")]
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|FILTER col("d")
#|  SELECT [col("d"), col("b")]
#|    HEAD 4
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=3 d:bool=[true, true, true] | b:str=[x, z, x]
#|-- sort
#|FILTER (col("c") > lit(1))
#|  SORT BY [col("a") desc]
#|    SELECT [col("a"), col("c"), col("b")]
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|SORT BY [col("a") desc]
#|  SELECT [col("a"), col("c"), col("b")]
#|    FILTER (col("c") > lit(1))
#|      SELECT [col("a"), col("b"), col("c")]
#|        SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=4 a:u32=[null, 6, 5, 2] | c:f32=[2.5, 5.5, 4.5, 1.5] | b:str=[z, x, y, y]
#|-- group_by
#|FILTER (col("s") > lit(3))
#|  GROUP_BY [col("b")] AGG [col("a").sum().alias("s"), lit(1).len().alias("n")] MAINTAIN_ORDER
#|    SELECT [col("b"), col("a")]
#|      FILTER (col("d") != lit(false))
#|        SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|FILTER (col("s") > lit(3))
#|  GROUP_BY [col("b")] AGG [col("a").sum().alias("s"), lit(1).len().alias("n")] MAINTAIN_ORDER
#|    SELECT [col("b"), col("a")]
#|      FILTER (col("d") != lit(false))
#|        SELECT [col("a"), col("b"), col("d")]
#|          SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|same: h=1 b:str=[x] | s:u32=[11] | n:u32=[3]
#|-- join
#|SELECT [col("a"), col("label"), col("c_right")]
#|  FILTER (col("a") > lit(1))
#|    INNER JOIN ON [b = b]
#|      SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|      SOURCE u [b:str, label:str, c:f32]
#|=>
#|SELECT [col("a"), col("label"), col("c_right")]
#|  FILTER (col("a") > lit(1))
#|    INNER JOIN ON [b = b]
#|      SELECT [col("a"), col("b"), col("c")]
#|        SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|      SOURCE u [b:str, label:str, c:f32]
#|same: h=6 a:u32=[2, 4, 4, 5, 6, 6] | label:str=[y1, x1, x2, y1, x1, x2] | c_right:f32=[20, 10, 40, 20, 10, 40]
#|-- join + group_by
#|FILTER (col("qty_sum") > lit(10))
#|  GROUP_BY [col("category")] AGG [col("qty").sum().alias("qty_sum"), col("price_right").max()] MAINTAIN_ORDER
#|    INNER JOIN ON [product = product]
#|      SOURCE sales [id:u32, product:str, qty:u32, price:f32, ok:bool]
#|      SOURCE products [product:str, category:str, price:f32, weight:f32]
#|=>
#|FILTER (col("qty_sum") > lit(10))
#|  GROUP_BY [col("category")] AGG [col("qty").sum().alias("qty_sum"), col("price_right").max()] MAINTAIN_ORDER
#|    INNER JOIN ON [product = product]
#|      SELECT [col("product"), col("qty"), col("price")]
#|        SOURCE sales [id:u32, product:str, qty:u32, price:f32, ok:bool]
#|      SELECT [col("product"), col("category"), col("price")]
#|        SOURCE products [product:str, category:str, price:f32, weight:f32]
#|-- exec errors
#|error: InvalidOperation: source not in env (or used twice): t
#|error: InvalidOperation: source t: data schema [a:u32, b:str, c:f32, d:bool, e:u32] differs from the plan's [a:u32, b:u32]
#|error: InvalidOperation: source not in env (or used twice): nope
#|-- an ill-typed plan comes back unchanged
#|FILTER col("a")
#|  FILTER col("d")
#|    SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
#|=>
#|FILTER col("a")
#|  FILTER col("d")
#|    SOURCE t [a:u32, b:str, c:f32, d:bool, e:u32]
