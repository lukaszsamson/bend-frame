# T3.1 (DESIGN.md 16.2 rule 1): moves and borrows keep v0.1's results exactly. The liveness
# pass (Eval.mark) turns the LAST reference of a column the operator does not keep into a move
# (Frame.lend); earlier references copy (Frame.get_cloned). Covered: duplicate references and
# aliases in select, with_columns referencing a column it overwrites (and a swap), the
# with_columns input snapshot, empty selections, head(1) then select, strict-cast error rows
# and their precedence across columns / expressions, static errors before data errors, filter
# then select (eager and lazy), group_by with a key also read by an aggregation, the
# group_by entry points with moves (Eval.full_mv / Eval.expr_mv), a self join, unique's
# borrowed keys (repeated subset names), and Frame.lend / Frame.replace themselves.
# Every expectation not involving Frame.lend / Eval.*_mv was also produced by the build before
# T3.1 (commit 016727e, every reference copying) and is identical.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/expr.bend as X
import ./../src/eval.bend as V
import ./../src/groupby.bend as G
import ./../src/join.bend as J
import ./../src/table.bend as TV
import ./../src/plan.bend as P
import ./../src/exec.bend as Q

# ---- helpers ----------------------------------------------------------------------

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def scal(xs: List<&2, D.Scalar>) -> String:
  List.show(~&2, ~D.Scalar, ~(s => D.Scalar.show(s)), xs)

def cs.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scal(xs)

def cs.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cs.b(t, C.Column.to_scalars(c))

# a column as `dtype=[cells]`
def cs(c: C.Column) -> String:
  cs.a(C.Column.dtype(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs(c)) <> ncols(t)

# a frame as `h=N name:dtype=[cells] | ...`
def fs(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncols(cols), " | ")

def fr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fs(f)

# a frame whose columns may be hollow stand-ins (after a move): height and names only
def info.k(r: C.Frame & C.FInfo) -> String:
  (f, i) = r
  match i:
    case C.FInfo{h, ns}:
      "h=" ++ U32.show(h) ++ " names=" ++ String.join(ns, ",")

def ex.k(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      cs(c) ++ " / " ++ info.k(C.Frame.info(f))

# the column, then the frame in full (when nothing was moved out of it)
def ex.full(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      cs(c) ++ " / " ++ fs(f)

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def al(e: X.Expr, n: String) -> X.Expr:
  X.Alias{e, n}

def cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.Cast{e, t}

# a: u32 with a null; b: u32 (row 1 does not fit i32); s: str; c: f32 with a null (row 3 does not
# fit u32); k: bool with a null
def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}], D.TU32{}), mk("b", [D.SU32{10}, D.SU32{3000000000}, D.SU32{30}, D.SU32{40}], D.TU32{}), mk("s", [D.SStr{"x"}, D.SStr{"y"}, D.SStr{"x"}, D.SStr{"7"}], D.TStr{}), mk("c", [D.SF32{0.5}, D.SNull{}, D.SF32{2.5}, D.SF32{F32.neg(2.5)}], D.TF32{}), mk("k", [D.SBool{True{}}, D.SBool{False{}}, D.SBool{True{}}, D.SNull{}], D.TBool{})])

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

def on(g: C.Frame -> String) -> String:
  on.k(g, base())

def then(r: E.ResT(C.Frame), g: C.Frame -> E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      g(f)

# Frame.lend then Frame.replace: the lent column, then the frame put back together
def lend.d(+name: String, f: C.Frame, cc: C.Column & C.Column) -> String:
  (c1, c2) = cc
  "lent " ++ cs(c1) ++ " / back " ++ fr(C.Frame.replace(f, name, c2))

def lend.k(+name: String, r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e) ++ " / " ++ fs(f)
    case Done{c}:
      lend.d(name, f, C.Column.clone(c))

def lend(+name: String) -> String:
  on(f => lend.k(name, C.Frame.lend(f, name)))

def env.k(r: P.Env & P.Plan) -> P.Env:
  (env, p) = r
  env

def env.r(r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      P.Env.empty()
    case Done{f}:
      env.k(P.Env.add(P.Env.empty(), "t", f))

def src() -> P.Plan:
  P.Source{"t", [S.Field{"a", D.TU32{}}, S.Field{"b", D.TU32{}}, S.Field{"s", D.TStr{}}, S.Field{"c", D.TF32{}}, S.Field{"k", D.TBool{}}]}

def lazy(+p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- Q.Exec.run(p, env.r(base()))
    IO.print(fr(r))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- select: duplicate references and aliases (first copies, last moves)")
    IO.print(on(f => fr(V.Eval.select(f, [col("a"), al(col("a"), "y")]))))
    IO.print(on(f => fr(V.Eval.select(f, [al(bin(X.Add{}, col("a"), col("a")), "d"), al(X.Agg{X.Sum{}, col("a")}, "sa"), al(col("a"), "a2"), col("s")]))))
    IO.print(on(f => fr(V.Eval.select(f, [al(X.Agg{X.Sum{}, col("b")}, "sb"), al(X.Agg{X.Max{}, col("b")}, "mb")]))))
    IO.print(on(f => fr(V.Eval.select(f, Nil{}))))
    IO.print(on(f => fr(V.Eval.select(C.Frame.head(f, 1), [col("s"), al(bin(X.Mul{}, col("b"), lu(2)), "b2"), col("k")]))))
    IO.print("-- with_columns: the input snapshot; an overwritten input moves at its last reference")
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(bin(X.Add{}, col("a"), lu(1)), "a"), al(col("a"), "z")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(col("b"), "a"), al(col("a"), "b")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(X.Agg{X.Sum{}, col("a")}, "a"), al(col("a"), "a3")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [col("s"), al(bin(X.Mul{}, col("a"), lu(2)), "d")]))))
    IO.print("-- strict casts: the first failing row of the first failing expression")
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(cast(col("b"), D.TI32{}), "b"), al(cast(col("c"), D.TU32{}), "c")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(cast(col("c"), D.TU32{}), "c"), al(cast(col("b"), D.TI32{}), "b")]))))
    IO.print(on(f => fr(V.Eval.select(f, [al(cast(col("b"), D.TI32{}), "x"), al(cast(col("b"), D.TI32{}), "y")]))))
    IO.print(on(f => fr(V.Eval.select(f, [col("c"), al(cast(col("c"), D.TU32{}), "u")]))))
    IO.print(on(f => fr(V.Eval.select(f, [al(cast(col("a"), D.TI32{}), "ai"), al(cast(col("c"), D.TI32{}), "ci")]))))
    IO.print(on(f => fr(V.Eval.with_columns(f, [al(cast(col("b"), D.TI32{}), "b"), al(col("nope"), "x")]))))
    IO.print("-- filter, then select (eager, then lazy)")
    IO.print(on(f => fr(then(V.Eval.filter(f, col("k")), g => V.Eval.select(g, [col("a"), col("s")])))))
    IO.print(on(f => fr(then(V.Eval.filter(f, bin(X.Gt{}, col("b"), lu(15))), g => V.Eval.select(g, [al(bin(X.Add{}, col("b"), col("b")), "bb"), col("k")])))))
    lazy(P.Select{[col("a"), col("s")], P.Filter{col("k"), src()}})
    lazy(P.Select{[al(bin(X.Add{}, col("b"), lu(1)), "b1"), col("b")], P.Filter{bin(X.Gt{}, col("b"), lu(15)), src()}})
    IO.print("-- group_by: a key that an aggregation also reads")
    IO.print(on(f => fr(G.GroupBy.run(f, [col("s")], [al(X.Agg{X.Sum{}, col("a")}, "sa"), al(X.Agg{X.First{}, col("s")}, "fs"), al(X.Agg{X.Len{}, lu(1)}, "n")], True{}))))
    lazy(P.GroupBy{[col("k")], [al(X.Agg{X.Max{}, col("b")}, "mb"), al(X.Agg{X.Count{}, col("k")}, "ck")], True{}, src()})
    IO.print("-- the group_by entry points with moves (Eval.full_mv / Eval.expr_mv)")
    IO.print(on(f => ex.k(V.Eval.full_mv(f, bin(X.Add{}, col("a"), col("b")), Nil{}))))
    IO.print(on(f => ex.full(V.Eval.full_mv(f, col("a"), ["a"]))))
    IO.print(on(f => ex.k(V.Eval.full_mv(f, bin(X.Add{}, col("a"), col("a")), Nil{}))))
    IO.print(on(f => ex.k(V.Eval.expr_mv(f, X.Agg{X.Sum{}, col("b")}, Nil{}))))
    IO.print(on(f => ex.k(V.Eval.full_mv(f, X.Agg{X.Len{}, lu(1)}, Nil{}))))
    IO.print(on(f => ex.k(V.Eval.full_mv(f, cast(col("c"), D.TU32{}), Nil{}))))
    IO.print("-- self join: the first use of the Source copies the frame")
    lazy(P.Join{J.Inner{}, ["s"], ["s"], src(), P.Select{[col("s"), col("a")], src()}})
    IO.print("-- unique: borrowed keys (repeated names copy, the last one is lent and put back)")
    IO.print(on(f => fr(TV.Unique.run(f, ["s"]))))
    IO.print(on(f => fr(TV.Unique.run(f, ["s", "s"]))))
    IO.print(on(f => fr(TV.Unique.run(f, ["k", "s", "k"]))))
    IO.print(on(f => fr(TV.Unique.run(f, Nil{}))))
    IO.print(on(f => fr(TV.Unique.run(C.Frame.head(f, 2), ["c"]))))
    IO.print("-- Frame.lend / Frame.replace")
    IO.print(lend("c"))
    IO.print(lend("s"))
    IO.print(lend("nope"))
#|-- select: duplicate references and aliases (first copies, last moves)
#|h=4 a:u32=[1, 2, null, 4] | y:u32=[1, 2, null, 4]
#|h=4 d:u32=[2, 4, null, 8] | sa:u32=[7, 7, 7, 7] | a2:u32=[1, 2, null, 4] | s:str=[x, y, x, 7]
#|h=1 sb:u32=[3000000080] | mb:u32=[3000000000]
#|h=0
#|h=1 s:str=[x] | b2:u32=[20] | k:bool=[true]
#|-- with_columns: the input snapshot; an overwritten input moves at its last reference
#|h=4 a:u32=[2, 3, null, 5] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null] | z:u32=[1, 2, null, 4]
#|h=4 a:u32=[10, 3000000000, 30, 40] | b:u32=[1, 2, null, 4] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null]
#|h=4 a:u32=[7, 7, 7, 7] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null] | a3:u32=[1, 2, null, 4]
#|h=4 a:u32=[1, 2, null, 4] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null] | d:u32=[2, 4, null, 8]
#|-- strict casts: the first failing row of the first failing expression
#|error: InvalidOperation: cast u32 to i32: row 1 holds 3000000000
#|error: InvalidOperation: cast f32 to u32: row 3 holds -2.5
#|error: InvalidOperation: cast u32 to i32: row 1 holds 3000000000
#|error: InvalidOperation: cast f32 to u32: row 3 holds -2.5
#|h=4 ai:i32=[1, 2, null, 4] | ci:i32=[0, null, 2, -2]
#|error: ColumnNotFound: nope
#|-- filter, then select (eager, then lazy)
#|h=2 a:u32=[1, null] | s:str=[x, x]
#|h=3 bb:u32=[1705032704, 60, 80] | k:bool=[false, true, null]
#|h=2 a:u32=[1, null] | s:str=[x, x]
#|h=3 b1:u32=[3000000001, 31, 41] | b:u32=[3000000000, 30, 40]
#|-- group_by: a key that an aggregation also reads
#|h=3 s:str=[x, y, 7] | sa:u32=[1, 2, 4] | fs:str=[x, y, 7] | n:u32=[2, 1, 1]
#|h=3 k:bool=[true, false, null] | mb:u32=[30, 3000000000, 40] | ck:u32=[2, 1, 0]
#|-- the group_by entry points with moves (Eval.full_mv / Eval.expr_mv)
#|u32=[11, 3000000002, null, 44] / h=4 names=a,b,s,c,k
#|u32=[1, 2, null, 4] / h=4 a:u32=[1, 2, null, 4] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null]
#|u32=[2, 4, null, 8] / h=4 names=a,b,s,c,k
#|u32=[3000000080] / h=4 names=a,b,s,c,k
#|u32=[4, 4, 4, 4] / h=4 names=a,b,s,c,k
#|error: InvalidOperation: cast f32 to u32: row 3 holds -2.5
#|-- self join: the first use of the Source copies the frame
#|h=6 a:u32=[1, 1, 2, null, null, 4] | b:u32=[10, 10, 3000000000, 30, 30, 40] | s:str=[x, x, y, x, x, 7] | c:f32=[0.5, 0.5, null, 2.5, 2.5, -2.5] | k:bool=[true, true, false, true, true, null] | a_right:u32=[1, null, 2, 1, null, 4]
#|-- unique: borrowed keys (repeated names copy, the last one is lent and put back)
#|h=3 a:u32=[1, 2, 4] | b:u32=[10, 3000000000, 40] | s:str=[x, y, 7] | c:f32=[0.5, null, -2.5] | k:bool=[true, false, null]
#|h=3 a:u32=[1, 2, 4] | b:u32=[10, 3000000000, 40] | s:str=[x, y, 7] | c:f32=[0.5, null, -2.5] | k:bool=[true, false, null]
#|h=3 a:u32=[1, 2, 4] | b:u32=[10, 3000000000, 40] | s:str=[x, y, 7] | c:f32=[0.5, null, -2.5] | k:bool=[true, false, null]
#|h=4 a:u32=[1, 2, null, 4] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null]
#|h=2 a:u32=[1, 2] | b:u32=[10, 3000000000] | s:str=[x, y] | c:f32=[0.5, null] | k:bool=[true, false]
#|-- Frame.lend / Frame.replace
#|lent f32=[0.5, null, 2.5, -2.5] / back h=4 a:u32=[1, 2, null, 4] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null]
#|lent str=[x, y, x, 7] / back h=4 a:u32=[1, 2, null, 4] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null]
#|error: ColumnNotFound: nope / h=4 a:u32=[1, 2, null, 4] | b:u32=[10, 3000000000, 30, 40] | s:str=[x, y, x, 7] | c:f32=[0.5, null, 2.5, -2.5] | k:bool=[true, false, true, null]
