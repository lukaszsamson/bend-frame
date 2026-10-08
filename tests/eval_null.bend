# Eval null semantics (DESIGN.md section 5): comparisons, boolean ops (Kleene
# and/or, like Polars), is_null, fill_null, filter with null predicates, the
# null-slot invariant.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/eval.bend as V
import ./../src/fmt.bend as F

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

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def table(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def ex.k(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      cs(c)

def neg(v: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{v})}

def pos(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [D.SU32{1}, D.SU32{2}, D.SNull{}, D.SU32{4}, D.SU32{5}], D.TU32{}), mk("s", [D.SStr{"pear"}, D.SStr{"fig"}, D.SStr{"apple"}, D.SNull{}, D.SStr{"fig"}], D.TStr{}), mk("p", [D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}, D.SBool{False{}}], D.TBool{}), mk("b", [D.SF32{0.5}, D.SNull{}, D.SF32{2.5}, D.SNull{}, D.SF32{4.5}], D.TF32{})])

# a, b: the 9 combinations of true / false / null
def kl() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [D.SBool{True{}}, D.SBool{True{}}, D.SBool{True{}}, D.SBool{False{}}, D.SBool{False{}}, D.SBool{False{}}, D.SNull{}, D.SNull{}, D.SNull{}], D.TBool{}), mk("b", [D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}, D.SBool{False{}}, D.SNull{}], D.TBool{})])

# the raw data slots of a result (validity ignored): null slots hold the default
def raw.go(n: Nat, +i: U32, r: C.Column & D.Scalar) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (c, s) = r
      D.Scalar.show(s) <> raw.go(p, U32.inc(i), C.Column.data_cell(c, U32.inc(i)))

def raw.k(r: C.Column & U32) -> String:
  (c, +n) = r
  "raw=" ++ List.show(~&2, ~String, ~(s => s), raw.go(U32.to_nat(n), 0, C.Column.data_cell(c, 0)))

def raw.r(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{c}:
      raw.k(C.Column.len(c))

def on.k(g: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      g(f)

def on(g: C.Frame -> String) -> String:
  on.k(g, base())

def ex(e: X.Expr) -> String:
  on(f => ex.k(V.Eval.expr(f, e)))

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def ls(s: String) -> X.Expr:
  X.Lit{D.SStr{s}}

def lb(b: Bool) -> X.Expr:
  X.Lit{D.SBool{b}}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def rs(r: E.Res(D.Scalar)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{v}:
      D.Scalar.show(v)

def raw(e: X.Expr) -> String:
  on(f => raw.r(V.Eval.expr(f, e)))

# over the 9-row truth-table frame
def exk(e: X.Expr) -> String:
  on.k(f => ex.k(V.Eval.expr(f, e)), kl())

def rawk(e: X.Expr) -> String:
  on.k(f => raw.r(V.Eval.expr(f, e)), kl())

def nullb() -> X.Expr:
  X.Cast{X.Lit{D.SNull{}}, D.TBool{}}

def main() -> IO(Unit):
  do IO<Unit>:
    # comparisons: null in, null out
    IO.print(ex(bin(X.Eq{}, col("a"), lu(2))))
    IO.print(ex(bin(X.Ne{}, col("a"), lu(2))))
    IO.print(ex(bin(X.Lt{}, col("s"), ls("g"))))
    IO.print(ex(bin(X.Eq{}, col("s"), ls("fig"))))
    IO.print(ex(bin(X.Ge{}, col("s"), col("s"))))
    IO.print(ex(bin(X.Le{}, col("b"), X.Lit{D.SF32{2.5}})))
    IO.print(ex(bin(X.Eq{}, col("p"), lb(True{}))))
    IO.print(ex(bin(X.Lt{}, col("p"), lb(True{}))))
    # boolean ops over mixed validity (see the truth tables below)
    IO.print(ex(bin(X.And{}, col("p"), bin(X.Gt{}, col("a"), lu(1)))))
    IO.print(ex(bin(X.Or{}, col("p"), X.Un{X.IsNull{}, col("b")})))
    IO.print(ex(X.Un{X.Not{}, col("p")}))
    # is_null / is_not_null never answer null
    IO.print(ex(X.Un{X.IsNull{}, col("a")}))
    IO.print(ex(X.Un{X.IsNotNull{}, col("s")}))
    IO.print(ex(X.Un{X.IsNull{}, lu(1)}))
    # fill_null per dtype; null only where both sides are null
    IO.print(ex(X.FillNull{col("a"), lu(0)}))
    IO.print(ex(X.FillNull{col("b"), X.Cast{col("a"), D.TF32{}}}))
    IO.print(ex(X.FillNull{col("s"), ls("?")}))
    IO.print(ex(X.FillNull{col("p"), lb(False{})}))
    IO.print(ex(X.FillNull{col("a"), X.Cast{col("b"), D.TU32{}}}))
    IO.print(ex(X.FillNull{col("b"), X.Cast{X.Lit{D.SNull{}}, D.TF32{}}}))
    # the invariant: the slot of a null row holds the dtype default
    IO.print(raw(bin(X.Add{}, col("a"), lu(1))))
    IO.print(raw(X.Un{X.Not{}, col("p")}))
    IO.print(raw(bin(X.Eq{}, col("a"), lu(0))))
    IO.print(raw(X.Cast{col("b"), D.TStr{}}))
    # filter: a null predicate drops the row; a literal broadcasts
    IO.print(on(f => fr(V.Eval.filter(f, col("p")))))
    IO.print(on(f => fr(V.Eval.filter(f, X.Un{X.IsNull{}, col("a")}))))
    IO.print(on(f => fr(V.Eval.filter(f, lb(True{})))))
    IO.print(on(f => fr(V.Eval.filter(f, lb(False{})))))
    # 2 rows kept (a power of two) followed by dropped rows
    IO.print(on(f => fr(V.Eval.filter(f, bin(X.Lt{}, col("a"), lu(3))))))
    # Kleene logic (Polars): false & null = false, true | null = true, otherwise null
    IO.print(exk(bin(X.And{}, col("a"), col("b"))))
    IO.print(exk(bin(X.Or{}, col("a"), col("b"))))
    IO.print(exk(X.Un{X.Not{}, bin(X.And{}, col("a"), col("b"))}))
    IO.print(rawk(bin(X.And{}, col("a"), col("b"))))
    IO.print(rawk(bin(X.Or{}, col("a"), col("b"))))
    # a dense side against a null literal / a masked side
    IO.print(ex(bin(X.And{}, col("p"), nullb())))
    IO.print(ex(bin(X.Or{}, col("p"), nullb())))
    IO.print(ex(bin(X.And{}, lb(False{}), col("p"))))
    IO.print(ex(bin(X.Or{}, lb(True{}), col("p"))))
    IO.print(ex(bin(X.And{}, lb(True{}), col("p"))))
    IO.print(ex(bin(X.Or{}, lb(False{}), col("p"))))
#|bool=[false, true, null, false, false]
#|bool=[true, false, null, true, true]
#|bool=[false, true, true, null, true]
#|bool=[false, true, false, null, true]
#|bool=[true, true, true, null, true]
#|bool=[true, null, true, null, false]
#|bool=[true, false, null, true, false]
#|bool=[false, true, null, false, true]
#|bool=[false, false, null, true, false]
#|bool=[true, true, null, true, false]
#|bool=[false, true, null, false, true]
#|bool=[false, false, true, false, false]
#|bool=[true, true, true, false, true]
#|bool=[false, false, false, false, false]
#|u32=[1, 2, 0, 4, 5]
#|f32=[0.5, 2, 2.5, 4, 4.5]
#|str=[pear, fig, apple, ?, fig]
#|bool=[true, false, false, true, false]
#|u32=[1, 2, 2, 4, 5]
#|f32=[0.5, null, 2.5, null, 4.5]
#|raw=[2, 3, 0, 5, 6]
#|raw=[false, true, false, false, true]
#|raw=[false, false, false, false, false]
#|raw=[0.5, , 2.5, , 4.5]
#|h=2 a:u32=[1, 4] | s:str=[pear, null] | p:bool=[true, true] | b:f32=[0.5, null]
#|h=1 a:u32=[null] | s:str=[apple] | p:bool=[null] | b:f32=[2.5]
#|h=5 a:u32=[1, 2, null, 4, 5] | s:str=[pear, fig, apple, null, fig] | p:bool=[true, false, null, true, false] | b:f32=[0.5, null, 2.5, null, 4.5]
#|h=0 a:u32=[] | s:str=[] | p:bool=[] | b:f32=[]
#|h=2 a:u32=[1, 2] | s:str=[pear, fig] | p:bool=[true, false] | b:f32=[0.5, null]
#|bool=[true, false, null, false, false, false, null, false, null]
#|bool=[true, true, true, true, false, null, true, null, null]
#|bool=[false, true, null, true, true, true, null, true, null]
#|raw=[true, false, false, false, false, false, false, false, false]
#|raw=[true, true, true, true, false, false, true, false, false]
#|bool=[null, false, null, null, false]
#|bool=[true, null, null, true, null]
#|bool=[false, false, false, false, false]
#|bool=[true, true, true, true, true]
#|bool=[true, false, null, true, false]
#|bool=[true, false, null, true, false]
