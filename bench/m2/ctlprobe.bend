# bench/m2/ctlprobe.bend -- diagnostic for the 1k-row q3 / q5 control regression (GATES_V02.md G3).
# Reads sales_1000.csv and products.csv untimed, prepares each stage's input untimed, then runs ONE
# eager stage `reps` times over fresh clones and prints the total ms of the stage loop and of a
# clone-only loop (the difference is the stage). Uses only facade calls present at 3612482, so the
# same file builds against the pinned baseline and the candidate.
#   ./ctlprobe <stage> <reps>     stage: 0 withcols 1 groupby3 2 sort3 3 join 4 groupby5 5 sort5 6 q3 7 q5
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/expr.bend as X

def Pr.revenue() -> X.Expr:
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0))))

def Pr.un(x: E.ResT(C.Frame)) -> C.Frame:
  match x:
    case Fail{e}:
      C.Frame.empty()
    case Done{f}:
      f

def Pr.wc(f: C.Frame) -> E.ResT(C.Frame):
  DF.with_columns(f, [DF.alias(Pr.revenue(), "revenue")])

def Pr.g3(f: C.Frame) -> E.ResT(C.Frame):
  DF.group_by(f, [DF.col("region")], [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"), DF.alias(DF.mean(DF.col("price")), "price_mean"), DF.alias(DF.len(), "count"), DF.alias(DF.max(DF.col("qty")), "qty_max")])

def Pr.g5(f: C.Frame) -> E.ResT(C.Frame):
  DF.group_by(f, [DF.col("category")], [DF.alias(DF.sum(DF.col("qty")), "qty_sum")])

def Pr.j(a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  DF.inner_join(a, b, ["product"], ["product"])

def Pr.q3.b(x: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.sort(Pr.un(x), [DF.asc("region")])

def Pr.q3.c(x: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.sort(Pr.un(x), [DF.asc("category")])

# the stage k over (a, b): 0 withcols, 1 groupby3, 2 sort3, 3 join, 4 groupby5, 5 sort5, 6 q3, 7 q5
def Pr.op(+k: U32, a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  match k:
    case 0:
      Pr.wc(a)
    case 1:
      Pr.g3(a)
    case 2:
      DF.sort(a, [DF.asc("region")])
    case 3:
      Pr.j(a, b)
    case 4:
      Pr.g5(a)
    case 5:
      DF.sort(a, [DF.asc("category")])
    case 6:
      Pr.q3.b(Pr.g3(Pr.un(Pr.wc(a))))
    case _:
      Pr.q3.c(Pr.g5(Pr.un(Pr.j(a, b))))

def Pr.ht(r: C.Frame & U32) -> U32:
  (f, h) = r
  h

def Pr.h(x: E.ResT(C.Frame)) -> U32:
  match x:
    case Fail{e}:
      0
    case Done{f}:
      Pr.ht(C.Frame.height(f))

# one rep's work on the clones: the stage (run) or nothing but the clones' heights
def Pr.step(+run: Bool, +k: U32, ca: C.Frame, cb: C.Frame) -> U32:
  match run:
    case True{}:
      Pr.h(Pr.op(k, ca, cb))
    case False{}:
      U32.add(Pr.ht(C.Frame.height(ca)), Pr.ht(C.Frame.height(cb)))

# reps stage runs over clones (ra / rb: the inputs and a fresh clone each); answers the inputs back
# and the sum of the result heights
def Pr.loop(n: Nat, +k: U32, +run: Bool, +acc: U32, ra: C.Frame & C.Frame, rb: C.Frame & C.Frame) -> C.Frame & C.Frame & U32:
  match n:
    case 0n:
      (a, ca) = ra
      (b, cb) = rb
      (a, b, acc)
    case 1n+p:
      (a, ca) = ra
      (b, cb) = rb
      +s = Pr.step(run, k, ca, cb)
      Pr.loop(p, k, run, U32.add(acc, s), DF.clone(a), DF.clone(b))

# the stage's input: sales (withcols, join, q3, q5), withcols(sales) (groupby3), groupby3 (sort3),
# join (groupby5), groupby5 (sort5)
def Pr.input(+k: U32, s: C.Frame, p: C.Frame) -> C.Frame:
  match k:
    case 1:
      Pr.un(Pr.wc(s))
    case 2:
      Pr.un(Pr.g3(Pr.un(Pr.wc(s))))
    case 4:
      Pr.un(Pr.j(s, p))
    case 5:
      Pr.un(Pr.g5(Pr.un(Pr.j(s, p))))
    case _:
      s

def Pr.out(+t0: Nat, +t1: Nat, +t2: Nat, +h: U32) -> IO(Unit):
  IO.print("{\"clone_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"total_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"stage_ms\":" ++ Nat.show(Nat.sub(Nat.sub(t2, t1), Nat.sub(t1, t0))) ++ ",\"h\":" ++ U32.show(h) ++ "}")

def Pr.run.c(+t0: Nat, +t1: Nat, r: C.Frame & C.Frame & U32) -> IO(Unit):
  (a, b, h) = r
  do IO<Unit>:
    t2 : Nat <- IO.now
    Pr.out(t0, t1, t2, h)

def Pr.run.b(+k: U32, +reps: Nat, +t0: Nat, r: C.Frame & C.Frame & U32) -> IO(Unit):
  (a, b, h) = r
  do IO<Unit>:
    t1 : Nat <- IO.now
    Pr.run.c(t0, t1, Pr.loop(reps, k, True{}, 0, DF.clone(a), DF.clone(b)))

def Pr.run(+k: U32, +reps: Nat, a: C.Frame, b: C.Frame) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now
    Pr.run.b(k, reps, t0, Pr.loop(reps, k, False{}, 0, DF.clone(a), DF.clone(b)))

def Pr.go.b(+k: U32, +reps: Nat, s: C.Frame, rp: C.Frame & C.Frame) -> IO(Unit):
  (p, cp) = rp
  Pr.run(k, reps, Pr.input(k, s, cp), p)

def Pr.go(+k: U32, +reps: Nat, rs: E.ResT(C.Frame), rp: E.ResT(C.Frame)) -> IO(Unit):
  Pr.go.b(k, reps, Pr.un(rs), DF.clone(Pr.un(rp)))

def Pr.ab.b(x: String, rest: List<&1, String>) -> String & String:
  match rest:
    case Nil{}:
      (x, "2000")
    case y <> more:
      (x, y)

# the first two arguments after the program name (defaults "6" and "2000")
def Pr.ab(xs: List<&1, String>) -> String & String:
  match xs:
    case Nil{}:
      ("6", "2000")
    case x <> rest:
      Pr.ab.b(x, rest)

def Pr.num(m: Maybe<&2, U32>, +d: U32) -> U32:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def Pr.main.b(r: String & String, rs: E.ResT(C.Frame), rp: E.ResT(C.Frame)) -> IO(Unit):
  (a, b) = r
  Pr.go(Pr.num(U32.read(a), 6), U32.to_nat(Pr.num(U32.read(b), 2000)), rs, rp)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args
    rs : E.ResT(C.Frame) <- DF.read_csv("bench/data/sales_1000.csv")
    rp : E.ResT(C.Frame) <- DF.read_csv("bench/data/products.csv")
    Pr.main.b(Pr.ab(List.tail(&1, String, args)), rs, rp)
