# bench/w5/t54.bend -- T5.4 micro bench: ONE eager stage of the q1..q6 chain timed `reps` times in ONE process
# over fresh clones (bench/m2/driver.bend's `stages` mode times each stage once per process; a 1 ms clock
# on a 4-10 ms stage needs many samples). Same stage definitions as the m2 driver (it is imported), same
# clock boundary (IO.now around the eager verb, result alive afterwards).
#   bend bench/w5/t54.bend -o build/t54/<which>; build/t54/<which> [--threads N] <sales.csv> <products.csv> <k> <reps>
#   k: 3 groupby_q3 (over with_columns' output), 5 sort_q4 (full sort, 7 columns), 7 join_q5, 8 groupby_q5,
#      10 describe_q6; the stage's op runs over a clone of the sales frame (k = 3: of withcols_q2's output)
# stdout: {"k":..,"parse_ms":..,"ms":[..per rep..]}. Built against baseline-src and the candidate with the same file.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../m2/driver.bend as DR

def T.cat(+ms: Nat, +acc: String) -> String:
  acc ++ Nat.show(ms) ++ ","

def T.forced.k(r: C.Frame & U32) -> E.ResT(C.Frame):
  (f, h) = r
  Done{f}

# the stage's result with every cell walked inside the clock (what is still pending finishes here)
def T.forced(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      T.forced.k(DR.Fw.force(f))

def T.gb4(a: C.Frame) -> E.ResT(C.Frame):
  DF.group_by(a, [DF.col("region")], [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"), DF.alias(DF.mean(DF.col("price")), "price_mean"), DF.alias(DF.len(), "count"), DF.alias(DF.max(DF.col("qty")), "qty_max")])

# the stages: the driver's (k <= 10) and describe over a single column (20 id, 21 qty, 22 price, 23 discount)
def T.col(+k: U32) -> String:
  match k:
    case 20:
      "id"
    case 21:
      "qty"
    case 22:
      "price"
    case _:
      "discount"

def T.op(+k: U32, a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  match k:
    case 20:
      DF.describe(C.Frame.select_names(a, [T.col(k)]))
    case 21:
      DF.describe(C.Frame.select_names(a, [T.col(k)]))
    case 22:
      DF.describe(C.Frame.select_names(a, [T.col(k)]))
    case 23:
      DF.describe(C.Frame.select_names(a, [T.col(k)]))
    case 30:
      DF.group_by(a, [DF.col("region")], [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"), DF.alias(DF.mean(DF.col("price")), "price_mean"), DF.alias(DF.len(), "count"), DF.alias(DF.max(DF.col("qty")), "qty_max"), DF.alias(DF.sum(DF.col("qty")), "qty_sum"), DF.alias(DF.mean(DF.col("discount")), "disc_mean"), DF.alias(DF.min(DF.col("price")), "price_min"), DF.alias(DF.sum(DF.col("price")), "price_sum")])
    case 31:
      DF.group_by(a, [DF.col("region")], [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"), DF.alias(DF.mean(DF.col("price")), "price_mean")])
    case 105:
      T.forced(DR.Stg.op(5, a, b))
    case 41:
      DF.describe(C.Frame.select_names(C.Frame.head(a, 16384), ["id", "qty", "price", "discount"]))
    case 42:
      DF.describe(C.Frame.select_names(C.Frame.head(a, 32768), ["id", "qty", "price", "discount"]))
    case 43:
      DF.describe(C.Frame.select_names(C.Frame.head(a, 65536), ["id", "qty", "price", "discount"]))
    case 44:
      DF.describe(C.Frame.select_names(C.Frame.head(a, 131072), ["id", "qty", "price", "discount"]))
    case 51:
      T.gb4(C.Frame.head(a, 16384))
    case 52:
      T.gb4(C.Frame.head(a, 32768))
    case 53:
      T.gb4(C.Frame.head(a, 65536))
    case 54:
      T.gb4(C.Frame.head(a, 131072))
    case _:
      DR.Stg.op(k, a, b)

# one timed stage over the clones in pp / rs: (ms, the originals back)
def T.step(+k: U32, pp: C.Frame & C.Frame, rs: C.Frame & C.Frame) -> IO(Nat & C.Frame & C.Frame):
  (b, p2) = pp
  (a, a3) = rs
  do IO<Nat & C.Frame & C.Frame>:
    +t0 : Nat <- IO.now()
    x : E.ResT(C.Frame) <- IO.pure(E.ResT(C.Frame), T.op(k, a, b))
    +t1 : Nat <- IO.now()
    return (Nat.sub(t1, t0), p2, a3)

# st = (the last rep's ms, the products frame, the input frame); the first ms (0) is a placeholder
def T.go(left: Nat, +k: U32, +acc: String, st: Nat & C.Frame & C.Frame) -> IO(Unit):
  match left:
    case 0n:
      (ms, p, a) = st
      IO.print(T.cat(ms, acc) ++ "0]}")
    case 1n+r:
      (ms, p, a) = st
      do IO<Unit>:
        st2 : Nat & C.Frame & C.Frame <- T.step(k, DF.clone(p), DF.clone(a))
        T.go(r, k, T.cat(ms, acc), st2)

# the stage's input: k = 3 reads with_columns' output (the revenue column), the others the sales frame
def T.input(+k: U32, s: C.Frame, p: C.Frame) -> C.Frame:
  match k:
    case 3:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case 30:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case 31:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case 51:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case 52:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case 53:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case 54:
      DR.Stg.un(DR.Stg.op(2, s, p))
    case _:
      s

def T.start.i(left: Nat, +k: U32, +acc: String, p: C.Frame, a: C.Frame) -> IO(Unit):
  T.go(1n+left, k, acc, (0n, p, a))

def T.start.q(left: Nat, +k: U32, +acc: String, pp: C.Frame & C.Frame, s: C.Frame) -> IO(Unit):
  (p1, p2) = pp
  T.start.i(left, k, acc, p2, T.input(k, s, p1))

def T.start.w(left: Nat, +k: U32, +t0: Nat, +t1: Nat, ins: List<&1, DR.In>) -> IO(Unit):
  match ins:
    case Nil{}:
      IO.print("error: no input")
    case DR.In{s, p, ks, kp} <> t:
      T.start.q(left, k, "{\"k\":" ++ U32.show(k) ++ ",\"parse_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"ms\":[", DF.clone(p), s)

def T.start.r(left: Nat, +k: U32, +t0: Nat, +t1: Nat, r: E.ResT(List<&1, DR.In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      T.start.w(left, k, t0, t1, ins)

def T.start(left: Nat, +k: U32, +path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    r : E.ResT(List<&1, DR.In>) <- DR.rd.many(1n, path, ppath, Done{Nil{}})
    +t1 : Nat <- IO.now()
    T.start.r(left, k, t0, t1, r)

def T.go.args(+xs: List<&2, String>) -> IO(Unit):
  T.start(DR.nat.of(Nat.read(DR.nth(3n, xs, "10")), 10n), U32.from_nat(DR.nat.of(Nat.read(DR.nth(2n, xs, "3")), 3n)), DR.nth(0n, xs, "bench/data/sales_1000000.csv"), DR.nth(1n, xs, "bench/data/products.csv"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    T.go.args(List.tail(&2, String, DR.promote(args)))
