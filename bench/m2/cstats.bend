# bench/m2/cstats.bend -- the chunked executor's own conversion counters (CStats, src/cexec.bend) for ONE m2 workload
# collected over a FLAT env frame, exactly as the driver does under BF_ENGINE=chunked: DF.collect_with(
# engine_chunked(), ..) is Exec.prep + CX.run at grain 2^14 with the CStats dropped (CX.snd); this probe keeps them.
# The facade does not expose CStats, so `make m2-g6` runs this next to the instrumented driver to fill the
# "chunk conversions" columns of its table (conversion counts and LOGICAL bytes = 4 x rows x columns converted;
# the bytes the runtime really allocated for them are in the instrumented driver's counters).
#   bend bench/m2/cstats.bend -o build/m2/cstats; build/m2/cstats [--threads N] <op> <file> <aux|-> [param]
# stdout: {"op":..,"chk":<the driver's content hash of the result>,"stats":"conv_in n bytes_in b conv_out n bytes_out b walks n flat_ops n"}
# op: q1 q2 q3 q4 q5 nunique group unique join filter (the driver's plans: bench/m2/driver.bend Pl.of); q6 (eager describe)
# and parse do not collect, so there is nothing to count.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/csv.bend as R
import ./../../src/exec.bend as Q
import ./../../src/chunks.bend as CH
import ./../../src/cexec.bend as QC
import ./driver.bend as DR

def X.chk(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{f}:
      DR.Hc.frame(f)

def X.print(+op: String, r: QC.CStats & E.ResT(C.Frame)) -> IO(Unit):
  (st, x) = r
  IO.print("{\"op\":\"" ++ op ++ "\",\"chk\":" ++ U32.show(X.chk(x)) ++ ",\"stats\":\"" ++ QC.CStats.show(st) ++ "\"}")

def X.go(+g: Nat, +op: String, +p: P.Plan, r: E.ResT(P.Env)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{env}:
      X.print(op, QC.CX.run(g, p, env, Nil{}))

# Exec.run_with.c: the checks and scan reads, then the chunked runner
def X.prep(+g: Nat, +op: String, +p: P.Plan, env: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(P.Env) <- Q.Exec.prep(R.CsvV01{}, p, env)
    X.go(g, op, p, r)

# the driver's job: plan over the env {sales, products}, released (Lazy.collect_with releases before running)
def X.b(+g: Nat, +op: String, +par: U32, s: P.Plan, r: P.Env & P.Plan) -> IO(Unit):
  (env, +p) = r
  X.prep(g, op, P.Optimize.release(DR.Pl.of(op, par, s, p)), env)

def X.a(+g: Nat, +op: String, +par: U32, r: P.Env & P.Plan, p: C.Frame) -> IO(Unit):
  (env, +s) = r
  X.b(g, op, par, s, DF.add_source(env, "products", p))

def X.k(+g: Nat, +op: String, +par: U32, i: DR.In) -> IO(Unit):
  match i:
    case DR.In{s, p, ks, kp}:
      X.a(g, op, par, DF.source("sales", s), p)

def X.w(+op: String, +par: U32, ins: List<&1, DR.In>) -> IO(Unit):
  match ins:
    case Nil{}:
      IO.print("error: no input")
    case i <> t:
      X.k(CH.Ch.grain(), op, par, i)

def X.r(+op: String, +par: U32, r: E.ResT(List<&1, DR.In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      X.w(op, par, ins)

def X.start(+op: String, +par: U32, +path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(List<&1, DR.In>) <- DR.rd.many(1n, path, ppath, Done{Nil{}})
    X.r(op, par, r)

def X.args(+xs: List<&2, String>) -> IO(Unit):
  X.start(DR.nth(0n, xs, "q1"), U32.from_nat(DR.nat.of(Nat.read(DR.nth(3n, xs, "0")), 0n)), DR.nth(1n, xs, "bench/data/sales_1000000.csv"), DR.nth(2n, xs, "bench/data/products.csv"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.args(List.tail(&2, String, DR.promote(args)))
