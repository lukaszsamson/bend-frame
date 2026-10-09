# M4: scan_csv + collect end to end (plans/M_01.txt section 5: "CSV read and scan+collect end to end").
#   ~/.bend/bin/bend bench/scanbench.bend -o build/scanbench
#   ./build/scanbench [--threads N] <sales.csv> <q1..q5>
# Times DF.scan_csv of the sales file and of the sibling products.csv (the bounded prefix read
# that freezes each schema) plus DF.collect of the query (the files read with Csv.read_with, i.e.
# with the reader's default Str storage, Csv.enc_default: a binary built with another default
# measures another storage; bench/m4.sh builds both). stdout: {"query","ms","rows"}.
import Base
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/plan.bend as P
import ./../frame.bend as DF
import ./queries.bend as QS

def height.k(r: C.Frame & U32) -> U32:
  (f, h) = r
  h

def height(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      4294967295
    case Done{f}:
      height.k(C.Frame.height(f))

def plan_of(+q: String, +s: P.Plan, +p: P.Plan) -> P.Plan:
  Bool.pick(P.Plan, String.eq(q, "q1"), QS.Q.q1(s, p),
  Bool.pick(P.Plan, String.eq(q, "q2"), QS.Q.q2(s, p),
  Bool.pick(P.Plan, String.eq(q, "q3"), QS.Q.q3(s, p),
  Bool.pick(P.Plan, String.eq(q, "q4"), QS.Q.q4(s, p), QS.Q.q5(s, p)))))

def fin(+q: String, +t0: Nat, r: E.ResT(C.Frame)) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    IO.print("{\"query\":\"" ++ q ++ "\",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"rows\":" ++ U32.show(height(r)) ++ "}")

def scanned(+q: String, +t0: Nat, rs: E.Res(P.Plan), rp: E.Res(P.Plan)) -> IO(Unit):
  match rs rp:
    case Done{+s} Done{+p}:
      do IO<Unit>:
        r : E.ResT(C.Frame) <- DF.collect(plan_of(q, s, p), DF.empty_env())
        fin(q, t0, r)
    case Fail{e} _:
      IO.print("error: " ++ E.Err.show(e))
    case _ Fail{e}:
      IO.print("error: " ++ E.Err.show(e))

def dir.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{'/', t}:
      SCon{'/', t}
    case SCon{h, t}:
      dir.go(t)

def products_path(+path: String) -> String:
  String.reverse(dir.go(String.reverse(path))) ++ "products.csv"

def run(+path: String, +q: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    rs : E.Res(P.Plan) <- DF.scan_csv(path)
    rp : E.Res(P.Plan) <- DF.scan_csv(products_path(path))
    scanned(q, t0, rs, rp)

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def go(+xs: List<&2, String>) -> IO(Unit):
  run(nth(0n, xs, "bench/data/sales_1000.csv"), nth(1n, xs, "q1"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
