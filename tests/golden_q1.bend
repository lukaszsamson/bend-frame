# M5 golden q1: bench/queries.py q1 (filter + select) over bench/fixtures/tiny.csv, collected and
# printed with Csv.render(.., Some{4}); the `#|` lines are bench/golden/q1.csv byte for byte.
# Run from the repo root (make test does): the paths are relative.
import Base
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csv.bend as R
import ./../src/plan.bend as P
import ./../src/exec.bend as Q
import ./../bench/queries.bend as QS

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def rend(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(R.Csv.render(f, Some{4}))

def go(s: E.Res(P.Plan), p: E.Res(P.Plan)) -> IO(Unit):
  match s p:
    case Done{+a} Done{+b}:
      do IO<Unit>:
        r : E.ResT(C.Frame) <- Q.Lazy.collect(QS.Q.q1(a, b), P.Env.empty())
        IO.print(rend(r))
    case Fail{e} _:
      IO.print("scan error: " ++ E.Err.show(e))
    case _ Fail{e}:
      IO.print("scan error: " ++ E.Err.show(e))

def main() -> IO(Unit):
  do IO<Unit>:
    s : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/tiny.csv", R.Csv.default())
    p : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/products.csv", R.Csv.default())
    go(s, p)

#|id,region,price
#|1,inland,333.3700
#|10,coastal,197.4300
#|11,island,407.8700
#|18,coastal,190.9300
