# M5 golden q4: bench/queries.py q4 (sort + head) over bench/fixtures/tiny.csv, collected and
# printed with Csv.render(.., Some{4}); the `#|` lines are bench/golden/q4.csv byte for byte.
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
        r : E.ResT(C.Frame) <- Q.Lazy.collect(QS.Q.q4(a, b), P.Env.empty())
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

#|id,region,product,qty,price,discount,ok
#|15,central,prod_20,91,146.0700,0.2700,false
#|8,central,prod_33,17,65.7900,,false
#|10,coastal,prod_24,55,197.4300,0.1700,true
#|18,coastal,prod_33,88,190.9300,0.1400,true
#|13,coastal,prod_28,13,187.3400,,true
#|14,coastal,prod_20,54,45.4700,0.2800,false
#|2,inland,prod_40,97,446.7000,0.1700,false
#|5,inland,prod_47,33,416.9400,0.2400,false
#|3,inland,prod_17,47,409.6800,,true
#|1,inland,prod_61,78,333.3700,,true
