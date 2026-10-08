# M5 golden q3: bench/queries.py q3 (group_by + agg + sort) over bench/fixtures/tiny.csv, collected and
# printed with Csv.render(.., Some{4}); the `#|` lines are bench/golden/q3.csv byte for byte.
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
        r : E.ResT(C.Frame) <- Q.Lazy.collect(QS.Q.q3(a, b), P.Env.empty())
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

#|region,revenue_sum,price_mean,count,qty_max
#|central,10821.8604,105.9300,2,91
#|coastal,27665.5547,155.2925,4,88
#|inland,96373.4141,314.0467,6,97
#|island,17405.3223,211.1400,2,87
#|north,10436.5801,421.6800,1,33
#|south,32920.0742,269.1667,3,77
#|west,15958.3789,147.1950,2,62
