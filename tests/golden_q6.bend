# M5 golden q6: bench/queries.py q6 (describe) over bench/fixtures/tiny.csv, collected and
# printed with Csv.render(.., Some{4}); the `#|` lines are bench/golden/q6.csv byte for byte.
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

def go.q6(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      QS.Q.q6(f)

def go(s: E.Res(P.Plan)) -> IO(Unit):
  match s:
    case Done{a}:
      do IO<Unit>:
        f : E.ResT(C.Frame) <- Q.Lazy.collect(a, P.Env.empty())
        IO.print(rend(go.q6(f)))
    case Fail{e}:
      IO.print("scan error: " ++ E.Err.show(e))

def main() -> IO(Unit):
  do IO<Unit>:
    s : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/tiny.csv", R.Csv.default())
    go(s)

#|statistic,id,qty,price,discount
#|count,20.0000,20.0000,20.0000,15.0000
#|null_count,0.0000,0.0000,0.0000,5.0000
#|mean,9.5000,51.6500,233.1580,0.1773
#|std,5.9161,28.5736,146.2012,0.0819
#|min,0.0000,11.0000,14.4100,0.0600
#|25%,5.0000,33.0000,146.0700,0.1300
#|50%,10.0000,55.0000,233.6300,0.1700
#|75%,14.0000,77.0000,392.0300,0.2500
#|max,19.0000,97.0000,446.7000,0.2800
