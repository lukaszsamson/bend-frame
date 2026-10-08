# M5 golden q5: bench/queries.py q5 (inner join + group_by + sort) over bench/fixtures/tiny.csv + bench/fixtures/products.csv, collected and
# printed with Csv.render(.., Some{4}); the `#|` lines are bench/golden/q5.csv byte for byte.
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
        r : E.ResT(C.Frame) <- Q.Lazy.collect(QS.Q.q5(a, b), P.Env.empty())
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

#|category,qty_sum
#|books,182
#|food,202
#|garden,289
#|sports,91
#|tools,104
#|toys,165
