# M5 golden q2: bench/queries.py q2 (with_columns) over bench/fixtures/tiny.csv, collected and
# printed with Csv.render(.., Some{4}); the `#|` lines are bench/golden/q2.csv byte for byte.
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
        r : E.ResT(C.Frame) <- Q.Lazy.collect(QS.Q.q2(a, b), P.Env.empty())
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

#|id,region,product,qty,price,discount,ok,revenue
#|0,inland,prod_60,49,42.8400,0.1300,false,1826.2692
#|1,inland,prod_61,78,333.3700,,true,26002.8594
#|2,inland,prod_40,97,446.7000,0.1700,false,35963.8164
#|3,inland,prod_17,47,409.6800,,true,19254.9590
#|4,west,prod_08,57,60.7600,0.2400,false,2632.1230
#|5,inland,prod_47,33,416.9400,0.2400,false,10456.8555
#|6,south,prod_57,77,392.0300,0.0700,false,28073.2695
#|7,west,prod_34,62,233.6300,0.0800,false,13326.2559
#|8,central,prod_33,17,65.7900,,false,1118.4301
#|9,south,prod_58,16,247.5300,0.2100,true,3128.7793
#|10,coastal,prod_24,55,197.4300,0.1700,true,9012.6787
#|11,island,prod_04,55,407.8700,0.2800,true,16151.6523
#|12,inland,prod_52,13,234.7500,0.0600,true,2868.6450
#|13,coastal,prod_28,13,187.3400,,true,2435.4199
#|14,coastal,prod_20,54,45.4700,0.2800,false,1767.8738
#|15,central,prod_20,91,146.0700,0.2700,false,9703.4307
#|16,island,prod_31,87,14.4100,,false,1253.6700
#|17,north,prod_58,33,421.6800,0.2500,true,10436.5801
#|18,coastal,prod_33,88,190.9300,0.1400,true,14449.5820
#|19,south,prod_23,11,167.9400,0.0700,true,1718.0262
