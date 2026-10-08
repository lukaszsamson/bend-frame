# M4: scan_csv -> filter -> select -> collect (bench q1 over bench/fixtures/
# tiny.csv), plus a with_columns/head chain, the optimised plan, and early
# errors (a missing file, an ill-typed plan, a schema that lies about the
# file). Run from the repo root.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/expr.bend as X
import ./../src/csv.bend as R
import ./../src/fmt.bend as F
import ./../src/plan.bend as P
import ./../src/exec.bend as Q

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def table(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def col(n: String) -> X.Expr:
  X.Col{n}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def u32(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

# bench q1: filter(ok & qty > 50).select(id, region, price)
def q1(src: P.Plan) -> P.Plan:
  P.Select{[col("id"), col("region"), col("price")], P.Filter{bin(X.And{}, col("ok"), bin(X.Gt{}, col("qty"), u32(50))), src}}

# with_columns(revenue = qty * price).filter(region == "south").head(2)
def q2(src: P.Plan) -> P.Plan:
  P.Head{2, P.Filter{bin(X.Eq{}, col("region"), X.Lit{D.SStr{"south"}}), P.WithColumns{[X.Alias{bin(X.Mul{}, X.Cast{col("qty"), D.TF32{}}, col("price")), "revenue"}], P.Select{[col("id"), col("region"), col("qty"), col("price")], src}}}}

def run(+name: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- " ++ name)
    IO.print(P.Plan.explain(P.Plan.optimize(p)))
    r : E.ResT(C.Frame) <- Q.Lazy.collect(p, P.Env.empty())
    IO.print(table(r))

def go(r: E.Res(P.Plan)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("scan error: " ++ E.Err.show(e))
    case Done{+src}:
      do IO<Unit>:
        run("q1", q1(src))
        run("q2", q2(src))
        r2 : E.ResT(C.Frame) <- Q.Lazy.collect(P.Filter{col("qty"), src}, P.Env.empty())
        IO.print(table(r2))

def main() -> IO(Unit):
  do IO<Unit>:
    r : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/tiny.csv", R.Csv.default())
    go(r)
    m : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/missing.csv", R.Csv.default())
    go(m)
    # a declared schema whose names do not match the file
    lie : P.Plan = P.ScanCsv{"bench/fixtures/products.csv", R.Csv.default(), [S.Field{"product", D.TStr{}}, S.Field{"kind", D.TStr{}}, S.Field{"weight", D.TF32{}}]}
    x : E.ResT(C.Frame) <- Q.Lazy.collect(lie, P.Env.empty())
    IO.print(table(x))

#|-- q1
#|SELECT [col("id"), col("region"), col("price")]
#|  FILTER (col("ok") & (col("qty") > lit(50)))
#|    SELECT [col("id"), col("region"), col("qty"), col("price"), col("ok")]
#|      SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|shape: (4, 3)
#|+-----+---------+--------+
#|| id  | region  | price  |
#|| --- | ---     | ---    |
#|| u32 | str     | f32    |
#|+=====+=========+========+
#|| 1   | inland  | 333.37 |
#|| 10  | coastal | 197.43 |
#|| 11  | island  | 407.87 |
#|| 18  | coastal | 190.93 |
#|+-----+---------+--------+
#|-- q2
#|WITH_COLUMNS [(col("qty").cast(f32) * col("price")).alias("revenue")]
#|  SELECT [col("id"), col("region"), col("qty"), col("price")]
#|    HEAD 2
#|      FILTER (col("region") == lit("south"))
#|        SELECT [col("id"), col("region"), col("qty"), col("price")]
#|          SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|shape: (2, 5)
#|+-----+--------+-----+--------+----------+
#|| id  | region | qty | price  | revenue  |
#|| --- | ---    | --- | ---    | ---      |
#|| u32 | str    | u32 | f32    | f32      |
#|+=====+========+=====+========+==========+
#|| 6   | south  | 77  | 392.03 | 30186.31 |
#|| 9   | south  | 16  | 247.53 | 3960.48  |
#|+-----+--------+-----+--------+----------+
#|error: TypeMismatch in filter: expected bool, got u32
#|scan error: IoError 2: No such file or directory
#|error: InvalidOperation: scan_csv bench/fixtures/products.csv: data schema [product:str, category:str, weight:f32] differs from the plan's [product:str, kind:str, weight:f32]
