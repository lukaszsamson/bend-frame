# bench/queries.bend -- the canonical query set (bench/queries.py) as Plans.
# `Q.q1..Q.q5(sales, products) -> Plan` take the scan/source plans (a
# `Lazy.scan_csv` result, or a `Source` over an Env frame); q6 is eager:
# `Q.q6(sales_frame)` selects id/qty/price/discount and describes it.
# Floats are f32. Import as e.g. `import ./../bench/queries.bend as QS` and
# call `QS.Q.q1(..)` (def names keep their dots). Run from the repo root.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/sort.bend as O
import ./../src/join.bend as J
import ./../src/plan.bend as P
import ./../src/fmt.bend as F

def Q.col(n: String) -> X.Expr:
  X.Col{n}

def Q.bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def Q.u32(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def Q.f32(v: F32) -> X.Expr:
  X.Lit{D.SF32{v}}

def Q.agg(op: X.AggOp, e: X.Expr, name: String) -> X.Expr:
  X.Alias{X.Agg{op, e}, name}

# qty.cast(f32) * price * (1 - discount.fill_null(0.0))
def Q.revenue() -> X.Expr:
  Q.bin(X.Mul{}, Q.bin(X.Mul{}, X.Cast{Q.col("qty"), D.TF32{}}, Q.col("price")), Q.bin(X.Sub{}, Q.f32(1.0), X.FillNull{Q.col("discount"), Q.f32(0.0)}))

# filter(ok & qty > 50).select(id, region, price)
def Q.q1(sales: P.Plan, products: P.Plan) -> P.Plan:
  P.Select{[Q.col("id"), Q.col("region"), Q.col("price")], P.Filter{Q.bin(X.And{}, Q.col("ok"), Q.bin(X.Gt{}, Q.col("qty"), Q.u32(50))), sales}}

# with_columns(revenue = ...)
def Q.q2(sales: P.Plan, products: P.Plan) -> P.Plan:
  P.WithColumns{[X.Alias{Q.revenue(), "revenue"}], sales}

# q2 + group_by(region).agg(sum revenue, mean price, len, max qty).sort(region)
def Q.q3(sales: P.Plan, products: P.Plan) -> P.Plan:
  P.Sort{[O.SortKey{"region", False{}, False{}}], P.GroupBy{[Q.col("region")], [Q.agg(X.Sum{}, Q.col("revenue"), "revenue_sum"), Q.agg(X.Mean{}, Q.col("price"), "price_mean"), Q.agg(X.Len{}, Q.u32(1), "count"), Q.agg(X.Max{}, Q.col("qty"), "qty_max")], False{}, Q.q2(sales, products)}}

# sort(region asc, price desc, id asc).head(10)
def Q.q4(sales: P.Plan, products: P.Plan) -> P.Plan:
  P.Head{10, P.Sort{[O.SortKey{"region", False{}, False{}}, O.SortKey{"price", True{}, False{}}, O.SortKey{"id", False{}, False{}}], sales}}

# inner join on product, group_by(category).agg(sum qty).sort(category)
def Q.q5(sales: P.Plan, products: P.Plan) -> P.Plan:
  P.Sort{[O.SortKey{"category", False{}, False{}}], P.GroupBy{[Q.col("category")], [Q.agg(X.Sum{}, Q.col("qty"), "qty_sum")], False{}, P.Join{J.Inner{}, ["product"], ["product"], sales, products}}}

def Q.q6.k(r: C.Frame & E.ResT(C.Frame)) -> E.ResT(C.Frame):
  (f, res) = r
  res

def Q.q6.sel(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Q.q6.k(F.Fmt.describe(f))

# sales.select(id, qty, price, discount).describe()
def Q.q6(f: C.Frame) -> E.ResT(C.Frame):
  Q.q6.sel(C.Frame.select_names(f, ["id", "qty", "price", "discount"]))
