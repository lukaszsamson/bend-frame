# Sales summary: revenue per region with the M3 reducers (sum, median, std, n_unique), a ratio of
# two aggregations (two named aggs, then with_columns), a when() tier, sorted by revenue.
# The same pipeline runs lazily (scan_csv -> collect) and eagerly (read_csv -> DF.then chain);
# both print the same table.
# Run from the repo root:  ~/.bend/bin/bend examples/sales_summary.bend
import ./../frame.bend as DF

# revenue = qty * price * (1 - discount), a missing discount counts as 0
def revenue() -> DF.Expr():
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")),
         DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0))))

def keys() -> List<&2, DF.Expr()>:
  [DF.col("region")]

def aggs() -> List<&2, DF.Expr()>:
  [DF.alias(DF.sum(DF.col("revenue")), "revenue"),
   DF.alias(DF.sum(DF.col("qty")), "units"),
   DF.alias(DF.median(DF.col("price")), "median_price"),
   DF.alias(DF.std(DF.col("price")), "std_price"),
   DF.alias(DF.n_unique(DF.col("product")), "products"),
   DF.alias(DF.len(), "orders")]

# revenue per unit (a ratio of two aggregations) and a tier
def derived() -> List<&2, DF.Expr()>:
  [DF.alias(DF.div(DF.col("revenue"), DF.cast_f32(DF.col("units"))), "per_unit"),
   DF.alias(DF.when(DF.gt(DF.col("revenue"), DF.lit_f32(20000.0)), DF.lit_str("big"), DF.lit_str("small")), "tier")]

def order() -> List<&2, DF.SortKey()>:
  [DF.desc("revenue")]

def plan(p: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(DF.lazy_with_columns(DF.lazy_group_by(DF.lazy_with_columns(p, [DF.alias(revenue(), "revenue")]), keys(), aggs()), derived()), order())

def eager(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(DF.then(DF.then(DF.then(r,
    f => DF.with_columns(f, [DF.alias(revenue(), "revenue")])),
    f => DF.group_by(f, keys(), aggs())),
    f => DF.with_columns(f, derived())),
    f => DF.sort(f, order()))

def lazy(s: DF.Res(DF.Plan())) -> IO(Unit):
  match s:
    case Fail{e}:
      IO.print("scan error: " ++ DF.err_show(e))
    case Done{p}:
      do IO<Unit>:
        +q : DF.Plan() = plan(p)
        IO.print("-- plan")
        IO.print(DF.explain(q))
        IO.print("-- schema: " ++ DF.schema_show(DF.collect_schema(q)))
        r : DF.ResT(DF.Frame()) <- DF.collect(q, DF.empty_env())
        IO.print("-- lazy result")
        IO.print(DF.show(r))

def main() -> IO(Unit):
  do IO<Unit>:
    s : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/tiny.csv")
    lazy(s)
    r : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/tiny.csv")
    IO.print("-- eager result")
    IO.print(DF.show(eager(r)))
