# Lazy API: scan_csv -> filter -> group_by -> sort. Prints the schema (no data
# read), the plan before and after optimize_full, and the rows. Then a plan with a
# type error: collect_schema and collect both refuse it before any row is read.
# Run from the repo root:  ~/.bend/bin/bend examples/lazy.bend
import ./../frame.bend as DF

# ok sales only; per region: total qty, mean price, row count; sorted by region
def report_plan(p: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_filter(p, DF.col("ok")),
      [DF.col("region")],
      [DF.alias(DF.sum(DF.col("qty")), "qty_sum"),
       DF.alias(DF.mean(DF.col("price")), "price_mean"),
       DF.alias(DF.len(), "count")]),
    [DF.asc("region")])

# a filter needs a bool predicate: qty is u32, so the schema check refuses it
def bad_plan(p: DF.Plan()) -> DF.Plan():
  DF.lazy_filter(p, DF.col("qty"))

def run(+p: DF.Plan()) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- schema of the plan (no data read)")
    IO.print(DF.schema_show(DF.collect_schema(p)))
    IO.print("-- plan")
    IO.print(DF.explain(p))
    IO.print("-- optimized plan (optimize_full)")
    IO.print(DF.explain(DF.optimize_full(p)))
    r : DF.ResT(DF.Frame()) <- DF.collect(p, DF.empty_env())
    IO.print("-- result")
    IO.print(DF.show(r))

def strict(+p: DF.Plan()) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- strict: a filter on a u32 column")
    +bad : DF.Plan() = bad_plan(p)
    IO.print("collect_schema: " ++ DF.schema_show(DF.collect_schema(bad)))
    r : DF.ResT(DF.Frame()) <- DF.collect(bad, DF.empty_env())
    IO.print("collect: " ++ DF.show(r))

def go(s: DF.Res(DF.Plan())) -> IO(Unit):
  match s:
    case Fail{e}:
      IO.print("scan error: " ++ DF.err_show(e))
    case Done{+p}:
      do IO<Unit>:
        run(report_plan(p))
        strict(p)

def main() -> IO(Unit):
  do IO<Unit>:
    s : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/tiny.csv")
    go(s)
