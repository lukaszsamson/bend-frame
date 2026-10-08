# Eager API in one file: read a CSV, add a column, filter, show the table.
# Run from the repo root:  ~/.bend/bin/bend examples/quickstart.bend
import ./../frame.bend as DF

# revenue = qty * price * (1 - discount), a missing discount counts as 0
# (the same formula as bench/queries.py q2)
def revenue() -> DF.Expr():
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")),
         DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0))))

# with_columns: a Done frame gets the new column, an error passes through
def add_revenue(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.with_columns(f, [DF.alias(revenue(), "revenue")])

# ok sales of more than 50 units
def big_ok(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.filter(f, DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))

def main() -> IO(Unit):
  do IO<Unit>:
    r : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/tiny.csv")
    IO.print(DF.show(big_ok(add_revenue(r))))
