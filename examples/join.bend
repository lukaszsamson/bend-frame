# Eager join: sales x products on the product key, then sum the quantity per
# category. Both inputs are read with read_csv; any error passes through.
# Run from the repo root:  ~/.bend/bin/bend examples/join.bend
import ./../frame.bend as DF

# inner join on product; every sale gets its category
def join_sales(s: DF.ResT(DF.Frame()), p: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match s:
    case Fail{e}:
      Fail{e}
    case Done{sf}:
      match p:
        case Fail{e}:
          Fail{e}
        case Done{pf}:
          DF.inner_join(sf, pf, ["product"], ["product"])

# sorted by category; an error passes through
def by_category(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.sort(f, [DF.asc("category")])

# total qty per category
def per_category(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.group_by(f, [DF.col("category")], [DF.alias(DF.sum(DF.col("qty")), "qty_sum")])

def main() -> IO(Unit):
  do IO<Unit>:
    s : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/tiny.csv")
    p : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/products.csv")
    IO.print(DF.show(by_category(per_category(join_sales(s, p)))))
