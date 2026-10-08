# The public facade alone (frame.bend as DF): eager verbs, expressions,
# aggregations, joins, the lazy plan and its schema and explain, and errors
# as values. Run from the repo root (scripts/test.sh does).
import ./../frame.bend as DF

# one line per result: the table, or the error text
def tbl(r: DF.ResT(DF.Frame())) -> String:
  DF.show(r)

def tiny() -> IO(DF.ResT(DF.Frame())):
  DF.read_csv("bench/fixtures/tiny.csv")

# qty * price * (1 - discount), a missing discount counts as 0
def revenue() -> DF.Expr():
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")),
         DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0))))

def with_rev(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.with_columns(f, [DF.alias(revenue(), "revenue")])

def by_region(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.group_by(f, [DF.col("region")],
        [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"),
         DF.alias(DF.count(DF.col("qty")), "n"),
         DF.alias(DF.max(DF.col("qty")), "qty_max")])

def sorted_desc(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.sort(f, [DF.desc("qty"), DF.asc("id")])

def first_two(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.head(f, 2)

def ok_rows(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.filter(f, DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))

def bad_filter(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.filter(f, DF.col("qty"))

def unknown_col(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.select(f, [DF.col("nope")])

def with_neg(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.with_columns(f, [DF.alias(DF.lit_i32_neg(3), "m3"), DF.alias(DF.lit_str("south"), "s"), DF.alias(DF.not(DF.lit_bool(False{})), "t")])

def sel(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.select(f, [DF.col("id"), DF.col("region"), DF.alias(DF.is_null(DF.col("discount")), "no_disc")])

def join_products(s: DF.ResT(DF.Frame()), p: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match s:
    case Fail{e}:
      Fail{e}
    case Done{sf}:
      match p:
        case Fail{e}:
          Fail{e}
        case Done{pf}:
          DF.inner_join(sf, pf, ["product"], ["product"])

def products() -> IO(DF.ResT(DF.Frame())):
  DF.read_csv("bench/fixtures/products.csv")

# the lazy side: a plan over scan_csv, collected and explained
def plan_ok(p: DF.Plan()) -> DF.Plan():
  DF.lazy_group_by(DF.lazy_filter(p, DF.col("ok")), [DF.col("region")], [DF.alias(DF.len(), "n")])

def scan_side(s: DF.Res(DF.Plan())) -> IO(Unit):
  match s:
    case Fail{e}:
      IO.print("scan error: " ++ DF.err_show(e))
    case Done{+p}:
      do IO<Unit>:
        IO.print(DF.schema_show(DF.collect_schema(p)))
        IO.print(DF.explain(DF.optimize(plan_ok(p))))
        r : DF.ResT(DF.Frame()) <- DF.collect(plan_ok(p), DF.empty_env())
        IO.print(DF.show(r))

def main() -> IO(Unit):
  do IO<Unit>:
    t : DF.ResT(DF.Frame()) <- tiny()
    IO.print(DF.show(ok_rows(t)))
    t2 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(DF.show(first_two(sorted_desc(t2))))
    t3 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(DF.show(by_region(with_rev(t3))))
    t4 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(DF.show(with_neg(sel(t4))))
    t5 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(DF.show(bad_filter(t5)))
    t6 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(DF.show(unknown_col(t6)))
    s : DF.ResT(DF.Frame()) <- tiny()
    pr : DF.ResT(DF.Frame()) <- products()
    IO.print(DF.show(first_two(join_products(s, pr))))
    sc : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/tiny.csv")
    scan_side(sc)
    ms : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/missing.csv")
    scan_side(ms)
    w1 : DF.ResT(DF.Frame()) <- tiny()
    wr : DF.ResT(DF.Frame()) <- DF.write_csv(w1, "/tmp/bend_frame_facade.csv")
    IO.print(DF.show(first_two(wr)))
    back : DF.ResT(DF.Frame()) <- DF.read_csv("/tmp/bend_frame_facade.csv")
    IO.print(DF.show(first_two(back)))
    w2 : DF.ResT(DF.Frame()) <- tiny()
    nowhere : DF.ResT(DF.Frame()) <- DF.write_csv(w2, "/no/such/dir/x.csv")
    IO.print(DF.show(nowhere))
    IO.print(DF.show(DF.from_columns([])))

#|shape: (4, 7)
#|+-----+---------+---------+-----+--------+----------+------+
#|| id  | region  | product | qty | price  | discount | ok   |
#|| --- | ---     | ---     | --- | ---    | ---      | ---  |
#|| u32 | str     | str     | u32 | f32    | f32      | bool |
#|+=====+=========+=========+=====+========+==========+======+
#|| 1   | inland  | prod_61 | 78  | 333.37 |          | true |
#|| 10  | coastal | prod_24 | 55  | 197.43 | 0.17     | true |
#|| 11  | island  | prod_04 | 55  | 407.87 | 0.28     | true |
#|| 18  | coastal | prod_33 | 88  | 190.93 | 0.14     | true |
#|+-----+---------+---------+-----+--------+----------+------+
#|shape: (2, 7)
#|+-----+---------+---------+-----+--------+----------+-------+
#|| id  | region  | product | qty | price  | discount | ok    |
#|| --- | ---     | ---     | --- | ---    | ---      | ---   |
#|| u32 | str     | str     | u32 | f32    | f32      | bool  |
#|+=====+=========+=========+=====+========+==========+=======+
#|| 2   | inland  | prod_40 | 97  | 446.7  | 0.17     | false |
#|| 15  | central | prod_20 | 91  | 146.07 | 0.27     | false |
#|+-----+---------+---------+-----+--------+----------+-------+
#|shape: (7, 4)
#|+---------+-------------+-----+---------+
#|| region  | revenue_sum | n   | qty_max |
#|| ---     | ---         | --- | ---     |
#|| str     | f32         | u32 | u32     |
#|+=========+=============+=====+=========+
#|| inland  | 96373.41    | 6   | 97      |
#|| west    | 15958.379   | 2   | 62      |
#|| south   | 32920.074   | 3   | 77      |
#|| central | 10821.86    | 2   | 91      |
#|| coastal | 27665.555   | 4   | 88      |
#|| island  | 17405.322   | 2   | 87      |
#|| north   | 10436.58    | 1   | 33      |
#|+---------+-------------+-----+---------+
#|shape: (20, 6)
#|+-----+---------+---------+-----+-------+------+
#|| id  | region  | no_disc | m3  | s     | t    |
#|| --- | ---     | ---     | --- | ---   | ---  |
#|| u32 | str     | bool    | i32 | str   | bool |
#|+=====+=========+=========+=====+=======+======+
#|| 0   | inland  | false   | -3  | south | true |
#|| 1   | inland  | true    | -3  | south | true |
#|| 2   | inland  | false   | -3  | south | true |
#|| 3   | inland  | true    | -3  | south | true |
#|| 4   | west    | false   | -3  | south | true |
#|| ... | ...     | ...     | ... | ...   | ...  |
#|| 15  | central | false   | -3  | south | true |
#|| 16  | island  | true    | -3  | south | true |
#|| 17  | north   | false   | -3  | south | true |
#|| 18  | coastal | false   | -3  | south | true |
#|| 19  | south   | false   | -3  | south | true |
#|+-----+---------+---------+-----+-------+------+
#|error: TypeMismatch in filter: expected bool, got u32
#|error: ColumnNotFound: nope
#|shape: (2, 9)
#|+-----+--------+---------+-----+--------+----------+-------+----------+--------+
#|| id  | region | product | qty | price  | discount | ok    | category | weight |
#|| --- | ---    | ---     | --- | ---    | ---      | ---   | ---      | ---    |
#|| u32 | str    | str     | u32 | f32    | f32      | bool  | str      | f32    |
#|+=====+========+=========+=====+========+==========+=======+==========+========+
#|| 0   | inland | prod_60 | 49  | 42.84  | 0.13     | false | tools    | 46.13  |
#|| 1   | inland | prod_61 | 78  | 333.37 |          | true  | toys     | 37.26  |
#|+-----+--------+---------+-----+--------+----------+-------+----------+--------+
#|id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool
#|GROUP_BY [col("region")] AGG [lit(1).len().alias("n")] MAINTAIN_ORDER
#|  FILTER col("ok")
#|    SELECT [col("region"), col("ok")]
#|      SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|shape: (5, 2)
#|+---------+-----+
#|| region  | n   |
#|| ---     | --- |
#|| str     | u32 |
#|+=========+=====+
#|| inland  | 3   |
#|| south   | 2   |
#|| coastal | 3   |
#|| island  | 1   |
#|| north   | 1   |
#|+---------+-----+
#|scan error: IoError 2: No such file or directory
#|shape: (2, 7)
#|+-----+--------+---------+-----+--------+----------+-------+
#|| id  | region | product | qty | price  | discount | ok    |
#|| --- | ---    | ---     | --- | ---    | ---      | ---   |
#|| u32 | str    | str     | u32 | f32    | f32      | bool  |
#|+=====+========+=========+=====+========+==========+=======+
#|| 0   | inland | prod_60 | 49  | 42.84  | 0.13     | false |
#|| 1   | inland | prod_61 | 78  | 333.37 |          | true  |
#|+-----+--------+---------+-----+--------+----------+-------+
#|shape: (2, 7)
#|+-----+--------+---------+-----+--------+----------+-------+
#|| id  | region | product | qty | price  | discount | ok    |
#|| --- | ---    | ---     | --- | ---    | ---      | ---   |
#|| u32 | str    | str     | u32 | f32    | f32      | bool  |
#|+=====+========+=========+=====+========+==========+=======+
#|| 0   | inland | prod_60 | 49  | 42.84  | 0.13     | false |
#|| 1   | inland | prod_61 | 78  | 333.37 |          | true  |
#|+-----+--------+---------+-----+--------+----------+-------+
#|error: IoError 2: No such file or directory
#|shape: (0, 0)
