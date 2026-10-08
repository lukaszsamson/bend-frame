# The M3 examples run end to end (plans/M_01.txt section 7 M3 exit): examples/sales_summary.bend
# (lazy and eager agree; the table was checked against Polars 2.0.0 on bench/fixtures/tiny.csv)
# and examples/dirty_csv.bend (try_cast, when, is_in, string predicates, a median fill).
import Base
import ./../examples/sales_summary.bend as S1
import ./../examples/dirty_csv.bend as S2

def main() -> IO(Unit):
  do IO<Unit>:
    S1.main()
    S2.main()
#|-- plan
#|SORT BY [col("revenue") desc]
#|  WITH_COLUMNS [(col("revenue") / col("units").cast(f32)).alias("per_unit"), when((col("revenue") > lit(20000))).then(lit("big")).otherwise(lit("small")).alias("tier")]
#|    GROUP_BY [col("region")] AGG [col("revenue").sum().alias("revenue"), col("qty").sum().alias("units"), col("price").median().alias("median_price"), col("price").std().alias("std_price"), col("product").n_unique().alias("products"), lit(1).len().alias("orders")] MAINTAIN_ORDER
#|      WITH_COLUMNS [((col("qty").cast(f32) * col("price")) * (lit(1) - col("discount").fill_null(lit(0)))).alias("revenue")]
#|        SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|-- schema: region:str, revenue:f32, units:u32, median_price:f32, std_price:f32, products:u32, orders:u32, per_unit:f32, tier:str
#|-- lazy result
#|shape: (7, 9)
#|+---------+-----------+-------+--------------+-----------+----------+--------+-----------+-------+
#|| region  | revenue   | units | median_price | std_price | products | orders | per_unit  | tier  |
#|| ---     | ---       | ---   | ---          | ---       | ---      | ---    | ---       | ---   |
#|| str     | f32       | u32   | f32          | f32       | u32      | u32    | f32       | str   |
#|+=========+===========+=======+==============+===========+==========+========+===========+=======+
#|| inland  | 96373.41  | 317   | 371.525      | 153.32585 | 6        | 6      | 304.01706 | big   |
#|| south   | 32920.074 | 104   | 247.53       | 113.60101 | 3        | 3      | 316.53918 | big   |
#|| coastal | 27665.555 | 210   | 189.135      | 73.33399  | 4        | 4      | 131.74074 | big   |
#|| island  | 17405.322 | 142   | 211.14       | 278.21823 | 2        | 2      | 122.57269 | small |
#|| west    | 15958.379 | 119   | 147.195      | 122.23756 | 2        | 2      | 134.10402 | small |
#|| central | 10821.86  | 108   | 105.93001    | 56.76654  | 2        | 2      | 100.20241 | small |
#|| north   | 10436.58  | 33    | 421.68       |           | 1        | 1      | 316.26    | small |
#|+---------+-----------+-------+--------------+-----------+----------+--------+-----------+-------+
#|-- eager result
#|shape: (7, 9)
#|+---------+-----------+-------+--------------+-----------+----------+--------+-----------+-------+
#|| region  | revenue   | units | median_price | std_price | products | orders | per_unit  | tier  |
#|| ---     | ---       | ---   | ---          | ---       | ---      | ---    | ---       | ---   |
#|| str     | f32       | u32   | f32          | f32       | u32      | u32    | f32       | str   |
#|+=========+===========+=======+==============+===========+==========+========+===========+=======+
#|| inland  | 96373.41  | 317   | 371.525      | 153.32585 | 6        | 6      | 304.01706 | big   |
#|| south   | 32920.074 | 104   | 247.53       | 113.60101 | 3        | 3      | 316.53918 | big   |
#|| coastal | 27665.555 | 210   | 189.135      | 73.33399  | 4        | 4      | 131.74074 | big   |
#|| island  | 17405.322 | 142   | 211.14       | 278.21823 | 2        | 2      | 122.57269 | small |
#|| west    | 15958.379 | 119   | 147.195      | 122.23756 | 2        | 2      | 134.10402 | small |
#|| central | 10821.86  | 108   | 105.93001    | 56.76654  | 2        | 2      | 100.20241 | small |
#|| north   | 10436.58  | 33    | 421.68       |           | 1        | 1      | 316.26    | small |
#|+---------+-----------+-------+--------------+-----------+----------+--------+-----------+-------+
#|-- schema as scanned: id:u32, name:str, qty:str, price:str, status:str, email:str
#|-- cleaned (lazy)
#|shape: (5, 7)
#|+-----+-------+-----+-------+--------+---------+----------+
#|| id  | name  | qty | price | total  | status  | email_ok |
#|| --- | ---   | --- | ---   | ---    | ---     | ---      |
#|| u32 | str   | u32 | f32   | f32    | str     | bool     |
#|+=====+=======+=====+=======+========+=========+==========+
#|| 1   | Alice | 12  | 3.5   | 42     | ok      | true     |
#|| 4   | Dan   | 5   | 3.875 | 19.375 | bad     | false    |
#|| 6   | Frank | 20  | 3.875 | 77.5   | ok      | true     |
#|| 7   | Grace | 3   | 10    | 30     | pending | true     |
#|| 9   | Ivan  | 8   | 3.875 | 31     | ok      |          |
#|+-----+-------+-----+-------+--------+---------+----------+
#|-- rows whose qty did not parse (dropped)
#|shape: (4, 3)
#|+-----+-------+------------+
#|| id  | name  | qty        |
#|| --- | ---   | ---        |
#|| u32 | str   | str        |
#|+=====+=======+============+
#|| 2   | Bob   | 7 units    |
#|| 3   | Carol | n/a        |
#|| 5   | Eve   |            |
#|| 8   | Heidi | 4294967296 |
#|+-----+-------+------------+
#|-- cleaned (eager)
#|shape: (5, 7)
#|+-----+-------+-----+-------+--------+---------+----------+
#|| id  | name  | qty | price | total  | status  | email_ok |
#|| --- | ---   | --- | ---   | ---    | ---     | ---      |
#|| u32 | str   | u32 | f32   | f32    | str     | bool     |
#|+=====+=======+=====+=======+========+=========+==========+
#|| 1   | Alice | 12  | 3.5   | 42     | ok      | true     |
#|| 4   | Dan   | 5   | 3.875 | 19.375 | bad     | false    |
#|| 6   | Frank | 20  | 3.875 | 77.5   | ok      | true     |
#|| 7   | Grace | 3   | 10    | 30     | pending | true     |
#|| 9   | Ivan  | 8   | 3.875 | 31     | ok      |          |
#|+-----+-------+-----+-------+--------+---------+----------+
#|-- a strict cast of qty instead of try_cast
#|error: InvalidOperation: cast str to u32: row 1 holds "7 units"
