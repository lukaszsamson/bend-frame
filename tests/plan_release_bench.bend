# The release optimizer on the benchmark plans (bench/queries.bend q1-q5; q6 is eager). Since
# M5 part 2 the default optimizer merges adjacent Heads only (Opt.hmerge, proven result-preserving
# for every plan: LAWS.bend release_run); the analysis-certified Head sink (R3) stays in
# optimize_full. No benchmark plan has a Head above a Select / WithColumns (q4's Head sits on a
# Sort, a barrier for both passes), so the plans q1-q5 are unchanged by the release optimizer
# AND by the previous head pass (Opt.head, still the optimize_full pass): the fallback costs
# nothing on the benchmark. This test pins that: for each plan the explain text of
# P.Optimize.release(q), of P.Opt.head(q, None{}) and of q itself are one and the same (DF.optimize adds the
# tested projection pushdown on top since D1, DESIGN.md 14 "Pre-release"; tests/plan_* pin its plans).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/schema.bend as S
import ./../src/plan.bend as P
import ./../bench/queries.bend as QS

def sales() -> P.Plan:
  P.Source{"sales", [S.Field{"id", D.TU32{}}, S.Field{"region", D.TStr{}}, S.Field{"product", D.TStr{}}, S.Field{"qty", D.TU32{}}, S.Field{"price", D.TF32{}}, S.Field{"discount", D.TF32{}}, S.Field{"ok", D.TBool{}}]}

def products() -> P.Plan:
  P.Source{"products", [S.Field{"product", D.TStr{}}, S.Field{"category", D.TStr{}}, S.Field{"weight", D.TF32{}}]}

def same(+a: String, +b: String, +c: String) -> String:
  Bool.pick(String, Bool.and(String.eq(a, b), String.eq(a, c)), "same", "DIFFERENT")

def one(+name: String, +q: P.Plan) -> IO(Unit):
  do IO<Unit>:
    +raw : String = DF.explain(q)
    +rel : String = DF.explain(P.Optimize.release(q))
    +sink : String = DF.explain(P.Opt.head(q, None{}))
    IO.print("-- " ++ name ++ ": release vs head pass vs raw: " ++ same(raw, rel, sink) ++ "\n")
    IO.print(rel ++ "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    one("q1", QS.Q.q1(sales(), products()))
    one("q2", QS.Q.q2(sales(), products()))
    one("q3", QS.Q.q3(sales(), products()))
    one("q4", QS.Q.q4(sales(), products()))
    one("q5", QS.Q.q5(sales(), products()))

#|-- q1: release vs head pass vs raw: same
#|
#|SELECT [col("id"), col("region"), col("price")]
#|  FILTER (col("ok") & (col("qty") > lit(50)))
#|    SOURCE sales [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|
#|-- q2: release vs head pass vs raw: same
#|
#|WITH_COLUMNS [((col("qty").cast(f32) * col("price")) * (lit(1) - col("discount").fill_null(lit(0)))).alias("revenue")]
#|  SOURCE sales [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|
#|-- q3: release vs head pass vs raw: same
#|
#|SORT BY [col("region")]
#|  GROUP_BY [col("region")] AGG [col("revenue").sum().alias("revenue_sum"), col("price").mean().alias("price_mean"), lit(1).len().alias("count"), col("qty").max().alias("qty_max")]
#|    WITH_COLUMNS [((col("qty").cast(f32) * col("price")) * (lit(1) - col("discount").fill_null(lit(0)))).alias("revenue")]
#|      SOURCE sales [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|
#|-- q4: release vs head pass vs raw: same
#|
#|HEAD 10
#|  SORT BY [col("region"), col("price") desc, col("id")]
#|    SOURCE sales [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|
#|-- q5: release vs head pass vs raw: same
#|
#|SORT BY [col("category")]
#|  GROUP_BY [col("category")] AGG [col("qty").sum().alias("qty_sum")]
#|    INNER JOIN ON [product = product]
#|      SOURCE sales [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|      SOURCE products [product:str, category:str, weight:f32]
#|
