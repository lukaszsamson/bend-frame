# Prints DF.explain of every bench/tpch query over scan_csv plans of the tables in
# bench/data/tpch/sf0.01, as written and after DF.optimize_full. Run from the repo root:
#   ~/.bend/bin/bend bench/tpch/explain.bend
import ./../../frame.bend as DF
import ./queries.bend as Q

def plan(r: DF.Res(DF.Plan())) -> DF.Plan():
  match r:
    case Done{p}:
      p
    case Fail{e}:
      DF.lazy_head(DF.scan_csv_schema("", DF.csv_opts(',', True{}, 1), []), 0)

def show(+l: DF.Plan(), +o: DF.Plan(), +c: DF.Plan(), +s: DF.Plan(), +n: DF.Plan(), +r: DF.Plan(), qs: List<&2, String>) -> IO(Unit):
  match qs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +q <> t:
      do IO<Unit>:
        IO.print("== " ++ q)
        IO.print(DF.explain(Q.T.plan(q, l, o, c, s, n, r)))
        IO.print("-- optimize_full")
        IO.print(DF.explain(DF.optimize_full(Q.T.plan(q, l, o, c, s, n, r))))
        show(l, o, c, s, n, r, t)

def main() -> IO(Unit):
  do IO<Unit>:
    l : DF.Res(DF.Plan()) <- DF.scan_csv("bench/data/tpch/sf0.01/lineitem.csv")
    o : DF.Res(DF.Plan()) <- DF.scan_csv("bench/data/tpch/sf0.01/orders.csv")
    c : DF.Res(DF.Plan()) <- DF.scan_csv("bench/data/tpch/sf0.01/customer.csv")
    s : DF.Res(DF.Plan()) <- DF.scan_csv("bench/data/tpch/sf0.01/supplier.csv")
    n : DF.Res(DF.Plan()) <- DF.scan_csv("bench/data/tpch/sf0.01/nation.csv")
    r : DF.Res(DF.Plan()) <- DF.scan_csv("bench/data/tpch/sf0.01/region.csv")
    show(plan(l), plan(o), plan(c), plan(s), plan(n), plan(r), Q.T.names())
