# PDS-H-style queries (the Polars benchmark suite's TPC-H shapes) over the bench/tpch/gen.py tables,
# written with the public facade only. Dates are u32 yyyymmdd; money is f32. Each `T.qK` takes the
# Source plans of lineitem, orders, customer, supplier, nation, region and answers a Plan.
# The Polars twins are in bench/tpch/run_polars.py (same names, same semantics).
import ./../../frame.bend as DF

def T.c(n: String) -> DF.Expr():
  DF.col(n)

def T.u(v: U32) -> DF.Expr():
  DF.lit_u32(v)

def T.f(v: F32) -> DF.Expr():
  DF.lit_f32(v)

# l_extendedprice * (1 - l_discount)
def T.disc_price() -> DF.Expr():
  DF.mul(T.c("l_extendedprice"), DF.sub(T.f(1.0), T.c("l_discount")))

def T.rev() -> DF.Expr():
  DF.alias(T.disc_price(), "revenue")

# lo <= c < hi
def T.range(+n: String, lo: U32, hi: U32) -> DF.Expr():
  DF.and(DF.ge(T.c(n), T.u(lo)), DF.lt(T.c(n), T.u(hi)))

# Q1: pricing summary report
def T.q1(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_with_columns(
        DF.lazy_filter(l, DF.le(T.c("l_shipdate"), T.u(19980902))),
        [DF.alias(T.disc_price(), "disc_price")]),
      [T.c("l_returnflag"), T.c("l_linestatus")],
      [DF.alias(DF.sum(T.c("l_quantity")), "sum_qty"),
       DF.alias(DF.sum(T.c("l_extendedprice")), "sum_base_price"),
       DF.alias(DF.sum(T.c("disc_price")), "sum_disc_price"),
       DF.alias(DF.sum(DF.mul(T.c("disc_price"), DF.add(T.f(1.0), T.c("l_tax")))), "sum_charge"),
       DF.alias(DF.mean(T.c("l_quantity")), "avg_qty"),
       DF.alias(DF.mean(T.c("l_extendedprice")), "avg_price"),
       DF.alias(DF.mean(T.c("l_discount")), "avg_disc"),
       DF.alias(DF.len(), "count_order")]),
    [DF.asc("l_returnflag"), DF.asc("l_linestatus")])

# Q3: shipping priority
def T.q3(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_head(
    DF.lazy_sort(
      DF.lazy_group_by(
        DF.lazy_inner_join(
          DF.lazy_inner_join(
            DF.lazy_filter(c, DF.eq(T.c("c_mktsegment"), DF.lit_str("BUILDING"))),
            DF.lazy_filter(o, DF.lt(T.c("o_orderdate"), T.u(19950315))),
            ["c_custkey"], ["o_custkey"]),
          DF.lazy_filter(l, DF.gt(T.c("l_shipdate"), T.u(19950315))),
          ["o_orderkey"], ["l_orderkey"]),
        [T.c("o_orderkey"), T.c("o_orderdate"), T.c("o_shippriority")],
        [DF.alias(DF.sum(T.disc_price()), "revenue")]),
      [DF.desc("revenue"), DF.asc("o_orderdate")]),
    10)

# Q4: order priority checking (a semi join)
def T.q4(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_semi_join(
        DF.lazy_filter(o, T.range("o_orderdate", 19930701, 19931001)),
        DF.lazy_filter(l, DF.lt(T.c("l_commitdate"), T.c("l_receiptdate"))),
        ["o_orderkey"], ["l_orderkey"]),
      [T.c("o_orderpriority")],
      [DF.alias(DF.len(), "order_count")]),
    [DF.asc("o_orderpriority")])

# Q5: local supplier volume (five joins, the last on two keys)
def T.q5(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_inner_join(
        DF.lazy_inner_join(
          DF.lazy_inner_join(
            DF.lazy_inner_join(
              DF.lazy_inner_join(
                DF.lazy_filter(r, DF.eq(T.c("r_name"), DF.lit_str("ASIA"))),
                n, ["r_regionkey"], ["n_regionkey"]),
              c, ["n_nationkey"], ["c_nationkey"]),
            DF.lazy_filter(o, T.range("o_orderdate", 19940101, 19950101)),
            ["c_custkey"], ["o_custkey"]),
          l, ["o_orderkey"], ["l_orderkey"]),
        s, ["l_suppkey", "n_nationkey"], ["s_suppkey", "s_nationkey"]),
      [T.c("n_name")],
      [DF.alias(DF.sum(T.disc_price()), "revenue")]),
    [DF.desc("revenue")])

# Q6: forecasting revenue change (a filter and one global sum)
def T.q6(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_select(
    DF.lazy_filter(l,
      DF.and(DF.and(T.range("l_shipdate", 19940101, 19950101),
                    DF.is_between(T.c("l_discount"), T.f(0.05), T.f(0.07))),
             DF.lt(T.c("l_quantity"), T.u(24)))),
    [DF.alias(DF.sum(DF.mul(T.c("l_extendedprice"), T.c("l_discount"))), "revenue")])

# Q10: returned item reporting (group by four keys, one of them a distinct string)
def T.q10(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_head(
    DF.lazy_sort(
      DF.lazy_group_by(
        DF.lazy_inner_join(
          DF.lazy_inner_join(
            DF.lazy_inner_join(
              c,
              DF.lazy_filter(o, T.range("o_orderdate", 19931001, 19940101)),
              ["c_custkey"], ["o_custkey"]),
            DF.lazy_filter(l, DF.eq(T.c("l_returnflag"), DF.lit_str("R"))),
            ["o_orderkey"], ["l_orderkey"]),
          n, ["c_nationkey"], ["n_nationkey"]),
        [T.c("c_custkey"), T.c("c_name"), T.c("c_acctbal"), T.c("n_name")],
        [DF.alias(DF.sum(T.disc_price()), "revenue")]),
      [DF.desc("revenue"), DF.asc("c_custkey")]),
    20)

# Q12: shipping modes and order priority (is_in, column-to-column compares, when)
def T.q12.urgent() -> DF.Expr():
  DF.is_in(T.c("o_orderpriority"), [DF.s_str("1-URGENT"), DF.s_str("2-HIGH")])

def T.q12(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_inner_join(
        o,
        DF.lazy_filter(l,
          DF.and(DF.and(DF.is_in(T.c("l_shipmode"), [DF.s_str("MAIL"), DF.s_str("SHIP")]),
                        DF.lt(T.c("l_commitdate"), T.c("l_receiptdate"))),
                 DF.and(DF.lt(T.c("l_shipdate"), T.c("l_commitdate")),
                        T.range("l_receiptdate", 19940101, 19950101)))),
        ["o_orderkey"], ["l_orderkey"]),
      [T.c("l_shipmode")],
      [DF.alias(DF.sum(DF.when(T.q12.urgent(), T.u(1), T.u(0))), "high_line_count"),
       DF.alias(DF.sum(DF.when(T.q12.urgent(), T.u(0), T.u(1))), "low_line_count")]),
    [DF.asc("l_shipmode")])

# Q13: customer distribution (a left join, count of a nullable key, two group_bys)
def T.q13(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_group_by(
        DF.lazy_left_join(c, o, ["c_custkey"], ["o_custkey"]),
        [T.c("c_custkey")],
        [DF.alias(DF.count(T.c("o_orderkey")), "c_count")]),
      [T.c("c_count")],
      [DF.alias(DF.len(), "custdist")]),
    [DF.desc("custdist"), DF.desc("c_count")])

# Q18: large volume customer (a group_by over every order key, then joins back)
def T.q18(l: DF.Plan(), o: DF.Plan(), c: DF.Plan(), s: DF.Plan(), n: DF.Plan(), r: DF.Plan()) -> DF.Plan():
  DF.lazy_head(
    DF.lazy_sort(
      DF.lazy_select(
        DF.lazy_inner_join(
          DF.lazy_inner_join(
            DF.lazy_filter(
              DF.lazy_group_by(l, [T.c("l_orderkey")], [DF.alias(DF.sum(T.c("l_quantity")), "sum_qty")]),
              DF.gt(T.c("sum_qty"), T.u(250))),
            o, ["l_orderkey"], ["o_orderkey"]),
          c, ["o_custkey"], ["c_custkey"]),
        [T.c("c_name"), T.c("o_custkey"), T.c("l_orderkey"), T.c("o_orderdate"), T.c("o_totalprice"), T.c("sum_qty")]),
      [DF.desc("o_totalprice"), DF.asc("o_orderdate"), DF.asc("l_orderkey")]),
    100)

def T.names() -> List<&2, String>:
  ["q1", "q3", "q4", "q5", "q6", "q10", "q12", "q13", "q18"]

def T.pick(+q: String, +want: String, +k: DF.Plan(), +rest: DF.Plan()) -> DF.Plan():
  Bool.pick(DF.Plan(), String.eq(q, want), k, rest)

def T.plan(+q: String, +l: DF.Plan(), +o: DF.Plan(), +c: DF.Plan(), +s: DF.Plan(), +n: DF.Plan(), +r: DF.Plan()) -> DF.Plan():
  T.pick(q, "q1", T.q1(l, o, c, s, n, r),
  T.pick(q, "q3", T.q3(l, o, c, s, n, r),
  T.pick(q, "q4", T.q4(l, o, c, s, n, r),
  T.pick(q, "q5", T.q5(l, o, c, s, n, r),
  T.pick(q, "q6", T.q6(l, o, c, s, n, r),
  T.pick(q, "q10", T.q10(l, o, c, s, n, r),
  T.pick(q, "q12", T.q12(l, o, c, s, n, r),
  T.pick(q, "q13", T.q13(l, o, c, s, n, r),
  T.q18(l, o, c, s, n, r)))))))))
