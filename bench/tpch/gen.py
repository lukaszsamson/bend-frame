"""TPC-H-shaped data for the PDS-H-style workload (bench/tpch/README.md).

Usage: uv run --project bench python bench/tpch/gen.py [scale ...]   (default 0.01 0.2)
-> bench/data/tpch/sf<scale>/{lineitem,orders,customer,supplier,nation,region}.csv

Not the official dbgen: the same tables, keys, value ranges and selectivities, seeded and
deterministic, with what bend-frame can hold (dates are u32 yyyymmdd, money is f32, no
part / partsupp). Row counts per scale factor: lineitem ~6M*sf, orders 1.5M*sf, customer
150k*sf, supplier 10k*sf.
"""
import datetime as dt
import sys
from pathlib import Path

import numpy as np
import polars as pl

HERE = Path(__file__).parent
DATA = HERE.parent / "data" / "tpch"
SEED = 7

NATIONS = [("ALGERIA", 0), ("ARGENTINA", 1), ("BRAZIL", 1), ("CANADA", 1), ("EGYPT", 4),
           ("ETHIOPIA", 0), ("FRANCE", 3), ("GERMANY", 3), ("INDIA", 2), ("INDONESIA", 2),
           ("IRAN", 4), ("IRAQ", 4), ("JAPAN", 2), ("JORDAN", 4), ("KENYA", 0),
           ("MOROCCO", 0), ("MOZAMBIQUE", 0), ("PERU", 1), ("CHINA", 2), ("ROMANIA", 3),
           ("SAUDI ARABIA", 4), ("VIETNAM", 2), ("RUSSIA", 3), ("UNITED KINGDOM", 3),
           ("UNITED STATES", 1)]
REGIONS = ["AFRICA", "AMERICA", "ASIA", "EUROPE", "MIDDLE EAST"]
SEGMENTS = ["AUTOMOBILE", "BUILDING", "FURNITURE", "HOUSEHOLD", "MACHINERY"]
PRIORITIES = ["1-URGENT", "2-HIGH", "3-MEDIUM", "4-NOT SPECIFIED", "5-LOW"]
SHIPMODES = ["REG AIR", "AIR", "RAIL", "SHIP", "TRUCK", "MAIL", "FOB"]
START = dt.date(1992, 1, 1)
DAYS = (dt.date(1998, 8, 2) - START).days  # orderdate range, as in dbgen
CURRENT = 19950617  # dbgen's "current date": shipped after it -> linestatus O


def ymd(days: np.ndarray) -> np.ndarray:
    """day offsets from START -> u32 yyyymmdd"""
    d = (np.datetime64(START.isoformat()) + days.astype("timedelta64[D]")).astype("datetime64[D]")
    y = d.astype("datetime64[Y]").astype(np.int64) + 1970
    m = d.astype("datetime64[M]").astype(np.int64) % 12 + 1
    dd = (d - d.astype("datetime64[M]")).astype(np.int64) + 1
    return (y * 10000 + m * 100 + dd).astype(np.uint32)


def money(rng, lo: int, hi: int, n: int) -> np.ndarray:
    return (rng.integers(lo, hi + 1, n) / 100).astype(np.float32)


def tables(sf: float) -> dict[str, pl.DataFrame]:
    rng = np.random.default_rng(SEED)
    n_cust, n_supp, n_ord = int(150_000 * sf), max(int(10_000 * sf), 25), int(1_500_000 * sf)
    nation = pl.DataFrame({"n_nationkey": np.arange(25, dtype=np.uint32),
                           "n_name": [n for n, _ in NATIONS],
                           "n_regionkey": np.array([r for _, r in NATIONS], dtype=np.uint32)})
    region = pl.DataFrame({"r_regionkey": np.arange(5, dtype=np.uint32), "r_name": REGIONS})
    supplier = pl.DataFrame({"s_suppkey": np.arange(1, n_supp + 1, dtype=np.uint32),
                             "s_name": [f"Supplier#{i:09d}" for i in range(1, n_supp + 1)],
                             "s_nationkey": rng.integers(0, 25, n_supp, dtype=np.uint32),
                             "s_acctbal": money(rng, -99999, 999999, n_supp)})
    customer = pl.DataFrame({"c_custkey": np.arange(1, n_cust + 1, dtype=np.uint32),
                             "c_name": [f"Customer#{i:09d}" for i in range(1, n_cust + 1)],
                             "c_nationkey": rng.integers(0, 25, n_cust, dtype=np.uint32),
                             "c_acctbal": money(rng, -99999, 999999, n_cust),
                             "c_mktsegment": np.array(SEGMENTS)[rng.integers(0, 5, n_cust)]})
    # dbgen: order keys are sparse (8 of every 32), a third of customers never order
    okey = (np.arange(n_ord, dtype=np.int64) // 8 * 32 + np.arange(n_ord) % 8 + 1).astype(np.uint32)
    ocust = rng.integers(1, n_cust + 1, n_ord)
    ocust = np.where(ocust % 3 == 0, ocust - 1, ocust)
    ocust = np.where(ocust == 0, 1, ocust).astype(np.uint32)
    odays = rng.integers(0, DAYS - 151 + 1, n_ord)
    lines = rng.integers(1, 8, n_ord)
    n_li = int(lines.sum())
    li_ord = np.repeat(np.arange(n_ord), lines)
    ship = odays[li_ord] + rng.integers(1, 122, n_li)
    commit = odays[li_ord] + rng.integers(30, 91, n_li)
    receipt = ship + rng.integers(1, 31, n_li)
    qty = rng.integers(1, 51, n_li).astype(np.uint32)
    price = (qty * rng.integers(90_000, 200_000, n_li) / 100).astype(np.float32)
    shipymd, receiptymd = ymd(ship), ymd(receipt)
    returnflag = np.where(receiptymd <= CURRENT, np.where(rng.random(n_li) < 0.5, "R", "A"), "N")
    lineitem = pl.DataFrame({
        "l_orderkey": okey[li_ord],
        "l_suppkey": rng.integers(1, n_supp + 1, n_li, dtype=np.uint32),
        "l_linenumber": (np.arange(n_li) - np.repeat(np.cumsum(lines) - lines, lines) + 1).astype(np.uint32),
        "l_quantity": qty,
        "l_extendedprice": price,
        "l_discount": (rng.integers(0, 11, n_li) / 100).astype(np.float32),
        "l_tax": (rng.integers(0, 9, n_li) / 100).astype(np.float32),
        "l_returnflag": returnflag,
        "l_linestatus": np.where(shipymd > CURRENT, "O", "F"),
        "l_shipdate": shipymd,
        "l_commitdate": ymd(commit),
        "l_receiptdate": receiptymd,
        "l_shipmode": np.array(SHIPMODES)[rng.integers(0, 7, n_li)],
    })
    # o_totalprice / o_orderstatus from the lines, as dbgen derives them
    agg = (lineitem.with_columns(pl.Series("o", li_ord))
           .group_by("o", maintain_order=True)
           .agg(pl.col("l_extendedprice").sum().alias("tp"),
                (pl.col("l_linestatus") == "F").all().alias("allf"),
                (pl.col("l_linestatus") == "O").all().alias("allo")))
    status = np.where(agg["allf"].to_numpy(), "F", np.where(agg["allo"].to_numpy(), "O", "P"))
    orders = pl.DataFrame({"o_orderkey": okey, "o_custkey": ocust, "o_orderstatus": status,
                           "o_totalprice": agg["tp"].cast(pl.Float32),
                           "o_orderdate": ymd(odays),
                           "o_orderpriority": np.array(PRIORITIES)[rng.integers(0, 5, n_ord)],
                           "o_shippriority": np.zeros(n_ord, dtype=np.uint32)})
    return {"lineitem": lineitem, "orders": orders, "customer": customer,
            "supplier": supplier, "nation": nation, "region": region}


def main(scales: list[str]) -> None:
    for s in scales:
        out = DATA / f"sf{s}"
        out.mkdir(parents=True, exist_ok=True)
        for name, df in tables(float(s)).items():
            df.write_csv(out / f"{name}.csv")
            print(f"{out / name}.csv {df.height} rows")


if __name__ == "__main__":
    main(sys.argv[1:] or ["0.01", "0.2"])
