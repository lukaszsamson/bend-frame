"""Polars 2.0.0 twin of tests/coverage/agg.bend (see fx.py)."""
import polars as pl
from fx import err, frame, show, t, z

c = pl.col


def g():
    return frame([
        ("k", "str", ["a", "b", "a", None, "b", "a", None, "c"]),
        ("v", "u32", [1, 2, 4, None, 8, 2, 3, None]),
        ("w", "f32", [1.5, 2.5, None, 4.0, 0.5, 3.5, 2.0, 1.0]),
        ("i", "i32", [-1, 5, -3, 2, None, 7, -8, 0]),
        ("e", "f32", [2.0, 4.0, None, 6.0, 8.0, None, 5.0, None]),
        ("b", "bool", [True, False, True, None, False, True, None, False]),
    ])


def gz():
    return g().clear()


F32 = pl.Float32


def any10(n):
    x = c(n)
    return [x.count().alias(n + "_count"), pl.len().alias(n + "_len"), x.min().alias(n + "_min"),
            x.max().alias(n + "_max"), x.first().alias(n + "_first"), x.last().alias(n + "_last"),
            x.n_unique().alias(n + "_nuniq")]


def num(n):
    x = c(n)
    # D: mean and median of u32 / i32 are f32 (Polars f64)
    return [x.sum().alias(n + "_sum"), x.mean().cast(F32).alias(n + "_mean"), x.count().alias(n + "_count"),
            x.min().alias(n + "_min"), x.max().alias(n + "_max"), x.first().alias(n + "_first"),
            x.last().alias(n + "_last"), x.n_unique().alias(n + "_nuniq"), x.median().cast(F32).alias(n + "_median")]


def spread(n):
    x = c(n)
    return [x.std().cast(F32).alias(n + "_std"), x.var().cast(F32).alias(n + "_var"), x.median().cast(F32).alias(n + "_median")]


def sel(tag, es, base=g):
    show(tag, base().select(es))


def grp(tag, ks, es, base=g):
    show(tag, base().group_by(ks, maintain_order=True).agg(es))


sel("global reductions of u32 with nulls", num("v"))
sel("global reductions of i32 with nulls", num("i"))
sel("global reductions of f32 with nulls", num("w"))
sel("global std var median of f32 with nulls", spread("e") + [c("e").sum().alias("e_sum"), c("e").mean().alias("e_mean")])
sel("global min max count first last n_unique of str and bool", any10("k") + any10("b"))
x = c("x")
show("global reductions of f32 with NaN inf -0.0 and a null", t().select([
    x.sum().alias("x_sum"), x.mean().alias("x_mean"), x.count().alias("x_count"), x.min().alias("x_min"),
    x.max().alias("x_max"), x.first().alias("x_first"), x.last().alias("x_last"), x.n_unique().alias("x_nuniq"),
    x.median().alias("x_median"), x.std().alias("x_std"), x.var().alias("x_var")]))
# Bend's pl.len() twin is named "literal" (Agg{Len, lit 1}, DESIGN 14 M2.2); Polars names it "len"
sel("global len", [pl.len().alias("literal")])
sel("a reduction broadcast beside a column", [c("v"), c("v").sum().alias("total"), c("v").count().alias("n")])
show("with_columns broadcasts a reduction", g().with_columns(c("w").max().alias("w_max"), c("e").mean().alias("e_mean")))
show("filter by a reduction", g().filter(c("w") > c("w").mean()))
grp("group_by str key, u32 aggregates", ["k"], num("v"))
grp("group_by str key, i32 aggregates", ["k"], num("i"))
grp("group_by str key, f32 aggregates", ["k"], num("w"))
grp("group_by str key, std var median", ["k"], spread("e"))
grp("group_by str key, std var median of w", ["k"], spread("w"))
grp("group_by str key, str and bool aggregates", ["k"], any10("b") + [c("k").min().alias("k_min")])
grp("group_by bool key and len", ["b"], [pl.len().alias("literal"), c("v").sum().alias("v_sum")])
sel("global reductions, zero rows", num("v") + spread("e") + any10("k"), gz)
grp("group_by, zero rows", ["k"], num("v") + spread("e"), gz)

T = "TypeMismatch in "
err("invalid sum of str", T + "sum: expected numeric, got str", lambda: g().select(c("k").sum()))
err("invalid sum of bool", T + "sum: expected numeric, got bool", lambda: g().select(c("b").sum()))  # D: Polars sums bool
err("invalid mean of bool", T + "mean: expected numeric, got bool", lambda: g().select(c("b").mean()))
err("invalid std of str", T + "std: expected numeric, got str", lambda: g().select(c("k").std()))
err("invalid var of bool", T + "var: expected numeric, got bool", lambda: g().select(c("b").var()))
err("invalid median of str", T + "median: expected numeric, got str", lambda: g().select(c("k").median()))
for op, name in [("min", "min"), ("max", "max"), ("count", "count"), ("first", "first"), ("last", "last"), ("n_unique", "n_unique")]:
    err("invalid %s of a missing column" % op, "ColumnNotFound: nope", lambda op=op: g().select(getattr(c("nope"), op)()))
err("invalid nested reduction sum of sum", "InvalidOperation: nested aggregation: col(\"v\").sum().sum()", lambda: g().select(c("v").sum().sum()))  # D: Polars allows
err("invalid nested reduction mean of max", "InvalidOperation: nested aggregation: col(\"w\").max().mean()", lambda: g().select(c("w").max().mean()))
err("invalid group_by aggregate that is no reduction", "InvalidOperation: agg expects an aggregation: col(\"v\")", lambda: g().group_by("k").agg(c("v")))  # D: Polars returns lists
err("invalid group_by no keys", "InvalidOperation: group_by needs at least one key", lambda: g().group_by().agg(c("v").sum()))
err("invalid group_by key is a reduction", "InvalidOperation: group_by key is an aggregation: col(\"v\").sum()", lambda: g().group_by(c("v").sum()).agg(pl.len()))
err("invalid group_by nested reduction", "InvalidOperation: nested aggregation in agg: col(\"v\").sum().sum()", lambda: g().group_by("k").agg(c("v").sum().sum()))
err("invalid group_by sum of str", T + "sum: expected numeric, got str", lambda: g().group_by("k").agg(c("k").sum()))
err("invalid group_by duplicate output names", "DuplicateColumn: v", lambda: g().group_by("k").agg(c("v").sum(), c("v").min()))

