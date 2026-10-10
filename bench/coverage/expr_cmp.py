"""Polars 2.0.0 twin of tests/coverage/expr_cmp.bend (see fx.py)."""
import polars as pl
from fx import err, show, t, z

c = pl.col
U = lambda v: pl.lit(v, dtype=pl.UInt32)  # noqa: E731
I = lambda v: pl.lit(v, dtype=pl.Int32)  # noqa: E731
F = lambda v: pl.lit(v, dtype=pl.Float32)  # noqa: E731


def six(p, l, r):
    return [(l == r).alias(p + "_eq"), (l != r).alias(p + "_ne"), (l < r).alias(p + "_lt"),
            (l <= r).alias(p + "_le"), (l > r).alias(p + "_gt"), (l >= r).alias(p + "_ge")]


def sel(tag, es, base=t):
    show(tag, base().select(es))


sel("cmp u32 with nulls", six("u", c("a"), c("b")))
sel("cmp i32 MIN and negatives", six("i", c("p"), c("q")))
sel("cmp f32 NaN inf -0.0 (the 15.5.2 order)", six("f", c("x"), c("y")))
sel("cmp f32 against a literal", six("f0", c("x"), F(0.0)))
sel("cmp str against a literal", six("s", c("s"), pl.lit("ab", dtype=pl.String)))
sel("cmp bool against a literal", six("k", c("k"), pl.lit(True)))
sel("cmp i32 against literals", six("i1", c("p"), I(-7)) + six("i2", c("q"), I(2)))

m = c("a") > U(1)
m2 = c("b") > U(0)
sel("and or not Kleene, both operands nullable", [
    (c("k") & m).alias("and_a"), (c("k") | m).alias("or_a"), (c("k") & m2).alias("and_b"), (c("k") | m2).alias("or_b"),
    (~c("k")).alias("not_k"), (~m).alias("not_a")])
sel("is_null is_not_null on every dtype", [
    c("a").is_null().alias("n_a"), c("p").is_null().alias("n_p"), c("x").is_null().alias("n_x"),
    c("k").is_null().alias("n_k"), c("s").is_null().alias("n_s"),
    c("a").is_not_null().alias("v_a"), c("p").is_not_null().alias("v_p"), c("x").is_not_null().alias("v_x"),
    c("k").is_not_null().alias("v_k"), c("s").is_not_null().alias("v_s")])
sel("fill_null with a literal and with a column", [
    c("a").fill_null(U(9)).alias("fa"), c("p").fill_null(I(-1)).alias("fp"), c("x").fill_null(F(0.5)).alias("fx"),
    c("s").fill_null(pl.lit("?", dtype=pl.String)).alias("fs"), c("k").fill_null(pl.lit(False)).alias("fk"),
    c("b").fill_null(c("a")).alias("fb")])

allx = (six("u", c("a"), c("b")) + six("i", c("p"), c("q")) + six("f", c("x"), c("y"))
        + six("s", c("s"), pl.lit("ab", dtype=pl.String)) + six("k", c("k"), pl.lit(True))
        + [(c("k") & (c("a") > U(1))).alias("and"), (c("k") | (c("a") > U(1))).alias("or"), (~c("k")).alias("not"),
           c("x").is_null().alias("isnull"), c("s").is_not_null().alias("notnull"), c("a").fill_null(U(9)).alias("fill")])
sel("every comparison logic and null test, zero rows", allx, z)

T = "TypeMismatch in "
err("invalid eq u32 vs i32", T + "eq: expected u32, got i32", lambda: t().select(c("a") == c("p")))
err("invalid ne bool vs u32", T + "ne: expected bool, got u32", lambda: t().select(c("k") != c("a")))
err("invalid lt str vs f32", T + "lt: expected str, got f32", lambda: t().select(c("s") < c("x")))
err("invalid le f32 vs literal u32", T + "le: expected f32, got u32", lambda: t().select(c("x") <= U(1)))
err("invalid gt missing column", "ColumnNotFound: nope", lambda: t().select(c("nope") > c("a")))
err("invalid ge i32 vs u32 literal", T + "ge: expected i32, got u32", lambda: t().select(c("p") >= U(1)))
err("invalid and u32", T + "and: expected bool, got u32", lambda: t().select(c("a") & c("k")))
err("invalid and bool and u32", T + "and: expected bool, got u32", lambda: t().select(c("k") & c("a")))
err("invalid or str", T + "or: expected bool, got str", lambda: t().select(c("s") | c("k")))
err("invalid not u32", T + "not: expected bool, got u32", lambda: t().select(~c("a")))
err("invalid is_null missing column", "ColumnNotFound: nope", lambda: t().select(c("nope").is_null()))
err("invalid is_not_null missing column", "ColumnNotFound: nope", lambda: t().select(c("nope").is_not_null()))
err("invalid fill_null u32 with f32", T + "fill_null: expected u32, got f32", lambda: t().select(c("a").fill_null(F(1.0))))
err("invalid fill_null str with u32 column", T + "fill_null: expected str, got u32", lambda: t().select(c("s").fill_null(c("a"))))
