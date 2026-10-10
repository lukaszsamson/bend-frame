"""Polars 2.0.0 twin of tests/coverage/expr_cond.bend (see fx.py)."""
import polars as pl
from fx import NAN, err, show, t, z

c = pl.col
U = lambda v: pl.lit(v, dtype=pl.UInt32)  # noqa: E731
I = lambda v: pl.lit(v, dtype=pl.Int32)  # noqa: E731
F = lambda v: pl.lit(v, dtype=pl.Float32)  # noqa: E731
S = lambda v: pl.lit(v, dtype=pl.String)  # noqa: E731


def conds():
    return [pl.when(c("k")).then(c("a")).otherwise(c("b")).alias("w_u"),
            pl.when(c("k")).then(c("p")).otherwise(c("q")).alias("w_i"),
            pl.when(c("k")).then(c("x")).otherwise(c("y")).alias("w_f"),
            pl.when(c("k")).then(c("s")).otherwise(S("z")).alias("w_s"),
            pl.when(c("k")).then(c("k")).otherwise(pl.lit(False)).alias("w_k"),
            pl.when(c("a") > U(1)).then(c("x")).otherwise(F(-1.0)).alias("w_g")]


def isins():
    return [c("a").is_in(pl.Series([7, 2, 4294967295], dtype=pl.UInt32)).alias("in_u"),
            c("p").is_in(pl.Series([7, -2147483648], dtype=pl.Int32)).alias("in_i"),
            c("x").is_in(pl.Series([NAN, 0.0], dtype=pl.Float32)).alias("in_f"),
            c("s").is_in(pl.Series(["a", "abc"], dtype=pl.String)).alias("in_s"),
            c("k").is_in(pl.Series([True], dtype=pl.Boolean)).alias("in_k"),
            c("a").is_in(pl.Series([], dtype=pl.UInt32)).alias("in_none")]


def clips():
    return [c("a").clip(U(1), U(5)).alias("c_u"), c("p").clip(I(-3), I(3)).alias("c_i"),
            c("x").clip(F(0.0), F(1.0)).alias("c_f"), c("a").clip(U(5), U(2)).alias("c_lohi")]


def betweens():
    return [c("a").is_between(U(1), U(5)).alias("b_both"), c("a").is_between(U(1), U(5), closed="both").alias("b_cboth"),
            c("a").is_between(U(1), U(5), closed="left").alias("b_left"),
            c("a").is_between(U(1), U(5), closed="right").alias("b_right"),
            c("a").is_between(U(1), U(5), closed="none").alias("b_neither"),
            c("a").is_between(U(5), U(1)).alias("b_lohi"), c("x").is_between(F(0.0), c("y")).alias("b_f"),
            c("s").is_between(S("a"), S("abc")).alias("b_s"), c("p").is_between(I(-7), I(0)).alias("b_i")]


def sel(tag, es, base=t):
    show(tag, base().select(es))


sel("when then else, a null condition picks else", conds())
sel("is_in u32 i32 f32 str bool, and an empty list", isins())
sel("clip u32 i32 f32 with NaN and lo > hi", clips())
sel("is_between closed both left right neither", betweens())
sel("when is_in clip is_between, zero rows", conds() + isins() + clips() + betweens(), z)

T = "TypeMismatch in "
err("invalid when condition u32", T + "when: expected bool, got u32", lambda: t().select(pl.when(c("a")).then(c("a")).otherwise(c("b"))))
err("invalid when branches u32 i32", T + "when: expected u32, got i32", lambda: t().select(pl.when(c("k")).then(c("a")).otherwise(c("p"))))
err("invalid when missing column", "ColumnNotFound: nope", lambda: t().select(pl.when(c("k")).then(c("a")).otherwise(c("nope"))))
err("invalid is_in f32 scalar in u32 column", T + "is_in: expected u32, got f32", lambda: t().select(c("a").is_in(pl.Series([1.0], dtype=pl.Float32))))
err("invalid is_in null scalar", T + "is_in: expected u32, got null", lambda: t().select(c("a").is_in(pl.Series([1, None], dtype=pl.UInt32))))
err("invalid is_in str scalar in bool column", T + "is_in: expected bool, got str", lambda: t().select(c("k").is_in(pl.Series(["t"], dtype=pl.String))))
err("invalid is_in missing column", "ColumnNotFound: nope", lambda: t().select(c("nope").is_in(pl.Series([1], dtype=pl.UInt32))))
err("invalid clip str", T + "clip: expected numeric, got str", lambda: t().select(c("s").clip(S("a"), S("b"))))
err("invalid clip bool", T + "clip: expected numeric, got bool", lambda: t().select(c("k").clip(pl.lit(False), pl.lit(True))))
err("invalid clip f32 bounds on u32", T + "clip: expected u32, got f32", lambda: t().select(c("a").clip(F(0.0), F(1.0))))
err("invalid clip null upper bound", T + "clip: expected u32, got null", lambda: t().select(c("a").clip(U(1), None)))
err("invalid is_between f32 bounds on u32", T + "ge: expected u32, got f32", lambda: t().select(c("a").is_between(F(0.0), F(1.0))))
err("invalid is_between_closed left on i32 vs u32", T + "ge: expected i32, got u32", lambda: t().select(c("p").is_between(U(0), U(1), closed="left")))
err("invalid is_between_closed missing column", "ColumnNotFound: nope", lambda: t().select(c("nope").is_between(U(0), U(1), closed="right")))
err("invalid is_between_closed neither str vs u32", T + "gt: expected str, got u32", lambda: t().select(c("s").is_between(U(0), U(1), closed="none")))
