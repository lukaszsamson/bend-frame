"""Polars 2.0.0 twin of tests/coverage/expr_arith.bend (see fx.py)."""
import polars as pl
from fx import INF, MIN, NAN, err, frame, show, t, z

c = pl.col


def sel(tag, es, base=t):
    show(tag, base().select(es))


def with_depart(df, name, vals, dtype):
    """Replace a column's cells by hand where the contract departs from Polars."""
    return df.with_columns(pl.Series(name, vals, dtype=dtype))


sel("add sub mul u32 i32 f32 with nulls", [
    c("a"),
    (c("a") + c("b")).alias("add_u"), (c("p") + c("q")).alias("add_i"), (c("x") + c("y")).alias("add_f"),
    (c("a") - c("b")).alias("sub_u"), (c("p") - c("q")).alias("sub_i"), (c("x") - c("y")).alias("sub_f"),
    (c("a") * c("b")).alias("mul_u"), (c("p") * c("q")).alias("mul_i"), (c("x") * c("y")).alias("mul_f")])
sel("add with a literal", [(c("a") + pl.lit(1, dtype=pl.UInt32)).alias("a1"),
                           (c("x") + pl.lit(0.5, dtype=pl.Float32)).alias("x5")])
sel("div f32", [(c("x") / c("y")).alias("div_f"), (c("x") / pl.lit(0.0, dtype=pl.Float32)).alias("div_zero")])

# floor_div: Polars `//` on integers; x // 0 is null; D: i32 MIN // -1 is null here (Polars MIN)
fd = t().select([(c("a") // c("b")).alias("fdiv_u"), (c("p") // c("q")).alias("fdiv_i")])
assert fd["fdiv_i"].to_list()[4] == MIN
fd = with_depart(fd, "fdiv_i", [3, -4, -4, 3, None, None, None], pl.Int32)
show("floor_div u32 i32", fd)
sel("mod u32 i32", [(c("a") % c("b")).alias("mod_u"), (c("p") % c("q")).alias("mod_i")])
sel("neg abs sqrt", [(-c("p")).alias("neg_i"), (-c("x")).alias("neg_f"), c("p").abs().alias("abs_i"),
                     c("x").abs().alias("abs_f"), c("x").sqrt().alias("sqrt_f")])
# zero rows: dtypes only
zz = z().select([
    (c("a") + c("b")).alias("add_u"), (c("p") + c("q")).alias("add_i"), (c("x") + c("y")).alias("add_f"),
    (c("a") - c("b")).alias("sub_u"), (c("p") - c("q")).alias("sub_i"), (c("x") - c("y")).alias("sub_f"),
    (c("a") * c("b")).alias("mul_u"), (c("p") * c("q")).alias("mul_i"), (c("x") * c("y")).alias("mul_f"),
    (c("x") / c("y")).alias("div_f"), (c("a") // c("b")).alias("fdiv_u"), (c("p") // c("q")).alias("fdiv_i"),
    (c("a") % c("b")).alias("mod_u"), (c("p") % c("q")).alias("mod_i"),
    (-c("p")).alias("neg_i"), (-c("x")).alias("neg_f"), c("p").abs().alias("abs_i"), c("x").abs().alias("abs_f"),
    c("x").sqrt().alias("sqrt_f")])
show("all operators, zero rows", zz)

# invalid input: Bend never coerces; the contract's text (DESIGN 15.3, 15.9). The lambda is what
# Polars is asked to do with the same program: stderr says whether it refuses too or accepts (a departure)
T = "TypeMismatch in "
err("invalid add u32 + i32", T + "add: expected u32, got i32", lambda: t().select(c("a") + c("p")))
err("invalid add bool", T + "add: expected numeric, got bool", lambda: t().select(c("k") + c("k")))
err("invalid sub u32 - f32", T + "sub: expected u32, got f32", lambda: t().select(c("a") - c("x")))
err("invalid mul str", T + "mul: expected numeric, got str", lambda: t().select(c("s") * c("s")))
err("invalid add missing column", "ColumnNotFound: nope", lambda: t().select(c("nope") + c("a")))
err("invalid div u32", T + "div: expected f32, got u32", lambda: t().select(c("a") / c("b")))
err("invalid div f32 by u32", T + "div: expected f32, got u32", lambda: t().select(c("x") / c("b")))
err("invalid floor_div f32", T + "floor_div: expected u32 or i32, got f32", lambda: t().select(c("x") // c("y")))
err("invalid floor_div u32 i32", T + "floor_div: expected u32, got i32", lambda: t().select(c("a") // c("p")))
err("invalid mod f32", T + "mod: expected u32 or i32, got f32", lambda: t().select(c("x") % c("y")))
err("invalid mod u32 i32", T + "mod: expected u32, got i32", lambda: t().select(c("a") % c("p")))
err("invalid neg u32", T + "neg: expected i32 or f32, got u32", lambda: t().select(-c("a")))
err("invalid neg str", T + "neg: expected i32 or f32, got str", lambda: t().select(-c("s")))
err("invalid abs u32", T + "abs: expected i32 or f32, got u32", lambda: t().select(c("a").abs()))
err("invalid abs bool", T + "abs: expected i32 or f32, got bool", lambda: t().select(c("k").abs()))
err("invalid sqrt i32", T + "sqrt: expected f32, got i32", lambda: t().select(c("p").sqrt()))
err("invalid sqrt u32", T + "sqrt: expected f32, got u32", lambda: t().select(c("a").sqrt()))
