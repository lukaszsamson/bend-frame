"""Polars 2.0.0 twin of tests/coverage/expr_lit.bend (see fx.py)."""
import sys

import polars as pl
from fx import err, show, t, z

c = pl.col
U = lambda v: pl.lit(v, dtype=pl.UInt32)  # noqa: E731
I = lambda v: pl.lit(v, dtype=pl.Int32)  # noqa: E731
F = lambda v: pl.lit(v, dtype=pl.Float32)  # noqa: E731
S = lambda v: pl.lit(v, dtype=pl.String)  # noqa: E731


def lits():
    return [U(1).alias("u"), F(1.5).alias("f"), S("é").alias("s"), pl.lit(True).alias("b"), I(7).alias("i"),
            I(-7).alias("n"), I(2147483647).alias("imax"), I(-2147483648).alias("imin"),
            U(4294967295).alias("umax"), S("").alias("empty")]


def z0():
    return t().head(3).drop(*t().columns)


show("literals beside a nullable column are broadcast", t().select([c("a")] + lits()))
show("literals alone are one row", t().select(lits()))
show("literals beside a zero-row column", z().select([c("a")] + lits()))
show("literals alone over zero rows are one row", z().select(lits()))
show("literals over a zero-column frame are one row", z0().select(lits()))
show("with_columns literals are broadcast", t().with_columns([U(1).alias("u"), S("s").alias("s")]))
show("with_columns literals over zero rows", z().with_columns([U(1).alias("u"), F(0.5).alias("f"), pl.lit(False).alias("b")]))
show("a literal beside a null column compares to null", t().select([
    (c("a") == U(7)).alias("eq7"), (c("a") + U(1)).alias("a1"), U(1).is_null().alias("litnull")]))
show("lit_i32 holds v < 2^31", t().select([I(0).alias("z"), I(2147483647).alias("imax"), I(0).alias("nz"),
                                          I(-1).alias("n1"), I(-2147483648).alias("imin")]).head(1))
err("invalid lit_i32 above the i32 range fails when evaluated", "InvalidOperation: cast u32 to i32: row 0 holds 2147483648",
    lambda: t().select(U(2147483648).cast(pl.Int32)))
err("invalid lit_i32 at the u32 maximum", "InvalidOperation: cast u32 to i32: row 0 holds 4294967295",
    lambda: t().select(U(4294967295).cast(pl.Int32).alias("big")))
err("invalid lit_i32_neg above 2^31 fails when evaluated", "InvalidOperation: cast u32 to i32: row 0 holds 2147483649",
    lambda: t().select(-U(2147483649).cast(pl.Int32)))
err("invalid lit_i32 over zero rows is still evaluated", "InvalidOperation: cast u32 to i32: row 0 holds 2147483648",
    lambda: z().select(U(2147483648).cast(pl.Int32)))
err("invalid lit_u32 plus lit_f32", "TypeMismatch in add: expected u32, got f32", lambda: t().select(U(1) + F(1.0)))
err("invalid lit_str times lit_bool", "TypeMismatch in mul: expected numeric, got str", lambda: t().select(S("a") * pl.lit(True)))
show("is_in with checked i32 scalars", t().select(c("p").is_in(pl.Series([7, -2147483648], dtype=pl.Int32)).alias("in")))
show("is_in with checked i32 scalars, zero rows", z().select(c("p").is_in(pl.Series([7], dtype=pl.Int32)).alias("in")))
err("invalid is_in with a refused i32 scalar (null)", "TypeMismatch in is_in: expected i32, got null",
    lambda: t().select(c("p").is_in(pl.Series([None], dtype=pl.Int32))))
err("invalid is_in i32 scalars in a u32 column", "TypeMismatch in is_in: expected u32, got i32",
    lambda: t().select(c("a").is_in(pl.Series([7], dtype=pl.Int32))))
# the checked i32 builders: v < 2^31 (v <= 2^31 negated), else "i32 out of range: <v>"; not a Polars operation
sys.stdout.write("-- i32 and i32_neg\n")
for v in [0, 7, 2147483647, 2147483648, 4294967295]:
    sys.stdout.write(("ok %d" % v if v < 2**31 else "error: InvalidOperation: i32 out of range: %d" % v) + "\n")
for v in [0, 7, 2147483648, 2147483649]:
    sys.stdout.write(("ok %d" % -v if v <= 2**31 else "error: InvalidOperation: i32 out of range: %d" % v) + "\n")
sys.stdout.write("\n")
