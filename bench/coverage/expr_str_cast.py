"""Polars 2.0.0 twin of tests/coverage/expr_str_cast.bend (see fx.py)."""
import polars as pl
from fx import INF, NAN, err, frame, show, t, z

c = pl.col
U = lambda v: pl.lit(v, dtype=pl.UInt32)  # noqa: E731
I = lambda v: pl.lit(v, dtype=pl.Int32)  # noqa: E731
F = lambda v: pl.lit(v, dtype=pl.Float32)  # noqa: E731


def n():
    return frame([
        ("u", "str", ["1", "42", None, "4294967295", "007", "0", "3"]),
        ("i", "str", ["-1", "42", None, "2147483647", "-2147483648", "0", "5"]),
        ("f", "str", ["1.5", "-2", "nan", "inf", ".5", "1e3", None]),
        ("b", "str", ["true", "False", None, "True", "false", "true", "false"]),
        ("g", "f32", [-1.9, 2147483520.0, -2147483648.0, None, 0.5, 3.0, -0.0]),
        ("h", "f32", [1.9, 0.5, None, 4294967040.0, 0.0, -0.5, 7.0]),
        ("v", "u32", [0, 1, 2147483647, None, 5, 6, 7]),
        ("w", "i32", [0, 1, 2147483647, None, 5, 6, 7]),
        ("m", "str", ["1", " 2 ", "x", "+5", None, "4294967295", ""]),
        ("pl", "str", ["1", "+5", "3", None, "4", "0", "7"]),
        ("nn", "f32", [1.0, NAN, 2.0, None, 3.0, 4.0, 5.0]),
    ])


def nz():
    return n().select("u", "h", "v").clear()


def sel(tag, es, base=t):
    show(tag, base().select(es))


def seln(tag, es):
    show(tag, n().select(es))


def dfix(df, name, vals, dtype=pl.String):
    return df.with_columns(pl.Series(name, vals, dtype=dtype))


sel("len_chars and the string predicates, with nulls", [
    c("s").str.len_chars().alias("len"), c("s").str.contains("b", literal=True).alias("has_b"),
    c("s").str.contains("é", literal=True).alias("has_e"), c("s").str.starts_with("a").alias("sw_a"),
    c("s").str.ends_with("c").alias("ew_c"), c("s").str.contains("", literal=True).alias("has_empty"),
    c("s").str.starts_with("ab").alias("sw_ab"), c("s").str.ends_with("bc").alias("ew_bc")])
sel("len_chars and the string predicates, zero rows", [
    c("s").str.len_chars().alias("len"), c("s").str.contains("b", literal=True).alias("has_b"),
    c("s").str.starts_with("a").alias("sw_a"), c("s").str.ends_with("c").alias("ew_c")], z)

# str -> bool: Polars has no such cast; D: the contract accepts true/false/True/False
r = n().select([c("u").cast(pl.UInt32).alias("u32"), c("i").cast(pl.Int32).alias("i32"),
                c("f").cast(pl.Float32).alias("f32")])
r = r.with_columns(pl.Series("bool", [True, False, None, True, False, True, False], dtype=pl.Boolean),
                   n()["f"].cast(pl.Float32).alias("f32b"))
show("cast str to u32 i32 f32 bool", r)
seln("cast f32 to u32 and i32 (truncate toward zero)", [
    c("h").cast(pl.UInt32).alias("h_u32"), c("g").cast(pl.Int32).alias("g_i32"),
    c("v").cast(pl.Int32).alias("v_i32"), c("w").cast(pl.UInt32).alias("w_u32")])

# D: f32 -> str is F32.show: `1.9`, `0.5`, `4294967000`, `0`, `-0.5`, `7` (Polars `1.9`, `0.5`, `4294967000.0`, `0.0`, `-0.5`, `7.0`)
hs = n().select(c("h").cast(pl.String)).to_series().to_list()
hs = [None if v is None else (v[:-2] if v.endswith(".0") else v) for v in hs]
r = n().select([c("v").cast(pl.Float32).alias("v_f"), c("w").cast(pl.Float32).alias("w_f"),
                c("v").cast(pl.String).alias("v_s"), c("w").cast(pl.String).alias("w_s")])
r = r.with_columns(pl.Series("h_s", hs, dtype=pl.String), n().select(c("v").cast(pl.UInt32).alias("v_same")).to_series())
show("cast numbers to f32 and str, bool to numbers", r)

# D: f32 -> str: NaN `nan`, inf `inf`, 0.0 `0`, -0.0 `-0`, 1.5 `1.5`, -2.0 `-2`
xs = ["1.5", "-2", None, "nan", "inf", "0", "-0"]
r = t().select([c("k").cast(pl.UInt32).alias("k_u"), c("k").cast(pl.Int32).alias("k_i"),
                c("k").cast(pl.Float32).alias("k_f"), c("k").cast(pl.String).alias("k_s"),
                c("a").cast(pl.Float32).alias("a_f")])
r = r.with_columns(pl.Series("x_s", xs, dtype=pl.String))
r = r.with_columns(pl.Series("k_s", ["true", "false", None, "true", "false", "true", None], dtype=pl.String))  # D: Polars casts bool to str as "true"/"false" too
show("cast bool to u32 i32 f32 str, u32 to f32 above 2^24", r)

# try_cast: strict=False. D: "+5" -> u32 is null here (Polars 5); " 2 " is null in both
mu = n().select(c("m").cast(pl.UInt32, strict=False).alias("m_u"))
mu = mu.with_columns(pl.Series("m_u", [1, None, None, None, None, 4294967295, None], dtype=pl.UInt32))
r = mu.with_columns(
    n().select(c("m").cast(pl.Float32, strict=False).alias("m_f")).to_series(),
    n().select(c("f").cast(pl.Int32, strict=False).alias("f_i")).to_series(),
    n().select(c("h").cast(pl.UInt32, strict=False).alias("h_u")).to_series(),
    n().select(c("v").cast(pl.Int32, strict=False).alias("v_i")).to_series())
show("try_cast turns failing cells into null", r)
sel("try_cast with out-of-range and non-finite cells", [
    c("a").cast(pl.Int32, strict=False).alias("a_i"), c("x").cast(pl.UInt32, strict=False).alias("x_u"),
    c("p").cast(pl.UInt32, strict=False).alias("p_u"), c("x").cast(pl.Int32, strict=False).alias("x_i"),
    c("s").cast(pl.Float32, strict=False).alias("s_f")])
sel("lit_null of every dtype beside a column", [
    c("a"), pl.lit(None, dtype=pl.UInt32).alias("nu"), pl.lit(None, dtype=pl.Int32).alias("ni"),
    pl.lit(None, dtype=pl.Float32).alias("nf"), pl.lit(None, dtype=pl.Boolean).alias("nb"),
    pl.lit(None, dtype=pl.String).alias("ns")])
sel("lit_null alone is one row", [pl.lit(None, dtype=pl.UInt32).alias("nu"), pl.lit("lit", dtype=pl.String).alias("l")])
sel("lit_null beside a zero-row column", [c("a"), pl.lit(None, dtype=pl.Float32).alias("nf")], z)
show("cast and try_cast, zero rows", nz().select([
    c("u").cast(pl.UInt32).alias("u32"), c("u").cast(pl.Float32, strict=False).alias("uf"),
    c("v").cast(pl.Float32).alias("vf"), c("h").cast(pl.UInt32).alias("hu"), c("v").cast(pl.String).alias("vs")]))

T = "TypeMismatch in "
err("invalid len_chars u32", T + "len_chars: expected str, got u32", lambda: t().select(c("a").str.len_chars()))
err("invalid contains_literal bool", T + "contains_literal: expected str, got bool", lambda: t().select(c("k").str.contains("t", literal=True)))
err("invalid starts_with f32", T + "starts_with: expected str, got f32", lambda: t().select(c("x").str.starts_with("1")))
err("invalid ends_with i32", T + "ends_with: expected str, got i32", lambda: t().select(c("p").str.ends_with("1")))
err("invalid len_chars missing column", "ColumnNotFound: nope", lambda: t().select(c("nope").str.len_chars()))
err("invalid cast u32 above i32 range (strict, row 2)", "InvalidOperation: cast u32 to i32: row 0 holds 2147483648",
    lambda: n().select((c("v") + U(2147483648)).cast(pl.Int32)))
err("invalid cast u32 MAX to i32 (strict, row 2)", "InvalidOperation: cast u32 to i32: row 2 holds 4294967295", lambda: t().select(c("a").cast(pl.Int32)))
err("invalid cast negative f32 to u32 (strict, row 1)", "InvalidOperation: cast f32 to u32: row 1 holds -2", lambda: t().select(c("x").cast(pl.UInt32)))
err("invalid cast i32 negative to u32 (strict, row 0)", "InvalidOperation: cast i32 to u32: row 0 holds -1", lambda: n().select((c("w") - I(1)).cast(pl.UInt32)))
err("invalid cast_f32 of bad strings (strict, row 1)", 'InvalidOperation: cast str to f32: row 1 holds " 2 "', lambda: n().select(c("m").cast(pl.Float32)))
err("invalid cast str to u32 with a plus sign (strict, row 1)", 'InvalidOperation: cast str to u32: row 1 holds "+5"', lambda: n().select(c("pl").cast(pl.UInt32)))  # D: Polars accepts "+5"
err("invalid cast f32 NaN to u32 (strict, row 1)", "InvalidOperation: cast f32 to u32: row 1 holds nan", lambda: n().select(c("nn").cast(pl.UInt32)))
err("invalid cast to bool from u32 (static)", T + "cast: expected castable to bool, got u32", lambda: t().select(c("a").cast(pl.Boolean)))
err("invalid cast f32 to bool (static)", T + "cast: expected castable to bool, got f32", lambda: t().select(c("x").cast(pl.Boolean)))
err("invalid try_cast to bool from i32 (static)", T + "try_cast: expected castable to bool, got i32", lambda: t().select(c("p").cast(pl.Boolean, strict=False)))
err("invalid cast missing column", "ColumnNotFound: nope", lambda: t().select(c("nope").cast(pl.UInt32)))
