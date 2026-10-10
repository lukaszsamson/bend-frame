"""Polars 2.0.0 twin of tests/coverage/verbs_basic.bend (see fx.py)."""
import polars as pl
from fx import NAN, err, frame, show

c = pl.col
U = lambda v: pl.lit(v, dtype=pl.UInt32)  # noqa: E731
F = lambda v: pl.lit(v, dtype=pl.Float32)  # noqa: E731


def m():
    return frame([
        ("id", "u32", [1, 2, 3, 4, 5, 6, 7]),
        ("g", "str", ["x", "y", "x", None, "y", "x", None]),
        ("v", "f32", [1.5, None, 3.0, NAN, NAN, 0.0, -0.0]),
        ("k", "bool", [True, False, None, True, None, False, True]),
    ])


def mz():
    return m().clear()


def m2():
    return frame([("id", "u32", [8, 9]), ("g", "str", ["z", None]), ("v", "f32", [None, 2.5]),
                  ("k", "bool", [None, False])])


def z0():
    """A frame with 3 rows and no columns, as Polars makes it: drop every column of a 3-row frame."""
    return m().head(3).drop("id", "g", "v", "k")


def sel(tag, es, base=m):
    show(tag, base().select(es))


def wth(tag, es, base=m):
    show(tag, base().with_columns(es))


def flt(tag, e, base=m):
    show(tag, base().filter(e))


sel("select reorders, aliases and keeps nulls", [c("v").alias("value"), c("id"), c("g")])
# select([]) is the (0, 0) frame (Polars (0, 0))
show("select nothing is a frame of no rows and no columns", pl.DataFrame())
sel("select a literal alone is one row", [U(1).alias("one")])
sel("select a literal beside columns broadcasts", [c("id"), U(9).alias("nine")])
sel("select, zero rows", [c("v"), pl.len().alias("n")], mz)
show("select a literal over a zero-column frame", z0().select(U(1).alias("one")))  # C23
show("select len over a zero-column frame", z0().select(pl.len().alias("literal")))  # C23; D: Bend names it literal
T = "TypeMismatch in "
err("invalid select duplicate output", "DuplicateColumn: id", lambda: m().select(c("id"), c("id")))
err("invalid select two unaliased literals", "DuplicateColumn: literal", lambda: m().select(U(1), U(2)))
err("invalid select missing column", "ColumnNotFound: nope", lambda: m().select(c("id"), c("nope")))
wth("with_columns replaces in place and appends", [c("id").cast(pl.Float32).alias("id"), (c("id") + U(10)).alias("id10")])
wth("with_columns a literal is broadcast", [U(7).alias("seven")])
wth("with_columns nothing is the frame", [])
wth("with_columns on zero rows", [U(7).alias("seven"), c("id").cast(pl.Float32).alias("idf")], mz)
show("with_columns on a zero-column frame keeps its height", z0().with_columns(U(1).alias("o")))  # C22
err("invalid with_columns duplicate output names", "DuplicateColumn: x", lambda: m().with_columns(U(1).alias("x"), U(2).alias("x")))
err("invalid with_columns type mismatch", T + "add: expected u32, got f32", lambda: m().with_columns(c("id") + c("v")))
err("invalid with_columns missing column", "ColumnNotFound: nope", lambda: m().with_columns(c("nope").is_null()))
flt("filter keeps true rows and drops null predicate rows", c("k"))
flt("filter a comparison with nulls", c("v") > F(1.0))
flt("filter a constant true", pl.lit(True))
flt("filter a constant false", pl.lit(False))
flt("filter a null predicate", pl.lit(None, dtype=pl.Boolean))
flt("filter on zero rows", c("k"), mz)
show("filter true over a zero-column frame", z0().filter(pl.lit(True)))  # C24 (h, 0)
show("filter false over a zero-column frame", z0().filter(pl.lit(False)))
err("invalid filter u32 predicate", T + "filter: expected bool, got u32", lambda: m().filter(c("id")))
err("invalid filter missing column", "ColumnNotFound: nope", lambda: m().filter(c("nope") > U(1)))


def hd(tag, n):
    show(tag, m().head(n))


hd("head 3", 3)
hd("head 0", 0)
hd("head more than the height", 100)


def slice_clamped(df, o, n):
    # D: unsigned offsets, clamped (rows [min(o, h), min(o, h) + min(n, h - min(o, h))))
    h = df.height
    s = min(o, h)
    return df.slice(s, min(n, h - s))


show("slice from 2, 3 rows", slice_clamped(m(), 2, 3))
show("slice past the end", slice_clamped(m(), 9, 3))
show("slice length past the end", slice_clamped(m(), 5, 100))
show("slice 0 rows", slice_clamped(m(), 3, 0))
show("tail 3", m().tail(3))
show("tail 0", m().tail(0))
show("tail more than the height", m().tail(100))
show("head slice tail, zero rows", slice_clamped(mz().head(3), 1, 5).tail(2))
# zero-column, height 3: head 2 -> 2, slice(1, 5) -> 1, tail 4 -> 1  (C24)
show("head slice tail, zero columns", slice_clamped(z0().head(2), 1, 5).tail(4))
show("drop one and several columns", m().drop("v", "g"))
show("drop the same column twice", m().drop("v"))  # Polars errors on a repeated name in `drop` kwargs; the contract allows it (DESIGN 15.2.3)
show("drop every column keeps the height", m().drop("id", "g", "v", "k"))  # (h, 0)
show("drop on zero rows", mz().drop("g"))
show("drop on zero columns", z0().drop())
err("invalid drop missing column", "ColumnNotFound: nope", lambda: m().drop("id", "nope"))
show("rename a column", m().rename({"v": "value"}))
# simultaneous rename: Polars applies the mapping at once
show("rename swaps two columns", m().rename({"id": "g", "g": "id"}))
show("rename a column to itself", m().rename({"id": "id"}))
show("rename on zero rows", mz().rename({"id": "key"}))
err("invalid rename missing column", "ColumnNotFound: nope", lambda: m().rename({"nope": "x"}))
err("invalid rename same column twice", "DuplicateColumn: id", lambda: m().rename({"id": "a"}).rename({"id": "b"}))
err("invalid rename onto an existing column", "DuplicateColumn: g", lambda: m().rename({"id": "g"}))
err("invalid rename two to one name", "DuplicateColumn: z", lambda: m().rename({"id": "z", "g": "z"}))
show("unique over every column keeps all distinct rows", m().unique(maintain_order=True, keep="first"))
show("unique by a str key with a null key", m().unique(subset=["g"], maintain_order=True, keep="first"))
show("unique by an f32 key: NaN equals NaN, -0.0 equals 0.0", m().unique(subset=["v"], maintain_order=True, keep="first"))
show("unique by two keys", m().unique(subset=["g", "k"], maintain_order=True, keep="first"))
show("unique on zero rows", mz().unique(subset=["g"], maintain_order=True, keep="first"))
show("unique on a zero-column frame keeps one row", z0().unique())  # C24 (1, 0)
err("invalid unique missing column", "ColumnNotFound: nope", lambda: m().unique(subset=["g", "nope"]))
show("concat two frames with nulls", pl.concat([m(), m2()]))
show("concat the same frame three times", pl.concat([m2(), m2(), m2()]))
show("concat one frame", pl.concat([m2()]))
show("concat with a zero-row frame", pl.concat([mz(), m2(), mz()]))
show("concat zero-column frames adds their heights", pl.concat([z0(), z0()]))  # C24 (2h, 0)
err("invalid concat no inputs", "InvalidOperation: concat_vertical: no inputs", lambda: pl.concat([]))
err("invalid concat schema differs", "InvalidOperation: concat_vertical: input 1 schema [id:u32, g:str, v:f32] differs from input 0's [id:u32, g:str, v:f32, k:bool]",
    lambda: pl.concat([m(), m2().drop("k")]))
err("invalid concat column order differs", "InvalidOperation: concat_vertical: input 1 schema [g:str, id:u32, v:f32, k:bool] differs from input 0's [id:u32, g:str, v:f32, k:bool]",
    lambda: pl.concat([m(), m2().select("g", "id", "v", "k")]))
