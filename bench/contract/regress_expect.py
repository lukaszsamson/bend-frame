"""Expected output of the defect regressions (tests/regress/*.bend), derived from the contract.

    cd bench && uv run python contract/regress_expect.py            # check every file's #| block
    cd bench && uv run python contract/regress_expect.py --write    # rewrite the #| blocks
    cd bench && uv run python contract/regress_expect.py B03_c      # only files matching

Each regression prints, per scenario, `-- <ID> <case> <eager|raw|opt>` followed by the
DF.dump text (DESIGN.md 15.1) and a blank line. The expected dumps below are the CORRECT
behaviour per DESIGN.md 15 (not today's output). Where Polars 2.0.0 has the same semantics,
the dump is computed by running the same program in Polars and rendering it with
bench/dump_polars.py; where the contract departs from Polars (f32 means of integers, a
1-row scalar predicate in lazy Polars, blank CSV lines, trimming, error texts, ...), the
dump is written by hand here, with the contract row cited next to it.

Specs also cover tests/regress/pending/<name>.bend.txt (tests written against API that does
not exist yet; see tests/regress/PENDING.md). The `#|` block of a .bend file is everything from its first `#|` line to the end of the
file; --write replaces it, so the .bend files keep their code above the block.
"""
import math
import pathlib
import re
import sys

import numpy as np
import polars as pl

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from dump_polars import dump, dump_error, quote  # noqa: E402

assert pl.__version__ == "2.0.0", pl.__version__

ROOT = HERE.parent.parent
REGRESS = ROOT / "tests" / "regress"

U32, I32, F32, STR, BOOL = pl.UInt32, pl.Int32, pl.Float32, pl.String, pl.Boolean
NAN = float("nan")
INF = float("inf")
MIN = -(2**31)
MAX = 2**31 - 1


# ---- dump text built by hand -----------------------------------------------------------

def fb(x) -> str:
    """the dump cell of an f32 value (NaN as 0x7fc00000, the quiet NaN the interpreter makes)"""
    if x is None:
        return "null"
    v = np.float32(x)
    if math.isnan(v):
        return "0x7fc00000"
    return "0x%08x" % int(np.array([v], dtype=np.float32).view(np.uint32)[0])


def cell(t: str, v) -> str:
    if v is None:
        return "null"
    if t == "f32":
        return fb(v)
    if t == "str":
        return quote(v)
    if t == "bool":
        return "true" if v else "false"
    return str(int(v))


def frame(cols, rows=None, height=None) -> str:
    """cols: [(dtype, name)], rows: [[python values]] (converted by dtype)"""
    rows = rows or []
    h = len(rows) if height is None else height
    lines = ["frame", f"height\t{h}", f"width\t{len(cols)}"]
    lines += [f"col\t{t}\t{quote(n)}" for t, n in cols]
    if cols:
        lines += ["row\t" + "\t".join(cell(t, v) for (t, _), v in zip(cols, r)) for r in rows]
    return "\n".join(lines) + "\n"


def columns(*cols, height=None) -> str:
    """columns given as (dtype, name, [values])"""
    h = len(cols[0][2]) if cols else (height or 0)
    rows = [[c[2][i] for c in cols] for i in range(h)]
    return frame([(c[0], c[1]) for c in cols], rows, height=h if cols else height)


def err(text: str) -> str:
    return dump_error(text)


def pdump(df: pl.DataFrame) -> str:
    """a Polars frame in dump text (dtypes must be the five bend-frame ones)"""
    return dump(df)


# ---- expected blocks ---------------------------------------------------------------------

def three(tag: str, text: str):
    return [(f"-- {tag} {how}", text) for how in ("eager", "raw", "opt")]


def lazy2(tag: str, text: str):
    return [(f"-- {tag} {how}", text) for how in ("raw", "opt")]


def one(tag: str, how: str, text: str):
    return [(f"-- {tag} {how}", text)]


def block(items) -> str:
    out = []
    for header, text in items:
        out.append("#|" + header)
        for line in text.rstrip("\n").split("\n"):
            out.append("#|" + line)
        out.append("#|")
    return "\n".join(out) + "\n"


SPECS = {}


def spec(name):
    def reg(f):
        SPECS[name] = f
        return f
    return reg


# =====================================================================================
# B01 cardinality (DESIGN.md 15.4; bench/contract/cardinality.py has the Polars side)
# =====================================================================================

@spec("B01_a_head_literal_select")
def _():
    one_row = columns(("u32", "one", [1]))
    zero = frame([("u32", "one")], [])
    pl_c5 = pl.DataFrame({"a": [1, 2, 3]}, schema={"a": U32}).select(pl.lit(1, U32).alias("one")).head(0)
    pl_c4 = pl.DataFrame({"a": [1, 2, 3]}, schema={"a": U32}).head(0).select(pl.lit(1, U32).alias("one"))
    assert pdump(pl_c5) == zero and pdump(pl_c4) == one_row
    return (three("B01-a C5 head0-over-literal-select", zero)
            + three("B01-a C4 literal-select-over-head0", one_row)
            + three("B01-a head2-over-literal-select", one_row))


def t3():
    return pl.DataFrame({"a": [1, 2, 3]}, schema={"a": U32})


@spec("B01_b_empty_select")
def _():
    empty = frame([], [], height=0)
    df = pl.DataFrame({"a": [1, 2, None, 4, 5, 6]}, schema={"a": U32})
    assert pdump(df.select([])) == empty and pdump(df.lazy().select([]).collect()) == empty
    assert pdump(df.select([]).head(3)) == empty
    return three("B01-b C1 select-empty", empty) + three("B01-b C1 head3-over-select-empty", empty)


@spec("B01_c_zero_column_height")
def _():
    df = pl.DataFrame({"a": [1, 2, None, 4, 5, 6]}, schema={"a": U32})
    z = df.drop("a")
    lit1 = pl.lit(1, U32)
    c1 = pdump(df.select([]).with_columns(lit1.alias("o")))
    c1n = pdump(df.select([]).select(pl.len().cast(U32).alias("n")))
    c22 = pdump(z.with_columns(lit1.alias("o")))
    c23n = pdump(z.select(pl.len().cast(U32).alias("n")))
    c23l = pdump(z.select(lit1))
    c24h = pdump(z.head(2))
    c24f = pdump(z.filter(pl.lit(True)))
    assert c1 == frame([("u32", "o")], []) and c1n == columns(("u32", "n", [0]))
    assert c22 == columns(("u32", "o", [1] * 6)) and c23n == columns(("u32", "n", [6]))
    assert c23l == columns(("u32", "literal", [1]))
    assert c24h == frame([], [], height=2) and c24f == frame([], [], height=6)
    return (three("B01-c C1 select-empty-then-with-literal", c1)
            + three("B01-c C1 select-empty-then-len", c1n)
            + three("B01-c C22 zero-col-with-literal", c22)
            + three("B01-c C23 zero-col-select-len", c23n)
            + three("B01-c C23 zero-col-select-literal", c23l)
            + three("B01-c C24 zero-col-head2", c24h)
            + three("B01-c C24 zero-col-filter-true", c24f))


@spec("B01_d_constant_predicate")
def _():
    one = pl.lit(1, U32).alias("one")
    sel = t3().select(one)
    c19f = pdump(sel.filter(pl.lit(False)))  # eager Polars; lazy Polars answers (1, 1): departure
    assert pdump(t3().lazy().select(one).filter(pl.lit(False)).collect()) == columns(("u32", "one", [1]))
    c19t = pdump(sel.filter(pl.lit(True)))
    eq2 = pdump(t3().lazy().select(one).filter(pl.col("one") == 2).collect())
    c18t = pdump(t3().filter(pl.lit(True)))
    c18f = pdump(t3().filter(pl.lit(False)))
    c20 = pdump(t3().filter(pl.lit(None, BOOL)))
    assert c19f == frame([("u32", "one")], []) and eq2 == c19f
    return (three("B01-d C19 literal-select-filter-false", c19f)
            + three("B01-d C19 literal-select-filter-true", c19t)
            + three("B01-d literal-select-filter-one-eq-2", eq2)
            + three("B01-d C18 filter-true", c18t)
            + three("B01-d C18 filter-false", c18f)
            + three("B01-d C20 filter-null", c20))


@spec("B01_e_zero_row_inputs")
def _():
    t0 = pl.DataFrame({"a": [], "x": []}, schema={"a": U32, "x": F32})
    A = pl.col("a")
    c3 = pdump(t0.select(pl.lit(1, U32).alias("one")))
    # Polars: mean is f64 (null here) and len() is u32; the contract's mean is f32 (15.2.5)
    red = t0.select(A.sum().alias("sum"), A.mean().cast(F32).alias("mean"), A.min().alias("min"),
                    A.max().alias("max"), A.first().alias("first"), A.last().alias("last"),
                    A.count().cast(U32).alias("count"), pl.len().cast(U32).alias("len"),
                    A.n_unique().cast(U32).alias("n_unique"))
    c7 = pdump(red)
    assert c7 == columns(("u32", "sum", [0]), ("f32", "mean", [None]), ("u32", "min", [None]),
                         ("u32", "max", [None]), ("u32", "first", [None]), ("u32", "last", [None]),
                         ("u32", "count", [0]), ("u32", "len", [0]), ("u32", "n_unique", [0]))
    c10 = pdump(t0.select(A, A.sum().alias("s")))
    c13 = pdump(t0.with_columns(A.sum().alias("s")))
    c14 = pdump(t0.with_columns(pl.lit(1, U32).alias("one")))
    c21 = pdump(t0.filter(A > 1))
    c26 = pdump(t0.group_by("a", maintain_order=True).agg(pl.col("x").count().cast(U32).alias("n")))
    return (three("B01-e C3 literal-select", c3) + three("B01-e C7 reductions", c7)
            + three("B01-e C10 mixed-select", c10) + three("B01-e C13 with-reduction", c13)
            + three("B01-e C14 with-literal", c14) + three("B01-e C21 filter", c21)
            + three("B01-e C26 group-by", c26))


@spec("B01_f_head_sink_kinds")
def _():
    t = pl.DataFrame({"a": [1, 2, 3, 4, 5, 6], "x": [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]}, schema={"a": U32, "x": F32})
    A, X = pl.col("a"), pl.col("x")
    s = A.sum().alias("s")
    c1 = pdump(t.lazy().with_columns(s).head(2).collect())
    c2 = pdump(t.lazy().select(A, s).head(1).collect())
    c3 = pdump(t.lazy().select(s).head(0).collect())
    c4 = pdump(t.lazy().select((X - X.mean()).alias("d")).head(2).collect())
    c5 = pdump(t.lazy().select(A, (A * 2).alias("b")).head(2).collect())
    assert c4 == columns(("f32", "d", [-2.5, -1.5]))
    return (three("B01-f head2-over-with-sum", c1) + three("B01-f head1-over-mixed-select", c2)
            + three("B01-f head0-over-reduction-select", c3) + three("B01-f head2-over-centered", c4)
            + three("B01-f head2-over-row-select", c5))


# =====================================================================================
# B02 CSV (DESIGN.md 15.6)
# =====================================================================================

DATA = REGRESS / "data"


def pread(name, **kw):
    return pl.read_csv(DATA / name, **kw)


def csv_items(tag, text):
    """csv3: eager read_csv, then the scan collected raw and optimised"""
    return three(tag, text)


@spec("B02_a_read_quoted_empty")
def _():
    a = pdump(pread("B02_a_quoted_empty.csv"))
    one = pdump(pread("B02_a_one_col.csv"))
    num = pdump(pread("B02_a_numeric.csv", schema_overrides={"n": U32}))  # inference: str (see header)
    assert a == columns(("str", "a", ["", None]), ("str", "b", ["x", "z"]))
    return (csv_items("B02-a quoted-empty-vs-null", a) + csv_items("B02-a one-column", one)
            + csv_items("B02-a numeric", num))


@spec("B02_b_write_empty_string")
def _():
    df = pl.DataFrame({"s": ["", None, "x"], "n": [1, 2, 3]}, schema={"s": STR, "n": U32})
    text = df.write_csv()
    assert text == 's,n\n"",1\n,2\nx,3\n'
    d = pdump(df)
    return [("-- B02-b csv", quote(text))] + one("B02-b write", "result", d) + csv_items("B02-b round-trip", d)


@spec("B02_c_scan_prefix")
def _():
    malformed = err("ParseError at line 0: malformed csv")
    bad = err('ParseError at line 5001: column id: cannot parse "x" as u32')
    return (one("B02-c tail-malformed", "eager", malformed)
            + [("-- B02-c tail-malformed scan", "scan ok, schema id:u32, s:str")]
            + lazy2("B02-c tail-malformed", malformed)
            + one("B02-c tail-badvalue", "eager", bad)
            + [("-- B02-c tail-badvalue scan", "scan ok, schema id:u32, s:str")]
            + lazy2("B02-c tail-badvalue", bad))


@spec("B02_d_write_quoting")
def _():
    df = pl.DataFrame({"a,b": ["x,y", 'q"q', " s ", "multi\nline", "cr\rx", "plain"], 'c"d': [1, 2, 3, 4, 5, 6]},
                      schema={"a,b": STR, 'c"d': U32})
    text = df.write_csv()
    d = pdump(df)
    back = pl.read_csv(text.encode())
    # Polars 2.0.0 reads the header "c""d" back as c""d (it does not undouble quotes in names);
    # the cells come back intact
    back.columns = ["a,b", 'c"d']
    assert pdump(back.with_columns(pl.col('c"d').cast(U32))) == d
    return [("-- B02-d csv", quote(text))] + one("B02-d write", "result", d) + csv_items("B02-d round-trip", d)


@spec("B02_f_blank_lines")
def _():
    one_col = pdump(pread("B02_f_one_col.csv", schema_overrides={"a": U32}))
    assert one_col == columns(("u32", "a", [1, None, 3]))
    # departure: Polars gives an all-null middle row; the contract skips the blank line
    two = columns(("u32", "a", [1, 3]), ("str", "b", ["x", "y"]))
    line = err("ParseError at line 4: expected 2 fields, got 1")  # the blank line 3 is counted
    return (csv_items("B02-f one-column", one_col) + csv_items("B02-f two-columns", two)
            + csv_items("B02-f line-number", line))


@spec("B02_g_ragged_rows")
def _():
    return (csv_items("B02-g short-row", err("ParseError at line 3: expected 2 fields, got 1"))
            + csv_items("B02-g long-row", err("ParseError at line 3: expected 2 fields, got 3")))


@spec("B02_h_text_fields")
def _():
    text = pdump(pread("B02_h_text.csv", schema_overrides={"n": U32}))
    crlf = pdump(pread("B02_h_crlf.csv", schema_overrides={"n": U32}))
    line = err("ParseError at line 4: expected 2 fields, got 1")  # record 2 starts on line 4
    return (csv_items("B02-h text", text) + csv_items("B02-h crlf", crlf)
            + csv_items("B02-h line-after-multiline", line))


@spec("B02_j_trim_numeric")
def _():
    assert pread("B02_j_trim.csv").dtypes == [STR, STR]  # Polars: a is str (no trim)
    d = columns(("u32", "a", [1, 2, 3]), ("str", "s", [" s ", "t", "u"]))
    return csv_items("B02-j trim", d)


@spec("B02_k_inference_roundtrip")
def _():
    df = pl.DataFrame({"s": ["007", "1"]})
    back = pl.read_csv(df.write_csv().encode())
    assert back.get_column("s").to_list() == [7, 1]
    return one("B02-k write", "result", pdump(df)) + csv_items("B02-k round-trip", columns(("u32", "s", [7, 1])))


@spec("B02_i_schema_count_src")
def _():
    df = pread("B02_h_crlf.csv", schema_overrides={"n": I32})
    return (one("B02-i count", "eager", err("InvalidOperation: csv schema: 1 dtypes for 2 columns"))
            + one("B02-i explicit", "eager", pdump(df))
            + one("B02-i bad-cell", "eager", err('ParseError at line 2: column s: cannot parse "a,b" as u32')))


# =====================================================================================
# B03 numerics (DESIGN.md 15.5)
# =====================================================================================

def neumaier(xs):
    """15.5.3 in f32 arithmetic (valid cells in row order)"""
    f = np.float32
    s, c = f(0.0), f(0.0)
    with np.errstate(all="ignore"):
        for x in xs:
            x = f(x)
            t = f(s + x)
            if np.isfinite(t):
                c = f(c + (f(f(s - t) + x) if abs(s) >= abs(x) else f(f(x - t) + s)))
            s = t
        return f(s + c) if np.isfinite(s) else s


def cast_err(frm, to, row, cell):
    return err(f"InvalidOperation: cast {frm} to {to}: row {row} holds {cell}")


def raises(series, to):
    try:
        series.cast(to, strict=True)
    except pl.exceptions.InvalidOperationError:
        return True
    return False


@spec("B03_a_group_mean_inf")
def _():
    g = [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 5, 6, 6]
    x = [INF, 1.0, 1.0, INF, INF, -INF, NAN, 1.0, 1e8, 1.0, -1e8, None, None]
    df = pl.DataFrame({"g": g, "x": x}, schema={"g": U32, "x": F32})
    got = pdump(df.group_by("g", maintain_order=True).agg(pl.col("x").mean().alias("m")))
    want = columns(("u32", "g", [1, 2, 3, 4, 5, 6]), ("f32", "m", [INF, INF, NAN, NAN, 1 / 3, None]))
    assert got == want, got
    assert fb(neumaier([1e8, 1.0, -1e8]) / np.float32(3)) == fb(1 / 3)
    return three("B03-a group-mean", want)


@spec("B03_b_eager_fsum_inf")
def _():
    cols = {"p": [INF, 1.0, None], "q": [1.0, INF, None], "r": [INF, -INF, None], "w": [NAN, 1.0, None], "c": [1e8, 1.0, -1e8]}
    df = pl.DataFrame(cols, schema={k: F32 for k in cols})
    sums = df.select([pl.col(k).sum().alias("s" + k) for k in cols])
    means = df.select([pl.col(k).mean().cast(F32).alias("m" + k) for k in cols])
    ws = columns(*[("f32", "s" + k, [v]) for k, v in zip(cols, [INF, INF, NAN, NAN, 1.0])])
    wm = columns(*[("f32", "m" + k, [v]) for k, v in zip(cols, [INF, INF, NAN, NAN, 1 / 3])])
    # Polars agrees except sum(c): its f32 sum answers 0.0; the contract's Neumaier sum gives
    # 1.0, the f64 reference (15.5.3: T2.3 checks against f64, not Polars bits)
    assert [fb(v) for v in sums.row(0)] == [fb(v) for v in [INF, INF, NAN, NAN, 0.0]]
    assert pdump(means) == wm and fb(neumaier(cols["c"])) == fb(1.0)
    return three("B03-b sums", ws) + three("B03-b means", wm)


@spec("B03_c_f32_compare")
def _():
    x = pl.Series("x", [NAN, 1.0, -0.0, 0.0, INF, -INF, None], dtype=F32)
    df = pl.DataFrame({"x": x})
    X = pl.col("x")
    lit = lambda v: pl.lit(v, F32)  # noqa: E731
    out = df.with_columns((X == X).alias("eq"), (X != X).alias("ne"), (X > lit(0.0)).alias("gt0"),
                          (X == lit(0.0)).alias("eq0"), (X < lit(NAN)).alias("ltnan"), (X >= lit(NAN)).alias("genan"),
                          (X <= lit(-0.0)).alias("lenz"), (X < lit(INF)).alias("ltinf"))
    flt = df.filter(X >= lit(NAN))
    return three("B03-c compare", pdump(out)) + three("B03-c filter-ge-nan", pdump(flt))


@spec("B03_d_int_mod_by_zero")
def _():
    d = pl.DataFrame({"a": [7, 7, None, 0], "b": [2, 0, 0, 0], "ai": [7, -7, 5, 0], "bi": [0, 0, 2, 0]},
                     schema={"a": U32, "b": U32, "ai": I32, "bi": I32})
    out = d.select((pl.col("a") % pl.col("b")).alias("m"), (pl.col("ai") % pl.col("bi")).alias("mi"))
    assert pdump(out) == columns(("u32", "m", [1, None, None, None]), ("i32", "mi", [None, None, 1, None]))
    return three("B03-d mod-by-zero", pdump(out))


@spec("B03_e_cast_f32_u32")
def _():
    cases = [("negative", [1.5, -1.5], 1, "-1.5"), ("minus-one", [-1.0], 0, "-1"),
             ("huge", [1e12], 0, "1000000000000"), ("two-pow-32", [4294967296.0], 0, "4294967300"),
             ("nan", [NAN], 0, "nan"), ("inf", [INF], 0, "inf"), ("neg-inf", [-INF], 0, "-inf")]
    items = []
    for name, xs, row, shown in cases:
        assert raises(pl.Series(xs, dtype=F32), U32), name
        items += three(f"B03-e {name}", cast_err("f32", "u32", row, shown))
    ok = pl.Series([-0.5, 4294967040.0, 2.9, None], dtype=F32).cast(U32, strict=True)
    items += three("B03-e valid", columns(("u32", "y", ok.to_list())))
    items += [("-- B03-e negative schema", "y:u32")]
    return items


@spec("B03_f_int_div_refused")
def _():
    items = []
    for name, got in [("u32-div", "u32"), ("i32-div", "i32"), ("f32-div-u32", "u32")]:
        text = f"TypeMismatch in div: expected f32, got {got}"
        items += three(f"B03-f {name}", err(text)) + [(f"-- B03-f {name} schema", "error: " + text)]
    x = pl.Series([1.0, -1.0, 0.0], dtype=F32)
    y = pl.Series([0.0, 0.0, 0.0], dtype=F32)
    q = pl.DataFrame({"q": x / y})
    assert q.dtypes == [F32]
    items += three("B03-f f32-div-f32", pdump(q)) + [("-- B03-f f32-div-f32 schema", "q:f32")]
    return items


@spec("B03_g_int_mean_f32")
def _():
    df = pl.DataFrame({"g": [1, 1, 2, 2], "a": [1, 2, 16777217, 16777219], "ai": [-1, -2, 3, 4]},
                      schema={"g": U32, "a": U32, "ai": I32})
    out = df.group_by("g", maintain_order=True).agg(pl.col("a").mean().alias("ma"), pl.col("ai").mean().alias("mai"))
    assert out.get_column("ma").to_list() == [1.5, 16777218.0]  # f64 in Polars
    # contract: each cell to f32 first, then the f32 sum / count (15.5.3)
    want = columns(("u32", "g", [1, 2]), ("f32", "ma", [1.5, 16777218.0]), ("f32", "mai", [-1.5, 3.5]))
    return three("B03-g int-mean", want)


@spec("B03_h_group_sum_compensated")
def _():
    tenths = [0.1] * 10
    g = [1] * 10 + [2, 2, 2, 3, 3]
    x = tenths + [1e8, 1.0, -1e8, INF, 1.0]
    sums = [neumaier(tenths), neumaier([1e8, 1.0, -1e8]), neumaier([INF, 1.0])]
    assert [fb(v) for v in sums] == ["0x3f800000", "0x3f800000", "0x7f800000"]
    df = pl.DataFrame({"g": g, "x": x}, schema={"g": U32, "x": F32})
    pol = df.group_by("g", maintain_order=True).agg(pl.col("x").sum())
    print("  B03-h Polars group sums:", [fb(v) for v in pol.get_column("x").to_list()], file=sys.stderr)
    want = columns(("u32", "g", [1, 2, 3]), ("f32", "s", sums))
    return three("B03-h group-sum", want) + three("B03-h eager-sum-ten-tenths", columns(("f32", "s", [sums[0]])))


@spec("B03_i_lit_i32_range")
def _():
    items = []
    for name, val in [("max", 2147483647), ("min", -2147483648)]:
        items += three(f"B03-i {name}", columns(("i32", "x", [val]))) + [(f"-- B03-i {name} schema", "x:i32")]
    for name, v in [("too-big", 3000000000), ("two-pow-31", 2147483648), ("neg-too-big", 2147483649)]:
        items += three(f"B03-i {name}", cast_err("u32", "i32", 0, str(v))) + [(f"-- B03-i {name} schema", "x:i32")]
    return items


@spec("B03_j_u32_wrap")
def _():
    df = pl.DataFrame({"g": [1, 1], "a": [4294967295, 1], "ai": [MIN, MAX]}, schema={"g": U32, "a": U32, "ai": I32})
    A, AI = pl.col("a"), pl.col("ai")
    out = df.with_columns((A + pl.lit(1, U32)).alias("a_plus_1"), (pl.lit(0, U32) - A).alias("zero_minus_a"),
                          (A * pl.lit(2, U32)).alias("a_times_2"), (AI - pl.lit(1, I32)).alias("ai_minus_1"),
                          (AI + pl.lit(1, I32)).alias("ai_plus_1"))
    grp = df.group_by("g", maintain_order=True).agg(A.sum().alias("sa"), AI.sum().alias("sai"))
    assert grp.get_column("sa").to_list() == [0] and grp.get_column("sai").to_list() == [-1]
    return three("B03-j arith", pdump(out)) + three("B03-j group-sum", pdump(grp))


@spec("B03_k_n_unique_nan")
def _():
    nneg = float(np.array([0xffc00000], dtype=np.uint32).view(np.float32)[0])
    df = pl.DataFrame({"g": [1] * 6, "x": [NAN, nneg, -0.0, 0.0, 1.0, None]}, schema={"g": U32, "x": F32})
    assert df.select(pl.col("x").n_unique()).item() == 4
    assert df.group_by("g").agg(pl.col("x").n_unique()).get_column("x").to_list() == [4]
    return (three("B03-k select", columns(("u32", "n", [4])))
            + three("B03-k group", columns(("u32", "g", [1]), ("u32", "n", [4]))))


@spec("B03_l_i32_min_mod")
def _():
    df = pl.DataFrame({"a": [MIN] * 3, "b": [-1, 1, MIN]}, schema={"a": I32, "b": I32})
    out = df.with_columns((pl.col("a") % pl.col("b")).alias("m"))
    assert out.get_column("m").to_list() == [0, 0, 0]
    return three("B03-l min-mod", pdump(out))


@spec("B03_m_cast_int_ranges")
def _():
    items = []
    errs = [("f32-i32-two-pow-31", [1.0, 2147483648.0], F32, I32, "f32", "i32", 1, "2147483600"),
            ("f32-i32-below-min", [-2147483904.0], F32, I32, "f32", "i32", 0, "-2147484000"),
            ("f32-i32-nan", [NAN], F32, I32, "f32", "i32", 0, "nan"),
            ("f32-i32-inf", [-INF], F32, I32, "f32", "i32", 0, "-inf")]
    valid = {"f32-i32-valid": ([-2147483648.0, 2147483520.0, -1.9, None], F32, I32, "i32")}
    for name, xs, dt, to, fs, ts, row, shown in errs:
        assert raises(pl.Series(xs, dtype=dt), to), name
        items += three(f"B03-m {name}", cast_err(fs, ts, row, shown))
    xs, dt, to, ts = valid["f32-i32-valid"]
    items += three("B03-m f32-i32-valid", columns((ts, "y", pl.Series(xs, dtype=dt).cast(to).to_list())))
    assert raises(pl.Series([5, 2147483648], dtype=U32), I32)
    items += three("B03-m u32-i32", cast_err("u32", "i32", 1, "2147483648"))
    items += three("B03-m u32-i32-valid", columns(("i32", "y", [0, 2147483647, None])))
    assert raises(pl.Series([5, -1], dtype=I32), U32)
    items += three("B03-m i32-u32", cast_err("i32", "u32", 1, "-1"))
    items += three("B03-m i32-u32-valid", columns(("u32", "y", [0, 2147483647, None])))
    return items


@spec("B03_n_f32_min_max")
def _():
    cols = {"p": [NAN, 2.0, 1.0], "q": [NAN, NAN, None], "v": [1.0, NAN, None], "r": [-0.0, 0.0, None], "w": [0.0, -0.0, None]}
    df = pl.DataFrame({"g": [1, 1, 1], **cols}, schema={"g": U32, **{k: F32 for k in cols}})
    exprs = []
    for k in cols:
        exprs += [pl.col(k).min().alias("min_" + k), pl.col(k).max().alias("max_" + k)]
    sel = df.select(exprs)
    want = [1.0, 2.0, NAN, NAN, 1.0, 1.0, -0.0, 0.0, -0.0, 0.0]
    assert pdump(sel) == columns(*[("f32", c, [v]) for c, v in zip(sel.columns, want)])
    grp = df.group_by("g", maintain_order=True).agg(exprs)
    return three("B03-n select", pdump(sel)) + three("B03-n group", pdump(grp))


@spec("B03_o_i32_mod_sign")
def _():
    df = pl.DataFrame({"a": [7, -7, 7, -7, 6, -1, MAX], "b": [2, 2, -2, -2, -3, 5, MIN]}, schema={"a": I32, "b": I32})
    out = df.with_columns((pl.col("a") % pl.col("b")).alias("m"))
    assert out.get_column("m").to_list() == [1, 1, -1, -1, 0, 4, -1]
    return three("B03-o mod-sign", pdump(out))


@spec("B03_p_cast_str_strict")
def _():
    items = []
    for name, xs, to, ts, row, shown in [("str-u32", ["1", None, "x"], U32, "u32", 2, '"x"'),
                                         ("str-i32-empty", ["-3", ""], I32, "i32", 1, '""'),
                                         ("str-f32", ["1.5", "abc"], F32, "f32", 1, '"abc"'),
                                         ("str-bool", ["true", "False", "yes"], BOOL, "bool", 2, '"yes"')]:
        if to != BOOL:  # Polars refuses str -> bool entirely
            assert raises(pl.Series(xs, dtype=STR), to), name
        items += three(f"B03-p {name}", cast_err("str", ts, row, shown))
    items += three("B03-p str-u32-valid", columns(("u32", "y", pl.Series(["1", None, "4294967295"]).cast(U32).to_list())))
    return items


@spec("B03_q_cast_str_no_trim")
def _():
    items = []
    for name, xs, to, ts, row, shown in [("u32-padded", ["1", " 2 "], U32, "u32", 1, '" 2 "'),
                                         ("u32-plus", ["+5"], U32, "u32", 0, '"+5"'),
                                         ("i32-padded", [" -3"], I32, "i32", 0, '" -3"'),
                                         ("f32-padded", ["2.5 "], F32, "f32", 0, '"2.5 "')]:
        if name != "u32-plus":  # Polars reads "+5" as 5: departure (15.5.5 lists "+5" as failing for u32)
            assert raises(pl.Series(xs, dtype=STR), to), name
        items += three(f"B03-q {name}", cast_err("str", ts, row, shown))
    sp = pl.Series(["nan", "inf", "-inf", "1e3", ".5", "5.", "+5"]).cast(F32, strict=True)
    items += three("B03-q f32-spellings", columns(("f32", "y", sp.to_list())))
    return items


# =====================================================================================
# B04 sources and contracts (DESIGN.md 15.2, 15.4, 15.7)
# =====================================================================================

@spec("B04_a_lazy_reductions")
def _():
    t = pl.DataFrame({"a": [1, 2, 3], "x": [1.0, 2.0, 3.0]}, schema={"a": U32, "x": F32})
    A, X = pl.col("a"), pl.col("x")
    items = []

    def sel(tag, exprs, schema):
        nonlocal items
        items += three(tag, pdump(t.lazy().select(exprs).collect())) + [(f"-- {tag} schema", schema)]

    sel("B04-a C6 sum", [A.sum()], "a:u32")
    sel("B04-a C8 literal-and-sum", [pl.lit(1, U32).alias("one"), A.sum()], "one:u32, a:u32")
    sel("B04-a C10 column-and-sum", [A, A.sum().alias("s")], "a:u32, s:u32")
    sel("B04-a C11 centered", [X - X.mean()], "x:f32")
    sel("B04-a C12 sum-plus-1", [A.sum() + pl.lit(1, U32)], "a:u32")
    items += three("B04-a C13 with-sum", pdump(t.lazy().with_columns(A.sum().alias("s")).collect()))
    items += [("-- B04-a C13 with-sum schema", "a:u32, x:f32, s:u32")]
    for tag, pred in [("B04-a C16 above-mean", X > X.mean()), ("B04-a C17 sum-gt-5", A.sum() > 5), ("B04-a C17 sum-gt-6", A.sum() > 6)]:
        items += three(tag, pdump(t.lazy().filter(pred).collect())) + [(f"-- {tag} schema", "a:u32, x:f32")]
    return items


@spec("B04_b_self_join")
def _():
    t = pl.DataFrame({"k": [1, 2, 2], "v": ["a", "b", "c"]}, schema={"k": U32, "v": STR})
    inner = t.join(t, on="k", maintain_order="left_right")
    left = t.filter(pl.col("v") != "a").join(t, on="k", how="left", maintain_order="left_right")
    assert inner.columns == ["k", "v", "v_right"]
    return (three("B04-b self-inner-join", pdump(inner)) + [("-- B04-b self-inner-join schema", "k:u32, v:str, v_right:str")]
            + three("B04-b self-left-join-filtered", pdump(left)))


@spec("B04_d_bindings")
def _():
    return (lazy2("B04-d missing", err("InvalidOperation: source not in env: u"))
            + [("-- B04-d missing schema", "a:u32")]
            + lazy2("B04-d duplicate", err("InvalidOperation: source bound twice in env: t"))
            + lazy2("B04-d duplicate-before-missing", err("InvalidOperation: source bound twice in env: t"))
            + lazy2("B04-d schema", err("InvalidOperation: source t: data schema [a:u32] differs from the plan's [a:str]")))


@spec("B04_e_frozen_scan_schema")
def _():
    path = "/tmp/bend_frame_regress_B04_e.csv"
    return ([("-- B04-e renamed-column schema", "a:u32, b:u32")]
            + lazy2("B04-e renamed-column", err(f"InvalidOperation: scan_csv {path}: data schema [a:u32, c:u32] differs from the plan's [a:u32, b:u32]"))
            + [("-- B04-e bad-value schema", "a:u32, b:u32")]
            + lazy2("B04-e bad-value", err('ParseError at line 3: column b: cannot parse "x" as u32')))


@spec("B04_g_join_right_key")
def _():
    l = pl.DataFrame({"id": [1, 2, 3], "x": ["a", "b", "c"]}, schema={"id": U32, "x": STR})
    r = pl.DataFrame({"rid": [2, 1], "y": ["two", "one"]}, schema={"rid": U32, "y": STR})
    inner = l.join(r, left_on="id", right_on="rid", maintain_order="left_right")
    left = l.join(r, left_on="id", right_on="rid", how="left", maintain_order="left_right")
    assert inner.columns == ["id", "x", "y"]
    return three("B04-g inner", pdump(inner)) + three("B04-g left", pdump(left))


@spec("B04_h_group_agg_shape")
def _():
    t = pl.DataFrame({"g": [1, 1, 2], "x": [1.0, 3.0, 5.0], "y": [2.0, 2.0, 4.0]}, schema={"g": U32, "x": F32, "y": F32})
    text = 'InvalidOperation: agg expects an aggregation: (col("x").sum() / col("y").sum()).alias("r")'
    w = t.group_by("g", maintain_order=True).agg(pl.col("x").sum().alias("sx"), pl.col("y").sum().alias("sy"))
    w = w.with_columns((pl.col("sx") / pl.col("sy")).alias("r"))
    return (three("B04-h ratio-agg", err(text)) + [("-- B04-h ratio-agg schema", "error: " + text)]
            + three("B04-h workaround", pdump(w)))


@spec("B04_j_cast_barrier")
def _():
    e1 = cast_err("f32", "u32", 1, "-5")
    ok = columns(("u32", "a", [1, 3]), ("f32", "x", [1.0, 3.0]))
    return (three("B04-j filter-over-cast-select", e1) + three("B04-j head-over-cast-select", e1)
            + three("B04-j head-over-cast-with", e1) + three("B04-j cast-filter-over-filter", ok)
            + three("B04-j cast-after-filter-row-index", cast_err("f32", "u32", 0, "-5")))


@spec("B04_k_maintain_order_false")
def _():
    t = pl.DataFrame({"k": ["b", "a", "b", "c"], "v": [1, 2, 3, 4]}, schema={"k": STR, "v": U32})
    return three("B04-k group-unordered", pdump(t.group_by("k", maintain_order=True).agg(pl.col("v").sum().alias("s"))))


# =====================================================================================
# B05 harness
# =====================================================================================

def review_t():
    return pl.DataFrame({"a": [1, 2, None, 4, 5, 6], "b": ["x", "y", "z", "x", "y", "x"],
                         "c": [0.5, 1.5, 2.5, None, 4.5, 5.5], "d": [True, False, True, True, None, True],
                         "e": [0] * 6}, schema={"a": U32, "b": STR, "c": F32, "d": BOOL, "e": U32})


def review_u():
    return pl.DataFrame({"b": ["x", "y", "w", "x"], "label": ["x1", "y1", "w1", "x2"], "c": [10.0, 20.0, 30.0, 40.0]},
                        schema={"b": STR, "label": STR, "c": F32})


@spec("B05_g_optimizer_traps")
def _():
    t = review_t().lazy()
    A = pl.col("a")
    k = lambda v: pl.lit(v, U32)  # noqa: E731
    traps = [
        ("trap1 replace-then-filter", t.with_columns((A * k(10)).alias("a")).filter(A > k(2))),
        ("trap2 swap-aliases", t.select(pl.col("e").alias("a"), A.alias("e")).filter(A > k(0))),
        ("trap3 head-filter-head", t.head(4).filter(pl.col("d")).head(3)),
        ("trap4 head-with-sort", t.sort("a", descending=True, nulls_last=False, maintain_order=True).with_columns((A * k(2)).alias("n")).head(2)),
        ("trap5 literal-select", t.select(k(1).alias("one"))),
        ("trap6 filter-over-group", t.group_by("b", maintain_order=True).agg(A.sum().alias("s")).filter(pl.col("b") == "x")),
        ("trap7 select-over-with", t.with_columns((A * k(2)).alias("n")).select("n")),
        ("trap8 filter-through-alias", t.select(pl.col("c").alias("a")).filter(A > pl.lit(1.0, F32))),
        ("trap9 two-filters", t.with_columns((A * k(2)).alias("n")).filter(pl.col("n") > k(4)).filter(A > k(1))),
        ("trap10 left-join-null-head", t.join(review_u().lazy(), on="b", how="left", maintain_order="left_right").filter(pl.col("label").is_null()).head(2)),
    ]
    items = []
    for name, lf in traps:
        items += three(f"B05-g {name}", pdump(lf.collect()))
    return items


# =====================================================================================
# pending (tests/regress/pending/*.bend.txt: API from M1/M3, see tests/regress/PENDING.md)
# =====================================================================================

@spec("B01_c_zero_column_m3")
def _():
    t = pl.DataFrame({"a": [1, 2, None, 4, 5, 6]}, schema={"a": U32})
    z = t.drop("a")
    return (three("B01-c C22 drop-all", pdump(z))
            + three("B01-c C22 drop-all-then-literal", pdump(z.with_columns(pl.lit(1, U32).alias("o"))))
            + three("B01-c C24 unique-all", pdump(z.unique(maintain_order=True)))
            + three("B01-c C24 concat", pdump(pl.concat([z, z]))))


@spec("B02_e_csv_opts")
def _():
    semi = pdump(pread("B02_e_semicolon.csv", separator=";", schema_overrides={"a": U32}))
    df = pl.DataFrame({"x": [1.0, 2.345], "s": ["a;b", "c"]}, schema={"x": F32, "s": STR})
    text = df.write_csv(separator=";", include_header=False, float_precision=2)
    assert text == '1.00;"a;b"\n2.35;c\n'
    back = pl.read_csv(text.encode(), separator=";", has_header=False, schema_overrides={"column_0": F32})
    return three("B02-e semicolon", semi) + one("B02-e written", "eager", pdump(back))


@spec("B02_i_read_csv_schema")
def _():
    return (one("B02-i count", "eager", err("InvalidOperation: csv schema: 1 dtypes for 2 columns"))
            + one("B02-i explicit", "eager", pdump(pread("B02_h_crlf.csv", schema_overrides={"n": I32})))
            + one("B02-i bad-cell", "eager", err('ParseError at line 2: column s: cannot parse "a,b" as u32'))
            + one("B02-i quoted-empty", "eager", pdump(pread("B02_a_numeric.csv", schema_overrides={"n": STR})))
            + one("B02-i quoted-empty-u32", "eager", pdump(pread("B02_a_numeric.csv", schema_overrides={"n": U32}))))


@spec("B03_d_floor_div")
def _():
    d = pl.DataFrame({"a": [7, 7, None, 0, 9, 4294967295, 1], "b": [2, 0, 0, 0, 3, 2, None],
                      "ai": [7, -7, 7, -7, MIN, 5, 0], "bi": [2, 2, -2, -2, -1, 0, 0]},
                     schema={"a": U32, "b": U32, "ai": I32, "bi": I32})
    q = (d["a"] // d["b"]).to_list()
    qi = (d["ai"] // d["bi"]).to_list()
    assert qi[4] == MIN
    qi[4] = None  # MIN // -1: null in the contract, MIN in Polars (15.5.1 departure)
    t1 = "TypeMismatch in floor_div: expected u32 or i32, got f32"
    t2 = "TypeMismatch in floor_div: expected u32, got i32"
    return (three("B03-d floor-div", columns(("u32", "q", q), ("i32", "qi", qi)))
            + three("B03-f floor-div-f32", err(t1)) + [("-- B03-f floor-div-f32 schema", "error: " + t1)]
            + three("B03-f floor-div-mixed", err(t2)) + [("-- B03-f floor-div-mixed schema", "error: " + t2)])


@spec("B03_e_try_cast")
def _():
    x = pl.Series([1.5, -1.5, 1e12, NAN, INF, -0.5, None], dtype=F32).cast(U32, strict=False).to_list()
    s_ = pl.Series(["1", " 2 ", "x", "+5", None, "4294967295", ""]).cast(U32, strict=False).to_list()
    assert s_[3] == 5
    s_[3] = None  # "+5": U32.read refuses it (15.5.5); Polars reads 5
    big = pl.Series([2147483648.0, -2147483648.0, NAN, 1.9, -1.9, None, 0.0], dtype=F32).cast(I32, strict=False).to_list()
    u = pl.Series([2147483648, 5, None, 0, 2147483647, 4294967295, 1], dtype=U32).cast(I32, strict=False).to_list()
    d = columns(("u32", "x_u32", x), ("u32", "s_u32", s_), ("i32", "big_i32", big), ("i32", "u_i32", u))
    return (three("B03-e try-cast", d) + [("-- B03-e try-cast schema", "x_u32:u32, s_u32:u32, big_i32:i32, u_i32:i32")]
            + [("-- B03-e try-cast-refused schema", "error: TypeMismatch in try_cast: expected castable to bool, got u32")])


@spec("B03_i_checked_i32")
def _():
    return [("-- B03-i checked", "5\n2147483647\nerror: InvalidOperation: i32 out of range: 2147483648\n"
             "-2147483648\nerror: InvalidOperation: i32 out of range: 2147483649\n-1")]


@spec("B04_c_add_source")
def _():
    l = pl.DataFrame({"id": [1, 2, 3], "x": ["a", "b", "c"]}, schema={"id": U32, "x": STR})
    r = pl.DataFrame({"id": [3, 1], "y": [0.5, 1.5]}, schema={"id": U32, "y": F32})
    return three("B04-c two-sources", pdump(l.join(r, on="id", maintain_order="left_right")))


@spec("B04_d_validate_bindings")
def _():
    return [("-- B04-d ok", "ok"), ("-- B04-d missing", "error: InvalidOperation: source not in env: u"),
            ("-- B04-d duplicate", "error: InvalidOperation: source bound twice in env: t"),
            ("-- B04-d duplicate-before-missing", "error: InvalidOperation: source bound twice in env: t"),
            ("-- B04-d schema", "error: InvalidOperation: source t: data schema [a:u32] differs from the plan's [a:str]"),
            ("-- B04-d self-join-ok", "ok")]


@spec("B04_i_row_cap")
def _():
    cap = 8388608
    assert 2900 * 2900 == 8410000 > cap
    assert 65536 * 65536 == 2**32  # the wrapped sum is 0: the join saturates at 2**32 - 1 instead
    over = lambda n, c: err(f"InvalidOperation: too many rows: {n} exceeds {c}")
    ones4 = frame([("u32", "x")], [[1]] * 4)
    return ([("-- B04-i guard", f"{cap}\nnone\nsome InvalidOperation: too many rows: {cap + 1} exceeds {cap}\n"
                                f"some InvalidOperation: too many rows: {2**32 - 1} exceeds {cap}\nnone\n"
                                "some InvalidOperation: too many rows: 6 exceeds 5")]
            + one("B04-i join", "eager", over(8410000, cap))
            + one("B04-i left-join", "eager", over(8410000, cap))
            + one("B04-i join-wrap", "eager", over(2**32 - 1, cap))
            + one("B04-i join-under", "eager", frame([("u32", "k")], [[1]] * 6))
            + one("B04-i group-by", "eager", over(cap + 1, cap))
            + one("B04-i group-by-under", "eager", frame([("u32", "k"), ("u32", "n")], [[1, 3]]))
            + [("-- B04-i from_scalars over", over(4, 3)), ("-- B04-i from_scalars at-cap", ones4),
               ("-- B04-i from_scalars over-bad-dtype", over(4, 3)), ("-- B04-i from_scalars default-cap", ones4)]
            + one("B04-i csv over", "eager", over(4, 3))
            + one("B04-i csv at-cap", "eager", frame([("u32", "a")], [[1], [2], [3], [4]]))
            + one("B04-i csv over-explicit-dtypes", "eager", over(4, 3))
            + one("B04-i csv no-header", "eager", over(3, 2))
            + one("B04-i csv blank-lines-not-counted", "eager", frame([("u32", "a"), ("u32", "b")], [[1, 2], [3, 4]]))
            + one("B04-i csv header-only", "eager", frame([("str", "a"), ("str", "b")], []))
            + one("B04-i csv ragged-before-cap", "eager", err("ParseError at line 3: expected 2 fields, got 1"))
            + one("B04-i csv default-cap", "eager", frame([("u32", "a")], [[1], [2]])))


# concat_vertical (M3) waits in pending/B04_i_concat_cap.bend.txt
@spec("B04_i_concat_cap")
def _():
    cap = 8388608
    return (one("B04-i concat-zero-col", "eager", err(f"InvalidOperation: too many rows: {cap + 1} exceeds {cap}"))
            + one("B04-i concat-at-cap", "eager", frame([], [], height=cap))
            + one("B04-i concat-wrap", "eager", err(f"InvalidOperation: too many rows: {2**32 - 1} exceeds {cap}")))


# M1 B02 review leftovers (DESIGN.md 14, 15.6.2 / 15.6.3). Polars 2.0.0: `\n\na,b\n1,2\n` reads a:1 b:2
# (leading blank lines skipped with a header; without one they are null records); the separator
# refusal and the dtype count on an empty file are contract decisions (no Polars counterpart).
@spec("B02_m_sep_lead_blank_empty_schema")
def _():
    sep = err("InvalidOperation: csv: separator must not be a double quote, CR or LF")
    ab = frame([("u32", "a"), ("u32", "b")], [[1, 2]])
    count = lambda d: err(f"InvalidOperation: csv schema: {d} dtypes for 0 columns")
    return (one("B02-m lead-blank", "eager", ab)
            + one("B02-m lead-blank-crlf", "eager", ab)
            + one("B02-m lead-blank-only", "eager", frame([], [], height=0))
            + one("B02-m lead-blank-one-col", "eager", frame([("u32", "1")], [[2]]))
            + one("B02-m lead-blank-no-header", "eager", frame([("u32", "column_0")], [[None], [1], [2]]))
            + one("B02-m inner-blank-unchanged", "eager", frame([("u32", "a")], [[None], [1]]))
            + one("B02-m lead-blank-line-numbers", "eager", err("ParseError at line 5: expected 2 fields, got 1"))
            + one("B02-m lead-blank-explicit", "eager", frame([("u32", "a"), ("str", "b")], [[1, "x"]]))
            + [("-- B02-m infer-lead-blank", "a:u32 b:str ")]
            + one("B02-m sep-quote", "eager", sep)
            + one("B02-m sep-lf", "eager", sep)
            + one("B02-m sep-cr", "eager", sep)
            + one("B02-m sep-explicit-schema", "eager", sep)
            + [("-- B02-m sep-infer", "error InvalidOperation: csv: separator must not be a double quote, CR or LF")]
            + one("B02-m sep-tab-ok", "eager", ab)
            + one("B02-m sep-semicolon-ok", "eager", ab)
            + one("B02-m sep-read-file", "eager", sep)
            + lazy2("B02-m sep-scan", sep)
            + one("B02-m sep-write", "eager", sep)
            + one("B02-m sep-write-cr", "eager", sep)
            + one("B02-m empty-schema-none", "eager", frame([], [], height=0))
            + one("B02-m empty-schema-count", "eager", count(2))
            + one("B02-m empty-schema-count-no-header", "eager", count(1))
            + one("B02-m blank-only-schema-count", "eager", count(1))
            # no header: the width is the first non-blank record's; a blank line in k > 1 columns is
            # skipped (15.6.2 D; Polars gives an all-null row), in 1 column it is a null row
            + one("B02-m nohdr-lead-blank-wide", "eager", frame([("u32", "column_0"), ("u32", "column_1")], [[1, 2], [3, 4]]))
            + one("B02-m nohdr-lead-blank-ragged", "eager", err("ParseError at line 4: expected 2 fields, got 1"))
            + one("B02-m nohdr-blank-only", "eager", frame([("str", "column_0")], [[None], [None]]))
            + [("-- B02-m nohdr-infer-lead-blank", "column_0:u32 column_1:str ")]
            # the separator is refused before the file is opened (read like scan)
            + one("B02-m sep-read-missing-file", "eager", sep)
            + one("B02-m sep-read-schema-missing-file", "eager", sep))


# =====================================================================================
# Defects found by the differential generator (bench/diff; DESIGN.md 15.10 NEW-*)
# =====================================================================================

# NEW-1: every eager verb makes all its static checks before it evaluates data (DESIGN.md 15.9
# order of errors); the 15.9 admissibility rule: a later verb's static error vs an earlier
# verb's data error differ between eager (verb by verb) and lazy (the whole plan typed first).
@spec("NEW_1_static_checks_first")
def _():
    bad = cast_err("str", "f32", 0, quote("caf\u00e9"))
    dup = lambda n: err(f"DuplicateColumn: {n}")
    return (three("NEW-1 select-dup-after-cast", dup("x"))
            + three("NEW-1 select-cast-is-the-dup", dup("a"))
            + three("NEW-1 group-by-agg-dup", dup("b"))
            + three("NEW-1 group-by-key-cast-dup", dup("k"))
            + three("NEW-1 group-by-dup-before-cap", dup("k"))
            + three("NEW-1 sort-first-missing-key", err("ColumnNotFound: p"))
            + three("NEW-1 with-columns-dup-after-cast", dup("x"))
            + three("NEW-1 filter-type-before-cast", err("TypeMismatch in filter: expected bool, got f32"))
            + three("NEW-1 join-clash-before-cap", dup("v_right"))
            + one("NEW-1 15.9-inadmissible", "eager", bad)
            + lazy2("NEW-1 15.9-inadmissible", err("ColumnNotFound: p")))


def summary(text: str) -> str:
    """what tests/regress/NEW_2_*.bend prints for a dump: chars, lines, FNV-1a over code points"""
    h = 2166136261
    for ch in text:
        h = ((h ^ ord(ch)) * 16777619) & 0xFFFFFFFF
    return f"chars {len(text)} lines {text.count(chr(10))} fnv {h}"


# NEW-2: results of >= 2^15 rows in the interpreter. Built here with plain Python (the join is
# left rows in order, each with its matches in right order; DESIGN.md 15.2.4).
@spec("NEW_2_interp_large_results")
def _():
    n = 780
    t = [(i % 3, f"s{i}", np.float32(i) / np.float32(4.0)) for i in range(n)]
    j = [(k, s, x, s2, x2) for (k, s, x) in t for (k2, s2, x2) in t if k2 == k]
    assert len(j) == 3 * 260 ** 2 == 202800
    jcols = [("u32", "k"), ("str", "s"), ("f32", "x"), ("str", "s_right"), ("f32", "x_right")]
    jsum = summary(frame(jcols, j))
    vs = [None if i % 7 == 3 else i for i in range(70000)]
    groups = []
    for k in (0, 1, 2):  # first appearance: left row 0 has k = 0
        g = [r for r in j if r[0] == k]
        groups.append([k, len(g), neumaier([r[2] for r in g]), len({r[3] for r in g}), max(r[1] for r in g)])
    gb = frame([("u32", "k"), ("u32", "n"), ("f32", "sx"), ("u32", "u"), ("str", "ms")], groups)
    top = sorted(j, key=lambda r: r[3])          # stable: s_right ascending, then x descending
    top = sorted(top, key=lambda r: -r[2])[:3]
    return ([("-- NEW-2 from-scalars-70000 eager", summary(frame([("u32", "v")], [[v] for v in vs])))]
            + three("NEW-2 self-join-202800", jsum)
            + three("NEW-2 self-join-group-by", gb)
            + three("NEW-2 self-join-sort-head", frame(jcols, top)))


def main(argv) -> int:
    write = "--write" in argv
    pats = [a for a in argv if not a.startswith("--")]
    bad = 0
    for name, f in sorted(SPECS.items()):
        if pats and not any(p in name for p in pats):
            continue
        path = REGRESS / f"{name}.bend"
        if not path.exists():  # an M1/M3 API test waiting in pending/ (tests/regress/PENDING.md)
            path = REGRESS / "pending" / f"{name}.bend.txt"
        with open(path, encoding="utf-8", newline="") as fh:
            src = fh.read()
        lines = src.split("\n")
        first = next((i for i, l in enumerate(lines) if l.startswith("#|")), len(lines))
        code = "\n".join(lines[:first]).rstrip("\n") + "\n"
        want = block(f())
        have = "\n".join(lines[first:])
        if have.rstrip("\n") + "\n" == want:
            print(f"ok      {name}")
            continue
        if write:
            with open(path, "w", encoding="utf-8", newline="") as fh:
                fh.write(code + want)
            print(f"written {name}")
        else:
            print(f"DIFFERS {name}")
            bad += 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
