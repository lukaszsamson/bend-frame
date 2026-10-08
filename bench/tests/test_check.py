"""Tests for bench/check.py (the typed comparator) and bench/dump_polars.py.

Run:  cd bench && uv run python tests/test_check.py        (plain asserts, no pytest needed)
  or: cd bench && uv run python -m pytest tests            (when pytest is installed)

The comparator is tested with intentional mismatches: it must exit 1 on each of them.
"""
import io
import contextlib
import math
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

import check  # noqa: E402
import dump_polars  # noqa: E402
import polars as pl  # noqa: E402

REPO = os.path.dirname(os.path.dirname(HERE))


# ---- helpers ------------------------------------------------------------------------------

def csv_diffs(got, want, **kw):
    """Diff lines for two CSV texts given as lists of rows."""
    return check.compare_csv_rows(got, want, **kw)[0]


def run_cli(args):
    """check.main(args) -> (exit code, stdout)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = check.main(args)
    return rc, buf.getvalue()


def write_tmp(dirname, name, text):
    path = os.path.join(dirname, name)
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    return path


def frame_dump(cols, rows, height=None):
    """A dump text: cols = [(dtype, name_quoted)], rows = [[cell text]]."""
    h = len(rows) if height is None else height
    lines = ["frame", f"height\t{h}", f"width\t{len(cols)}"]
    lines += [f"col\t{t}\t{n}" for t, n in cols]
    if cols:
        lines += ["row\t" + "\t".join(r) for r in rows]
    return "\n".join(lines) + "\n"


# ---- CSV mode: regressions ----------------------------------------------------------------

def test_100000_vs_100001_fails():
    # the old comparator parsed both as floats: rel 1e-5 <= rtol 1e-5 passed
    got = [["n"], ["100000"]]
    want = [["n"], ["100001"]]
    assert csv_diffs(got, want) and csv_diffs(got, want, rtol=1e-5)
    assert csv_diffs(got, want, ulp=4)  # ulp tolerance never applies to ints


def test_nan_vs_integer_fails():
    # the old comparator: rel = nan, `nan > rtol` is False, so it passed
    for kw in ({}, {"rtol": 1e-5}, {"ulp": 8}):
        assert csv_diffs([["n"], ["nan"]], [["n"], ["5"]], **kw), kw
        assert csv_diffs([["n"], ["5"]], [["n"], ["nan"]], **kw), kw
        # a float column too
        assert csv_diffs([["x"], ["NaN"]], [["x"], ["5.0000"]], **kw), kw
        assert csv_diffs([["x"], ["5.0000"]], [["x"], ["NaN"]], **kw), kw


def test_nan_equals_only_nan():
    assert not csv_diffs([["x"], ["NaN"], ["1.5000"]], [["x"], ["nan"], ["1.5000"]])
    assert not csv_diffs([["x"], ["-nan"]], [["x"], ["NaN"]])
    assert csv_diffs([["x"], ["inf"]], [["x"], ["NaN"]])


def test_infinities():
    assert not csv_diffs([["x"], ["inf"], ["-inf"]], [["x"], ["inf"], ["-inf"]])
    assert csv_diffs([["x"], ["inf"]], [["x"], ["-inf"]])
    assert csv_diffs([["x"], ["inf"]], [["x"], ["1.0000"]], rtol=0.5)
    assert csv_diffs([["x"], ["3.4e38"]], [["x"], ["inf"]], ulp=1000)


def test_signed_zero_modes():
    got, want = [["x"], ["-0.0000"], ["1.5000"]], [["x"], ["0.0000"], ["1.5000"]]
    assert csv_diffs(got, want)                                  # strict (default)
    assert csv_diffs(got, want, ulp=4)                           # a tolerance does not excuse a sign
    assert not csv_diffs(got, want, signed_zero="ignore")
    assert not csv_diffs(want, want)
    assert not csv_diffs(got, got)


def test_ulp_and_rtol_for_floats():
    one, next_up = "1.0", repr(float.fromhex("0x1.000002p+0"))   # 1 ulp apart in f32
    assert csv_diffs([["x"], [next_up]], [["x"], [one]])                 # exact by default
    assert not csv_diffs([["x"], [next_up]], [["x"], [one]], ulp=1)
    assert csv_diffs([["x"], ["1.0000050"]], [["x"], [one]], ulp=1)      # ~42 ulp apart
    assert not csv_diffs([["x"], ["1.0000050"]], [["x"], [one]], rtol=1e-5)
    assert csv_diffs([["x"], ["1.0001000"]], [["x"], [one]], rtol=1e-5)
    # the ulp distance crosses zero correctly: -tiny vs +tiny are 2 apart
    assert not csv_diffs([["x"], ["1e-45"]], [["x"], ["-1e-45"]], ulp=2)
    assert csv_diffs([["x"], ["1e-45"]], [["x"], ["-1e-45"]], ulp=1)


def test_float_inexact_count():
    diffs, inexact = check.compare_csv_rows([["x"], ["1.00001"]], [["x"], ["1.00000"]], rtol=1e-4)
    assert diffs == [] and inexact == 1
    diffs, inexact = check.compare_csv_rows([["x"], ["1.0"]], [["x"], ["1.00"]])
    assert diffs == [] and inexact == 1   # different text, equal value: counted, not an error


def test_strings_bools_exact():
    assert not csv_diffs([["s", "b"], ["a", "true"]], [["s", "b"], ["a", "true"]])
    assert csv_diffs([["s"], ["a"]], [["s"], ["b"]])
    assert csv_diffs([["s"], ["1.0"]], [["s"], ["one"]], rtol=1.0)    # a string column is never numeric
    assert csv_diffs([["b"], ["false"]], [["b"], ["true"]])
    assert csv_diffs([["s"], [""]], [["s"], ["a"]])                   # null vs value
    assert csv_diffs([["x"], [""]], [["x"], ["1.5000"]], rtol=1.0)
    assert not csv_diffs([["x"], [""]], [["x"], [""]])


def test_int_column_rejects_non_integers():
    assert csv_diffs([["n"], ["1.0"]], [["n"], ["1"]])
    assert csv_diffs([["n"], ["abc"]], [["n"], ["1"]])
    assert not csv_diffs([["n"], ["-12"]], [["n"], ["-12"]])


def test_header_and_shape():
    assert csv_diffs([["a", "b"], ["1", "2"]], [["a", "c"], ["1", "2"]])         # name
    assert csv_diffs([["b", "a"], ["1", "2"]], [["a", "b"], ["2", "1"]])         # order
    assert csv_diffs([["a"], ["1"]], [["a"], ["1"], ["2"]])                      # row count
    assert csv_diffs([["a"], ["1"], ["2"]], [["a"], ["1"]])
    assert csv_diffs([["a", "b"], ["1"]], [["a", "b"], ["1", "2"]])              # ragged
    assert csv_diffs([], [["a"]]) and csv_diffs([["a"]], [])
    assert not csv_diffs([], [])
    assert not csv_diffs([["a"]], [["a"]])                                       # header only


def test_csv_module_quoting():
    with tempfile.TemporaryDirectory() as d:
        a = write_tmp(d, "a.csv", 'k,s\n1,"x,y"\n2,"line1\nline2"\n3,"say ""hi"""\n')
        b = write_tmp(d, "b.csv", 'k,s\n1,"x,y"\n2,"line1\nline2"\n3,"say ""hi"""\n')
        c = write_tmp(d, "c.csv", 'k,s\n1,"x,y"\n2,"line1\nline2"\n3,"say ""ho"""\n')
        assert run_cli([a, b])[0] == 0
        rc, out = run_cli([a, c])
        assert rc == 1 and "MISMATCH" in out and "'k'" not in out and "'s'" in out


def test_cli_exit_codes():
    with tempfile.TemporaryDirectory() as d:
        a = write_tmp(d, "a.csv", "n,x\n100000,1.5000\n")
        b = write_tmp(d, "b.csv", "n,x\n100001,1.5000\n")
        ok = write_tmp(d, "ok.csv", "n,x\n100000,1.5000\n")
        assert run_cli([a, ok]) == (0, "identical\n")
        rc, out = run_cli([a, b, "--rtol", "1e-3", "--ulp", "100"])
        assert rc == 1 and "ints differ" in out
        assert run_cli([a, os.path.join(d, "missing.csv")])[0] == 2   # unusable input, nonzero
        assert run_cli([os.path.join(d, "missing.csv"), a])[0] == 2


def test_diff_report_is_capped_and_located():
    got = [["n"]] + [[str(i)] for i in range(100)]
    want = [["n"]] + [[str(i + 1)] for i in range(100)]
    diffs = csv_diffs(got, want)
    assert len(diffs) == check.MAX_DIFFS + 1 and diffs[-1].startswith("... 80 more")
    assert diffs[0].startswith("line 2, column 'n' (int): '0' vs '1'")


def test_int_cells_are_ascii_text_exact():
    # review of M0: INT_RE used `$` (matches before a trailing newline) and `\d` (any script's
    # digits), so a quoted "5\n" cell or Arabic-Indic digits passed as 5; ints compare as text
    assert csv_diffs([["n"], ["5\n"]], [["n"], ["5"]])
    assert csv_diffs([["n"], ["\u0665"]], [["n"], ["5"]])
    assert csv_diffs([["n"], ["007"]], [["n"], ["7"]])
    assert csv_diffs([["n"], ["+7"]], [["n"], ["7"]])
    assert csv_diffs([["x"], ["1.5\n"]], [["x"], ["1.5"]])
    assert csv_diffs([["x"], [" 1.5"]], [["x"], ["1.5"]])      # no whitespace stripping
    assert csv_diffs([["x"], ["nan "]], [["x"], ["nan"]])


# ---- dump mode ----------------------------------------------------------------------------

BASE_COLS = [("u32", '"id"'), ("f32", '"x"'), ("str", '"s"')]
BASE_ROWS = [["1", "0x3f800000", '""'], ["2", "null", "null"], ["3", "0x80000000", '"a\\tb"']]
BASE = frame_dump(BASE_COLS, BASE_ROWS)


def dump_diffs(a, b, **kw):
    return check.compare_dumps(a, b, **kw)


def test_dump_equal_and_parse():
    assert dump_diffs(BASE, BASE) == []
    assert dump_diffs(BASE, BASE + "\n") == []          # IO.print's extra newline
    kind, d = check.parse_dump(BASE)
    assert kind == "frame" and d["height"] == 3 and d["width"] == 3
    assert d["cols"] == [("u32", "id"), ("f32", "x"), ("str", "s")]
    assert d["rows"][2] == [3, 0x80000000, "a\tb"] and d["rows"][1] == [2, None, None]
    assert d["rows"][0][2] == ""            # "" is a value, null is None


def test_dump_intentional_mismatches():
    def mutate(old, new):
        assert old in BASE
        return BASE.replace(old, new, 1)

    cases = {
        "changed cell": mutate("row\t2\t", "row\t9\t"),
        "changed name": mutate('"x"', '"y"'),
        "changed dtype": mutate("col\tf32", "col\tu32").replace("0x3f800000", "7").replace("0x80000000", "8"),
        "empty string vs null": mutate('0x3f800000\t""', "0x3f800000\tnull"),
        "null vs empty string": mutate("2\tnull\tnull", "2\tnull\t\"\""),
        "-0.0 vs 0.0": mutate("0x80000000", "0x00000000"),
        "extra row": BASE.replace("height\t3", "height\t4") + "row\t4\tnull\tnull\n",
        "swapped columns": frame_dump([BASE_COLS[1], BASE_COLS[0], BASE_COLS[2]],
                                      [[r[1], r[0], r[2]] for r in BASE_ROWS]),
        "string differs": mutate('"a\\tb"', '"a b"'),
        "ulp apart": mutate("0x3f800000", "0x3f800001"),
    }
    for label, other in cases.items():
        assert dump_diffs(BASE, other), label
        assert dump_diffs(other, BASE), label
        with tempfile.TemporaryDirectory() as d:
            rc, _ = run_cli(["--dump", write_tmp(d, "a", BASE), write_tmp(d, "b", other)])
            assert rc == 1, label


def test_dump_nan_payloads_compare_equal():
    nan_a, nan_b, num = "0x7fc00000", "0x7f800001", "0x3f800000"
    one = frame_dump([("f32", '"f"')], [[nan_a], [num]])
    two = frame_dump([("f32", '"f"')], [[nan_b], [num]])
    neg = frame_dump([("f32", '"f"')], [["0xffc00000"], [num]])
    assert dump_diffs(one, two) == [] and dump_diffs(one, neg) == []
    # NaN is never a number, and a number is never NaN
    assert dump_diffs(one, frame_dump([("f32", '"f"')], [[num], [num]]))
    assert dump_diffs(one, frame_dump([("f32", '"f"')], [["null"], [num]]))
    assert dump_diffs(one, frame_dump([("f32", '"f"')], [["0x7f800000"], [num]]))   # +inf


def test_dump_ulp_and_signed_zero_options():
    a = frame_dump([("f32", '"f"')], [["0x3f800000"]])
    b = frame_dump([("f32", '"f"')], [["0x3f800002"]])
    assert dump_diffs(a, b) and not dump_diffs(a, b, ulp=2) and dump_diffs(a, b, ulp=1)
    z = frame_dump([("f32", '"f"')], [["0x80000000"]])
    p = frame_dump([("f32", '"f"')], [["0x00000000"]])
    assert dump_diffs(z, p) and dump_diffs(z, p, ulp=5)
    assert not dump_diffs(z, p, signed_zero="ignore")
    # ulp never applies to integer or string cells
    ia = frame_dump([("u32", '"n"')], [["100000"]])
    ib = frame_dump([("u32", '"n"')], [["100001"]])
    assert dump_diffs(ia, ib, ulp=10)


def test_dump_ulp_never_reaches_infinity():
    # review of M0: FLT_MAX (0x7f7fffff) is 1 ulp from +inf (0x7f800000) in the ordered key
    for big, inf in (("0x7f7fffff", "0x7f800000"), ("0xff7fffff", "0xff800000")):
        a = frame_dump([("f32", '"f"')], [[big]])
        b = frame_dump([("f32", '"f"')], [[inf]])
        assert dump_diffs(a, b, ulp=1) and dump_diffs(b, a, ulp=1000)
    assert not check.bits_equal(0x7F800000, 0x7F7FFFFF, ulp=10)
    assert check.bits_equal(0x7F800000, 0x7F800000, ulp=10)


def test_dump_rejects_non_canonical_text():
    # review of M0: two different dump texts must not compare equal (15.1: byte-exact but NaN)
    one = frame_dump([("u32", '"n"'), ("i32", '"i"'), ("str", '"s"')], [["7", "-3", '"A\\x01"']])
    variants = [
        one.replace("row\t7", "row\t007"),                 # padded u32
        one.replace("row\t7", "row\t-7"),                  # signed u32 (was accepted)
        one.replace("row\t7", "row\t4294967296"),          # u32 out of range
        one.replace("\t-3\t", "\t-03\t"),                  # padded i32
        one.replace("\t-3\t", "\t2147483648\t"),           # i32 out of range
        one.replace('"A\\x01"', '"\\x41\\x01"'),           # \x for a printable char
        one.replace('"A\\x01"', '"A\x01"'),                 # raw control character
        one.replace('"A\\x01"', '"A\\x09"'),                # \x09 instead of \t
        one.replace("height\t1", "height\t01"),
        one.replace("height\t1", "height\t1_0"),           # int() accepts underscores
    ]
    assert check.parse_dump(one)
    for v in variants:
        assert v != one
        try:
            diffs = check.compare_dumps(one, v)
        except check.DumpError:
            continue
        raise AssertionError(f"accepted {v!r} as equal-or-comparable: {diffs}")
    # a column's dtype is checked even with no rows
    try:
        check.parse_dump(frame_dump([("u64", '"n"')], []))
    except check.DumpError:
        pass
    else:
        raise AssertionError("accepted dtype u64")


def test_dump_marks_inconsistent_heights():
    # tests/dump_malformed.bend: Bend's dump of a column longer / shorter than the height
    longer = "frame\nheight\t1\nwidth\t1\ncol\tu32\t\"a\"\nrow\t1\nexcess\n"
    shorter = "frame\nheight\t3\nwidth\t1\ncol\tu32\t\"a\"\nrow\t1\nrow\t2\nrow\t?\n"
    valid = "frame\nheight\t1\nwidth\t1\ncol\tu32\t\"a\"\nrow\t1\n"
    for bad in (longer, shorter):
        with tempfile.TemporaryDirectory() as d:
            assert run_cli(["--dump", write_tmp(d, "a", bad), write_tmp(d, "b", valid)])[0] == 2


def test_dump_errors_and_shapes():
    e1 = "error\tColumnNotFound: a\n"
    e2 = "error\tColumnNotFound: b\n"
    assert dump_diffs(e1, e1) == [] and dump_diffs(e1, e2)
    assert dump_diffs(e1, BASE) and dump_diffs(BASE, e1)
    # a zero-column frame keeps its height, which tells select([]) from an empty frame
    z3 = "frame\nheight\t3\nwidth\t0\n"
    z0 = "frame\nheight\t0\nwidth\t0\n"
    assert dump_diffs(z3, z3) == [] and dump_diffs(z3, z0)
    # zero rows, with columns
    zr = frame_dump([("u32", '"a"'), ("str", '"s"')], [])
    assert dump_diffs(zr, zr) == [] and dump_diffs(zr, z0)


def test_dump_malformed_is_an_error():
    bad = [
        "",
        "frame\nheight\t1\nwidth\t1\ncol\tu32\t\"a\"\nrow\t1\t2\n",         # too many cells
        "frame\nheight\t2\nwidth\t1\ncol\tu32\t\"a\"\nrow\t1\n",            # missing row
        "frame\nheight\t1\nwidth\t1\ncol\tu32\t\"a\"\nrow\tx\n",            # bad u32
        "frame\nheight\t1\nwidth\t1\ncol\tf32\t\"a\"\nrow\t1.0\n",          # f32 must be bits
        "frame\nheight\t1\nwidth\t1\ncol\tstr\t\"a\"\nrow\tab\n",           # unquoted string
        "frame\nheight\t1\nwidth\t0\nrow\t\n",                              # row in a zero-column frame
        "table\n",
    ]
    for text in bad:
        try:
            check.parse_dump(text if text.endswith("\n") or not text else text + "\n")
        except check.DumpError:
            continue
        except ValueError:
            continue
        raise AssertionError(f"accepted malformed dump {text!r}")
    with tempfile.TemporaryDirectory() as d:
        p = write_tmp(d, "bad", "frame\nheight\t1\n")
        assert run_cli(["--dump", p, p])[0] == 2


def test_unquote_roundtrip_with_polars_quote():
    samples = ["", "plain", 'q"uote', "back\\slash", "tab\there", "nl\nx\r", "\x01\x1f\x7f", "café 中",
               '\\"', "a\\x41", " "]
    for s in samples:
        q = dump_polars.quote(s)
        assert "\t" not in q and "\n" not in q and "\r" not in q
        assert check.unquote(q) == s, s


# ---- Polars-side dumper -------------------------------------------------------------------

def bend_expected(section):
    """The `#|` lines of tests/dump_basic.bend for one `-- section` (what Bend's DF.dump printed)."""
    with open(os.path.join(REPO, "tests", "dump_basic.bend"), encoding="utf-8") as f:
        lines = [l[2:].rstrip("\n") for l in f if l.startswith("#|")]
    start = lines.index(f"-- {section}") + 1
    end = next((i for i in range(start, len(lines)) if lines[i].startswith("-- ")), len(lines))
    body = [l for l in lines[start:end]]
    while body and body[-1] == "":
        body.pop()
    return "\n".join(body) + "\n"


def test_polars_dump_matches_bend_wide():
    nan = float("nan")
    df = pl.DataFrame({
        "b": pl.Series([True, None, False, True], dtype=pl.Boolean),
        "u": pl.Series([0, 4294967295, None, 7], dtype=pl.UInt32),
        "i": pl.Series([-2, None, -2147483648, 0], dtype=pl.Int32),
        "f": pl.Series([1.0, None, -0.0, 0.0], dtype=pl.Float32),
        "s": pl.Series(["", None, 'a\tb"c\\d\ne\x01\r\x7ffé', "plain"], dtype=pl.String),
    })
    got = dump_polars.dump(df)
    assert got == bend_expected("wide"), got
    assert dump_diffs(got, bend_expected("wide")) == []


def test_polars_dump_matches_bend_specials_and_shapes():
    inf = float("inf")
    df = pl.DataFrame({"f": pl.Series([float("nan"), inf, -inf, -0.0, 0.5, None], dtype=pl.Float32)})
    assert dump_diffs(dump_polars.dump(df), bend_expected("specials")) == []
    zr = pl.DataFrame({"a": pl.Series([], dtype=pl.UInt32), "s": pl.Series([], dtype=pl.String)})
    assert dump_polars.dump(zr) == bend_expected("zero_rows")
    assert dump_polars.dump(pl.DataFrame({"a\tb\"": pl.Series([1], dtype=pl.UInt32)})) == bend_expected("odd_name")
    assert dump_polars.dump(pl.DataFrame()) == bend_expected("empty")
    assert dump_polars.dump_error("ColumnNotFound: nope") == bend_expected("error missing column")


def test_polars_dump_rejects_unsupported_dtypes():
    for s in (pl.Series([1], dtype=pl.Int64), pl.Series([1.0], dtype=pl.Float64)):
        try:
            dump_polars.dump(pl.DataFrame({"x": s}))
        except TypeError:
            continue
        raise AssertionError(f"accepted {s.dtype}")


def test_polars_dump_cli_on_csv():
    with tempfile.TemporaryDirectory() as d:
        p = write_tmp(d, "t.csv", "id,s,x\n1,a,1.5\n2,,\n")
        out = os.path.join(d, "out.txt")
        assert dump_polars.main([p, "--schema", "id=u32,s=str,x=f32", "-o", out]) == 0
        text = open(out, encoding="utf-8").read()
        assert text == frame_dump([("u32", '"id"'), ("str", '"s"'), ("f32", '"x"')],
                                  [["1", '"a"', "0x3fc00000"], ["2", "null", "null"]])


# ---- runner -------------------------------------------------------------------------------

if __name__ == "__main__":
    tests = sorted((n, f) for n, f in globals().items() if n.startswith("test_") and callable(f))
    failed = 0
    for name, fn in tests:
        try:
            fn()
            print(f"PASS {name}")
        except Exception as e:  # noqa: BLE001
            failed += 1
            print(f"FAIL {name}: {type(e).__name__}: {e}")
    print(f"{len(tests) - failed} / {len(tests)} passed")
    sys.exit(1 if failed else 0)
