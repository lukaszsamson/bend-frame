"""Polars twins of tests/coverage/lib/fx.bend (the T6 fixture frames) and the case printer.

Every tests/coverage/<name>.bend has a bench/coverage/<name>.py that prints, for each case, the text
the Bend test prints (`-- <tag>`, the DF.dump of the eager result, and the `raw same, ...` line a
passing eager/lazy agreement gives), computed by Polars 2.0.0 with the contract's documented
departures applied by hand (marked `# D:` in the script). `bench/coverage/check.sh <name>` diffs it
against what `bend` prints. Run one by hand from bench/: `uv run python coverage/<name>.py`.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import polars as pl  # noqa: E402
from dump_polars import dump, dump_error  # noqa: E402

NAN = float("nan")
INF = float("inf")
MIN = -2147483648
SAME = "raw same, opt same, full same\n"

DT = {"u32": pl.UInt32, "i32": pl.Int32, "f32": pl.Float32, "bool": pl.Boolean, "str": pl.String}


def frame(cols):
    """cols: list of (name, dtype name, values)."""
    return pl.DataFrame([pl.Series(n, v, dtype=DT[t]) for n, t, v in cols])


def t():
    return frame([
        ("a", "u32", [7, 0, 4294967295, None, 5, 1, 2]),
        ("b", "u32", [2, 3, 1, 1, None, 0, 0]),
        ("p", "i32", [7, -7, 7, -7, MIN, None, 0]),
        ("q", "i32", [2, 2, -2, -2, -1, 1, 0]),
        ("x", "f32", [1.5, -2.0, None, NAN, INF, 0.0, -0.0]),
        ("y", "f32", [2.0, 0.5, 1.0, 1.0, INF, 0.0, None]),
        ("k", "bool", [True, False, None, True, False, True, None]),
        ("s", "str", ["a", "", "é", None, "abc", "ab", "a"]),
    ])


def z():
    return t().clear()


def canon_nan(text):
    """DF.dump prints every NaN as 0x7fc00000 (src/dump.bend Dump.fbits); Polars keeps the sign and payload."""
    def fix(m):
        b = int(m.group(0), 16)
        return "0x7fc00000" if (b & 0x7FFFFFFF) > 0x7F800000 else m.group(0)
    return re.sub(r"0x[0-9a-f]{8}", fix, text)


def show(tag, df, same=True):
    sys.stdout.write("-- %s\n" % tag)
    sys.stdout.write(canon_nan(dump(df)))
    if same:
        sys.stdout.write(SAME)
    sys.stdout.write("\n")


def err(tag, text, fn=None):
    """An invalid-input case: Bend refuses with the contract's text. Polars is asked too (fn raises
    when it refuses); where it coerces or accepts, the contract departs from it (DESIGN 15) and the
    note goes to stderr."""
    note = "polars refuses"
    if fn is not None:
        try:
            fn()
            note = "polars ACCEPTS (departure)"
        except Exception:
            pass
    sys.stderr.write("%s: %s\n" % (tag, note))
    sys.stdout.write("-- %s\n" % tag)
    sys.stdout.write(dump_error(text))
    sys.stdout.write(SAME)
    sys.stdout.write("\n")
