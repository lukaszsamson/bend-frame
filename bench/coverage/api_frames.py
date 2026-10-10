"""Polars 2.0.0 reference values for tests/coverage/api_frames.bend (not a line-by-line twin: the Bend
test prints DF.show / DF.describe tables whose layout is Bend's own). Run from bench/:
`uv run python coverage/api_frames.py`; compare by eye with the `describe` and `from_columns` cases.

describe: Polars (default percentiles 25/50/75, interpolation "nearest") over the same frame. The
contract differs only in the dtype of the statistics (numeric columns are f32, Polars f64) and in
showing bool / str columns' min / max as text.
"""
import polars as pl
from fx import NAN, INF, frame

ds = frame([
    ("n", "u32", [1, 2, None, 4]),
    ("f", "f32", [1.5, None, 3.5, 5.0]),
    ("s", "str", ["a", "b", None, "d"]),
    ("b", "bool", [True, False, True, None]),
])
with pl.Config(tbl_rows=20, tbl_cols=20):
    print(ds.describe(interpolation="nearest"))
    x = frame([("x", "f32", [1.0, NAN, None, INF, -0.0])])
    print(x.describe(interpolation="nearest"))
    print(frame([("a", "u32", []), ("s", "str", [])]).describe(interpolation="nearest"))

# from_columns / column: ragged and repeated names are refused by Polars as well
for name, fn in [("ragged", lambda: pl.DataFrame([pl.Series("a", [1, 2]), pl.Series("b", [1.0])])),
                 ("repeated name", lambda: pl.DataFrame([pl.Series("a", [1]), pl.Series("a", [2])])),
                 ("str in a u32 series", lambda: pl.Series("c", [1, "x"], dtype=pl.UInt32)),
                 ("f32 in a bool series", lambda: pl.Series("c", [1.0], dtype=pl.Boolean))]:
    try:
        fn()
        print(name, "-> polars accepts")
    except Exception as e:
        print(name, "-> polars refuses:", type(e).__name__)
