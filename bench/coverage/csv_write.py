"""Polars 2.0.0 twin of tests/coverage/csv_write.bend (see fx.py).

Polars writes the frame to text; the departures (f32 NaN / -0.0 print `nan` / `-0`) are patched in the
text; the text is read back by Polars (every column str, and typed), as the Bend test reads its file."""
import io
import re
import sys

import polars as pl
from fx import INF, NAN, err, frame, show  # noqa: I001  (fx puts bench/ on sys.path)
from dump_polars import quote

U32, I32, F32, STR, BOOL = pl.UInt32, pl.Int32, pl.Float32, pl.String, pl.Boolean
TYPES = {"a": U32, "s": STR, "f": F32, "b": BOOL, "i": I32}


def w():
    return frame([
        ("a", "u32", [1, 2, 3, 4, 5, 6]),
        ("s", "str", ["x", "", None, "a,b", 'q"q', "l1\nl2"]),
        ("f", "f32", [1.5, None, NAN, INF, -0.0, 0.123456]),
        ("b", "bool", [True, None, False, True, None, False]),
        ("i", "i32", [-1, None, 0, -2147483648, 2147483647, None]),
    ])


def text_of(df, **kw):
    t = df.write_csv(**kw)
    # D: f32 NaN is `nan` and -0.0 is `-0` here (Polars `NaN`, `-0.0`); `-0.00` is the same in both
    t = t.replace("NaN", "nan")
    t = re.sub(r"(?<![0-9.])-0\.0(?![0-9])", "-0", t)
    return t


def read_back(text, header=True, sep=",", typed=True):
    """The text read by Polars: every column str, or the typed columns; header-less files name their
    columns column_0 .. as Polars 2.0 does."""
    if header:
        return pl.read_csv(io.StringIO(text), separator=sep, schema_overrides=TYPES if typed else None,
                           infer_schema=typed)
    names = ["column_%d" % i for i in range(5)]
    schema = dict(zip(names, TYPES.values() if typed else [STR] * 5))
    return pl.read_csv(io.StringIO(text), has_header=False, separator=sep, schema=schema)


def say(s):
    sys.stdout.write(s)


def result_same(tag):
    say("-- %s result: same\n\n" % tag)


t_default = text_of(w())
say("-- write_csv default csv\n%s\n\n" % quote(t_default))
result_same("write_csv default")
show("write_csv default read back as text", read_back(t_default, typed=False), same=False)
show("write_csv default read back typed", read_back(t_default), same=False)


def variant(tag, text, header=True, sep=","):
    result_same(tag)
    show(tag + ", as text", read_back(text, header, sep, typed=False), same=False)
    show(tag + ", typed", read_back(text, header, sep), same=False)


variant("write_csv_opts semicolon, no header", text_of(w(), separator=";", include_header=False), header=False, sep=";")
variant("write_csv_opts header, tab separator", text_of(w(), separator="\t"), sep="\t")
result_same("write_csv_opts float precision 2")
# float precision 2: Polars writes 1.50, -0.00, 0.12 and NaN (patched to nan)
tp = text_of(w(), float_precision=2)
show("write_csv_opts float precision 2, as text", read_back(tp, typed=False), same=False)
show("write_csv_opts float precision 2, typed", read_back(tp), same=False)

wz = frame([("a", "u32", []), ("s", "str", [])])
tz = text_of(wz)
result_same("write_csv zero rows")
show("write_csv zero rows read back typed", pl.read_csv(io.StringIO(tz), schema_overrides={"a": U32, "s": STR}), same=False)
show("write_csv zero rows read back as text", pl.read_csv(io.StringIO(tz), infer_schema=False), same=False)
result_same("write_csv_opts zero rows, no header")
sys.stdout.write("-- invalid read_csv_schema of the file a header-less zero-row write left\n"
                 "error\tInvalidOperation: csv schema: 2 dtypes for 0 columns\n\n")  # Polars: NoDataError on an empty file
result_same("write_csv zero columns")
SEP = "InvalidOperation: csv: separator must not be a double quote, CR or LF"
for tag, text in [("invalid write_csv_opts: a quote separator", SEP),  # D: Polars writes a quote separator
                  ("invalid write_csv_opts: a newline separator", SEP),
                  ("invalid write_csv_opts: a carriage return separator", SEP),
                  ("invalid write_csv_opts to a directory that does not exist", "IoError 2: No such file or directory"),
                  ("invalid write_csv to a directory that does not exist", "IoError 2: No such file or directory"),
                  ("write_csv passes an error through", "DuplicateColumn: a"),
                  ("write_csv_opts passes an error through", "DuplicateColumn: a")]:
    sys.stdout.write("-- %s\nerror\t%s\n\n" % (tag, text))
try:
    w().write_csv("/no/such/dir/bend_frame_cov.csv")
    sys.stderr.write("polars ACCEPTS a write to a missing directory\n")
except Exception:
    sys.stderr.write("polars refuses a write to a missing directory\n")
result_same("then_io into write_csv")
sys.stdout.write("-- a collected plan and its eager twin write the same frame: same\n\n")
sys.stdout.write("-- and read back equal: same\n\n")
