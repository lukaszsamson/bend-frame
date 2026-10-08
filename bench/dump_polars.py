"""Write a Polars DataFrame in the DF.dump format (DESIGN.md 15.1) for differential tests.

    from dump_polars import dump, dump_error
    text = dump(df)            # "frame\nheight\t..." ; same bytes as DF.dump of the equal frame
    text = dump_error("ColumnNotFound: x")

or from the command line (a CSV read with an explicit schema, Bend's dtype names):

    python dump_polars.py data/sales_1000.csv --schema id=u32,region=str,product=str,qty=u32,price=f32,discount=f32,ok=bool

Supported dtypes (Polars -> dump): Boolean bool, UInt32 u32, Int32 i32, Float32 f32, String str.
Anything else raises TypeError (the Bend library has no other dtype). f32 cells are the exact
IEEE bits of the stored value (NaN payloads as Polars stores them; the comparator treats all
NaNs as equal). Strings are quoted and escaped like DF.dump: \\" \\\\ \\n \\r \\t, \\xHH for the
other C0 controls and U+007F, every other code point written as is. A CSV cannot tell "" from
null, so build frames from Python values (pl.DataFrame(...)) when that matters.
"""
import argparse
import sys

import numpy as np
import polars as pl

DTYPES = {
    pl.Boolean: "bool",
    pl.UInt32: "u32",
    pl.Int32: "i32",
    pl.Float32: "f32",
    pl.String: "str",
}
BY_NAME = {"bool": pl.Boolean, "u32": pl.UInt32, "i32": pl.Int32, "f32": pl.Float32, "str": pl.String}
SIMPLE = {'"': '\\"', "\\": "\\\\", "\n": "\\n", "\r": "\\r", "\t": "\\t"}


def quote(s: str) -> str:
    out = []
    for ch in s:
        if ch in SIMPLE:
            out.append(SIMPLE[ch])
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append("\\x%02x" % ord(ch))
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


def dtype_name(dt) -> str:
    try:
        return DTYPES[dt]
    except (KeyError, TypeError):
        raise TypeError(f"dtype {dt} has no bend-frame counterpart") from None


def column_cells(s: pl.Series, name: str):
    """The dump text of every cell of a column."""
    t = dtype_name(s.dtype)
    nulls = s.is_null().to_list()
    if t == "f32":
        bits = s.fill_null(0.0).to_numpy().astype(np.float32, copy=False).view(np.uint32)
        vals = [f"0x{int(b):08x}" for b in bits]
    elif t == "str":
        vals = [quote(v) if v is not None else "" for v in s.to_list()]
    elif t == "bool":
        vals = ["true" if v else "false" for v in s.to_list()]
    else:
        vals = [str(v) for v in s.to_list()]
    return ["null" if n else v for n, v in zip(nulls, vals)]


def dump(df: pl.DataFrame) -> str:
    h, w = df.height, df.width
    lines = ["frame", f"height\t{h}", f"width\t{w}"]
    cols = [column_cells(df.get_column(n), n) for n in df.columns]
    for n in df.columns:
        lines.append(f"col\t{dtype_name(df.schema[n])}\t{quote(n)}")
    if w > 0:
        lines.extend("row\t" + "\t".join(c[i] for c in cols) for i in range(h))
    return "\n".join(lines) + "\n"


def dump_error(text: str) -> str:
    assert "\n" not in text and "\r" not in text, "error text must be one line"
    return f"error\t{text}\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("csv")
    ap.add_argument("--schema", help="name=dtype,... with bend dtype names (bool u32 i32 f32 str); required unless every column infers to a supported dtype")
    ap.add_argument("-o", "--out", help="output file (default stdout)")
    a = ap.parse_args(argv)
    overrides = None
    if a.schema:
        overrides = {}
        for item in a.schema.split(","):
            name, _, t = item.partition("=")
            if t not in BY_NAME:
                ap.error(f"unknown dtype {t!r} in --schema (want one of {sorted(BY_NAME)})")
            overrides[name] = BY_NAME[t]
    df = pl.read_csv(a.csv, schema_overrides=overrides)
    text = dump(df)
    if a.out:
        with open(a.out, "w", encoding="utf-8", newline="") as f:
            f.write(text)
    else:
        sys.stdout.buffer.write(text.encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
