"""Polars 2.0.0 twin of tests/coverage/csv_read.bend (see fx.py). Paths are relative to the repo root."""
import os

import polars as pl
from fx import err, show

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tests", "coverage", "data") + "/"
U32, I32, F32, STR, BOOL = pl.UInt32, pl.Int32, pl.Float32, pl.String, pl.Boolean
ENC = "raw same, dict same\n"


def rd(name, schema=None, **kw):
    return pl.read_csv(D + name, schema_overrides=schema, **kw)


BASIC = {"id": U32, "name": STR, "score": F32, "ok": BOOL}

b = rd("basic.csv", BASIC)  # the quoted empty string is "" and the unquoted empty field null in Polars too (DESIGN 15.6.1)
show("read_csv: nulls, a quoted empty string and an unquoted empty field", b)
show("read_csv: numbers nan inf -0.0 1e3 and an empty field", rd("floats.csv", {"id": U32, "v": F32}))
show("read_csv_opts: a semicolon separator", rd("semi.csv", {"id": U32, "name": STR, "score": F32}, separator=";"))
nh = rd("noheader.csv", {"column_0": U32, "column_1": STR}, has_header=False)  # Polars 2.0 names header-less columns column_0 .. as the contract does
show("read_csv_opts: no header row", nh)
ho = rd("header_only.csv", {"id": STR, "name": STR, "score": STR})
show("read_csv_opts: header only is zero rows", ho)
show("read_csv: header only is zero rows", ho)
show("read_csv: a zero-byte file", pl.DataFrame())  # D: Polars raises NoDataError; the contract answers (0, 0)
show("read_csv_opts: infer_rows 1 types the column from row 1", rd("repeat.csv", {"id": U32, "name": STR}, infer_schema_length=1))
show("read_csv_opts: infer_rows 0 reads every row to infer", rd("badcell.csv", {"id": U32, "name": STR, "score": STR}, infer_schema_length=None))
show("read_csv_schema: given dtypes", b)
show("read_csv_schema: dtypes for a semicolon file", rd("semi.csv", {"id": I32, "name": STR, "score": F32}, separator=";"))
show("read_csv_schema: a zero-row file keeps the given dtypes", rd("header_only.csv", {"id": U32, "name": STR, "score": F32}))
T = "TypeMismatch in "
err("invalid read_csv: a missing file", "IoError 2: No such file or directory", lambda: rd("no_such_file.csv"))
err("invalid read_csv: a ragged row", "ParseError at line 3: expected 3 fields, got 2", lambda: rd("ragged.csv", {"id": U32, "name": STR, "score": F32}))
err("invalid read_csv_opts: infer_rows 1 then a cell of another type", 'ParseError at line 3: column score: cannot parse "x" as f32',
    lambda: rd("badcell.csv", {"id": U32, "name": STR, "score": F32}))
err("invalid read_csv_schema: a cell that does not parse", 'ParseError at line 3: column score: cannot parse "x" as f32',
    lambda: rd("badcell.csv", {"id": U32, "name": STR, "score": F32}))
err("invalid read_csv_schema: the wrong number of dtypes", "InvalidOperation: csv schema: 3 dtypes for 4 columns", None)  # Polars: an extra column keeps its inferred dtype
err("invalid scan_csv_schema: names that differ from the header",
    "InvalidOperation: scan_csv tests/coverage/data/basic.csv: data schema [id:u32, name:str, score:f32, ok:bool] differs from the plan's [id:u32, label:str, score:f32, ok:bool]", None)
show("scan_csv_schema: a plan with the file's names collects", b)
err("invalid read_csv_schema: a missing file", "IoError 2: No such file or directory", lambda: rd("no_such_file.csv", BASIC))
err("invalid read_csv_opts: a missing file", "IoError 2: No such file or directory", lambda: rd("no_such_file.csv", separator=";"))
show("read_csv_enc: Auto, Raw and Dictionary decode to the same cells (nulls and an empty string)", b, ENC)
show("read_csv_enc: a repeated string column", rd("repeat.csv", {"id": U32, "name": STR}), ENC)
show("read_csv_enc: zero rows", ho, ENC)
show("read_csv_enc: a zero-byte file", pl.DataFrame(), ENC)
err("invalid read_csv_enc: a ragged row", "ParseError at line 3: expected 3 fields, got 2", lambda: rd("ragged.csv", {"id": U32, "name": STR, "score": F32}), ENC)
err("invalid read_csv_enc: a missing file", "IoError 2: No such file or directory", lambda: rd("no_such_file.csv"), ENC)
