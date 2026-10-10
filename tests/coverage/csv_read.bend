# T6 coverage: reading CSV: csv_opts, read_csv, read_csv_opts, read_csv_schema, read_csv_enc, the
# string storages str_raw / str_dict / str_auto, encode_strings, dict_columns, and the lazy twins
# scan_csv, scan_csv_opts, scan_csv_schema. Fixtures: tests/coverage/data/*.csv: nulls (empty fields,
# a quoted empty string kept as ""), a header-only file and a zero-byte file (zero rows), a `;`
# separator, no header, inferred and given dtypes, ragged and badly typed files and a missing file
# (invalid). Every read is compared with its scan: DF.collect_raw / DF.collect / DF.collect_full of the
# scan dump the same as the eager read (R.four.text).
# Expectations: DESIGN.md 15.6 (CSV contract), 15.2.7, confirmed by bench/coverage/csv_read.py (Polars
# 2.0.0 read_csv with the dtypes Bend infers: Polars reads the same cells, the quoted "" as "" and the
# unquoted empty field as null); departures applied there: a ragged row is an error (Polars pads), a
# zero-byte file reads as zero rows and zero columns (Polars: NoDataError), an error text is the
# contract's (ParseError / IoError / InvalidOperation lines), numeric fields are trimmed only by the reader.
#@ cover csv_opts,read_csv,read_csv_opts,read_csv_schema,read_csv_enc success null empty invalid eager lazy
#@ cover scan_csv,scan_csv_opts,scan_csv_schema success null empty invalid eager lazy
#@ cover str_raw,str_dict,str_auto success null empty invalid eager
#@ na str_raw,str_dict,str_auto lazy -- scan_csv always uses the default (Auto) storage: the readers' choice is eager-only, the Auto reads are compared with the scans
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/schema.bend as S
import ./../regress/lib/rx.bend as R

def d() -> String:
  "tests/coverage/data/"

# the lazy runs of a scan that planned: raw, optimised, fully optimised; the eager dump once and
# whether each lazy dump equals it. A scan that failed at plan time prints its error as all three.
def lz3.k(+tag: String, +d0: String, +d1: String, +d2: String, +d3: String) -> String:
  R.four.text(tag, d0, d1, d2, d3)

def lz.err(+tag: String, +d0: String, +e: E.Err) -> String:
  lz3.k(tag, d0, DF.dump(Fail{e}), DF.dump(Fail{e}), DF.dump(Fail{e}))

def lz.run(+tag: String, +d0: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_raw(p, DF.empty_env())
    r2 : E.ResT(C.Frame) <- DF.collect(p, DF.empty_env())
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, DF.empty_env())
    IO.print(lz3.k(tag, d0, DF.dump(r1), DF.dump(r2), DF.dump(r3)))

def lz(+tag: String, +d0: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print(lz.err(tag, d0, e))
    case Done{p}:
      lz.run(tag, d0, p)

def readA(+tag: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    r0 : E.ResT(C.Frame) <- DF.read_csv(path)
    rp : E.Res(P.Plan) <- DF.scan_csv(path)
    lz(tag, DF.dump(r0), rp)

def readB(+tag: String, +path: String, +o: DF.CsvOpts()) -> IO(Unit):
  do IO<Unit>:
    r0 : E.ResT(C.Frame) <- DF.read_csv_opts(path, o)
    rp : E.Res(P.Plan) <- DF.scan_csv_opts(path, o)
    lz(tag, DF.dump(r0), rp)

# explicit dtypes: read_csv_schema against scan_csv_schema (pure: no IO, no inference at plan time)
def readC(+tag: String, +path: String, +o: DF.CsvOpts(), +ts: List<&2, D.DType>, +sc: List<&2, S.Field>) -> IO(Unit):
  do IO<Unit>:
    r0 : E.ResT(C.Frame) <- DF.read_csv_schema(path, o, ts)
    lz(tag, DF.dump(r0), Done{DF.scan_csv_schema(path, o, sc)})

# a plan with no eager twin: raw, optimised and fully optimised collects against the raw one
def scanC.k(+tag: String, +d1: String, +d2: String, +d3: String) -> String:
  R.four.text(tag, d1, d1, d2, d3)

def scanC(+tag: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_raw(p, DF.empty_env())
    r2 : E.ResT(C.Frame) <- DF.collect(p, DF.empty_env())
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, DF.empty_env())
    IO.print(scanC.k(tag, DF.dump(r1), DF.dump(r2), DF.dump(r3)))

def basic_ts() -> List<&2, D.DType>:
  [DF.t_u32(), DF.t_str(), DF.t_f32(), DF.t_bool()]

def basic_sc() -> List<&2, S.Field>:
  [S.Field{"id", DF.t_u32()}, S.Field{"name", DF.t_str()}, S.Field{"score", DF.t_f32()}, S.Field{"ok", DF.t_bool()}]

def semi() -> DF.CsvOpts():
  DF.csv_opts(';', True{}, 100)

def enc3.k(+tag: String, +da: String, +db: String, +dc: String) -> String:
  "-- " ++ tag ++ "\n" ++ da ++ "raw " ++ R.agree.v(da, db) ++ ", dict " ++ R.agree.v(da, dc) ++ "\n"

def enc3(+tag: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    ra : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_auto())
    rb : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_raw())
    rc : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_dict())
    IO.print(enc3.k(tag, DF.dump(ra), DF.dump(rb), DF.dump(rc)))

def main() -> IO(Unit):
  do IO<Unit>:
    readA("read_csv: nulls, a quoted empty string and an unquoted empty field", d() ++ "basic.csv")
    readA("read_csv: numbers nan inf -0.0 1e3 and an empty field", d() ++ "floats.csv")
    readB("read_csv_opts: a semicolon separator", d() ++ "semi.csv", semi())
    readB("read_csv_opts: no header row", d() ++ "noheader.csv", DF.csv_opts(',', False{}, 100))
    readB("read_csv_opts: header only is zero rows", d() ++ "header_only.csv", DF.csv_opts(',', True{}, 100))
    readA("read_csv: header only is zero rows", d() ++ "header_only.csv")
    readA("read_csv: a zero-byte file", d() ++ "empty.csv")
    readB("read_csv_opts: infer_rows 1 types the column from row 1", d() ++ "repeat.csv", DF.csv_opts(',', True{}, 1))
    readB("read_csv_opts: infer_rows 0 reads every row to infer", d() ++ "badcell.csv", DF.csv_opts(',', True{}, 0))
    readC("read_csv_schema: given dtypes", d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), basic_ts(), basic_sc())
    readC("read_csv_schema: dtypes for a semicolon file", d() ++ "semi.csv", semi(), [DF.t_i32(), DF.t_str(), DF.t_f32()], [S.Field{"id", DF.t_i32()}, S.Field{"name", DF.t_str()}, S.Field{"score", DF.t_f32()}])
    readC("read_csv_schema: a zero-row file keeps the given dtypes", d() ++ "header_only.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32()], [S.Field{"id", DF.t_u32()}, S.Field{"name", DF.t_str()}, S.Field{"score", DF.t_f32()}])
    readA("invalid read_csv: a missing file", d() ++ "no_such_file.csv")
    readA("invalid read_csv: a ragged row", d() ++ "ragged.csv")
    readB("invalid read_csv_opts: infer_rows 1 then a cell of another type", d() ++ "badcell.csv", DF.csv_opts(',', True{}, 1))
    readC("invalid read_csv_schema: a cell that does not parse", d() ++ "badcell.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32()], [S.Field{"id", DF.t_u32()}, S.Field{"name", DF.t_str()}, S.Field{"score", DF.t_f32()}])
    readC("invalid read_csv_schema: the wrong number of dtypes", d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32()], [S.Field{"id", DF.t_u32()}, S.Field{"name", DF.t_str()}, S.Field{"score", DF.t_f32()}])
    scanC("invalid scan_csv_schema: names that differ from the header", DF.scan_csv_schema(d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), [S.Field{"id", DF.t_u32()}, S.Field{"label", DF.t_str()}, S.Field{"score", DF.t_f32()}, S.Field{"ok", DF.t_bool()}]))
    scanC("scan_csv_schema: a plan with the file's names collects", DF.scan_csv_schema(d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), basic_sc()))
    readC("invalid read_csv_schema: a missing file", d() ++ "no_such_file.csv", DF.csv_opts(',', True{}, 100), basic_ts(), basic_sc())
    readB("invalid read_csv_opts: a missing file", d() ++ "no_such_file.csv", semi())
    enc3("read_csv_enc: Auto, Raw and Dictionary decode to the same cells (nulls and an empty string)", d() ++ "basic.csv")
    enc3("read_csv_enc: a repeated string column", d() ++ "repeat.csv")
    enc3("read_csv_enc: zero rows", d() ++ "header_only.csv")
    enc3("read_csv_enc: a zero-byte file", d() ++ "empty.csv")
    enc3("invalid read_csv_enc: a ragged row", d() ++ "ragged.csv")
    enc3("invalid read_csv_enc: a missing file", d() ++ "no_such_file.csv")
#|-- read_csv: nulls, a quoted empty string and an unquoted empty field
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|col	bool	"ok"
#|row	1	"ann"	0x3fc00000	true
#|row	2	null	0x40200000	false
#|row	3	"bo,b"	null	true
#|row	4	"dee"	0x40900000	null
#|row	5	""	0x3f000000	false
#|raw same, opt same, full same
#|
#|-- read_csv: numbers nan inf -0.0 1e3 and an empty field
#|frame
#|height	5
#|width	2
#|col	u32	"id"
#|col	f32	"v"
#|row	1	0x7fc00000
#|row	2	0x7f800000
#|row	3	0x80000000
#|row	4	null
#|row	5	0x447a0000
#|raw same, opt same, full same
#|
#|-- read_csv_opts: a semicolon separator
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|row	1	"ann"	0x3fc00000
#|row	2	null	0x40200000
#|row	3	"bo"	null
#|raw same, opt same, full same
#|
#|-- read_csv_opts: no header row
#|frame
#|height	3
#|width	2
#|col	u32	"column_0"
#|col	str	"column_1"
#|row	1	"x"
#|row	2	"y"
#|row	3	null
#|raw same, opt same, full same
#|
#|-- read_csv_opts: header only is zero rows
#|frame
#|height	0
#|width	3
#|col	str	"id"
#|col	str	"name"
#|col	str	"score"
#|raw same, opt same, full same
#|
#|-- read_csv: header only is zero rows
#|frame
#|height	0
#|width	3
#|col	str	"id"
#|col	str	"name"
#|col	str	"score"
#|raw same, opt same, full same
#|
#|-- read_csv: a zero-byte file
#|frame
#|height	0
#|width	0
#|raw same, opt same, full same
#|
#|-- read_csv_opts: infer_rows 1 types the column from row 1
#|frame
#|height	6
#|width	2
#|col	u32	"id"
#|col	str	"name"
#|row	1	"a"
#|row	2	"b"
#|row	3	"a"
#|row	4	"b"
#|row	5	"a"
#|row	6	"c"
#|raw same, opt same, full same
#|
#|-- read_csv_opts: infer_rows 0 reads every row to infer
#|frame
#|height	2
#|width	3
#|col	u32	"id"
#|col	str	"name"
#|col	str	"score"
#|row	1	"ann"	"1.5"
#|row	2	"bo"	"x"
#|raw same, opt same, full same
#|
#|-- read_csv_schema: given dtypes
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|col	bool	"ok"
#|row	1	"ann"	0x3fc00000	true
#|row	2	null	0x40200000	false
#|row	3	"bo,b"	null	true
#|row	4	"dee"	0x40900000	null
#|row	5	""	0x3f000000	false
#|raw same, opt same, full same
#|
#|-- read_csv_schema: dtypes for a semicolon file
#|frame
#|height	3
#|width	3
#|col	i32	"id"
#|col	str	"name"
#|col	f32	"score"
#|row	1	"ann"	0x3fc00000
#|row	2	null	0x40200000
#|row	3	"bo"	null
#|raw same, opt same, full same
#|
#|-- read_csv_schema: a zero-row file keeps the given dtypes
#|frame
#|height	0
#|width	3
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|raw same, opt same, full same
#|
#|-- invalid read_csv: a missing file
#|error	IoError 2: No such file or directory
#|raw same, opt same, full same
#|
#|-- invalid read_csv: a ragged row
#|error	ParseError at line 3: expected 3 fields, got 2
#|raw same, opt same, full same
#|
#|-- invalid read_csv_opts: infer_rows 1 then a cell of another type
#|error	ParseError at line 3: column score: cannot parse "x" as f32
#|raw same, opt same, full same
#|
#|-- invalid read_csv_schema: a cell that does not parse
#|error	ParseError at line 3: column score: cannot parse "x" as f32
#|raw same, opt same, full same
#|
#|-- invalid read_csv_schema: the wrong number of dtypes
#|error	InvalidOperation: csv schema: 3 dtypes for 4 columns
#|raw same, opt same, full same
#|
#|-- invalid scan_csv_schema: names that differ from the header
#|error	InvalidOperation: scan_csv tests/coverage/data/basic.csv: data schema [id:u32, name:str, score:f32, ok:bool] differs from the plan's [id:u32, label:str, score:f32, ok:bool]
#|raw same, opt same, full same
#|
#|-- scan_csv_schema: a plan with the file's names collects
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|col	bool	"ok"
#|row	1	"ann"	0x3fc00000	true
#|row	2	null	0x40200000	false
#|row	3	"bo,b"	null	true
#|row	4	"dee"	0x40900000	null
#|row	5	""	0x3f000000	false
#|raw same, opt same, full same
#|
#|-- invalid read_csv_schema: a missing file
#|error	IoError 2: No such file or directory
#|raw same, opt same, full same
#|
#|-- invalid read_csv_opts: a missing file
#|error	IoError 2: No such file or directory
#|raw same, opt same, full same
#|
#|-- read_csv_enc: Auto, Raw and Dictionary decode to the same cells (nulls and an empty string)
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|col	bool	"ok"
#|row	1	"ann"	0x3fc00000	true
#|row	2	null	0x40200000	false
#|row	3	"bo,b"	null	true
#|row	4	"dee"	0x40900000	null
#|row	5	""	0x3f000000	false
#|raw same, dict same
#|
#|-- read_csv_enc: a repeated string column
#|frame
#|height	6
#|width	2
#|col	u32	"id"
#|col	str	"name"
#|row	1	"a"
#|row	2	"b"
#|row	3	"a"
#|row	4	"b"
#|row	5	"a"
#|row	6	"c"
#|raw same, dict same
#|
#|-- read_csv_enc: zero rows
#|frame
#|height	0
#|width	3
#|col	str	"id"
#|col	str	"name"
#|col	str	"score"
#|raw same, dict same
#|
#|-- read_csv_enc: a zero-byte file
#|frame
#|height	0
#|width	0
#|raw same, dict same
#|
#|-- invalid read_csv_enc: a ragged row
#|error	ParseError at line 3: expected 3 fields, got 2
#|raw same, dict same
#|
#|-- invalid read_csv_enc: a missing file
#|error	IoError 2: No such file or directory
#|raw same, dict same
#|
