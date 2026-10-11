# T6 coverage (v0.2 W6.3): the CSV reader engine (DESIGN.md 16.5 D7, 17.4): csv_engine_v01,
# csv_engine_v02, read_csv_engine, read_csv_v02 and collect_engine (scan_csv collected with a reader
# engine). Every read is made by BOTH engines and the v0.2 dump is printed with "v01 same" when the v0.1
# dump is identical (the v0.2 reader's contract: the same frame or the same error as v0.1). Fixtures
# tests/coverage/data/*.csv (tests/coverage/csv_read.bend's): nulls, a quoted empty string, a zero-byte
# file and a header-only file (zero rows), no header, a `;` separator, inferred and given dtypes, a
# ragged row, a cell that does not parse, a wrong dtype count, a missing file (invalid); scans whose
# frozen schema meets a later cell of another type or a header that differs.
#@ cover csv_engine_v01,csv_engine_v02,read_csv_engine,read_csv_v02 success null empty invalid eager
#@ na csv_engine_v01,csv_engine_v02,read_csv_engine,read_csv_v02 lazy -- a read's lazy twin is scan_csv + collect_engine (the collect_engine row), compared here with the eager reads
#@ cover collect_engine success null empty invalid lazy
#@ na collect_engine eager -- collecting a plan is the lazy API itself; its eager twins are the reads above
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/schema.bend as S

def d() -> String:
  "tests/coverage/data/"

def same(+a: String, +b: String) -> String:
  Bool.pick(String, String.eq(a, b), "v01 same", "v01 DIFF:\n" ++ a)

def show(+tag: String, +a: String, +b: String) -> String:
  "-- " ++ tag ++ "\n" ++ b ++ same(a, b) ++ "\n"

# read_csv_engine with both engines (dtypes [] infers)
def rd(+tag: String, +path: String, +o: DF.CsvOpts(), +ts: List<&2, D.DType>) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.read_csv_engine(DF.csv_engine_v01(), path, o, ts, DF.str_auto())
    r2 : E.ResT(C.Frame) <- DF.read_csv_engine(DF.csv_engine_v02(), path, o, ts, DF.str_auto())
    IO.print(show(tag, DF.dump(r1), DF.dump(r2)))

# read_csv (v0.1) against read_csv_v02
def rdv(+tag: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.read_csv(path)
    r2 : E.ResT(C.Frame) <- DF.read_csv_v02(path)
    IO.print(show(tag, DF.dump(r1), DF.dump(r2)))

# a scan collected by both engines
def sc.run(+tag: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_engine(DF.csv_engine_v01(), p, DF.empty_env())
    r2 : E.ResT(C.Frame) <- DF.collect_engine(DF.csv_engine_v02(), p, DF.empty_env())
    IO.print(show(tag, DF.dump(r1), DF.dump(r2)))

def sc(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("-- " ++ tag ++ "\nplan " ++ DF.err_show(e) ++ "\n")
    case Done{p}:
      sc.run(tag, p)

def scan(+tag: String, +path: String, +o: DF.CsvOpts()) -> IO(Unit):
  do IO<Unit>:
    rp : E.Res(P.Plan) <- DF.scan_csv_opts(path, o)
    sc(tag, rp)

# a file whose first 100 rows are u32 and whose row 120 is not: the scan freezes u32 and its collect
# meets the cell (a ParseError at its line), the eager read infers the same prefix and fails alike
def late.rows(f: Nat, +i: U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+p:
      late.rows(p, U32.sub(i, 1), Bool.pick(String, U32.is_eq(i, 120), "x", U32.show(i)) ++ "\n" ++ acc)

def late.write.k(f: File, r: Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  do IO<Unit>:
    File.close(f)
    return Unit{}

def late.write.got(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  late.write.k(f, res)

def late.write.open(o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{f}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, "n\n" ++ late.rows(150n, 150, ""))
        late.write.got(r)
    case Fail{(code, msg)}:
      IO.print("cannot write: " ++ msg)

def late.path() -> String:
  "/tmp/bend_frame_csv_engine_late.csv"

def late.write() -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(late.path(), "w")
    late.write.open(o)

def basic_sc() -> List<&2, S.Field>:
  [S.Field{"id", DF.t_u32()}, S.Field{"name", DF.t_str()}, S.Field{"score", DF.t_f32()}, S.Field{"ok", DF.t_bool()}]

def main() -> IO(Unit):
  do IO<Unit>:
    late.write()
    rdv("read_csv_v02: nulls, a quoted empty string and an unquoted empty field", d() ++ "basic.csv")
    rdv("read_csv_v02: nan inf -0.0 1e3 and an empty field", d() ++ "floats.csv")
    rdv("read_csv_v02: header only is zero rows", d() ++ "header_only.csv")
    rdv("read_csv_v02: a zero-byte file", d() ++ "empty.csv")
    rdv("invalid read_csv_v02: a ragged row", d() ++ "ragged.csv")
    rdv("invalid read_csv_v02: a missing file", d() ++ "no_such_file.csv")
    rd("read_csv_engine: a semicolon separator", d() ++ "semi.csv", DF.csv_opts(';', True{}, 100), [])
    rd("read_csv_engine: no header row", d() ++ "noheader.csv", DF.csv_opts(',', False{}, 100), [])
    rd("read_csv_engine: infer_rows 1", d() ++ "repeat.csv", DF.csv_opts(',', True{}, 1), [])
    rd("read_csv_engine: infer_rows 0 reads every row to infer", d() ++ "badcell.csv", DF.csv_opts(',', True{}, 0), [])
    rd("read_csv_engine: given dtypes", d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32(), DF.t_bool()])
    rd("read_csv_engine: zero rows keep the given dtypes", d() ++ "header_only.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32()])
    rd("invalid read_csv_engine: infer_rows 1 then a cell of another type", d() ++ "badcell.csv", DF.csv_opts(',', True{}, 1), [])
    rd("invalid read_csv_engine: a cell that does not parse", d() ++ "badcell.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32()])
    rd("invalid read_csv_engine: the wrong number of dtypes", d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32(), DF.t_str(), DF.t_f32()])
    rd("invalid read_csv_engine: dtypes for a zero-byte file", d() ++ "empty.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32()])
    rd("invalid read_csv_engine: a separator that is a quote", d() ++ "basic.csv", DF.csv_opts('"', True{}, 100), [])
    rd("invalid read_csv_engine: the late cell of another type", late.path(), DF.csv_opts(',', True{}, 100), [])
    scan("collect_engine: scan_csv of nulls", d() ++ "basic.csv", DF.csv_opts(',', True{}, 100))
    scan("collect_engine: scan_csv of zero rows", d() ++ "header_only.csv", DF.csv_opts(',', True{}, 100))
    scan("collect_engine: scan_csv of a zero-byte file", d() ++ "empty.csv", DF.csv_opts(',', True{}, 100))
    scan("collect_engine: scan_csv with no header", d() ++ "noheader.csv", DF.csv_opts(',', False{}, 100))
    scan("invalid collect_engine: the frozen u32 meets a later cell", late.path(), DF.csv_opts(',', True{}, 100))
    sc("collect_engine: scan_csv_schema with the file's names", Done{DF.scan_csv_schema(d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), basic_sc())})
    sc("invalid collect_engine: scan_csv_schema names that differ from the header", Done{DF.scan_csv_schema(d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), [S.Field{"id", DF.t_u32()}, S.Field{"label", DF.t_str()}, S.Field{"score", DF.t_f32()}, S.Field{"ok", DF.t_bool()}])})
    sc("invalid collect_engine: scan_csv_schema of a missing file", Done{DF.scan_csv_schema(d() ++ "no_such_file.csv", DF.csv_opts(',', True{}, 100), basic_sc())})
    sc("collect_engine: a filter over a scan", Done{DF.lazy_filter(DF.scan_csv_schema(d() ++ "basic.csv", DF.csv_opts(',', True{}, 100), basic_sc()), DF.gt(DF.col("id"), DF.lit_u32(2)))})
#|-- read_csv_v02: nulls, a quoted empty string and an unquoted empty field
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
#|v01 same
#|
#|-- read_csv_v02: nan inf -0.0 1e3 and an empty field
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
#|v01 same
#|
#|-- read_csv_v02: header only is zero rows
#|frame
#|height	0
#|width	3
#|col	str	"id"
#|col	str	"name"
#|col	str	"score"
#|v01 same
#|
#|-- read_csv_v02: a zero-byte file
#|frame
#|height	0
#|width	0
#|v01 same
#|
#|-- invalid read_csv_v02: a ragged row
#|error	ParseError at line 3: expected 3 fields, got 2
#|v01 same
#|
#|-- invalid read_csv_v02: a missing file
#|error	IoError 2: No such file or directory
#|v01 same
#|
#|-- read_csv_engine: a semicolon separator
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|row	1	"ann"	0x3fc00000
#|row	2	null	0x40200000
#|row	3	"bo"	null
#|v01 same
#|
#|-- read_csv_engine: no header row
#|frame
#|height	3
#|width	2
#|col	u32	"column_0"
#|col	str	"column_1"
#|row	1	"x"
#|row	2	"y"
#|row	3	null
#|v01 same
#|
#|-- read_csv_engine: infer_rows 1
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
#|v01 same
#|
#|-- read_csv_engine: infer_rows 0 reads every row to infer
#|frame
#|height	2
#|width	3
#|col	u32	"id"
#|col	str	"name"
#|col	str	"score"
#|row	1	"ann"	"1.5"
#|row	2	"bo"	"x"
#|v01 same
#|
#|-- read_csv_engine: given dtypes
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
#|v01 same
#|
#|-- read_csv_engine: zero rows keep the given dtypes
#|frame
#|height	0
#|width	3
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|v01 same
#|
#|-- invalid read_csv_engine: infer_rows 1 then a cell of another type
#|error	ParseError at line 3: column score: cannot parse "x" as f32
#|v01 same
#|
#|-- invalid read_csv_engine: a cell that does not parse
#|error	ParseError at line 3: column score: cannot parse "x" as f32
#|v01 same
#|
#|-- invalid read_csv_engine: the wrong number of dtypes
#|error	InvalidOperation: csv schema: 3 dtypes for 4 columns
#|v01 same
#|
#|-- invalid read_csv_engine: dtypes for a zero-byte file
#|error	InvalidOperation: csv schema: 1 dtypes for 0 columns
#|v01 same
#|
#|-- invalid read_csv_engine: a separator that is a quote
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|v01 same
#|
#|-- invalid read_csv_engine: the late cell of another type
#|error	ParseError at line 121: column n: cannot parse "x" as u32
#|v01 same
#|
#|-- collect_engine: scan_csv of nulls
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
#|v01 same
#|
#|-- collect_engine: scan_csv of zero rows
#|frame
#|height	0
#|width	3
#|col	str	"id"
#|col	str	"name"
#|col	str	"score"
#|v01 same
#|
#|-- collect_engine: scan_csv of a zero-byte file
#|frame
#|height	0
#|width	0
#|v01 same
#|
#|-- collect_engine: scan_csv with no header
#|frame
#|height	3
#|width	2
#|col	u32	"column_0"
#|col	str	"column_1"
#|row	1	"x"
#|row	2	"y"
#|row	3	null
#|v01 same
#|
#|-- invalid collect_engine: the frozen u32 meets a later cell
#|error	ParseError at line 121: column n: cannot parse "x" as u32
#|v01 same
#|
#|-- collect_engine: scan_csv_schema with the file's names
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
#|v01 same
#|
#|-- invalid collect_engine: scan_csv_schema names that differ from the header
#|error	InvalidOperation: scan_csv tests/coverage/data/basic.csv: data schema [id:u32, name:str, score:f32, ok:bool] differs from the plan's [id:u32, label:str, score:f32, ok:bool]
#|v01 same
#|
#|-- invalid collect_engine: scan_csv_schema of a missing file
#|error	IoError 2: No such file or directory
#|v01 same
#|
#|-- collect_engine: a filter over a scan
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"name"
#|col	f32	"score"
#|col	bool	"ok"
#|row	3	"bo,b"	null	true
#|row	4	"dee"	0x40900000	null
#|row	5	""	0x3f000000	false
#|v01 same
