# T6 coverage: writing CSV: write_opts, write_csv, write_csv_opts (with csv_opts / read_csv_schema to
# read the files back). The frame w holds nulls, a valid empty string, a separator, a quote and a
# newline inside strings, and f32 NaN / inf / -0.0. For each option set the test writes w, checks the
# result is the same frame, and reads the file back twice with the same CSV options: as text (every
# column str: the exact fields) and as the typed columns (the round trip). The default write's whole
# text is also printed (Csv.render, via rx `render`). The lazy twin: a collected plan and its eager
# twin write files that read back equal. Refusals: a separator that is a quote / CR / LF (before the
# file is touched), a path that cannot be written (IoError), an error value passed through.
# Expectations: DESIGN.md 15.6 (a valid "" or a field holding the separator, a quote, CR or LF is
# quoted, null is an empty unquoted field), 15.2.7, confirmed by bench/coverage/csv_write.py (Polars
# 2.0.0 write_csv): the files Polars writes for the same frame read back to the same cells; departures
# applied there: f32 NaN / inf / -0.0 are written `nan` / `inf` / `-0` (Polars `NaN` / `inf` / `-0.0`),
# a separator that is a quote / CR / LF is refused (Polars refuses only some), a zero-byte file read
# with a schema is `csv schema: 2 dtypes for 0 columns`.
#@ cover write_csv,write_csv_opts,write_opts success null empty invalid eager lazy
#@ cover csv_opts,read_csv_schema success null empty invalid eager
#@ cover then_io,from_columns,then success eager
#@ na then_io,from_columns,then null empty invalid lazy -- the cases here only chain / build the frame being written; their own null / empty / invalid cases are in api_frames.bend
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../regress/lib/rx.bend as R

def w() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], DF.t_u32()),
    R.mk("s", [R.s("x"), R.s(""), R.null(), R.s("a,b"), R.s("q\"q"), R.s("l1\nl2")], DF.t_str()),
    R.mk("f", [R.f(1.5), R.null(), R.f(R.nan()), R.f(R.inf()), R.f(R.nzero()), R.f(0.123456)], DF.t_f32()),
    R.mk("b", [R.b(True{}), R.null(), R.b(False{}), R.b(True{}), R.null(), R.b(False{})], DF.t_bool()),
    R.mk("i", [R.ineg(1), R.null(), R.i(0), R.ineg(2147483648), R.i(2147483647), R.null()], DF.t_i32())])

def wz() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [], DF.t_u32()), R.mk("s", [], DF.t_str())])

def ws() -> List<&2, D.DType>:
  [DF.t_u32(), DF.t_str(), DF.t_f32(), DF.t_bool(), DF.t_i32()]

def ss() -> List<&2, D.DType>:
  [DF.t_str(), DF.t_str(), DF.t_str(), DF.t_str(), DF.t_str()]

def wzs() -> List<&2, D.DType>:
  [DF.t_u32(), DF.t_str()]

def wzt() -> List<&2, D.DType>:
  [DF.t_str(), DF.t_str()]

def p1() -> String:
  "/tmp/bend_frame_cov_w1.csv"

def p2() -> String:
  "/tmp/bend_frame_cov_w2.csv"

def p3() -> String:
  "/tmp/bend_frame_cov_w3.csv"

def back(+tag: String, +path: String, +o: DF.CsvOpts(), +ts: List<&2, D.DType>) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- DF.read_csv_schema(path, o, ts)
    IO.print("-- " ++ tag ++ "\n" ++ DF.dump(r))

# the write's result is the frame it was given
def same(+tag: String, +ref: String, x: E.ResT(C.Frame)) -> IO(Unit):
  IO.print("-- " ++ tag ++ " result: " ++ R.agree.v(ref, DF.dump(x)) ++ "\n")

def wr(+tag: String, +ref: String, r: E.ResT(C.Frame), +path: String) -> IO(Unit):
  do IO<Unit>:
    x : E.ResT(C.Frame) <- DF.write_csv(r, path)
    same(tag, ref, x)

def wo(+tag: String, +ref: String, r: E.ResT(C.Frame), +path: String, +o: DF.CsvWriteOpts()) -> IO(Unit):
  do IO<Unit>:
    x : E.ResT(C.Frame) <- DF.write_csv_opts(r, path, o)
    same(tag, ref, x)

# the result of a write that failed, as the dump line
def fail(+tag: String, x: E.ResT(C.Frame)) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\n" ++ DF.dump(x))

# a write_csv_opts that fails: its result dump
def wf(+tag: String, r: E.ResT(C.Frame), +path: String, +o: DF.CsvWriteOpts()) -> IO(Unit):
  do IO<Unit>:
    x : E.ResT(C.Frame) <- DF.write_csv_opts(r, path, o)
    fail(tag, x)

def bad() -> E.ResT(C.Frame):
  DF.from_columns([R.mk("a", [R.u(1)], DF.t_u32()), R.mk("a", [R.u(2)], DF.t_u32())])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(R.render("write_csv default", w()))
    wr("write_csv default", DF.dump(w()), w(), p1())
    back("write_csv default read back as text", p1(), DF.csv_opts(',', True{}, 100), ss())
    back("write_csv default read back typed", p1(), DF.csv_opts(',', True{}, 100), ws())
    wo("write_csv_opts semicolon, no header", DF.dump(w()), w(), p1(), DF.write_opts(';', False{}, None{}))
    back("write_csv_opts semicolon, no header, as text", p1(), DF.csv_opts(';', False{}, 100), ss())
    back("write_csv_opts semicolon, no header, typed", p1(), DF.csv_opts(';', False{}, 100), ws())
    wo("write_csv_opts header, tab separator", DF.dump(w()), w(), p1(), DF.write_opts('\t', True{}, None{}))
    back("write_csv_opts header, tab separator, as text", p1(), DF.csv_opts('\t', True{}, 100), ss())
    back("write_csv_opts header, tab separator, typed", p1(), DF.csv_opts('\t', True{}, 100), ws())
    wo("write_csv_opts float precision 2", DF.dump(w()), w(), p1(), DF.write_opts(',', True{}, Some{2}))
    back("write_csv_opts float precision 2, as text", p1(), DF.csv_opts(',', True{}, 100), ss())
    back("write_csv_opts float precision 2, typed", p1(), DF.csv_opts(',', True{}, 100), ws())
    wr("write_csv zero rows", DF.dump(wz()), wz(), p1())
    back("write_csv zero rows read back typed", p1(), DF.csv_opts(',', True{}, 100), wzs())
    back("write_csv zero rows read back as text", p1(), DF.csv_opts(',', True{}, 100), wzt())
    wo("write_csv_opts zero rows, no header", DF.dump(wz()), wz(), p1(), DF.write_opts(',', False{}, None{}))
    back("invalid read_csv_schema of the file a header-less zero-row write left", p1(), DF.csv_opts(',', False{}, 100), wzs())
    wr("write_csv zero columns", DF.dump(R.zcols(3)), R.zcols(3), p1())
    wf("invalid write_csv_opts: a quote separator", w(), p2(), DF.write_opts('"', True{}, None{}))
    wf("invalid write_csv_opts: a newline separator", w(), p2(), DF.write_opts('\n', True{}, None{}))
    wf("invalid write_csv_opts: a carriage return separator", w(), p2(), DF.write_opts('\r', False{}, Some{3}))
    wf("invalid write_csv_opts to a directory that does not exist", w(), "/no/such/dir/bend_frame_cov.csv", DF.write_opts(';', True{}, None{}))
    r1 : E.ResT(C.Frame) <- DF.write_csv(w(), "/no/such/dir/bend_frame_cov.csv")
    fail("invalid write_csv to a directory that does not exist", r1)
    r4 : E.ResT(C.Frame) <- DF.write_csv(bad(), p2())
    fail("write_csv passes an error through", r4)
    wf("write_csv_opts passes an error through", bad(), p2(), DF.write_opts(',', True{}, None{}))
    r3 : E.ResT(C.Frame) <- DF.then_io(w(), f => DF.write_csv(Done{f}, p3()))
    same("then_io into write_csv", DF.dump(w()), r3)
    q : E.ResT(C.Frame) <- DF.collect(DF.lazy_head(DF.lazy_sort(R.src("w", w()), [DF.desc("a")]), 4), R.env1("w", w()))
    x1 : E.ResT(C.Frame) <- DF.write_csv(q, p2())
    x2 : E.ResT(C.Frame) <- DF.write_csv(DF.then(w(), f => DF.then(DF.sort(f, [DF.desc("a")]), g => DF.head(g, 4))), p1())
    IO.print("-- a collected plan and its eager twin write the same frame: " ++ R.agree.v(DF.dump(x1), DF.dump(x2)) ++ "\n")
    ra : E.ResT(C.Frame) <- DF.read_csv_schema(p2(), DF.csv_opts(',', True{}, 100), ws())
    rb : E.ResT(C.Frame) <- DF.read_csv_schema(p1(), DF.csv_opts(',', True{}, 100), ws())
    IO.print("-- and read back equal: " ++ R.agree.v(DF.dump(ra), DF.dump(rb)) ++ "\n")
#|-- write_csv default csv
#|"a,s,f,b,i\n1,x,1.5,true,-1\n2,\"\",,,\n3,,nan,false,0\n4,\"a,b\",inf,true,-2147483648\n5,\"q\"\"q\",-0,,2147483647\n6,\"l1\nl2\",0.123456,false,\n"
#|
#|-- write_csv default result: same
#|
#|-- write_csv default read back as text
#|frame
#|height	6
#|width	5
#|col	str	"a"
#|col	str	"s"
#|col	str	"f"
#|col	str	"b"
#|col	str	"i"
#|row	"1"	"x"	"1.5"	"true"	"-1"
#|row	"2"	""	null	null	null
#|row	"3"	null	"nan"	"false"	"0"
#|row	"4"	"a,b"	"inf"	"true"	"-2147483648"
#|row	"5"	"q\"q"	"-0"	null	"2147483647"
#|row	"6"	"l1\nl2"	"0.123456"	"false"	null
#|
#|-- write_csv default read back typed
#|frame
#|height	6
#|width	5
#|col	u32	"a"
#|col	str	"s"
#|col	f32	"f"
#|col	bool	"b"
#|col	i32	"i"
#|row	1	"x"	0x3fc00000	true	-1
#|row	2	""	null	null	null
#|row	3	null	0x7fc00000	false	0
#|row	4	"a,b"	0x7f800000	true	-2147483648
#|row	5	"q\"q"	0x80000000	null	2147483647
#|row	6	"l1\nl2"	0x3dfcd680	false	null
#|
#|-- write_csv_opts semicolon, no header result: same
#|
#|-- write_csv_opts semicolon, no header, as text
#|frame
#|height	6
#|width	5
#|col	str	"column_0"
#|col	str	"column_1"
#|col	str	"column_2"
#|col	str	"column_3"
#|col	str	"column_4"
#|row	"1"	"x"	"1.5"	"true"	"-1"
#|row	"2"	""	null	null	null
#|row	"3"	null	"nan"	"false"	"0"
#|row	"4"	"a,b"	"inf"	"true"	"-2147483648"
#|row	"5"	"q\"q"	"-0"	null	"2147483647"
#|row	"6"	"l1\nl2"	"0.123456"	"false"	null
#|
#|-- write_csv_opts semicolon, no header, typed
#|frame
#|height	6
#|width	5
#|col	u32	"column_0"
#|col	str	"column_1"
#|col	f32	"column_2"
#|col	bool	"column_3"
#|col	i32	"column_4"
#|row	1	"x"	0x3fc00000	true	-1
#|row	2	""	null	null	null
#|row	3	null	0x7fc00000	false	0
#|row	4	"a,b"	0x7f800000	true	-2147483648
#|row	5	"q\"q"	0x80000000	null	2147483647
#|row	6	"l1\nl2"	0x3dfcd680	false	null
#|
#|-- write_csv_opts header, tab separator result: same
#|
#|-- write_csv_opts header, tab separator, as text
#|frame
#|height	6
#|width	5
#|col	str	"a"
#|col	str	"s"
#|col	str	"f"
#|col	str	"b"
#|col	str	"i"
#|row	"1"	"x"	"1.5"	"true"	"-1"
#|row	"2"	""	null	null	null
#|row	"3"	null	"nan"	"false"	"0"
#|row	"4"	"a,b"	"inf"	"true"	"-2147483648"
#|row	"5"	"q\"q"	"-0"	null	"2147483647"
#|row	"6"	"l1\nl2"	"0.123456"	"false"	null
#|
#|-- write_csv_opts header, tab separator, typed
#|frame
#|height	6
#|width	5
#|col	u32	"a"
#|col	str	"s"
#|col	f32	"f"
#|col	bool	"b"
#|col	i32	"i"
#|row	1	"x"	0x3fc00000	true	-1
#|row	2	""	null	null	null
#|row	3	null	0x7fc00000	false	0
#|row	4	"a,b"	0x7f800000	true	-2147483648
#|row	5	"q\"q"	0x80000000	null	2147483647
#|row	6	"l1\nl2"	0x3dfcd680	false	null
#|
#|-- write_csv_opts float precision 2 result: same
#|
#|-- write_csv_opts float precision 2, as text
#|frame
#|height	6
#|width	5
#|col	str	"a"
#|col	str	"s"
#|col	str	"f"
#|col	str	"b"
#|col	str	"i"
#|row	"1"	"x"	"1.50"	"true"	"-1"
#|row	"2"	""	null	null	null
#|row	"3"	null	"nan"	"false"	"0"
#|row	"4"	"a,b"	"inf"	"true"	"-2147483648"
#|row	"5"	"q\"q"	"-0.00"	null	"2147483647"
#|row	"6"	"l1\nl2"	"0.12"	"false"	null
#|
#|-- write_csv_opts float precision 2, typed
#|frame
#|height	6
#|width	5
#|col	u32	"a"
#|col	str	"s"
#|col	f32	"f"
#|col	bool	"b"
#|col	i32	"i"
#|row	1	"x"	0x3fc00000	true	-1
#|row	2	""	null	null	null
#|row	3	null	0x7fc00000	false	0
#|row	4	"a,b"	0x7f800000	true	-2147483648
#|row	5	"q\"q"	0x80000000	null	2147483647
#|row	6	"l1\nl2"	0x3df5c28f	false	null
#|
#|-- write_csv zero rows result: same
#|
#|-- write_csv zero rows read back typed
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|
#|-- write_csv zero rows read back as text
#|frame
#|height	0
#|width	2
#|col	str	"a"
#|col	str	"s"
#|
#|-- write_csv_opts zero rows, no header result: same
#|
#|-- invalid read_csv_schema of the file a header-less zero-row write left
#|error	InvalidOperation: csv schema: 2 dtypes for 0 columns
#|
#|-- write_csv zero columns result: same
#|
#|-- invalid write_csv_opts: a quote separator
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- invalid write_csv_opts: a newline separator
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- invalid write_csv_opts: a carriage return separator
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- invalid write_csv_opts to a directory that does not exist
#|error	IoError 2: No such file or directory
#|
#|-- invalid write_csv to a directory that does not exist
#|error	IoError 2: No such file or directory
#|
#|-- write_csv passes an error through
#|error	DuplicateColumn: a
#|
#|-- write_csv_opts passes an error through
#|error	DuplicateColumn: a
#|
#|-- then_io into write_csv result: same
#|
#|-- a collected plan and its eager twin write the same frame: same
#|
#|-- and read back equal: same
#|
