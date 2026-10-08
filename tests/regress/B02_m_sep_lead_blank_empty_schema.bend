# B02 leftovers from the M1 CSV review (DESIGN.md 14 "M1 B02 review", 15.6.2, 15.6.3):
#  1. CsvOpts.sep / CsvWriteOpts.sep: a double quote, CR or LF cannot be told from the quoting and
#     the line ends, so read, scan and write refuse them with
#     InvalidOperation{"csv: separator must not be a double quote, CR or LF"} (before any file
#     is opened). Any other single char (';', TAB, '.') still works.
#  2. Blank lines before the header are skipped (Polars: `\n\na,b\n1,2\n` reads a:1 b:2); without a
#     header they are data (a null record in one column). Physical line numbers are unchanged.
#  2b. Without a header the column count is the first NON-blank record's: `\n1,2\n3,4\n` has two
#     columns and its leading blank line is skipped like any blank line in k > 1 columns (it used to
#     give one column and a ParseError on `1,2`). A file of blank lines only is one column of nulls.
#  1b. read refuses a bad separator before opening the file, as scan does (a missing file with a
#     bad separator used to be an IoError on read and an InvalidOperation on scan).
#  3. read_csv_schema of an empty file (or one of blank lines only, with a header) checks the dtype
#     count: [] gives the (0, 0) frame, d > 0 dtypes is "csv schema: d dtypes for 0 columns".
# Not changed, documented (DESIGN.md 14): a (0, 0) frame writes "\n" and reads back as one column
# named "" with 0 rows; a lone CR at the very end of the input is dropped as a line end.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/csv.bend as V
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def opts() -> V.CsvOpts:
  V.CsvOpts{',', True{}, 100}

def nohdr() -> V.CsvOpts:
  V.CsvOpts{',', False{}, 100}

def rd(+tag: String, +text: String, o: V.CsvOpts, ts: List<&2, D.DType>) -> String:
  R.show(tag, "eager", V.Csv.parse_with(text, o, ts))

def fields(xs: List<&2, V.CsvField>) -> String:
  match xs:
    case Nil{}:
      ""
    case V.CsvField{n, t} <> rest:
      n ++ ":" ++ D.DType.show(t) ++ " " ++ fields(rest)

def inf.k(r: E.Res(List<&2, V.CsvField>)) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.Err.show(e)
    case Done{xs}:
      fields(xs)

def inf(+tag: String, +text: String, o: V.CsvOpts) -> String:
  "-- " ++ tag ++ "\n" ++ inf.k(V.Csv.infer(text, o)) ++ "\n"


def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1)], D.TU32{})])

def scan.k(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print(R.errs(tag, e))
    case Done{p}:
      IO.print("-- " ++ tag ++ " scan unexpectedly succeeded")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(rd("B02-m lead-blank", "\n\na,b\n1,2\n", opts(), Nil{}))
    IO.print(rd("B02-m lead-blank-crlf", "\r\n\r\na,b\r\n1,2\r\n", opts(), Nil{}))
    IO.print(rd("B02-m lead-blank-only", "\n\n", opts(), Nil{}))
    IO.print(rd("B02-m lead-blank-one-col", "\n1\n2\n", opts(), Nil{}))
    IO.print(rd("B02-m lead-blank-no-header", "\n1\n2\n", nohdr(), Nil{}))
    IO.print(rd("B02-m inner-blank-unchanged", "a\n\n1\n", opts(), Nil{}))
    IO.print(rd("B02-m lead-blank-line-numbers", "\n\na,b\n1,2\n3\n", opts(), Nil{}))
    IO.print(rd("B02-m lead-blank-explicit", "\na,b\n1,x\n", opts(), [D.TU32{}, D.TStr{}]))
    IO.print(inf("B02-m infer-lead-blank", "\n\na,b\n1,x\n", opts()))
    IO.print(rd("B02-m sep-quote", "a\"b\n1\n", V.CsvOpts{'"', True{}, 100}, Nil{}))
    IO.print(rd("B02-m sep-lf", "a\n1\n", V.CsvOpts{Chr{10}, True{}, 100}, Nil{}))
    IO.print(rd("B02-m sep-cr", "a\n1\n", V.CsvOpts{Chr{13}, True{}, 100}, Nil{}))
    IO.print(rd("B02-m sep-explicit-schema", "a\n1\n", V.CsvOpts{'"', True{}, 100}, [D.TU32{}]))
    IO.print(inf("B02-m sep-infer", "a\n1\n", V.CsvOpts{'"', True{}, 100}))
    IO.print(rd("B02-m sep-tab-ok", "a\tb\n1\t2\n", V.CsvOpts{Chr{9}, True{}, 100}, Nil{}))
    IO.print(rd("B02-m sep-semicolon-ok", "a;b\n1;2\n", V.CsvOpts{';', True{}, 100}, Nil{}))
    r0 : E.ResT(C.Frame) <- DF.read_csv_opts("tests/regress/data/B02_e_semicolon.csv", DF.csv_opts('"', True{}, 100))
    IO.print(R.show("B02-m sep-read-file", "eager", r0))
    rp : E.Res(P.Plan) <- DF.scan_csv_opts("tests/regress/data/B02_e_semicolon.csv", DF.csv_opts(Chr{10}, True{}, 100))
    scan.k("B02-m sep-scan", rp)
    w : E.ResT(C.Frame) <- DF.write_csv_opts(t(), "/tmp/bend_frame_regress_B02_m.csv", DF.write_opts('"', True{}, None{}))
    IO.print(R.show("B02-m sep-write", "eager", w))
    w2 : E.ResT(C.Frame) <- DF.write_csv_opts(t(), "/tmp/bend_frame_regress_B02_m.csv", DF.write_opts(Chr{13}, False{}, None{}))
    IO.print(R.show("B02-m sep-write-cr", "eager", w2))
    e0 : E.ResT(C.Frame) <- DF.read_csv_schema("tests/regress/data/B02_scan_empty.csv", DF.csv_opts(',', True{}, 100), [])
    IO.print(R.show("B02-m empty-schema-none", "eager", e0))
    e1 : E.ResT(C.Frame) <- DF.read_csv_schema("tests/regress/data/B02_scan_empty.csv", DF.csv_opts(',', True{}, 100), [D.TU32{}, D.TStr{}])
    IO.print(R.show("B02-m empty-schema-count", "eager", e1))
    e2 : E.ResT(C.Frame) <- DF.read_csv_schema("tests/regress/data/B02_scan_empty.csv", DF.csv_opts(',', False{}, 100), [D.TU32{}])
    IO.print(R.show("B02-m empty-schema-count-no-header", "eager", e2))
    IO.print(rd("B02-m blank-only-schema-count", "\n\n", opts(), [D.TU32{}]))
    IO.print(rd("B02-m nohdr-lead-blank-wide", "\n1,2\n3,4\n", nohdr(), Nil{}))
    IO.print(rd("B02-m nohdr-lead-blank-ragged", "\n\n1,2\n3\n", nohdr(), Nil{}))
    IO.print(rd("B02-m nohdr-blank-only", "\n\n", nohdr(), Nil{}))
    IO.print(inf("B02-m nohdr-infer-lead-blank", "\n1,x\n", nohdr()))
    m0 : E.ResT(C.Frame) <- DF.read_csv_opts("tests/regress/data/B02_m_missing.csv", DF.csv_opts('"', True{}, 100))
    IO.print(R.show("B02-m sep-read-missing-file", "eager", m0))
    m1 : E.ResT(C.Frame) <- DF.read_csv_schema("tests/regress/data/B02_m_missing.csv", DF.csv_opts(Chr{13}, True{}, 100), [D.TU32{}])
    IO.print(R.show("B02-m sep-read-schema-missing-file", "eager", m1))
#|-- B02-m lead-blank eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|
#|-- B02-m lead-blank-crlf eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|
#|-- B02-m lead-blank-only eager
#|frame
#|height	0
#|width	0
#|
#|-- B02-m lead-blank-one-col eager
#|frame
#|height	1
#|width	1
#|col	u32	"1"
#|row	2
#|
#|-- B02-m lead-blank-no-header eager
#|frame
#|height	3
#|width	1
#|col	u32	"column_0"
#|row	null
#|row	1
#|row	2
#|
#|-- B02-m inner-blank-unchanged eager
#|frame
#|height	2
#|width	1
#|col	u32	"a"
#|row	null
#|row	1
#|
#|-- B02-m lead-blank-line-numbers eager
#|error	ParseError at line 5: expected 2 fields, got 1
#|
#|-- B02-m lead-blank-explicit eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	1	"x"
#|
#|-- B02-m infer-lead-blank
#|a:u32 b:str 
#|
#|-- B02-m sep-quote eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-lf eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-cr eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-explicit-schema eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-infer
#|error InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-tab-ok eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|
#|-- B02-m sep-semicolon-ok eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|
#|-- B02-m sep-read-file eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-scan raw
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-scan opt
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-write eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-write-cr eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m empty-schema-none eager
#|frame
#|height	0
#|width	0
#|
#|-- B02-m empty-schema-count eager
#|error	InvalidOperation: csv schema: 2 dtypes for 0 columns
#|
#|-- B02-m empty-schema-count-no-header eager
#|error	InvalidOperation: csv schema: 1 dtypes for 0 columns
#|
#|-- B02-m blank-only-schema-count eager
#|error	InvalidOperation: csv schema: 1 dtypes for 0 columns
#|
#|-- B02-m nohdr-lead-blank-wide eager
#|frame
#|height	2
#|width	2
#|col	u32	"column_0"
#|col	u32	"column_1"
#|row	1	2
#|row	3	4
#|
#|-- B02-m nohdr-lead-blank-ragged eager
#|error	ParseError at line 4: expected 2 fields, got 1
#|
#|-- B02-m nohdr-blank-only eager
#|frame
#|height	2
#|width	1
#|col	str	"column_0"
#|row	null
#|row	null
#|
#|-- B02-m nohdr-infer-lead-blank
#|column_0:u32 column_1:str 
#|
#|-- B02-m sep-read-missing-file eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
#|-- B02-m sep-read-schema-missing-file eager
#|error	InvalidOperation: csv: separator must not be a double quote, CR or LF
#|
