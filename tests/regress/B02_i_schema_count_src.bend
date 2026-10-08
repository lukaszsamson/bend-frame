# B02-i: an explicit schema was reachable only through src/ (Csv.read_with) and its
# dtype-count error text was unverified. DESIGN.md 15.2.7 / 15.6.3: dtypes by column
# position, [] means infer; a count mismatch is InvalidOperation{"csv schema: <d> dtypes
# for <k> columns"}; a cell that does not parse under the given dtype is
# ParseError{line, "column <name>: cannot parse \"<text>\" as <dtype>"}. This file checks
# the src entry (passes today); the facade DF.read_csv_schema is M3 API:
# tests/regress/pending/B02_i_read_csv_schema.bend.txt.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/csv.bend as V
import ./lib/rx.bend as R

def rd(+tag: String, +path: String, +ts: List<&2, D.DType>) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- V.Csv.read_with(path, V.Csv.default(), ts)
    IO.print(R.show(tag, "eager", r))

def main() -> IO(Unit):
  do IO<Unit>:
    rd("B02-i count", "tests/regress/data/B02_h_crlf.csv", [D.TStr{}])
    rd("B02-i explicit", "tests/regress/data/B02_h_crlf.csv", [D.TStr{}, D.TI32{}])
    rd("B02-i bad-cell", "tests/regress/data/B02_h_crlf.csv", [D.TU32{}, D.TU32{}])
#|-- B02-i count eager
#|error	InvalidOperation: csv schema: 1 dtypes for 2 columns
#|
#|-- B02-i explicit eager
#|frame
#|height	2
#|width	2
#|col	str	"s"
#|col	i32	"n"
#|row	"a,b"	1
#|row	"c"	2
#|
#|-- B02-i bad-cell eager
#|error	ParseError at line 2: column s: cannot parse "a,b" as u32
#|
