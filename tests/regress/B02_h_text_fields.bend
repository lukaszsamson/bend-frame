#! xfail B02-h
# B02-h: non-ASCII fields, multi-line fields and escaped quotes were not in a differential
# test. DESIGN.md 15.6.2: UTF-8 verbatim; "" inside quotes is one quote; CR/LF inside
# quotes belong to the field; CRLF line ends are accepted; error line numbers are the
# physical line of the record's first line. Polars 2.0.0 reads the first two files to the
# same frames (regress_expect.py). Eager and lazy.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    R.csv3("B02-h text", "tests/regress/data/B02_h_text.csv")
    R.csv3("B02-h crlf", "tests/regress/data/B02_h_crlf.csv")
    # a,b / "x<LF>y",1 / 2  ->  the short record starts on line 4
    R.csv3("B02-h line-after-multiline", "tests/regress/data/B02_h_line.csv")
#|-- B02-h text eager
#|frame
#|height	5
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	"日本語"	1
#|row	"a \"q\" b"	2
#|row	"multi\nline"	3
#|row	"x\r\ny"	4
#|row	"ü"	5
#|
#|-- B02-h text raw
#|frame
#|height	5
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	"日本語"	1
#|row	"a \"q\" b"	2
#|row	"multi\nline"	3
#|row	"x\r\ny"	4
#|row	"ü"	5
#|
#|-- B02-h text opt
#|frame
#|height	5
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	"日本語"	1
#|row	"a \"q\" b"	2
#|row	"multi\nline"	3
#|row	"x\r\ny"	4
#|row	"ü"	5
#|
#|-- B02-h crlf eager
#|frame
#|height	2
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	"a,b"	1
#|row	"c"	2
#|
#|-- B02-h crlf raw
#|frame
#|height	2
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	"a,b"	1
#|row	"c"	2
#|
#|-- B02-h crlf opt
#|frame
#|height	2
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	"a,b"	1
#|row	"c"	2
#|
#|-- B02-h line-after-multiline eager
#|error	ParseError at line 4: expected 2 fields, got 1
#|
#|-- B02-h line-after-multiline raw
#|error	ParseError at line 4: expected 2 fields, got 1
#|
#|-- B02-h line-after-multiline opt
#|error	ParseError at line 4: expected 2 fields, got 1
#|
