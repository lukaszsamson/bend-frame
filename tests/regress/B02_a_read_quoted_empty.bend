#! xfail B02-a
# B02-a (Astra B): reading `"",x` gives null for the quoted empty string. DESIGN.md
# 15.6.1: a quoted field of a str column is the valid content verbatim ("" is the empty
# string); an unquoted empty field is null; numeric columns read both as null. Polars 2.0.0
# read_csv agrees on the first two; on the third it infers n as str ("" is evidence of a
# string there), with schema n=u32 it reads [null, 1] like the contract (regress_expect.py).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    # a,b / "",x / ,z  ->  a = ["", null]
    R.csv3("B02-a quoted-empty-vs-null", "tests/regress/data/B02_a_quoted_empty.csv")
    # one column holding "" (not a blank line): one valid empty string
    R.csv3("B02-a one-column", "tests/regress/data/B02_a_one_col.csv")
    # a quoted empty field in a u32 column is null
    R.csv3("B02-a numeric", "tests/regress/data/B02_a_numeric.csv")
#|-- B02-a quoted-empty-vs-null eager
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	""	"x"
#|row	null	"z"
#|
#|-- B02-a quoted-empty-vs-null raw
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	""	"x"
#|row	null	"z"
#|
#|-- B02-a quoted-empty-vs-null opt
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	""	"x"
#|row	null	"z"
#|
#|-- B02-a one-column eager
#|frame
#|height	1
#|width	1
#|col	str	"x"
#|row	""
#|
#|-- B02-a one-column raw
#|frame
#|height	1
#|width	1
#|col	str	"x"
#|row	""
#|
#|-- B02-a one-column opt
#|frame
#|height	1
#|width	1
#|col	str	"x"
#|row	""
#|
#|-- B02-a numeric eager
#|frame
#|height	2
#|width	2
#|col	u32	"n"
#|col	str	"s"
#|row	null	"a"
#|row	1	"b"
#|
#|-- B02-a numeric raw
#|frame
#|height	2
#|width	2
#|col	u32	"n"
#|col	str	"s"
#|row	null	"a"
#|row	1	"b"
#|
#|-- B02-a numeric opt
#|frame
#|height	2
#|width	2
#|col	u32	"n"
#|col	str	"s"
#|row	null	"a"
#|row	1	"b"
#|
