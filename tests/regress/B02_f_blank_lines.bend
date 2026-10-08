#! xfail B02-f
# B02-f: blank-line handling (1 column vs k columns, and vs Polars) was undocumented.
# DESIGN.md 15.6.2: in a 1-column file a blank line is a null row (Polars same); with
# k > 1 columns it is skipped (Polars: an all-null row; documented departure); error line
# numbers still count it. Eager and lazy.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    # a / 1 / (blank) / 3  ->  [1, null, 3]
    R.csv3("B02-f one-column", "tests/regress/data/B02_f_one_col.csv")
    # a,b / 1,x / (blank) / 3,y  ->  two rows (departure)
    R.csv3("B02-f two-columns", "tests/regress/data/B02_f_two_col.csv")
    # a,b / 1,x / (blank) / 3  ->  the short record is line 4
    R.csv3("B02-f line-number", "tests/regress/data/B02_f_line.csv")
#|-- B02-f one-column eager
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	null
#|row	3
#|
#|-- B02-f one-column raw
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	null
#|row	3
#|
#|-- B02-f one-column opt
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	null
#|row	3
#|
#|-- B02-f two-columns eager
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	1	"x"
#|row	3	"y"
#|
#|-- B02-f two-columns raw
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	1	"x"
#|row	3	"y"
#|
#|-- B02-f two-columns opt
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	1	"x"
#|row	3	"y"
#|
#|-- B02-f line-number eager
#|error	ParseError at line 4: expected 2 fields, got 1
#|
#|-- B02-f line-number raw
#|error	ParseError at line 4: expected 2 fields, got 1
#|
#|-- B02-f line-number opt
#|error	ParseError at line 4: expected 2 fields, got 1
#|
