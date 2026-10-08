# B02-g: ragged rows. DESIGN.md 15.6.2: a short or long record is
# ParseError{line, "expected <k> fields, got <g>"} (strict; Polars fills a short row with
# nulls: documented departure, and errors on a long one). Eager and lazy.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    R.csv3("B02-g short-row", "tests/regress/data/B02_g_short.csv")
    R.csv3("B02-g long-row", "tests/regress/data/B02_g_long.csv")
#|-- B02-g short-row eager
#|error	ParseError at line 3: expected 2 fields, got 1
#|
#|-- B02-g short-row raw
#|error	ParseError at line 3: expected 2 fields, got 1
#|
#|-- B02-g short-row opt
#|error	ParseError at line 3: expected 2 fields, got 1
#|
#|-- B02-g long-row eager
#|error	ParseError at line 3: expected 2 fields, got 3
#|
#|-- B02-g long-row raw
#|error	ParseError at line 3: expected 2 fields, got 3
#|
#|-- B02-g long-row opt
#|error	ParseError at line 3: expected 2 fields, got 3
#|
