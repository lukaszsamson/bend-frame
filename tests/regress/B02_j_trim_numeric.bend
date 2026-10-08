# B02-j: numeric fields are trimmed on read while Polars infers str for " 1 ".
# DESIGN.md 15.6.1 (documented departure): a u32/i32/f32/bool field is parsed from its
# trimmed text, quoted or not; a str field is never trimmed. So a = [1, 2, 3] (u32) and
# s = [" s ", "t", "u"]. Polars 2.0.0 infers a as str (regress_expect.py prints it).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    R.csv3("B02-j trim", "tests/regress/data/B02_j_trim.csv")
#|-- B02-j trim eager
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|row	1	" s "
#|row	2	"t"
#|row	3	"u"
#|
#|-- B02-j trim raw
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|row	1	" s "
#|row	2	"t"
#|row	3	"u"
#|
#|-- B02-j trim opt
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|row	1	" s "
#|row	2	"t"
#|row	3	"u"
#|
