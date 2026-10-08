#! xfail B02-b
# B02-b (Astra B): writing a valid "" emits an empty field, the same text as null.
# DESIGN.md 15.6.1 (writing): null -> empty field; a valid str is quoted when it is empty
# (or holds the separator, a quote, CR or LF). So "" writes as `""` and reads back as "",
# null writes as nothing and reads back as null. Polars 2.0.0 write_csv writes the same
# bytes. The round trip read also needs B02-a.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def path() -> String:
  "/tmp/bend_frame_regress_B02_b.csv"

# s: "", null, "x"; n: 1, 2, 3
def t() -> E.ResT(C.Frame):
  R.frame([R.mk("s", [R.s(""), R.null(), R.s("x")], D.TStr{}), R.mk("n", [R.u(1), R.u(2), R.u(3)], D.TU32{})])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(R.render("B02-b", t()))
    w : E.ResT(C.Frame) <- DF.write_csv(t(), path())
    IO.print(R.show("B02-b write", "result", w))
    R.csv3("B02-b round-trip", path())
#|-- B02-b csv
#|"s,n\n\"\",1\n,2\nx,3\n"
#|
#|-- B02-b write result
#|frame
#|height	3
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	""	1
#|row	null	2
#|row	"x"	3
#|
#|-- B02-b round-trip eager
#|frame
#|height	3
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	""	1
#|row	null	2
#|row	"x"	3
#|
#|-- B02-b round-trip raw
#|frame
#|height	3
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	""	1
#|row	null	2
#|row	"x"	3
#|
#|-- B02-b round-trip opt
#|frame
#|height	3
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	""	1
#|row	null	2
#|row	"x"	3
#|
