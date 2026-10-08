# B02-d (Fable 2): write_csv quoting of fields holding the separator, a quote, CR or LF
# was untested. DESIGN.md 15.6.1 (writing): such a str cell is quoted and a quote inside
# is doubled; header names are quoted by the same rule; leading/trailing spaces stay bare.
# Polars 2.0.0 write_csv writes the same bytes for these cells (regress_expect.py). The
# file read back gives the same frame (eager and lazy). No "" cell here (that is B02-b).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def path() -> String:
  "/tmp/bend_frame_regress_B02_d.csv"

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a,b", [R.s("x,y"), R.s("q\"q"), R.s(" s "), R.s("multi\nline"), R.s("cr\rx"), R.s("plain")], D.TStr{}),
    R.mk("c\"d", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(R.render("B02-d", t()))
    w : E.ResT(C.Frame) <- DF.write_csv(t(), path())
    IO.print(R.show("B02-d write", "result", w))
    R.csv3("B02-d round-trip", path())
#|-- B02-d csv
#|"\"a,b\",\"c\"\"d\"\n\"x,y\",1\n\"q\"\"q\",2\n s ,3\n\"multi\nline\",4\n\"cr\rx\",5\nplain,6\n"
#|
#|-- B02-d write result
#|frame
#|height	6
#|width	2
#|col	str	"a,b"
#|col	u32	"c\"d"
#|row	"x,y"	1
#|row	"q\"q"	2
#|row	" s "	3
#|row	"multi\nline"	4
#|row	"cr\rx"	5
#|row	"plain"	6
#|
#|-- B02-d round-trip eager
#|frame
#|height	6
#|width	2
#|col	str	"a,b"
#|col	u32	"c\"d"
#|row	"x,y"	1
#|row	"q\"q"	2
#|row	" s "	3
#|row	"multi\nline"	4
#|row	"cr\rx"	5
#|row	"plain"	6
#|
#|-- B02-d round-trip raw
#|frame
#|height	6
#|width	2
#|col	str	"a,b"
#|col	u32	"c\"d"
#|row	"x,y"	1
#|row	"q\"q"	2
#|row	" s "	3
#|row	"multi\nline"	4
#|row	"cr\rx"	5
#|row	"plain"	6
#|
#|-- B02-d round-trip opt
#|frame
#|height	6
#|width	2
#|col	str	"a,b"
#|col	u32	"c\"d"
#|row	"x,y"	1
#|row	"q\"q"	2
#|row	" s "	3
#|row	"multi\nline"	4
#|row	"cr\rx"	5
#|row	"plain"	6
#|
