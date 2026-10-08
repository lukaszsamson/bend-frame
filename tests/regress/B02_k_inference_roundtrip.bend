# B02-k: README implied that inference round-trips numeric-looking strings. DESIGN.md
# 15.6.5: no such claim. Pinned here: a str column ["007", "1"] written and read back
# under inference comes back as u32 [7, 1] (Polars 2.0.0: i64 [7, 1], same values). The
# README part of the row (M1) is not testable here.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def path() -> String:
  "/tmp/bend_frame_regress_B02_k.csv"

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("s", [R.s("007"), R.s("1")], D.TStr{})])

def main() -> IO(Unit):
  do IO<Unit>:
    w : E.ResT(C.Frame) <- DF.write_csv(t(), path())
    IO.print(R.show("B02-k write", "result", w))
    R.csv3("B02-k round-trip", path())
#|-- B02-k write result
#|frame
#|height	2
#|width	1
#|col	str	"s"
#|row	"007"
#|row	"1"
#|
#|-- B02-k round-trip eager
#|frame
#|height	2
#|width	1
#|col	u32	"s"
#|row	7
#|row	1
#|
#|-- B02-k round-trip raw
#|frame
#|height	2
#|width	1
#|col	u32	"s"
#|row	7
#|row	1
#|
#|-- B02-k round-trip opt
#|frame
#|height	2
#|width	1
#|col	u32	"s"
#|row	7
#|row	1
#|
