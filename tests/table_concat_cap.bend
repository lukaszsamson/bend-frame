# concat_vertical and the 2^23 row cap (DESIGN.md 15.8), eager and lazy: zero-column frames
# Frame{h, []} carry a height without data, so nothing big is allocated. The lazy chain checks
# the cap at each binary step on the running (saturating) height sum, and the eager concat does
# the same after its schema checks, so both report the first prefix whose sum passes the cap.
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/plan.bend as P
import ./regress/lib/rx.bend as R

def z(h: U32) -> E.ResT(C.Frame):
  Done{C.Frame{h, Nil{}}}

def env3(+a: U32, +b: U32, +c: U32) -> P.Env:
  R.env_add(R.env_add(R.env1("a", z(a)), "b", z(b)), "c", z(c))

def plan3(+a: U32, +b: U32, +c: U32) -> P.Plan:
  DF.lazy_concat_vertical([R.src("a", z(a)), R.src("b", z(b)), R.src("c", z(c))])

def case3(+tag: String, +a: U32, +b: U32, +c: U32) -> IO(Unit):
  R.four(tag, DF.concat_vertical([C.Frame{a, Nil{}}, C.Frame{b, Nil{}}, C.Frame{c, Nil{}}]), plan3(a, b, c), env3(a, b, c), env3(a, b, c), env3(a, b, c))

def main() -> IO(Unit):
  do IO<Unit>:
    case3("at the cap", 8388600, 7, 1)
    case3("first prefix over the cap", 8388600, 9, 5)
    case3("second prefix over the cap", 8388600, 8, 5)
    case3("a sum that would wrap saturates", 2147483648, 2147483648, 1)
#|-- at the cap
#|frame
#|height	8388608
#|width	0
#|raw same, opt same, full same
#|
#|-- first prefix over the cap
#|error	InvalidOperation: too many rows: 8388609 exceeds 8388608
#|raw same, opt same, full same
#|
#|-- second prefix over the cap
#|error	InvalidOperation: too many rows: 8388613 exceeds 8388608
#|raw same, opt same, full same
#|
#|-- a sum that would wrap saturates
#|error	InvalidOperation: too many rows: 4294967295 exceeds 8388608
#|raw same, opt same, full same
