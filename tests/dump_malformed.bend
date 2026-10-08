# DF.dump of frames that break the height invariant (review of M0, DESIGN.md 15.1): a column
# longer than the height must not dump like the truncated, valid frame (it ends in an `excess`
# line), and a shorter one prints `?` cells. Neither is in the grammar, so bench/check.py
# rejects both dumps (bench/tests/test_check.py: test_dump_marks_inconsistent_heights).
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C

def mk.k(name: String, r: E.ResT(C.Column)) -> List<&1, C.Named>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{c}:
      [C.Named{name, c}]

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> List<&1, C.Named>:
  mk.k(name, C.Column.from_scalars(xs, t))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- longer")
    IO.print(DF.dump_frame(C.Frame{1, mk("a", [D.SU32{1}, D.SU32{2}], D.TU32{})}))
    IO.print("-- shorter")
    IO.print(DF.dump_frame(C.Frame{3, mk("a", [D.SU32{1}, D.SU32{2}], D.TU32{})}))
#|-- longer
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	1
#|excess
#|
#|-- shorter
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	2
#|row	?
