# entry: re-exports are not a thing; the entry imports each module it uses
import Base
import ./src/dtype.bend as D
import ./src/column.bend as C

def show(r: C.Column & D.DType) -> String:
  (c, t) = r
  D.DType.show(t)

def main() -> IO(Unit):
  IO.print(show(C.Column.dtype(C.CF32{[1.0 : F32*2n]})))

#|f32
