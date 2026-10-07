# can a test one level below the root import ../src modules?
import Base
import ./../src/dtype.bend as D

def main() -> IO(Unit):
  IO.print(D.DType.show(D.TF32{}))

#|f32
