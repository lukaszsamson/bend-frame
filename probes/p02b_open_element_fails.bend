# p02b: NEGATIVE probe. An erased type parameter (-T) over Array<T> checks
# and runs in the evaluator, but the C emitter refuses it. Expected when
# compiling with `-o`: "Error: an open Array element type". Do not write
# library kernels this way; use ~T templates (p02).
#   ~/.bend/bin/bend probes/p02b_open_element_fails.bend -o /tmp/p02b
import Base

def Arr.count(-T: Data, a: Array<T>) -> U32:
  match a:
    case ALeaf{x}:
      1
    case ANode{xs, ys}:
      U32.add(Arr.count(T, xs), Arr.count(T, ys))

def main() -> IO(Unit):
  IO.print(U32.show(Arr.count(F32, [1.0 : F32*8n])))

#|8
