# p20: a law about a Type-kinded value (a Column owning an Array): head
# keeps min(n, len) rows. The proof is a case split on the constructor;
# both sides then compute to the same U32.min.
import Base

type Column is Type:
  CU32{len: U32, data: Array<U32>}
  CF32{len: U32, data: Array<F32>}

def Column.len(c: Column) -> Column & U32:
  match c:
    case CU32{+n, d}:
      (CU32{n, d}, n)
    case CF32{+n, d}:
      (CF32{n, d}, n)

# head only lowers the logical length; the array is untouched
def Column.head(c: Column, +n: U32) -> Column:
  match c:
    case CU32{m, d}:
      CU32{U32.min(n, m), d}
    case CF32{m, d}:
      CF32{U32.min(n, m), d}

def main() -> IO(Unit):
  IO.print(U32.show(Pair.snd(Column, U32, Column.len(Column.head(CF32{5, [0.0 : F32*8n]}, 3)))))

#|3
