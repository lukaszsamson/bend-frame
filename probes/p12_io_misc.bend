# p12: IO.args, IO.now (Nat ms), IO.thread_count, IO.die with a code.
#   ~/.bend/bin/bend probes/p12_io_misc.bend foo bar
import Base

# IO.args answers List<&1, String>; String.join wants &2: rebuild the spine
def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    IO.print(Nat.show(List.length(&2, String, as)))
    t : Nat <- IO.now()
    IO.print(Bool.show(Nat.is_gt(t, 1000000n)))
    n : U32 <- IO.thread_count()
    IO.print(Bool.show(U32.is_ge(n, 1)))
    IO.print(String.join(List.tail(&2, String, as), " "))
