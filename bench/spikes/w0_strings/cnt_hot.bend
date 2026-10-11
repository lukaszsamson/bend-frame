# W0 spike T5a: cnt.bend with List hot: the program also (unreachably at run time, but reachably
# in the code) shares a List, as every bend-frame program does, so every byte cell File.read_at
# builds is rfc_sealed. Check with python3 tools/hot.py build/cnt_hot.c CON.
#   ./build/cnt_hot [x]       (run from the repo root; any argument takes the sharing branch)
import Base
import ./cnt.bend as N

def both(r: List<&2, U32> & List<&2, U32>) -> U32:
  (a, b) = r
  U32.add(N.cnt(a, 0), N.cnt(b, 0))

def share(+xs: List<&2, U32>) -> U32:
  both((xs, xs))

def pick(xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      N.Cn.run("count_hot")
    case h <> t:
      IO.print(U32.show(share(1 <> 2 <> Nil{})))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    pick(List.tail(&1, String, args))
