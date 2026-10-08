# Sort.str_codes (one Map, sequential) and Sort.pcodes (blocks coded in a
# parallel let, then merged) give the same first-appearance codes; the
# blocks split unevenly (13 rows in 16 slots: blocks of 4,4,4,1 and 0 rows).
import Base
import ./../src/kernels.bend as K
import ./../src/sort.bend as SO

def show.l(r: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  (a, xs) = r
  xs

def show.k(+n: U32, r: Array<String> & Array<U32> & SO.CS) -> String:
  (a, c, cs) = r
  match cs:
    case SO.CS{m, next}:
      "next=" ++ U32.show(next) ++ " " ++ List.show(~&2, ~U32, ~(x => U32.show(x)), show.l(K.Kernel.to_list(~U32, n, c)))

def show.a(r: U32 & Array<String>) -> Array<String>:
  (n, a) = r
  a

def strs(+n: U32) -> Array<String>:
  show.a(K.Kernel.from_list(~String, ["d", "b", "d", "a", "c", "b", "e", "a", "f", "d", "g", "b", "h"], ""))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show.k(13, SO.Sort.str_codes(13, 4n, 1, strs(13))))
    IO.print(show.k(13, SO.Sort.pcodes(1n, 13, 4n, 1, strs(13))))
    IO.print(show.k(13, SO.Sort.pcodes(2n, 13, 4n, 1, strs(13))))
    IO.print(show.k(13, SO.Sort.pcodes(4n, 13, 4n, 1, strs(13))))
    IO.print(show.k(3, SO.Sort.pcodes(3n, 3, 4n, 0, strs(13))))
#|next=9 [1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8]
#|next=9 [1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8]
#|next=9 [1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8]
#|next=9 [1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8]
#|next=2 [0, 1, 0]
