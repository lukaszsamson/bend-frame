# The group_by / unique coder (H.Hc.code.h: ST.Str.hash only, v0.2 W2.3) and the rank stage's coder
# (H.Hc.code.fnv: FNV-1a + byte lengths) give the first-appearance codes the v0.1 Map coder gave on
# these rows (this file pinned Sort.str_codes = Sort.pcodes before W2.3 deleted both): ids from
# `first`, 0 in the slots past n, next = first + distinct strings. 13 rows in 16 slots.
import Base
import ./../src/kernels.bend as K
import ./../src/hcode.bend as H

def show.l(r: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  (a, xs) = r
  xs

def show.k(+n: U32, hc: H.HC) -> String:
  match hc:
    case H.HC{next, a, hs, rp, ids, c, fr, bl}:
      "next=" ++ U32.show(next) ++ " " ++ List.show(~&2, ~U32, ~(x => U32.show(x)), show.l(K.Kernel.to_list(~U32, 16, c)))

def show.a(r: U32 & Array<String>) -> Array<String>:
  (n, a) = r
  a

def strs(+n: U32) -> Array<String>:
  show.a(K.Kernel.from_list(~String, ["d", "b", "d", "a", "c", "b", "e", "a", "f", "d", "g", "b", "h"], ""))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show.k(13, H.Hc.code.h(13, 4n, 1, strs(13))))
    IO.print(show.k(13, H.Hc.code.fnv(13, 4n, 1, strs(13))))
    IO.print(show.k(3, H.Hc.code.h(3, 4n, 0, strs(13))))
    IO.print(show.k(0, H.Hc.code.h(0, 4n, 1, strs(13))))
#|next=9 [1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8, 0, 0, 0]
#|next=9 [1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8, 0, 0, 0]
#|next=2 [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#|next=1 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
