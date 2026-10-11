# W2.2: pinned ranks (worked out by hand from code-point order, a prefix first):
#   "" < "B" (66) < "a" (97) < "a\0" < "ab" < "b" (98) < "é" (233) < "日" (26085) < U+10FFFF
# and the 8-byte round boundaries: "abcdefg" < "abcdefgh" < "abcdefgh\0" < "abcdefgh\0\0" <
# "abcdefghi" < "abcdefghijklmno" < "abcdefghijklmnop". Rk.words answers (rows, words);
# Rk.dict answers (dict, rank by code).
import Base
import ./../src/kernels.bend as K
import ./../src/strs.bend as ST
import ./../src/ranks.bend as R

def lst.k(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

def lst(+n: U32, a: Array<U32>) -> String:
  lst.k(K.Kernel.to_list(~U32, n, a))

def rows.k(r: U32 & Array<String>) -> Array<String>:
  (n, a) = r
  a

def rows(xs: List<&2, String>) -> Array<String>:
  rows.k(K.Kernel.from_list(~String, xs, ""))

def words.k(+n: U32, r: Array<String> & Array<U32>) -> String:
  (a, w) = r
  lst(n, w)

def words(+n: U32, +flip: U32, a: Array<String>) -> String:
  words.k(n, R.Rk.words(n, 4n, flip, a))

def mix() -> Array<String>:
  rows(["b", "a", "ab", "", "a\u{0}", "\u{e9}", "\u{65e5}", "\u{10ffff}", "B", "a", ""])

def bound() -> Array<String>:
  rows(["abcdefghijklmnop", "abcdefgh\u{0}", "abcdefg", "abcdefghi", "abcdefgh\u{0}\u{0}", "abcdefgh", "abcdefghijklmno"])

# the dictionary of the rows of mix(): "" is code 0, then first appearance
def dmix.go(n: Nat, +i: U32, d: ST.Dict, r: Array<String> & String) -> ST.Dict:
  match n:
    case 0n:
      (a, s) = r
      d
    case 1n+p:
      (a, s) = r
      +j = U32.inc(i)
      dmix.go(p, j, ST.Dict.fst(ST.Dict.code(d, s)), Array.get(String, a, j))

def dmix() -> ST.Dict:
  dmix.go(11n, 0, ST.Dict.empty(), Array.get(String, mix(), 0))

def dr.k(+k: U32, r: ST.Dict & Array<U32>) -> String:
  (d, rk) = r
  lst(k, rk)

def dr(d: ST.Dict) -> String:
  match d:
    case ST.Dict{+k, dd, strs, b, slots, tag}:
      dr.k(k, R.Rk.dict(ST.Dict{k, dd, strs, b, slots, tag}))

# the dictionary of "b", "a" only: three entries ("", "b", "a")
def dsmall() -> ST.Dict:
  ST.Dict.fst(ST.Dict.code(ST.Dict.fst(ST.Dict.code(ST.Dict.empty(), "b")), "a"))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(words(11, 0, mix()))
    IO.print(words(11, 4294967295, mix()))
    IO.print(words(7, 0, bound()))
    IO.print(words(0, 0, mix()))
    IO.print(words(1, 0, rows(["zz"])))
    IO.print(words(1, 4294967295, rows(["zz"])))
    IO.print(words(3, 0, rows(["x", "x", "x"])))
    IO.print(dr(dmix()))
    IO.print(dr(dsmall()))
    IO.print(dr(ST.Dict.empty()))
#|[5, 2, 4, 0, 3, 6, 7, 8, 1, 2, 0]
#|[4294967290, 4294967293, 4294967291, 4294967295, 4294967292, 4294967289, 4294967288, 4294967287, 4294967294, 4294967293, 4294967295]
#|[6, 2, 0, 4, 3, 1, 5]
#|[]
#|[0]
#|[4294967295]
#|[0, 0, 0]
#|[0, 5, 2, 4, 3, 6, 7, 8, 1]
#|[0, 2, 1]
#|[0]
