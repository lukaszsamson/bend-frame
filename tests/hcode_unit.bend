# W2.1: Hc.code pinned values (worked out by hand, not taken from a run):
#  - first-appearance codes from `first`, the next free id, the entries' first rows, their UTF-8
#    byte lengths;
#  - n = 0 and n = 1, "" keys (a key like any other), strings of every UTF-8 length class;
#  - REAL FNV-1a 32-bit collisions (found by search; ST.Str.hash is equal on each pair): the stored
#    hash matches, the strings differ, the probe goes on;
#  - the same rows under a constant template hash (every probe collides).
# The collision pairs: k32004 / k261338, k32005 / k261339, k32008 / k261334, k32009 / k261335 and
# "é日525970" / "é日1364293" (hash over code points, not bytes).
import Base
import ./../src/kernels.bend as K
import ./../src/strs.bend as ST
import ./../src/hcode.bend as H

def lst.k(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

# the first n slots of an array as a list text
def lst(+n: U32, a: Array<U32>) -> String:
  lst.k(K.Kernel.to_list(~U32, n, a))

def rows.k(r: U32 & Array<String>) -> Array<String>:
  (n, a) = r
  a

def rows(xs: List<&2, String>) -> Array<String>:
  rows.k(K.Kernel.from_list(~String, xs, ""))

# "next=.. codes=[..] fr=[..] bl=[..]" for the first n rows (every array printed to its extent)
def show.l(+n: U32, +d: Nat, +first: U32, hc: H.HC) -> String:
  match hc:
    case H.HC{+next, a, hs, rp, ids, codes, fr, bl}:
      "next=" ++ U32.show(next) ++ " codes=" ++ lst(n, codes) ++ " fr=" ++ lst(U32.sub(next, first), fr) ++ " bl=" ++ lst(U32.sub(next, first), bl)

def run(+n: U32, +first: U32, a: Array<String>) -> String:
  show.l(n, 4n, first, H.Hc.code(~(s => H.Hc.hash(s)), n, 4n, first, a))

def run.c(+n: U32, +first: U32, a: Array<String>) -> String:
  show.l(n, 4n, first, H.Hc.code(~(s => H.Hc.hash.const(7, s)), n, 4n, first, a))

def run.h(+n: U32, +first: U32, a: Array<String>) -> String:
  show.l(n, 4n, first, H.Hc.code.h(n, 4n, first, a))

def sort13() -> Array<String>:
  rows(["d", "b", "d", "a", "c", "b", "e", "a", "f", "d", "g", "b", "h"])

def collide() -> Array<String>:
  rows(["k32004", "k261338", "k32005", "k32004", "k261339", "k261338", "k32005", "k32008", "k261334", "k32009", "k261335", "k32008", "\u{e9}\u{65e5}525970", "\u{e9}\u{65e5}1364293", "\u{e9}\u{65e5}525970"])

# the hashes of a colliding pair are equal, the strings are not
def pair(+a: String, +b: String) -> String:
  Bool.show(U32.is_eq(ST.Str.hash(a), ST.Str.hash(b))) ++ " " ++ Bool.show(String.eq(a, b))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(run(13, 1, sort13()))
    IO.print(run(13, 0, sort13()))
    IO.print(run.c(13, 1, sort13()))
    IO.print(run.h(13, 1, sort13()))
    IO.print(run(0, 5, sort13()))
    IO.print(run(1, 5, rows(["x"])))
    IO.print(run(6, 0, rows(["", "", "a", "", "\u{e9}", ""])))
    IO.print(run(6, 3, rows(["", "", "", "", "", ""])))
    IO.print(run(13, 0, rows(["", "a", "\u{7f}", "\u{80}", "\u{7ff}", "\u{800}", "\u{ffff}", "\u{10000}", "\u{10ffff}", "\u{20ac}", "\u{1d11e}", "ab", "a\u{0}"])))
    IO.print(pair("k32004", "k261338"))
    IO.print(pair("k32005", "k261339"))
    IO.print(pair("k32008", "k261334"))
    IO.print(pair("k32009", "k261335"))
    IO.print(pair("\u{e9}\u{65e5}525970", "\u{e9}\u{65e5}1364293"))
    IO.print(run(15, 0, collide()))
    IO.print(run.c(15, 0, collide()))
#|next=9 codes=[1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8] fr=[0, 1, 3, 4, 6, 8, 10, 12] bl=[1, 1, 1, 1, 1, 1, 1, 1]
#|next=8 codes=[0, 1, 0, 2, 3, 1, 4, 2, 5, 0, 6, 1, 7] fr=[0, 1, 3, 4, 6, 8, 10, 12] bl=[1, 1, 1, 1, 1, 1, 1, 1]
#|next=9 codes=[1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8] fr=[0, 1, 3, 4, 6, 8, 10, 12] bl=[1, 1, 1, 1, 1, 1, 1, 1]
#|next=9 codes=[1, 2, 1, 3, 4, 2, 5, 3, 6, 1, 7, 2, 8] fr=[0, 1, 3, 4, 6, 8, 10, 12] bl=[0, 0, 0, 0, 0, 0, 0, 0]
#|next=5 codes=[] fr=[] bl=[]
#|next=6 codes=[5] fr=[0] bl=[1]
#|next=3 codes=[0, 0, 1, 0, 2, 0] fr=[0, 2, 4] bl=[0, 1, 2]
#|next=4 codes=[3, 3, 3, 3, 3, 3] fr=[0] bl=[0]
#|next=13 codes=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] fr=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] bl=[0, 1, 1, 2, 2, 3, 3, 4, 4, 3, 4, 2, 2]
#|True False
#|True False
#|True False
#|True False
#|True False
#|next=10 codes=[0, 1, 2, 0, 3, 1, 2, 4, 5, 6, 7, 4, 8, 9, 8] fr=[0, 1, 2, 4, 7, 8, 9, 10, 12, 13] bl=[6, 7, 6, 7, 6, 7, 6, 7, 11, 12]
#|next=10 codes=[0, 1, 2, 0, 3, 1, 2, 4, 5, 6, 7, 4, 8, 9, 8] fr=[0, 1, 2, 4, 7, 8, 9, 10, 12, 13] bl=[6, 7, 6, 7, 6, 7, 6, 7, 11, 12]
