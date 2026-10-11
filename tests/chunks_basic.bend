# T5.1 (DESIGN.md 16.1 D1): the chunk trees of src/chunks.bend at a tiny grain (2^2 = 4-row leaves) so
# every shape is small enough to work out by hand: the builder's binary counter (leaf i merges
# tz(i + 1) times, the last leaf partial, the final collapse), flatten, head / drop / slice, rechunk,
# concat (and its row cap), the lockstep fits walk. Skeletons print as nested pairs of leaf counts;
# `ok` checks every node's counts (lrows = rows(l), rows = lrows + rows(r)).
#
# Expected values (worked out from the builder's code, see IMPLEMENTING.md T5.1):
#   of(n, g=2): n <= 4 one leaf (the buffer moved); 5 -> (4 1); 8 -> (4 4); 12 -> ((4 4) 4);
#   13 -> ((4 4) (4 1)); 17 -> (((4 4) (4 4)) 1)
#   t13 = of(13) of 0..12: head 6 -> (4 2) [0..5]; drop 6 -> (2 (4 1)) [6..12]; slice 6 3 -> (2 1)
#   [6, 7, 8]; rechunk(2) of that -> 3 [6, 7, 8]; head 0 -> 0 []; drop 13 -> 0 []
#   concat(of(5), of(3)) -> ((4 1) 3); rechunk(2) keeps it; rechunk(3) -> 8 (5 + 3 <= 8)
import Base
import ./../src/kernels.bend as K
import ./../src/chunks.bend as CH
import ./../src/err.bend as E

def shu.k(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

def shu(+n: U32, a: Array<U32>) -> String:
  shu.k(K.Kernel.to_list(~U32, n, a))

def skel_show(s: CH.Skel) -> String:
  match s:
    case CH.KLeaf{n}:
      U32.show(n)
    case CH.KNode{rows, lrows, l, r}:
      "(" ++ skel_show(l) ++ " " ++ skel_show(r) ++ ")"

def skel_ok(s: CH.Skel) -> Bool:
  match s:
    case CH.KLeaf{n}:
      True{}
    case CH.KNode{+rows, +lrows, +l, +r}:
      Bool.and(Bool.and(U32.is_eq(lrows, CH.Skel.rows(l)), U32.is_eq(rows, U32.add(lrows, CH.Skel.rows(r)))), Bool.and(skel_ok(l), skel_ok(r)))

def ok_show(b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "BAD"

def cw.show.b(+s: CH.Skel, r: CH.CW & U32) -> String:
  (t, +rows) = r
  skel_show(s) ++ " " ++ ok_show(skel_ok(s)) ++ " " ++ shu(rows, CH.CW.flatten(K.Kernel.depth_for(U32.max(rows, 1)), t))

def cw.show.a(r: CH.CW & CH.Skel) -> String:
  (t, +s) = r
  cw.show.b(s, CH.CW.rows(t))

# skeleton, counts check, the rows in order
def cw.show(t: CH.CW) -> String:
  cw.show.a(CH.CW.skel(t))

# 0 .. n - 1 chunked at grain 2^2
def t(+n: U32) -> CH.CW:
  CH.CW.of(n, K.Kernel.depth_for(U32.max(n, 1)), 2n, K.Kernel.iota(n, K.Kernel.depth_for(U32.max(n, 1))))

# 100 + i
def t100(+n: U32) -> CH.CW:
  CH.CW.of(n, K.Kernel.depth_for(U32.max(n, 1)), 2n, K.Kernel.iota_from(n, K.Kernel.depth_for(U32.max(n, 1)), 100))

def res_show(r: E.ResT(CH.CW)) -> String:
  match r:
    case Fail{e}:
      E.Err.show(e)
    case Done{x}:
      cw.show(x)

def res_cw(r: E.ResT(CH.CW)) -> CH.CW:
  match r:
    case Fail{e}:
      CH.CW.empty()
    case Done{x}:
      x

def leaves.k(r: CH.CW & U32) -> String:
  (x, +k) = r
  U32.show(k)

def fits.k(r: CH.CW & Bool) -> String:
  (x, ok) = r
  Bool.show(ok)

def fits2.k(s: CH.Skel, r: CH.CW & CH.Skel) -> String:
  (x, sx) = r
  fits.k(CH.CW.fits(x, s))

def fits2.a(r: CH.CW & CH.Skel, y: CH.CW) -> String:
  (x, s) = r
  fits2.k(s, CH.CW.skel(y))

# does y have x's skeleton?
def same(x: CH.CW, y: CH.CW) -> String:
  fits2.a(CH.CW.skel(x), y)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("of 0  " ++ cw.show(t(0)))
    IO.print("of 1  " ++ cw.show(t(1)))
    IO.print("of 3  " ++ cw.show(t(3)))
    IO.print("of 4  " ++ cw.show(t(4)))
    IO.print("of 5  " ++ cw.show(t(5)))
    IO.print("of 8  " ++ cw.show(t(8)))
    IO.print("of 12 " ++ cw.show(t(12)))
    IO.print("of 13 " ++ cw.show(t(13)))
    IO.print("of 17 " ++ cw.show(t(17)))
    IO.print("leaves 17 " ++ leaves.k(CH.CW.leaves(t(17))))
    IO.print("head 6 " ++ cw.show(CH.CW.head(t(13), 6)))
    IO.print("head 0 " ++ cw.show(CH.CW.head(t(13), 0)))
    IO.print("head 99 " ++ cw.show(CH.CW.head(t(13), 99)))
    IO.print("drop 6 " ++ cw.show(CH.CW.drop(t(13), 6)))
    IO.print("drop 0 " ++ cw.show(CH.CW.drop(t(13), 0)))
    IO.print("drop 13 " ++ cw.show(CH.CW.drop(t(13), 13)))
    IO.print("slice 6 3 " ++ cw.show(CH.CW.slice(t(13), 6, 3)))
    IO.print("slice 3 9 " ++ cw.show(CH.CW.slice(t(13), 3, 9)))
    IO.print("rechunk slice " ++ cw.show(CH.CW.rechunk(2n, CH.CW.slice(t(13), 6, 3))))
    IO.print("rechunk 13 " ++ cw.show(CH.CW.rechunk(2n, t(13))))
    IO.print("rechunk3 13 " ++ cw.show(CH.CW.rechunk(3n, t(13))))
    IO.print("concat " ++ res_show(CH.CW.concat(t(5), t100(3))))
    IO.print("concat empty " ++ res_show(CH.CW.concat(t(0), t100(3))))
    IO.print("concat cap 8 " ++ res_show(CH.CW.concat.cap(8, t(5), t100(3))))
    IO.print("concat cap 7 " ++ res_show(CH.CW.concat.cap(7, t(5), t100(3))))
    IO.print("concat wrap " ++ res_show(CH.CW.concat(CH.WL{4294967295, 0n, Array.new(U32, 0n, 0)}, t100(3))))
    IO.print("rechunk2 concat " ++ cw.show(CH.CW.rechunk(2n, res_cw(CH.CW.concat(t(5), t100(3))))))
    IO.print("rechunk3 concat " ++ cw.show(CH.CW.rechunk(3n, res_cw(CH.CW.concat(t(5), t100(3))))))
    IO.print("fits same " ++ same(t(13), t100(13)))
    IO.print("fits other " ++ same(t(13), t100(12)))
    IO.print("fits head " ++ same(CH.CW.head(t(13), 6), CH.CW.head(t100(13), 6)))
#|of 0  0 ok []
#|of 1  1 ok [0]
#|of 3  3 ok [0, 1, 2]
#|of 4  4 ok [0, 1, 2, 3]
#|of 5  (4 1) ok [0, 1, 2, 3, 4]
#|of 8  (4 4) ok [0, 1, 2, 3, 4, 5, 6, 7]
#|of 12 ((4 4) 4) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
#|of 13 ((4 4) (4 1)) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
#|of 17 (((4 4) (4 4)) 1) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
#|leaves 17 5
#|head 6 (4 2) ok [0, 1, 2, 3, 4, 5]
#|head 0 0 ok []
#|head 99 ((4 4) (4 1)) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
#|drop 6 (2 (4 1)) ok [6, 7, 8, 9, 10, 11, 12]
#|drop 0 ((4 4) (4 1)) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
#|drop 13 0 ok []
#|slice 6 3 (2 1) ok [6, 7, 8]
#|slice 3 9 ((1 4) 4) ok [3, 4, 5, 6, 7, 8, 9, 10, 11]
#|rechunk slice 3 ok [6, 7, 8]
#|rechunk 13 ((4 4) (4 1)) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
#|rechunk3 13 (8 5) ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
#|concat ((4 1) 3) ok [0, 1, 2, 3, 4, 100, 101, 102]
#|concat empty (0 3) ok [100, 101, 102]
#|concat cap 8 ((4 1) 3) ok [0, 1, 2, 3, 4, 100, 101, 102]
#|concat cap 7 InvalidOperation: too many rows: 8 exceeds 7
#|concat wrap InvalidOperation: too many rows: 4294967295 exceeds 8388608
#|rechunk2 concat ((4 1) 3) ok [0, 1, 2, 3, 4, 100, 101, 102]
#|rechunk3 concat 8 ok [0, 1, 2, 3, 4, 100, 101, 102]
#|fits same True
#|fits other False
#|fits head True
