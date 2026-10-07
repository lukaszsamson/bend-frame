# p14: building a column from a List of parsed values: pad to the next
# power of two, write with a fuel loop, keep the logical length beside the
# array. Also Array<String> set/get and the size helper.
#   ~/.bend/bin/bend probes/p14_build_from_list.bend
import Base

# the least depth d with 2^d >= n (n >= 1); fuel 32. The loop's exit test
# is a PARAMETER computed by the previous step (Base's Array.swap.go idiom):
# a user file cannot use the law-above/def-below trick for a .go/.if pair
# (WONTFIX #793: only base.bend may call a law filled below it).
def depth_for.go(f: Nat, +n: U32, +d: Nat, fits: Bool) -> Nat:
  match f fits:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+p False{}:
      depth_for.go(p, n, 1n+d, U32.is_le(n, U32.shln(1, 1n+d)))

def depth_for(+n: U32) -> Nat:
  depth_for.go(32n, n, 0n, U32.is_le(n, 1))

# write xs into a (padding slots keep the fill value); structural on xs
def fill.go(~T: Data, xs: List<&2, T>, +i: U32, a: Array<T>) -> Array<T>:
  match xs:
    case Nil{}:
      a
    case h <> t:
      fill.go(~T, t, U32.inc(i), Array.set(T, a, i, h))

# (length, array) from a list; the empty list gets one padding slot
def from_list(~T: Data, +xs: List<&2, T>, +pad: T) -> U32 & Array<T>:
  +n = U32.from_nat(List.length(&2, T, xs))
  (n, fill.go(~T, xs, 0, Array.new(T, depth_for(U32.max(n, 1)), pad)))

def show_strs(r: U32 & Array<String>) -> String:
  (n, a) = r
  U32.show(n) ++ " " ++ List.show(~&1, ~String, ~(s => s), Array.to_list(~String, a))

def show_f32s(r: U32 & Array<F32>) -> String:
  (n, a) = r
  U32.show(n) ++ " " ++ List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, a))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_strs(from_list(~String, ["ann", "bob", "cy"], "")))
    IO.print(show_f32s(from_list(~F32, [1.5, 2.5, 3.5, 4.5, 5.5], 0.0)))
    IO.print(show_f32s(from_list(~F32, [], 0.0)))
    IO.print(Nat.show(depth_for(1)) ++ " " ++ Nat.show(depth_for(2)) ++ " " ++ Nat.show(depth_for(5)) ++ " " ++ Nat.show(depth_for(1024)) ++ " " ++ Nat.show(depth_for(1025)))

#|3 [ann, bob, cy, ]
#|5 [1.5, 2.5, 3.5, 4.5, 5.5, 0, 0, 0]
#|0 [0]
#|0 1 3 10 11
