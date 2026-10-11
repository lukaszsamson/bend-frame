# W2.1 / W2.2 native differential (v0.2): Hc.code vs Sort.str_codes and Rk.words / Rk.dict vs
# Sort.str_words / Dict.ranks (v0.1, tests/lib/v01str.bend), the same comparators as tests/hcode_diff.bend and
# tests/ranks_diff.bend (imported), at sizes and on shapes the interpreter tests cannot reach: the
# WIDE shape (code points above U+10FFFF: the interpreter refuses such a Chr, the native runtime
# holds any U32) and bigger n.
#   ~/.bend/bin/bend bench/w2/w2diff.bend -o build/w2/w2diff
#   build/w2/w2diff <shape> <n>        (bench/w2/diff.sh runs the whole matrix)
# Prints "codes <shape> <n>: ok", "codes const ..." (constant template hash, n capped at 129) and
# "words ..." (Rk.words with flip 0 and 2^32 - 1, and Rk.dict); BAD lines name the failing case.
import Base
import ./../../frame.bend as DF
import ./../../src/hcode.bend as H
import ./../../tests/lib/w2gen.bend as G
import ./../../tests/hcode_diff.bend as TH
import ./../../tests/ranks_diff.bend as TR

def shape_of(+s: String) -> G.Shape:
  Bool.pick(G.Shape, String.eq(s, "prefix"), G.ShP{},
  Bool.pick(G.Shape, String.eq(s, "longprefix"), G.ShQ{},
  Bool.pick(G.Shape, String.eq(s, "skew"), G.ShS{},
  Bool.pick(G.Shape, String.eq(s, "equal"), G.ShE{},
  Bool.pick(G.Shape, String.eq(s, "low"), G.ShL{},
  Bool.pick(G.Shape, String.eq(s, "uni"), G.ShU{},
  Bool.pick(G.Shape, String.eq(s, "empty"), G.ShZ{},
  Bool.pick(G.Shape, String.eq(s, "nul"), G.ShN{},
  Bool.pick(G.Shape, String.eq(s, "aligned"), G.ShM{},
  Bool.pick(G.Shape, String.eq(s, "wide"), G.ShW{}, G.ShD{}))))))))))

def diff.sizes(+n: U32) -> List<&2, U32>:
  [n]

def diff.run(+shape: String, +n: U32, +sh: G.Shape) -> IO(Unit):
  do IO<Unit>:
    IO.print(G.Rep.line("codes " ++ shape ++ " " ++ U32.show(n), TH.Hd.sizes(~(s => H.Hc.hash(s)), diff.sizes(n), sh)))
    IO.print(G.Rep.line("codes const " ++ shape ++ " " ++ U32.show(n), TH.Hd.sizes(~(s => TH.Hd.t.const(s)), diff.sizes(U32.min(n, 129)), sh)))
    IO.print(G.Rep.line("words " ++ shape ++ " " ++ U32.show(n), TR.Rd.sizes(diff.sizes(n), sh)))


def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      1000

def go(+xs: List<&2, String>) -> IO(Unit):
  diff.run(nth(0n, xs, "distinct"), num(U32.read(nth(1n, xs, "1000"))), shape_of(nth(0n, xs, "distinct")))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
