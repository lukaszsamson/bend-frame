# B3 (plans/REVIEW_V02_FABLE.txt; documented in README "Differences from Polars" and DESIGN.md 15.5.4 / 15.6):
# the SIGN of a zero median. bend-frame sorts the valid values stably by their 15.5.2 order words, where
# -0.0 and 0.0 are the SAME word, so the median of an odd count is the cell at the middle position of the
# STABLE order. When every value is a zero all words are equal and the stable sort is the identity: the
# median is the input's cell at index (n - 1) / 2, with its own sign. Polars 2.0.0 selects the middle with
# an unstable partition: for odd n <= 15 it agreed with that rule on every case tried (1,218 exhaustive
# cases: all {-0.0, 0.0} words of length 1..7 and all {-1, -0.0, 0.0, 1} words of length 3 and 5; 174 random
# cases of length 9, 11, 15), and for n >= 21 it differs in BOTH directions (107 of 226 random odd-count
# inputs of length 21, 31, 41, 61 over -0.0, 0.0, +-1.0), all checked in bench's uv project. The cases below are two of those, one per
# direction (the Polars answer is in each comment; it is NOT asserted here). An EVEN count averages the
# two middle cells and README already lists median([-0.0, 0.0]) (bend 0.0, Polars -0.0).
# This test PINS bend-frame's answer; it is a documented difference, not a claim that it is right.
#
# Expected values, derived by hand from the rule above (words: n = -0.0 = 0x80000000, p = 0.0 = 0x00000000):
#   z21  "nnnnnpnnnnnppnnnpppnp", 21 values, index 10 is 'n' (n n n n n p n n n n [n] p p ...): 0x80000000
#        (Polars answers 0.0)
#   z31  "nppnnnpppnppnnppnnppnnpnnpnpppn", 31 values, index 15 is 'p' (n p p n n n p p p n p p n n p
#        [p] n ...): 0x00000000 (Polars answers -0.0)
#   z5   "pnnpp", 5 values, index 2 is 'n': 0x80000000 (both agree; a small control)
#   zlit a column of one -0.0 (n = 1, index 0): 0x80000000 (both agree)
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

# 'n' -> -0.0, anything else -> 0.0
def zs(s: String) -> List<&2, D.Scalar>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Bool.pick(D.Scalar, U32.is_eq(c, 110), D.SF32{F32.neg(0.0)}, D.SF32{0.0}) <> zs(t)

def sel(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.select(f, [DF.alias(DF.median(DF.col("x")), "m")])

def one(+tag: String, +s: String) -> String:
  "-- " ++ tag ++ "\n" ++ DF.dump(sel(C.Frame.from_columns([mk.k("x", C.Column.from_scalars(zs(s), D.TF32{}))])))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(one("z21", "nnnnnpnnnnnppnnnpppnp"))
    IO.print(one("z31", "nppnnnpppnppnnppnnppnnpnnpnpppn"))
    IO.print(one("z5", "pnnpp"))
    IO.print(one("zlit", "n"))
#|-- z21
#|frame
#|height	1
#|width	1
#|col	f32	"m"
#|row	0x80000000
#|
#|-- z31
#|frame
#|height	1
#|width	1
#|col	f32	"m"
#|row	0x00000000
#|
#|-- z5
#|frame
#|height	1
#|width	1
#|col	f32	"m"
#|row	0x80000000
#|
#|-- zlit
#|frame
#|height	1
#|width	1
#|col	f32	"m"
#|row	0x80000000
#|
