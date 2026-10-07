# p03: number <-> text round trips in Base: F32.show/read, U32.show/read,
# including negatives, exponents, junk and the empty string.
#   ~/.bend/bin/bend probes/p03_num_text.bend
import Base

def mf(m: Maybe<&2, F32>) -> String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      F32.show(x)

def mu(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      U32.show(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(mf(F32.read("-1.5")))
    IO.print(mf(F32.read("1e3")))
    IO.print(mf(F32.read("3")))
    IO.print(mf(F32.read("abc")))
    IO.print(mf(F32.read("")))
    IO.print(mf(F32.read(" 2.5")))
    IO.print(mf(F32.read("0.1")))
    IO.print(F32.show(F32.div(1.0, 0.0)))
    IO.print(F32.show(F32.div(0.0, 0.0)))
    IO.print(F32.show(F32.neg(2.0)))
    IO.print(F32.show(F32.div(1.0, 3.0)))
    IO.print(F32.show(123456789.0))
    IO.print(mu(U32.read("12")))
    IO.print(mu(U32.read("-1")))
    IO.print(mu(U32.read("")))
    IO.print(mu(U32.read("4294967295")))
    IO.print(mu(U32.read("4294967296")))
    IO.print(mu(U32.read("1 ")))
    IO.print(U32.show(F32.to_u32(2.9)))
    IO.print(U32.show(F32.to_u32(F32.neg(1.0))))

#|-1.5
#|1000
#|3
#|None
#|None
#|2.5
#|0.1
#|inf
#|nan
#|-2
#|0.33333334
#|123456790
#|12
#|None
#|None
#|4294967295
#|None
#|None
#|2
#|0
