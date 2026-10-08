# M3: Fmt.fixed -- exact decimal expansion of the f32 value, round half to even
# (what Python's f"{x:.4f}" / Polars float_precision=4 print).
import Base
import ./../src/fmt.bend as F

def line.k(m: Maybe<&2, F32>, p: U32) -> String:
  match m:
    case None{}:
      "bad read"
    case Some{x}:
      F.Fmt.fixed(x, p)

def line(+s: String, +p: U32) -> IO(Unit):
  IO.print(s ++ " -> " ++ line.k(F32.read(s), p))

def main() -> IO(Unit):
  do IO<Unit>:
    line("146.07", 4)
    line("26002.8594", 4)
    line("0.1", 4)
    line("0.1", 9)
    line("0.00005", 4)
    line("0.99996", 4)
    line("9.99996", 4)
    line("0.5", 0)
    line("1.5", 0)
    line("2.5", 0)
    line("0.125", 2)
    line("0.375", 2)
    line("-0.00001", 4)
    line("-2.5", 1)
    line("0", 4)
    line("1e-30", 4)
    line("123456.789", 4)
    line("16777216", 4)
    line("4294967296", 2)
    line("3.4e38", 1)
    line("100", 0)
#|146.07 -> 146.0700
#|26002.8594 -> 26002.8594
#|0.1 -> 0.1000
#|0.1 -> 0.100000001
#|0.00005 -> 0.0000
#|0.99996 -> 1.0000
#|9.99996 -> 10.0000
#|0.5 -> 0
#|1.5 -> 2
#|2.5 -> 2
#|0.125 -> 0.12
#|0.375 -> 0.38
#|-0.00001 -> -0.0000
#|-2.5 -> -2.5
#|0 -> 0.0000
#|1e-30 -> 0.0000
#|123456.789 -> 123456.7891
#|16777216 -> 16777216.0000
#|4294967296 -> 4294967296.00
#|3.4e38 -> 339999995214436424907732413799364296704.0
#|100 -> 100
