# p06: a hub import by name@version, fetched at check time, and its I32.
#   ~/.bend/bin/bend probes/p06_hub_import.bend
import Base
import bend-kit-int@0.2.0.0/int.bend as Int

def mi(m: Maybe<&2, Int.I32>) -> String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      Int.I32.show(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(mi(Int.I32.read("-42")))
    IO.print(Int.I32.show(Int.I32.add(Int.I32{4294967295}, Int.I32{4294967295})))
    IO.print(Bool.show(Int.I32.is_lt(Int.I32{4294967295}, Int.I32{1})))
    IO.print(mi(Int.I32.read("abc")))

#|-42
#|-2
#|True
#|None
