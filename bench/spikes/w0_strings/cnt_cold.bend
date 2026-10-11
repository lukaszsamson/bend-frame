# W0 spike T5a: cnt.bend with List cold (nothing in the program shares a List).
#   ./build/cnt_cold          (run from the repo root)
import Base
import ./cnt.bend as N

def main() -> IO(Unit):
  N.Cn.run("count_cold")
