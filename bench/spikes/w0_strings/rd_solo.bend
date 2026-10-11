# W0 spike T4/T5: the piece reader in a program that does not import frame.bend (String and List
# are still hot here: the schema list is shared by every lane; pk_cold.bend is the cold producer).
#   ~/.bend/bin/bend bench/spikes/w0_strings/rd_solo.bend -o bench/spikes/w0_strings/build/rd_solo
#   ./build/rd_solo [--threads N] <file.csv> [piece bytes, default 1048576] [spike|pack] [column types, default USSUFFB]
import Base
import ./rd_drv.bend as V

def go(+xs: List<&2, String>) -> IO(Unit):
  V.Drv.run(V.Drv.nth(0n, xs, "bench/data/sales_1000.csv"), V.Drv.num(U32.read(V.Drv.nth(1n, xs, "1048576")), 1048576), V.Drv.nth(2n, xs, "spike"), V.Drv.nth(3n, xs, "USSUFFB"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, V.Drv.promote(args)))
