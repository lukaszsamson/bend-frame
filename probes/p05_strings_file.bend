# p05: text and files for CSV io: split/lines/trim, whole-file read via
# File.size + File.read, write-then-read round trip.
#   ~/.bend/bin/bend probes/p05_strings_file.bend
import Base

def show_fields(fs: List<&2, String>) -> String:
  String.join(fs, "|")

def read_all.go(r: File & Result<&1, &1, (U32 & String), String>) -> IO(String):
  (f, res) = r
  do IO<String>:
    text : String <- IO.pass(String, res)
    File.close(f)
    return text

def read_all.sized(r: File & Result<&1, &1, (U32 & String), U32>) -> IO(String):
  (f, res) = r
  do IO<String>:
    n : U32 <- IO.pass(U32, res)
    r2 : File & Result<&1, &1, (U32 & String), String> <- File.read(f, n)
    read_all.go(r2)

def read_all(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, (U32 & String), U32> <- File.size(f)
    read_all.sized(r)

def write_all.go(r: File & Result<&1, &1, (U32 & String), Unit>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    IO.pass(Unit, res)
    File.close(f)

def write_all(path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, (U32 & String), Unit> <- File.write(f, text)
    write_all.go(r)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_fields(String.split("a,b,,d", ',')))
    IO.print(show_fields(String.split("", ',')))
    IO.print(show_fields(String.lines("x\ny\n")))
    IO.print("[" ++ String.trim("  hi \t") ++ "]")
    IO.print(Nat.show(String.length("héllo")))
    write_all("/tmp/bend_frame_p05.csv", "name,age\nann,31\nbob,42\n")
    +text : String <- read_all("/tmp/bend_frame_p05.csv")
    IO.print(Nat.show(List.length(&2, String, String.lines(text))))
    IO.print(show_fields(String.lines(text)))

#|a|b||d
#|
#|x|y|
#|[hi]
#|5
#|4
#|name,age|ann,31|bob,42|
