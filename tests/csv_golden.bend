# M3: the bench goldens (Polars write_csv, float_precision=4) survive parse -> render(Some{4})
# byte for byte: checks Csv.read inference, nulls, bools and Fmt.fixed against Python/Polars.
# Run from the repo root (make test does): the paths are relative.
import Base
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csv.bend as V

def read_all.go(r: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, res) = r
  do IO<String>:
    text : String <- IO.pass(String, res)
    File.close(f)
    return text

def read_all.sized(r: File & Result<&1, &1, U32 & String, U32>) -> IO(String):
  (f, res) = r
  do IO<String>:
    n : U32 <- IO.pass(U32, res)
    r2 : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
    read_all.go(r2)

def read_all(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read_all.sized(r)

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def rend(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(V.Csv.render(f, Some{4}))

# read the golden file, render it back with 4 decimals, report whether it is identical to the file's text
def check(name: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    +text : String <- read_all(path)
    r : E.ResT(C.Frame) <- V.Csv.read(path, V.Csv.default())
    IO.print(name ++ " " ++ Bool.show(String.eq(text, rend(r))))

def main() -> IO(Unit):
  do IO<Unit>:
    check("q1", "bench/golden/q1.csv")
    check("q2", "bench/golden/q2.csv")
    check("q3", "bench/golden/q3.csv")
    check("q4", "bench/golden/q4.csv")
    check("q5", "bench/golden/q5.csv")
    check("q6", "bench/golden/q6.csv")
#|q1 True
#|q2 True
#|q3 True
#|q4 True
#|q5 True
#|q6 True
