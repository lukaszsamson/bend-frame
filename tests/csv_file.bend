# M3: Csv.write / Csv.read through a real file (p05 pattern), IO errors as values.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/fmt.bend as F
import ./../src/csv.bend as V

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def show(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def sample() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("id", [D.SU32{1}, D.SU32{2}, D.SU32{3}], D.TU32{}), mk("name", [D.SStr{"ann"}, D.SStr{"b,\"ob\""}, D.SNull{}], D.TStr{}), mk("score", [D.SF32{1.5}, D.SNull{}, D.SF32{0.25}], D.TF32{}), mk("ok", [D.SBool{True{}}, D.SBool{False{}}, D.SNull{}], D.TBool{}), mk("n", [D.SI32{D.I32.neg(D.I32{4})}, D.SI32{D.I32{0}}, D.SNull{}], D.TI32{})])

def wres(r: Result<&1, &1, U32 & String, Unit>) -> String:
  match r:
    case Done{u}:
      "write ok"
    case Fail{(code, msg)}:
      "write failed " ++ U32.show(code) ++ ": " ++ msg

def wrote(r: C.Frame & Result<&1, &1, U32 & String, Unit>) -> String:
  (f, res) = r
  wres(res)

def write(r: E.ResT(C.Frame), path: String) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ E.Err.show(e))
    case Done{f}:
      do IO<String>:
        w : C.Frame & Result<&1, &1, U32 & String, Unit> <- V.Csv.write(f, path)
        return wrote(w)

def main() -> IO(Unit):
  do IO<Unit>:
    +a : String <- write(sample(), "/tmp/bend_frame_test.csv")
    IO.print(a)
    r : E.ResT(C.Frame) <- V.Csv.read("/tmp/bend_frame_test.csv", V.Csv.default())
    IO.print(show(r))
    m : E.ResT(C.Frame) <- V.Csv.read("/tmp/bend_frame_no_such_file.csv", V.Csv.default())
    IO.print(show(m))
    s : E.ResT(C.Frame) <- V.Csv.read_with("/tmp/bend_frame_test.csv", V.Csv.default(), [D.TU32{}, D.TStr{}, D.TF32{}, D.TBool{}, D.TI32{}])
    IO.print(show(s))
    t : E.ResT(C.Frame) <- V.Csv.read_with("/tmp/bend_frame_test.csv", V.Csv.default(), [D.TU32{}, D.TU32{}, D.TF32{}, D.TBool{}, D.TI32{}])
    IO.print(show(t))
    +b : String <- write(sample(), "/tmp/bend_frame_no_such_dir/x.csv")
    IO.print(b)
#|write ok
#|shape: (3, 5)
#|+-----+--------+-------+-------+-----+
#|| id  | name   | score | ok    | n   |
#|| --- | ---    | ---   | ---   | --- |
#|| u32 | str    | f32   | bool  | i32 |
#|+=====+========+=======+=======+=====+
#|| 1   | ann    | 1.5   | true  | -4  |
#|| 2   | b,"ob" |       | false | 0   |
#|| 3   |        | 0.25  |       |     |
#|+-----+--------+-------+-------+-----+
#|error: IoError 2: No such file or directory
#|shape: (3, 5)
#|+-----+--------+-------+-------+-----+
#|| id  | name   | score | ok    | n   |
#|| --- | ---    | ---   | ---   | --- |
#|| u32 | str    | f32   | bool  | i32 |
#|+=====+========+=======+=======+=====+
#|| 1   | ann    | 1.5   | true  | -4  |
#|| 2   | b,"ob" |       | false | 0   |
#|| 3   |        | 0.25  |       |     |
#|+-----+--------+-------+-------+-----+
#|error: ParseError at line 2: column name: cannot parse "ann" as u32
#|write failed 2: No such file or directory
