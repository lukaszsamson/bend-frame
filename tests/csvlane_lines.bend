# W6.2: the `lines` array of a lane (the physical line of every kept row, DESIGN 15.6.2: "1-based
# physical line of the record's first line", every LF counting, also inside quotes and blank lines)
# against the reference parser's record lines (csvparse `CsvRec.line` of the records after the header,
# blank records dropped when the width is above 1): the same row count and the same line of every
# row, for every adversarial file of tests/csvadv read in pieces of 1, 3, 7, 64, 4096 and 1048576
# bytes. A file the reference parser rejects, with a ragged record or no data (the lane's rows are
# not meaningful there) prints `n/a`.
import Base
import ./../src/err.bend as E
import ./../bench/w6/cases.bend as CS
import ./../bench/w6/rd.bend as R

# the pieces still to run, the first difference from the answer at 1 MiB
type RP is Data:
  RP{ps: List<&2, U32>, v: String, go: Bool}

def Ln.next(+ps: List<&2, U32>, +p: U32, +base: String, +v: String) -> RP:
  Bool.pick(RP, String.eq(v, base), RP{ps, "", True{}}, RP{ps, "piece " ++ U32.show(p) ++ ": " ++ v ++ " (at 1 MiB: " ++ base ++ ")", False{}})

def Ln.loop(f: Nat, +path: String, +hdr: Bool, +sep: U32, +schema: String, +base: String, st: RP) -> IO(RP):
  match f st:
    case 0n _:
      IO.pure(RP, st)
    case _ RP{ps, v, False{}}:
      IO.pure(RP, RP{ps, v, False{}})
    case _ RP{Nil{}, v, True{}}:
      IO.pure(RP, RP{Nil{}, v, False{}})
    case 1n+p RP{+q <> t, v, True{}}:
      do IO<RP>:
        v2 : String <- R.Hr.linesig(path, hdr, sep, schema, q)
        Ln.loop(p, path, hdr, sep, schema, base, Ln.next(t, q, base, v2))

def Ln.fin(+base: String, rp: RP) -> String:
  match rp:
    case RP{ps, +v, go}:
      Bool.pick(String, String.is_empty(v), base, v)

def Case.run(+path: String, +hdr: Bool, +sep: U32, +schema: String, +base: String) -> IO(String):
  do IO<String>:
    rp : RP <- Ln.loop(10n, path, hdr, sep, schema, base, RP{[1, 3, 7, 64, 4096], "", True{}})
    return Ln.fin(base, rp)

def Case.one.k(+name: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    +path : String = "tests/csvadv/" ++ name ++ ".csv"
    +base : String <- R.Hr.linesig(path, hdr, sep, schema, 1048576)
    v : String <- Case.run(path, hdr, sep, schema, base)
    return name ++ ": " ++ v

# `only` (the first program argument, "" for every case) selects a case
def Case.one(+only: String, c: CS.Mf) -> IO(String):
  match c:
    case CS.Mf{+name, schema, +hdr, +sep}:
      Bool.pick(IO(String), Bool.or(String.is_empty(only), String.eq(only, name)), Case.one.k(name, hdr, sep, schema), IO.pure(String, ""))

def Case.print(+s: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(s), IO.pure(Unit, Unit{}), IO.print(s))

def Case.loop(+only: String, cs: List<&2, CS.Mf>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> t:
      do IO<Unit>:
        s : String <- Case.one(only, c)
        Case.print(s)
        Case.loop(only, t)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    Case.loop(Maybe.default(&2, String, List.get(&2, String, as, 1n), ""), CS.Cases.all())
