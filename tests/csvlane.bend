# W6.2: the CSV lane (src/csvlane.bend) behind the producer (src/csvprod.bend), against the v0.1
# reader (Csv.read_full: csvparse + the Csv conversions), at the DF.dump level: names, dtypes,
# every value, validity, F32 bit patterns, string contents (UTF-8 decoding included), dictionary
# merge results, and the first error of the v0.1 order with its physical line and text.
#
# Every adversarial file of tests/csvadv (bench/w6/gen_adv.py) is read with an explicit schema by
# bench/w6/rd.bend (header step, Pr.regions, one Ln.lane per region, malformed / ragged / bad
# cell / concatenation / Dictionary merge) in pieces of 1, 2, 3, 4, 5, 7, 8, 13, 16, 31, 64, 97,
# 256, 4096 and 1048576 bytes (Str columns as per-region Dictionaries, TyS) and at 7 and 4096
# bytes with Str columns as raw rows (TyR). The line is `<case>: <what v0.1 answers>` when every
# run gave the same dump, else the first run that differs and its first differing line.
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/csv.bend as V
import ./../bench/w6/hx.bend as X
import ./../bench/w6/cmp.bend as M
import ./../bench/w6/cases.bend as CS
import ./../bench/w6/rd.bend as R

# the v0.1 reader's dump
def Ref.dump(+path: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- V.Csv.read_full(path, V.CsvOpts{Chr{sep}, hdr, 100}, R.Hr.dts(schema), ST.EncRaw{}, 1048576, 8388608)
    return DF.dump(r)

# one candidate run: "" when its dump equals ref
def Cand.one(+path: String, +hdr: Bool, +sep: U32, +schema: String, +piece: U32, +raw: Bool, ref: String) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- R.Hr.read(path, hdr, sep, schema, piece, raw)
    return M.Cmp.diff(ref, DF.dump(r))

# the pieces still to run, the first difference
type RP is Data:
  RP{ps: List<&2, U32>, v: String, go: Bool}

def Cand.next(+ps: List<&2, U32>, +p: U32, +raw: Bool, +v: String) -> RP:
  Bool.pick(RP, String.is_empty(v), RP{ps, v, True{}}, RP{ps, Bool.pick(String, raw, "raw rows, ", "dictionary, ") ++ "piece " ++ U32.show(p) ++ ": " ++ v, False{}})

def Cand.loop(f: Nat, +path: String, +hdr: Bool, +sep: U32, +schema: String, +raw: Bool, +ref: String, st: RP) -> IO(RP):
  match f st:
    case 0n _:
      IO.pure(RP, st)
    case _ RP{ps, v, False{}}:
      IO.pure(RP, RP{ps, v, False{}})
    case _ RP{Nil{}, v, True{}}:
      IO.pure(RP, RP{Nil{}, v, False{}})
    case 1n+p RP{+q <> t, v, True{}}:
      do IO<RP>:
        v2 : String <- Cand.one(path, hdr, sep, schema, q, raw, ref)
        Cand.loop(p, path, hdr, sep, schema, raw, ref, Cand.next(t, q, raw, v2))

def Cand.fin(rp: RP) -> String:
  match rp:
    case RP{ps, v, go}:
      v

def Cand.run(+path: String, +hdr: Bool, +sep: U32, +schema: String, +raw: Bool, +ref: String, ps: List<&2, U32>) -> IO(String):
  do IO<String>:
    rp : RP <- Cand.loop(20n, path, hdr, sep, schema, raw, ref, RP{ps, "", True{}})
    return Cand.fin(rp)

def Case.join(+a: String, +b: String, +out: String) -> String:
  Bool.pick(String, String.is_empty(a), Bool.pick(String, String.is_empty(b), out, b), a)

def Case.run(+path: String, +hdr: Bool, +sep: U32, +schema: String, +ref: String) -> IO(String):
  do IO<String>:
    +a : String <- Cand.run(path, hdr, sep, schema, False{}, ref, X.Hx.pieces())
    +b : String <- Cand.run(path, hdr, sep, schema, True{}, ref, [7, 4096])
    return Case.join(a, b, M.Cmp.outcome(ref))

def Case.one.k(+name: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    +path : String = "tests/csvadv/" ++ name ++ ".csv"
    +ref : String <- Ref.dump(path, hdr, sep, schema)
    v : String <- Case.run(path, hdr, sep, schema, ref)
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
