# bench/diff/csvfuzz.bend -- W6.4 runner of the CSV fuzz harness (bench/diff/csvfuzz.py).
#
#   build/csvfuzz/runner MANIFEST [show]
#
# MANIFEST holds one case per line, nine space separated tokens (no token holds a space):
#   id path schema hdr sep inf enc cap pieces
#   schema  dtype letters U I F B S (bench/w6 convention), or `-` to infer
#   hdr     1 / 0       sep  the separator's code point       inf  infer_rows (0 = every record)
#   enc     R (EncRaw) | D (EncDict) | A (EncAuto) | T<floor>.<den> (EncAutoAt)
#   cap     the row cap   pieces  v0.2 piece sizes, comma separated
# Each case is read with the v0.1 reader (Csv.read_full, the reference) and with the v0.2 reader
# (Csv.read_v02_full) at every piece size, and the DF.dump text plus the Str storage (Raw, Dictionary
# size, hash of the codes) are compared exactly: tests/lib/v02cmp.bend's Run.file. One line per case:
#   `<id>: ok <runs> | <the v0.1 outcome>`   or   `<id>: DIFF <piece, first difference>`
# With `show` the full v0.1 text and the full v0.2 text (at the FIRST piece of the list) are printed
# instead, after `== <id> v01` / `== <id> v02 piece <p>` lines.
# Test-only code. Idioms as DESIGN 9: helpers above their callers, no mutual recursion.
import Base
import ./../../src/strs.bend as ST
import ./../../src/csv.bend as V
import ./../../tests/lib/v02cmp.bend as T
import ./../w6/hx.bend as HX

# ---- splitting a string at one code point -------------------------------------------------------------

type Sp is Data:
  Sp{cur: String, out: List<&2, String>}

def Fz.sp.step.k(hit: Bool, +c: U32, cur: String, out: List<&2, String>) -> Sp:
  match hit:
    case True{}:
      Sp{SNil{}, String.reverse(cur) <> out}
    case False{}:
      Sp{SCon{Chr{c}, cur}, out}

def Fz.sp.step(+c: U32, +sep: U32, st: Sp) -> Sp:
  match st:
    case Sp{cur, out}:
      Fz.sp.step.k(U32.is_eq(c, sep), c, cur, out)

def Fz.sp.go(s: String, +sep: U32, st: Sp) -> Sp:
  match s:
    case SNil{}:
      st
    case SCon{Chr{+c}, t}:
      Fz.sp.go(t, sep, Fz.sp.step(c, sep, st))

def Fz.rev(xs: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Fz.rev(t, h <> acc)

def Fz.sp.fin(st: Sp) -> List<&2, String>:
  match st:
    case Sp{cur, out}:
      Fz.rev(String.reverse(cur) <> out, Nil{})

# the pieces between the separators (a trailing empty piece included)
def Fz.split(s: String, +sep: U32) -> List<&2, String>:
  Fz.sp.fin(Fz.sp.go(s, sep, Sp{SNil{}, Nil{}}))

def Fz.at(+xs: List<&2, String>, f: Nat) -> String:
  match xs f:
    case Nil{} _:
      ""
    case h <> t 0n:
      h
    case h <> t 1n+p:
      Fz.at(t, p)

def Fz.num(+s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def Fz.nums(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Fz.num(h) <> Fz.nums(t)

# ---- one manifest line -> a configuration ---------------------------------------------------------------

def Fz.enc.t(+xs: List<&2, String>) -> ST.StrEnc:
  ST.EncAutoAt{Fz.num(Fz.at(xs, 0n)), Fz.num(Fz.at(xs, 1n))}

def Fz.enc.k(+c: U32, +rest: String) -> ST.StrEnc:
  Bool.pick(ST.StrEnc, U32.is_eq(c, 82), ST.EncRaw{}, Bool.pick(ST.StrEnc, U32.is_eq(c, 68), ST.EncDict{}, Bool.pick(ST.StrEnc, U32.is_eq(c, 84), Fz.enc.t(Fz.split(rest, 46)), ST.EncAuto{})))

def Fz.enc(s: String) -> ST.StrEnc:
  match s:
    case SNil{}:
      ST.EncAuto{}
    case SCon{Chr{c}, t}:
      Fz.enc.k(c, t)

def Fz.schema(+s: String) -> String:
  Bool.pick(String, String.eq(s, "-"), "", s)

def Fz.cfg(+id: String, +toks: List<&2, String>) -> T.Cf:
  T.Cf{id, Fz.schema(Fz.at(toks, 2n)), U32.is_eq(Fz.num(Fz.at(toks, 3n)), 1), Fz.num(Fz.at(toks, 4n)), Fz.num(Fz.at(toks, 5n)), Fz.enc(Fz.at(toks, 6n)), Fz.num(Fz.at(toks, 7n))}

def Fz.pieces(+toks: List<&2, String>) -> List<&2, U32>:
  Fz.nums(Fz.split(Fz.at(toks, 8n), 44))

def Fz.show(+c: T.Cf, +path: String, +piece: U32) -> IO(Unit):
  do IO<Unit>:
    +a : String <- T.Cf.ref(c, path)
    +b : String <- T.Cf.cand(c, path, piece)
    IO.print("== " ++ T.Cf.label(c) ++ " v01\n" ++ a)
    IO.print("== " ++ T.Cf.label(c) ++ " v02 piece " ++ U32.show(piece) ++ "\n" ++ b)

def Fz.run1(+id: String, +path: String, +c: T.Cf, ps: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    s : String <- T.Run.file(id, path, c, [T.CP{c, ps}])
    IO.print(s)

def Fz.case(+show: Bool, +toks: List<&2, String>) -> IO(Unit):
  Bool.pick(IO(Unit), show, Fz.show(Fz.cfg(Fz.at(toks, 0n), toks), Fz.at(toks, 1n), Fz.num(Fz.at(Fz.split(Fz.at(toks, 8n), 44), 0n))), Fz.run1(Fz.at(toks, 0n), Fz.at(toks, 1n), Fz.cfg(Fz.at(toks, 0n), toks), Fz.pieces(toks)))

def Fz.line(+show: Bool, +l: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(l), IO.pure(Unit, Unit{}), Fz.case(show, Fz.split(l, 32)))

def Fz.loop(+show: Bool, ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> t:
      do IO<Unit>:
        Fz.line(show, l)
        Fz.loop(show, t)

def Fz.arg(+xs: List<&2, String>, f: Nat) -> String:
  match xs f:
    case Nil{} _:
      ""
    case h <> t 0n:
      h
    case h <> t 1n+p:
      Fz.arg(t, p)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +a : List<&2, String> <- IO.pure(List<&2, String>, T.promote(args))
    man : String <- HX.Hx.text(Fz.arg(a, 1n))
    Fz.loop(String.eq(Fz.arg(a, 2n), "show"), Fz.split(man, 10))
