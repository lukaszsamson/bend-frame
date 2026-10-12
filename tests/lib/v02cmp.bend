# tests/lib/v02cmp.bend -- W6.3 test helpers: read one file with the v0.1 reader (Csv.read_full) and
# with the v0.2 reader (Csv.read_v02_full) at several piece sizes, and compare DF.dump AND the string
# storage of every Str column (Raw, or Dictionary with its size and a hash of its codes: DF.dump does
# not show storage, the contract keeps v0.1's codes, 17.4.7). Test-only.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/csv.bend as V
import ./../../bench/w6/cmp.bend as M
import ./../../src/p0.bend as Z

# ---- schema letters (bench/w6 cases): U u32, I i32, F f32, B bool, anything else str -------------------

def Sch.dt(+c: U32) -> D.DType:
  Bool.pick(D.DType, U32.is_eq(c, 85), D.TU32{}, Bool.pick(D.DType, U32.is_eq(c, 73), D.TI32{}, Bool.pick(D.DType, U32.is_eq(c, 70), D.TF32{}, Bool.pick(D.DType, U32.is_eq(c, 66), D.TBool{}, D.TStr{}))))

def Sch.dts(s: String) -> List<&2, D.DType>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Sch.dt(c) <> Sch.dts(t)

# ---- the storage signature of a frame's Str columns ---------------------------------------------------

def Sg.mix(+h: U32, +x: U32) -> U32:
  U32.mul(U32.xor(h, x), 16777619)

def Sg.go(f: Nat, +i: U32, +h: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match f:
    case 0n:
      (a, x) = r
      (a, h)
    case 1n+p:
      (a, +x) = r
      Sg.go(p, U32.inc(i), Sg.mix(h, x), Array.get(U32, a, U32.inc(i)))

def Sg.d3(+n: U32, d: Nat, v: C.Valid, codes: Array<U32>, +h: U32, r: ST.Dict & U32) -> C.Column & String:
  (dict, +k) = r
  (C.CStr{n, d, v, ST.SDict{codes, dict}}, "d" ++ U32.show(k) ++ ":" ++ U32.show(h))

def Sg.d2(+n: U32, d: Nat, v: C.Valid, dict: ST.Dict, r: Array<U32> & U32) -> C.Column & String:
  (codes, +h) = r
  Sg.d3(n, d, v, codes, h, ST.Dict.size(dict))

def Sg.col(c: C.Column) -> C.Column & String:
  match c:
    case C.CStr{+n, d, v, ST.SDict{codes, dict}}:
      Sg.d2(n, d, v, dict, Sg.go(U32.to_nat(n), 0, 2166136261, Array.get(U32, codes, 0)))
    case C.CStr{n, d, v, ST.SRaw{a}}:
      (C.CStr{n, d, v, ST.SRaw{a}}, "r")
    case other:
      (other, "-")

def Sg.named(name: String, r: C.Column & String) -> C.Named & String:
  (c, s) = r
  (C.Named{name, c}, s)

def Sg.cons(r1: C.Named & String, r2: List<&1, C.Named> & String) -> List<&1, C.Named> & String:
  (a, s) = r1
  (t, u) = r2
  (a <> t, s ++ "," ++ u)

def Sg.cols(cs: List<&1, C.Named>) -> List<&1, C.Named> & String:
  match cs:
    case Nil{}:
      (Nil{}, "")
    case C.Named{name, c} <> t:
      Sg.cons(Sg.named(name, Sg.col(c)), Sg.cols(t))

def Sg.fr(+h: U32, r: List<&1, C.Named> & String) -> E.ResT(C.Frame) & String:
  (cs, s) = r
  (Done{C.Frame{h, cs}}, s)

def Sg.frame(r: E.ResT(C.Frame)) -> E.ResT(C.Frame) & String:
  match r:
    case Fail{e}:
      (Fail{e}, "")
    case Done{C.Frame{+h, cs}}:
      Sg.fr(h, Sg.cols(cs))

def Sg.text.k(r: E.ResT(C.Frame) & String) -> String:
  (f, s) = r
  Z.P0.dump(f) ++ "storage " ++ s

# the dump, the P0 report line ("p0 ok": every null slot holds the dtype default, src/p0.bend; post-review
# B1) and the storage line of a read. Every comparison below compares the whole text, so a reader whose
# null slots differ from the reference's is a difference; Run.line.p0 also fails a reference that is dirty
def Sg.text(r: E.ResT(C.Frame)) -> String:
  Sg.text.k(Sg.frame(r))

# ---- one configuration: schema (letters, "" infers), header, separator, infer_rows, storage, row cap ----

type Cf is Data:
  Cf{label: String, schema: String, hdr: Bool, sep: U32, inf: U32, enc: ST.StrEnc, cap: U32}

def Cf.ref(c: Cf, +path: String) -> IO(String):
  match c:
    case Cf{l, +schema, +hdr, +sep, +inf, +enc, +cap}:
      do IO<String>:
        r : E.ResT(C.Frame) <- V.Csv.read_full(path, V.CsvOpts{Chr{sep}, hdr, inf}, Sch.dts(schema), enc, 1048576, cap)
        return Sg.text(r)

def Cf.cand(c: Cf, +path: String, +piece: U32) -> IO(String):
  match c:
    case Cf{l, +schema, +hdr, +sep, +inf, +enc, +cap}:
      do IO<String>:
        r : E.ResT(C.Frame) <- V.Csv.read_v02_full(path, V.CsvOpts{Chr{sep}, hdr, inf}, Sch.dts(schema), enc, piece, cap)
        return Sg.text(r)

def Cf.label(c: Cf) -> String:
  match c:
    case Cf{l, schema, hdr, sep, inf, enc, cap}:
      l

# the pieces still to run, the first difference, runs so far
type RP is Data:
  RP{ps: List<&2, U32>, v: String, go: Bool, n: U32}

def Run.next(+ps: List<&2, U32>, +p: U32, +lab: String, +v: String, +n: U32) -> RP:
  Bool.pick(RP, String.is_empty(v), RP{ps, v, True{}, U32.inc(n)}, RP{ps, lab ++ ", piece " ++ U32.show(p) ++ ": " ++ v, False{}, n})

def Run.loop(f: Nat, +c: Cf, +path: String, +ref: String, st: RP) -> IO(RP):
  match f st:
    case 0n _:
      IO.pure(RP, st)
    case _ RP{ps, v, False{}, n}:
      IO.pure(RP, RP{ps, v, False{}, n})
    case _ RP{Nil{}, v, True{}, n}:
      IO.pure(RP, RP{Nil{}, v, True{}, n})
    case 1n+p RP{+q <> t, v, True{}, +n}:
      do IO<RP>:
        +got : String <- Cf.cand(c, path, q)
        Run.loop(p, c, path, ref, Run.next(t, q, Cf.label(c), M.Cmp.diff(ref, got), n))

# one configuration at the pieces ps: (still equal, runs) carried in RP
def Run.cfg(+c: Cf, +path: String, ps: List<&2, U32>, st: RP) -> IO(RP):
  match st:
    case RP{x, v, False{}, n}:
      IO.pure(RP, RP{x, v, False{}, n})
    case RP{x, v, True{}, +n}:
      do IO<RP>:
        +ref : String <- Cf.ref(c, path)
        Run.loop(40n, c, path, ref, RP{ps, "", True{}, n})

type CP is Data:
  CP{c: Cf, ps: List<&2, U32>}

def Run.all(cs: List<&2, CP>, +path: String, st: RP) -> IO(RP):
  match cs:
    case Nil{}:
      IO.pure(RP, st)
    case CP{c, ps} <> t:
      do IO<RP>:
        st2 : RP <- Run.cfg(c, path, ps, st)
        Run.all(t, path, st2)

def Run.line(+name: String, +outcome: String, r: RP) -> String:
  match r:
    case RP{ps, +v, go, +n}:
      Bool.pick(String, go, name ++ ": ok " ++ U32.show(n) ++ " | " ++ outcome, name ++ ": DIFF " ++ v)

# Run.line, unless the reference read itself breaks the null-slot invariant (its text's P0 line is not
# "p0 ok"): then a DIFF naming it, since two readers that agree on a dirty slot would compare equal
def Run.line.p0(+name: String, +ref: String, +outcome: String, r: RP) -> String:
  Bool.pick(String, String.contains(ref, "\np0 ok\n"), Run.line(name, outcome, r), name ++ ": DIFF p0: the v0.1 reference's null slots do not hold the dtype default")

# every configuration of a file: "<name>: ok <runs> | <the first configuration's v0.1 outcome>", or the
# first run whose dump or storage differs from v0.1's
def Run.file(+name: String, +path: String, +first: Cf, cs: List<&2, CP>) -> IO(String):
  do IO<String>:
    +r0 : String <- Cf.ref(first, path)
    r : RP <- Run.all(cs, path, RP{Nil{}, "", True{}, 0})
    return Run.line.p0(name, r0, M.Cmp.outcome(r0), r)

def Run.print(+s: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(s), IO.pure(Unit, Unit{}), IO.print(s))

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

# the first program argument ("" when none): one case name
def Run.only(xs: List<&1, String>) -> String:
  Maybe.default(&2, String, List.get(&2, String, promote(xs), 1n), "")
