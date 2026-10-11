# bench/w6/hx.bend -- shared helpers of the W6.1 / W6.2 tests (tests/csvprod*.bend,
# tests/csvlane*.bend) and the bench probe: reading a file as bytes and as text the way the v0.1
# reader does, small list / string utilities, the piece sizes the differential runs use.
#
# Test-only code (never imported by src/). Idioms as DESIGN 9: helpers above callers, pairs taken
# apart in the next helper's parameter, no mutual recursion.
import Base

# ---- reading a file ---------------------------------------------------------------------------

def Hx.rb.k(f: File, res: Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  match res:
    case Fail{(code, msg)}:
      do IO<List<&2, U32>>:
        File.close(f)
        return Nil{}
    case Done{bs}:
      do IO<List<&2, U32>>:
        File.close(f)
        return bs

def Hx.rb.got(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (f, res) = r
  Hx.rb.k(f, res)

def Hx.rb.open(o: Result<&1, &1, U32 & String, File>) -> IO(List<&2, U32>):
  match o:
    case Done{f}:
      do IO<List<&2, U32>>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1073741824)
        Hx.rb.got(r)
    case Fail{(code, msg)}:
      IO.pure(List<&2, U32>, Nil{})

# the bytes of a file (empty when it cannot be read)
def Hx.bytes(path: String) -> IO(List<&2, U32>):
  do IO<List<&2, U32>>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Hx.rb.open(o)

def Hx.rt.k(f: File, res: Result<&1, &1, U32 & String, String>) -> IO(String):
  match res:
    case Fail{(code, msg)}:
      do IO<String>:
        File.close(f)
        return ""
    case Done{s}:
      do IO<String>:
        File.close(f)
        return s

def Hx.rt.got(r: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, res) = r
  Hx.rt.k(f, res)

def Hx.rt.open(o: Result<&1, &1, U32 & String, File>) -> IO(String):
  match o:
    case Done{f}:
      do IO<String>:
        r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
        Hx.rt.got(r)
    case Fail{(code, msg)}:
      IO.pure(String, "")

# the text of a file as the runtime's own UTF-8 decoder (File.read) gives it
def Hx.text(path: String) -> IO(String):
  do IO<String>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Hx.rt.open(o)

# ---- lists ------------------------------------------------------------------------------------

def Hx.rev.go(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Hx.rev.go(t, h <> acc)

def Hx.rev(xs: List<&2, U32>) -> List<&2, U32>:
  Hx.rev.go(xs, Nil{})

def Hx.len(xs: List<&2, U32>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case h <> t:
      Hx.len(t, U32.inc(n))

# the piece sizes of the differential runs: 1 byte .. 1 MiB (the spike's T5b set)
def Hx.pieces() -> List<&2, U32>:
  [1, 2, 3, 4, 5, 7, 8, 13, 16, 31, 64, 97, 256, 4096, 1048576]

# the dtype letters of a schema string -> the sort key used by the callers
def Hx.show_u(+x: U32) -> String:
  U32.show(x)

# ---- the file's facts ----------------------------------------------------------------------------
# the LF positions (ascending), the number of `"` bytes, the last byte, the size

type Sc is Data:
  Sc{n: U32, lf: List<&2, U32>, qn: U32, last: U32}

def Hx.scan(bs: List<&2, U32>, +i: U32, +lf: List<&2, U32>, +qn: U32, +last: U32) -> Sc:
  match bs:
    case Nil{}:
      Sc{i, lf, qn, last}
    case +b <> t:
      Hx.scan(t, U32.inc(i), Bool.pick(List<&2, U32>, U32.is_eq(b, 10), i <> lf, lf), U32.add(qn, Bool.to_u32(U32.is_eq(b, 34))), b)

# the checksum of the bytes of a list from index skip on (FNV-1a)
def Hx.lfold(bs: List<&2, U32>, +i: U32, +skip: U32, +h: U32) -> U32:
  match bs:
    case Nil{}:
      h
    case +b <> t:
      Hx.lfold(t, U32.inc(i), skip, Bool.pick(U32, U32.is_lt(i, skip), h, U32.mul(U32.xor(h, b), 16777619)))

# the number of LF positions < x
def Hx.lfcount(xs: List<&2, U32>, +x: U32, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case +p <> t:
      Bool.pick(U32, U32.is_lt(p, x), Hx.lfcount(t, x, U32.inc(n)), n)

# the number of quote bytes at index >= skip
def Hx.qcount(bs: List<&2, U32>, +i: U32, +skip: U32, +n: U32) -> U32:
  match bs:
    case Nil{}:
      n
    case +b <> t:
      Hx.qcount(t, U32.inc(i), skip, U32.add(n, Bool.to_u32(Bool.and(U32.is_ge(i, skip), U32.is_eq(b, 34)))))

# ---- text -----------------------------------------------------------------------------------------

def Hx.chars.go(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      Hx.chars.go(t, c <> acc)

# the code points of a string
def Hx.chars(s: String) -> List<&2, U32>:
  Hx.rev(Hx.chars.go(s, Nil{}))

# the start offsets of the records whose first lines are ls (ascending) from the LF positions lf
# (ascending): line 1 starts at 0, line j + 1 right after the j-th LF
type FO is Data:
  FO{ls: List<&2, U32>, acc: List<&2, U32>}

def Hx.pop.k(hit: Bool, +off: U32, l: U32, t: List<&2, U32>, acc: List<&2, U32>) -> FO:
  match hit:
    case True{}:
      FO{t, off <> acc}
    case False{}:
      FO{l <> t, acc}

# line `line` starts at offset `off`: emit it when it is the next record's
def Hx.pop(+off: U32, +line: U32, st: FO) -> FO:
  match st:
    case FO{ls, acc}:
      match ls:
        case Nil{}:
          FO{Nil{}, acc}
        case +l <> t:
          Hx.pop.k(U32.is_eq(l, line), off, l, t, acc)

# line j starts after the LF at p (the lines are numbered from 1; line 1 starts at 0)
def Hx.offs.go(lf: List<&2, U32>, +j: U32, st: FO) -> FO:
  match lf:
    case Nil{}:
      st
    case +p <> t:
      Hx.offs.go(t, U32.inc(j), Hx.pop(U32.inc(p), j, st))

def Hx.offs.fin(st: FO) -> List<&2, U32>:
  match st:
    case FO{ls, acc}:
      Hx.rev(acc)

def Hx.offs(lf: List<&2, U32>, ls: List<&2, U32>) -> List<&2, U32>:
  Hx.offs.fin(Hx.offs.go(lf, 2, Hx.pop(0, 1, FO{ls, Nil{}})))


# ---- writing a file --------------------------------------------------------------------------------

def Hx.wr.k(f: File, r: Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  do IO<Unit>:
    File.close(f)
    return Unit{}

def Hx.wr.got(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  Hx.wr.k(f, res)

def Hx.wr.open(text: String, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{f}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
        Hx.wr.got(r)
    case Fail{(code, msg)}:
      IO.print("cannot write: " ++ msg)

# a file holding exactly this text (UTF-8)
def Hx.write(path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    Hx.wr.open(text, o)

def Hx.wb.open(bs: List<&2, U32>, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{f}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, bs)
        Hx.wr.got(r)
    case Fail{(code, msg)}:
      IO.print("cannot write: " ++ msg)

# a file holding exactly these bytes
def Hx.write_bytes(path: String, bs: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    Hx.wb.open(bs, o)
