# src/csvprod.bend -- the CSV piece producer (v0.2, W6.1; DESIGN.md 17.4.1 / 17.4.2 / 17.5).
#
# Production form of the W0 spike's producer (bench/spikes/w0_strings/rd.bend, 1. and 2.). NOT
# wired into Csv.read / Csv.scan yet: W6.3 (src/csv.bend) drives it after its header step.
#
# What it does. `Pr.regions(path, off0, line0, piece)` reads the file from byte `off0` (the start
# of the first data record, answered by the header step) in pieces of `piece` bytes with
# `File.read_at` (the File API only returns cons lists, one cell per byte: DESIGN 17.1.1) and
# walks each piece's byte list EXACTLY ONCE. That one walk
#   * packs the bytes, 4 per word, little endian, into the region's flat `Array<U32>`, and
#   * runs the lexical scan: quote parity (a `"` flips it), LFs, and the last record terminator
#     (an LF after which the parity is even).
# A region ends after the last terminator of the bytes read so far; the bytes after it are
# REPLAYED into the next region (a carry of at most one record's tail). A piece holding no
# terminator (a record longer than the piece) leaves the region open: it simply keeps filling,
# and its array doubles when full (no replay, so a record of m pieces costs O(m) not O(m^2)).
# Regions therefore start at global record boundaries (17.4.2: before the first rejecting byte
# the parity is even exactly at a record boundary), so no lane ever guesses its start state.
# Cuts are at ASCII LF bytes, so a UTF-8 sequence, a CRLF pair or a doubled quote split across
# pieces needs no special case: all of them are carried bytes.
#
# A region (`Rg`): its bytes `a[0..n)` (little endian words: byte p is `a[p / 4] >> (8 * (p % 4))`),
# `off` the file offset of its first byte, `line0` the 1-based PHYSICAL line it starts on (every
# LF counts, also inside quotes and blank lines; the next region's line0 = this line0 + lfs),
# `nt` the record terminators inside it (so it holds at most nt + 1 records), `lfs` its LF
# count, `fin` = 1 for the last region (the input ends in it: its last record may be unterminated).
# Region i ends exactly where region i + 1 begins; together they cover [off0, file size).
#
# Result (`PrOut`): `PrOk{nr, odd, regs}` regions in file order, `odd` = the final quote parity
# (1: the input ends inside a quoted field, i.e. malformed quoting, 15.6.2), or `PrErr{code, msg}`
# for an IO error (open / size / read; the file is closed first).
#
# Ownership. `Pr.regions` takes the path (borrowed: a String), answers the regions, which the
# caller owns (one array each, moved to the lane that parses it; a lane frees it).
# Hot loop types: `PK` (the scan state) and `Rg`, `RS` are single-constructor private records,
# never `+`-shared, so they stay cold (unboxed in registers) even in a program importing
# frame.bend (DESIGN 17.1.3). The only hot value the walk touches is the piece's byte list.
#
# Malformed input. Nothing here judges quoting: the scan only counts parity. A region cut after
# the first malformed byte may be wrong; harmless, the lane that holds that byte rejects (or the
# final parity is odd) and malformed quoting outranks every other error (17.4.6). Invalid UTF-8
# is NOT touched here: bytes are bytes; the lane decodes them with the runtime's rules.
#
# Idioms (DESIGN 9): helpers above callers; a match on a parameter comes before any destructuring
# let; pairs are taken apart in the next helper's parameter; no mutual recursion (loops carry a
# record and a non-recursive step helper).
import Base
import ./kernels.bend as K

# branch select without boxing (`Bool.pick` evaluates both arms)
def Pr.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# byte k (0..3) of a packed word
def Pr.byte(+w: U32, +k: U32) -> U32:
  U32.and(U32.div(w, Pr.sel(U32.is_eq(k, 0), 1, Pr.sel(U32.is_eq(k, 1), 256, Pr.sel(U32.is_eq(k, 2), 65536, 16777216)))), 255)

def Pr.at.k(+p: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +w) = r
  (a, Pr.byte(w, U32.and(p, 3)))

# byte p of a packed array (the array comes back)
def Pr.at(a: Array<U32>, +p: U32) -> Array<U32> & U32:
  Pr.at.k(p, Array.get(U32, a, U32.div(p, 4)))

# ---- the scan state ---------------------------------------------------------------------------
# the region being filled: its packed bytes a (n of them), the word accumulator acc and the weight
# sh (1, 256, 65536, 2^24) of the next byte in it, the quote parity q, the LFs seen lf, the last
# terminator: cut = its index + 1 (0: none) and the LFs up to it lfc, the terminators nt, the
# capacity of a in bytes cap
type PK is Type:
  PK{a: Array<U32>, n: U32, acc: U32, sh: U32, q: U32, lf: U32, cut: U32, lfc: U32, nt: U32, cap: U32}

def Pk.step(+b: U32, st: PK) -> PK:
  match st:
    case PK{a, +n, +acc, +sh, +q, +lf, +cut, +lfc, +nt, cap}:
      +acc2 = U32.add(acc, U32.mul(b, sh))
      +full = U32.is_eq(sh, 16777216)
      +q2 = U32.xor(q, Bool.to_u32(U32.is_eq(b, 34)))
      +islf = U32.is_eq(b, 10)
      +term = Bool.and(islf, U32.is_eq(q2, 0))
      +lf2 = U32.add(lf, Bool.to_u32(islf))
      PK{Array.set(U32, a, U32.div(n, 4), acc2), U32.inc(n), Pr.sel(full, 0, acc2), Pr.sel(full, 1, U32.mul(sh, 256)), q2, lf2, Pr.sel(term, U32.inc(n), cut), Pr.sel(term, lf2, lfc), U32.add(nt, Bool.to_u32(term)), cap}

# the bytes of one piece, in order (the piece's list is consumed)
def Pk.go(bs: List<&2, U32>, st: PK) -> PK:
  match bs:
    case Nil{}:
      st
    case +b <> t:
      Pk.go(t, Pk.step(b, st))

# an empty region whose array has 2^d words
def Pk.new(+d: Nat) -> PK:
  PK{Array.new(U32, d, 0), 0, 0, 1, 0, 0, 0, 0, 0, U32.shln(4, d)}

# room for `bytes` bytes: 2^d words with 4 * 2^d >= bytes + 8
def Pk.depth(+bytes: U32) -> Nat:
  K.Kernel.depth_for(U32.add(U32.div(U32.add(bytes, 8), 4), 1))

# a larger array (the bytes so far copied once: the array doubles, so a record of m pieces costs
# O(m) copies in all)
def Pk.grow.k(+d: Nat, +m: U32, a: Array<U32>, acc: U32, sh: U32, q: U32, lf: U32, cut: U32, lfc: U32, nt: U32, +n: U32) -> PK:
  PK{K.Kernel.copy_into(~U32, m, 0, Array.new(U32, d, 0), a), n, acc, sh, q, lf, cut, lfc, nt, U32.shln(4, d)}

def Pk.room.k(need: Bool, +piece: U32, a: Array<U32>, +n: U32, acc: U32, sh: U32, q: U32, lf: U32, cut: U32, lfc: U32, nt: U32, cap: U32) -> PK:
  match need:
    case True{}:
      Pk.grow.k(Pk.depth(U32.add(n, U32.add(piece, piece))), U32.add(U32.div(n, 4), 1), a, acc, sh, q, lf, cut, lfc, nt, n)
    case False{}:
      PK{a, n, acc, sh, q, lf, cut, lfc, nt, cap}

# room for the next piece of `piece` bytes
def Pk.room(+piece: U32, st: PK) -> PK:
  match st:
    case PK{a, +n, acc, sh, q, lf, cut, lfc, nt, +cap}:
      Pk.room.k(U32.is_gt(U32.add(n, U32.add(piece, 8)), cap), piece, a, n, acc, sh, q, lf, cut, lfc, nt, cap)

# bytes [i, i + f) of a, replayed into st (the carry of a region into the next one)
def Pk.replay(f: Nat, +i: U32, st: PK, r: Array<U32> & U32) -> Array<U32> & PK:
  match f:
    case 0n:
      (a, b) = r
      (a, st)
    case 1n+p:
      (a, +b) = r
      Pk.replay(p, U32.inc(i), Pk.step(b, st), Pr.at(a, U32.inc(i)))

# ---- regions ----------------------------------------------------------------------------------

type Rg is Type:
  Rg{a: Array<U32>, n: U32, off: U32, line0: U32, nt: U32, lfs: U32, fin: U32}

# ---- the IO loop --------------------------------------------------------------------------------
# off: the file offset of the next read; size: the file size; ro: the file offset of the region
# being filled; line0: its first line; mark: its byte count before the piece being read (the
# piece's length is pk.n - mark, a short read ends the walk too); nr: regions so far
type RS is Type:
  RRun{f: File, off: U32, size: U32, piece: U32, ro: U32, line0: U32, mark: U32, nr: U32, pk: PK, regs: List<&1, Rg>}
  REnd{nr: U32, regs: List<&1, Rg>, odd: U32}
  RErr{code: U32, msg: String}

# a piece ended inside the input and held a terminator: the region up to the last one is done;
# the rest carries into a fresh region's array (r: the carried bytes replayed)
def Rd.cut.k(f: File, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +nr: U32, regs: List<&1, Rg>, +n: U32, +cut: U32, +lfc: U32, +nt: U32, r: Array<U32> & PK) -> RS:
  (a, pk2) = r
  match pk2:
    case PK{b, +n2, acc, sh, q, lf, cut2, lfc2, nt2, cap}:
      RRun{f, off, size, piece, U32.add(ro, cut), U32.add(line0, lfc), n2, U32.inc(nr), PK{b, n2, acc, sh, q, lf, cut2, lfc2, nt2, cap}, Rg{a, cut, ro, line0, nt, lfc, 0} <> regs}

# no terminator (cut = 0): the region stays open and keeps filling (Pk.room grows it)
def Rd.open.k(f: File, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +nr: U32, regs: List<&1, Rg>, pk: PK) -> RS:
  match pk:
    case PK{a, +n, acc, sh, q, lf, cut, lfc, nt, cap}:
      RRun{f, off, size, piece, ro, line0, n, nr, PK{a, n, acc, sh, q, lf, cut, lfc, nt, cap}, regs}

def Rd.split.k(cut0: Bool, f: File, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +nr: U32, regs: List<&1, Rg>, pk: PK) -> RS:
  match cut0:
    case True{}:
      Rd.open.k(f, off, size, piece, ro, line0, nr, regs, pk)
    case False{}:
      match pk:
        case PK{a, +n, acc, sh, q, lf, +cut, +lfc, +nt, cap}:
          Rd.cut.k(f, off, size, piece, ro, line0, nr, regs, n, cut, lfc, nt, Pk.replay(U32.to_nat(U32.sub(n, cut)), cut, Pk.new(Pk.depth(U32.add(U32.sub(n, cut), U32.add(piece, piece)))), Pr.at(a, cut)))

# the piece was walked: pk is the state after it
def Rd.split(+off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +nr: U32, f: File, regs: List<&1, Rg>, pk: PK) -> RS:
  match pk:
    case PK{a, n, acc, sh, q, lf, +cut, lfc, nt, cap}:
      Rd.split.k(U32.is_eq(cut, 0), f, off, size, piece, ro, line0, nr, regs, PK{a, n, acc, sh, q, lf, cut, lfc, nt, cap})

# the end of the input: everything left is the last region (its last record may be unterminated)
def Rd.last(+ro: U32, +line0: U32, +nr: U32, regs: List<&1, Rg>, pk: PK) -> RS:
  match pk:
    case PK{a, +n, acc, sh, +q, +lf, cut, lfc, +nt, cap}:
      REnd{U32.inc(nr), Rg{a, n, ro, line0, nt, lf, 1} <> regs, q}

def Rd.after.k(last: Bool, f: File, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +nr: U32, regs: List<&1, Rg>, pk: PK) -> IO(RS):
  match last:
    case True{}:
      do IO<RS>:
        File.close(f)
        return Rd.last(ro, line0, nr, regs, pk)
    case False{}:
      IO.pure(RS, Rd.split(off, size, piece, ro, line0, nr, f, regs, pk))

# pk: the state after the piece walked in; off2 = off + the bytes it held
def Rd.after(f: File, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +mark: U32, +nr: U32, regs: List<&1, Rg>, pk: PK) -> IO(RS):
  match pk:
    case PK{a, +n, acc, sh, q, lf, cut, lfc, nt, cap}:
      +got = U32.sub(n, mark)
      +off2 = U32.add(off, got)
      Rd.after.k(Bool.or(U32.is_eq(got, 0), U32.is_ge(off2, size)), f, off2, size, piece, ro, line0, nr, regs, PK{a, n, acc, sh, q, lf, cut, lfc, nt, cap})

def Rd.got(f: File, res: Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +mark: U32, +nr: U32, pk: PK, regs: List<&1, Rg>) -> IO(RS):
  match res:
    case Fail{(code, msg)}:
      do IO<RS>:
        File.close(f)
        return RErr{code, msg}
    case Done{bs}:
      Rd.after(f, off, size, piece, ro, line0, mark, nr, regs, Pk.go(bs, Pk.room(piece, pk)))

def Rd.step.k(r: File & Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +size: U32, +piece: U32, +ro: U32, +line0: U32, +mark: U32, +nr: U32, pk: PK, regs: List<&1, Rg>) -> IO(RS):
  (f, res) = r
  Rd.got(f, res, off, size, piece, ro, line0, mark, nr, pk, regs)

def Rd.step(st: RS) -> IO(RS):
  match st:
    case REnd{nr, regs, odd}:
      IO.pure(RS, REnd{nr, regs, odd})
    case RErr{code, msg}:
      IO.pure(RS, RErr{code, msg})
    case RRun{f, +off, +size, +piece, +ro, +line0, +mark, +nr, pk, regs}:
      do IO<RS>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, off, piece)
        Rd.step.k(r, off, size, piece, ro, line0, mark, nr, pk, regs)

# one step per piece; the fuel (pieces + 3) can never run out before the file does
def Rd.loop(fuel: Nat, st: RS) -> IO(RS):
  match fuel:
    case 0n:
      IO.pure(RS, st)
    case 1n+p:
      match st:
        case REnd{nr, regs, odd}:
          IO.pure(RS, REnd{nr, regs, odd})
        case RErr{code, msg}:
          IO.pure(RS, RErr{code, msg})
        case RRun{f, off, size, piece, ro, line0, mark, nr, pk, regs}:
          do IO<RS>:
            st2 : RS <- Rd.step(RRun{f, off, size, piece, ro, line0, mark, nr, pk, regs})
            Rd.loop(p, st2)

def Rd.sized(+off0: U32, +line0: U32, +piece: U32, f: File, res: Result<&1, &1, U32 & String, U32>) -> IO(RS):
  match res:
    case Done{+size}:
      Rd.loop(Nat.add(U32.to_nat(U32.div(U32.sub(size, U32.min(off0, size)), piece)), 3n), RRun{f, off0, size, piece, off0, line0, 0, 0, Pk.new(Pk.depth(U32.add(piece, piece))), Nil{}})
    case Fail{(code, msg)}:
      do IO<RS>:
        File.close(f)
        return RErr{code, msg}

def Rd.size(+off0: U32, +line0: U32, +piece: U32, r: File & Result<&1, &1, U32 & String, U32>) -> IO(RS):
  (f, res) = r
  Rd.sized(off0, line0, piece, f, res)

def Rd.opened(+off0: U32, +line0: U32, +piece: U32, o: Result<&1, &1, U32 & String, File>) -> IO(RS):
  match o:
    case Done{f}:
      do IO<RS>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Rd.size(off0, line0, piece, r)
    case Fail{(code, msg)}:
      IO.pure(RS, RErr{code, msg})

# ---- the answer -----------------------------------------------------------------------------------

type PrOut is Type:
  PrOk{nr: U32, odd: U32, regs: List<&1, Rg>}
  PrErr{code: U32, msg: String}

def Pr.out(st: RS) -> PrOut:
  match st:
    case REnd{nr, regs, odd}:
      PrOk{nr, odd, List.reverse(&1, Rg, regs)}
    case RErr{code, msg}:
      PrErr{code, msg}
    case RRun{f, off, size, piece, ro, line0, mark, nr, pk, regs}:
      PrErr{0, "csv producer: the read did not finish"}

# The regions of the file from byte `off0` (physical line `line0`, 1-based) to its end, read in
# pieces of `piece` bytes (256 KiB - 1 MiB; a piece of 2^k - 2^(k - 6) bytes fills its array
# without a wasted half: arrays have 2^d words). `piece` 0 reads one byte at a time.
def Pr.regions(path: String, +off0: U32, +line0: U32, +piece: U32) -> IO(PrOut):
  do IO<PrOut>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    st : RS <- Rd.opened(off0, line0, U32.max(piece, 1), o)
    return Pr.out(st)

# the default piece: 240 KiB. With the carry (< 16 KiB of a typical record's tail) a region's
# array holds exactly 2^16 words
def Pr.piece() -> U32:
  245760

# ---- the region tree: leaves in file order, paired into a balanced binary tree -------------------
# (the shape a fork walks: `a b = f(l) f(r)`; never 1-vs-rest. The fork itself belongs to the
# integration step: it needs the lane's result type.)

type Rt is Type:
  RE{}
  RL{rg: Rg}
  RN{l: Rt, r: Rt}

# regions (file order) -> leaves (file order)
def Rt.leaves(xs: List<&1, Rg>) -> List<&1, Rt>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      RL{h} <> Rt.leaves(t)

def Rt.pair(xs: List<&1, Rt>) -> List<&1, Rt>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      a <> Nil{}
    case Con{a, Con{b, u}}:
      RN{a, b} <> Rt.pair(u)

def Rt.top(f: Nat, xs: List<&1, Rt>) -> Rt:
  match f xs:
    case _ Nil{}:
      RE{}
    case _ Con{a, Nil{}}:
      a
    case 0n other:
      RE{}
    case 1n+p other:
      Rt.top(p, Rt.pair(other))

# a balanced tree over the regions, in file order (RE{} for none)
def Rt.of(regs: List<&1, Rg>) -> Rt:
  Rt.top(32n, Rt.leaves(regs))
