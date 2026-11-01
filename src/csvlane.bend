# src/csvlane.bend -- the CSV lane: tokenizer and typed column loops over ONE region
# (v0.2, W6.2; DESIGN.md 17.4.1 steps 3-4, 17.4.3, 17.4.4).
#
# Production form of the W0 spike's lane (bench/spikes/w0_strings/rd.bend, 3.). The v0.2
# reader (src/csv.bend Csv.v2.*, W6.3; opt-in, DESIGN.md 15.6.6) forks it over the regions of
# src/csvprod.bend and combines the results (error precedence, dictionary merge, row cap, concatenation).
# W6.3 split the lane into Ln.tok (tokenizer) and Ln.cols (typed loops) and added Ln.cls / Ln.clsr (the
# classification that inference uses, below).
#
#   Ln.lane(ts, w, sep, rg) -> LO       one region in, its typed columns out
#
# `ts`: the dtype of every column (`Ty`: TyU u32, TyI i32, TyF f32, TyB bool, TyS Dictionary
# string, TyR raw string, TyN skipped), `w`: the record width (the header's, >= 1), `sep`: the
# separator's code point (an ASCII byte), `rg`: a region (src/csvprod.bend: packed bytes starting
# at a record boundary). The lane is a pure function of those; it forks nothing (the caller makes
# ONE balanced fork over the regions, `a b = lane(l) lane(r)`), so a lane's cost is its region's.
#
# Per region, in order:
#  1. ONE tokenizer loop over the packed bytes (`Tk.go2`: one flat def, scalar state in registers,
#     the modes MS/MB/ME/MQ/MQC of the reference parser's walk; runs of text bytes are skipped by
#     two tiny loops `Tk.skipb` / `Tk.skipq`): it writes every field's content range [start, end),
#     its flags (bit 0: quoted, bit 1: holds a doubled quote) and every kept record's physical
#     line into flat `Array<U32>`s. No CsvCell, no per-field String, no reverse, no trim list.
#  2. one flat loop per column over those ranges (`Lw.go` u32 / i32 / bool, `Lf.go` f32, `Sc.go`
#     the per-region Dictionary coder, `Rw.go` raw strings): values and the validity word
#     (0 / 1) written straight into `Array<U32>` / `Array<F32>`. Numeric fields are trimmed (ASCII
#     `Char.is_space` bytes, DESIGN 15.6.1) and parsed with EXACTLY v0.1's rules (below).
#  3. the first cell of each numeric column that does not parse: its region row, its physical
#     line and its text (the content as csvparse decodes it: doubled quotes collapsed), decoded
#     inside the lane from the region's bytes (no second read).
#
# Output (`LO`): `n` kept rows; `rej` 1 = malformed quoting (a quote in a bare field, text after a
# closing quote, a CR after a closing quote not followed by LF, or the input ends inside quotes:
# the lane stops there and every other field of LO is meaningless; DESIGN 17.4.6 puts malformed
# first); `rag` the physical line of the region's first RAGGED record (a record whose field count
# is not w; 0: none) and `rgn` its field count (v0.1's "expected <w> fields, got <rgn>"); `lines`
# the physical line of every kept row; `cols` one `CO` per column in order.
# Blank records (one empty unquoted field) are skipped when w > 1 (their LFs still count towards
# lines) and kept as a null row when w = 1. A ragged record is dropped from the rows (the error
# wins anyway). A region is parsed to its end even after a ragged record or a bad cell: the
# caller combines the per-region findings in file order (first ragged region, then per column the
# first region with a bad cell).
#
#   CO.OW{a, v, nulls, bad, bl, bt}   u32 / i32 (two's complement bits) / bool: a[0..n) values (null
#                                     and bad slots hold 0), v[0..n) validity words
#   CO.OF{a, v, nulls, bad, bl, bt}   f32 (a: Array<F32>)
#   CO.OS{c, v, nulls, k, ents, fr}   Dictionary string part: c[0..n) LOCAL codes in first-appearance
#                                     order (a null row holds the code of the empty content), k
#                                     entries, fr[0..k) each entry's first local row (W6.3: the
#                                     EncAuto rule needs it), ents[0..k) the entries' strings, each decoded ONCE
#                                     (UTF-8 exactly as the runtime's File.read: an invalid byte
#                                     is U+FFFD and is read again). Region codes are never
#                                     exposed: two byte sequences may decode to one string, so the
#                                     merge codes the decoded entries into its own dictionary
#   CO.OR{a, v, nulls}                raw string part: a[0..n) decoded strings ("" for a null)
#   nulls = the rows with v = 0; bad = the first bad row + 1 (0: none), bl its physical line, bt the
#   field's text (untrimmed, quotes removed: v0.1's `ParseError{bl, "column <name>: cannot parse
#   \"<bt>\" as <dtype>"}`).
# All arrays have 2^depth_for(max(n, 1)) slots (n <= slots; a part's depth is not stored: the
# merge copies n rows), except v of a part with no null: ONE slot holding 1 (Col.vtrim), read with
# wrapping indices like the full array of ones it stands for.
#
# Field rules (v0.1 `Csv.ok` / `Csv.rd.w`, bit for bit; tests/csvlane*.bend check them against
# csvparse + Csv conversions): a numeric / bool field whose content is empty after trimming is
# null (quoted or not); u32 = `U32.read` (digits only, no sign, overflow is bad); i32 = `I32.read`
# ('-' then digits, no '+', in [-2^31, 2^31)); bool = exactly true / True / false / False; f32 = a
# correctly rounded `F32.read` (strtof): the exact fast path [+-]digits[.digits] with mantissa
# <= 2^24 and <= 10 fraction digits is one correctly rounded f32 division (Clinger), everything
# else (exponents, nan, inf, long mantissas, doubled quotes) decodes the field and calls
# `F32.read`. A str field is valid when quoted or non-empty, null otherwise (15.6.1).
#
# Ownership: `Ln.lane` consumes the region (its bytes are freed with the lane) and borrows `ts`
# (read once). The hot-loop state records (TK, LW, LF, LS, ...) are private single-constructor
# types: never `+`-shared, never returned, so in a program importing frame.bend they stay COLD
# (registers, no refcount), unlike String and List (DESIGN 17.1.3). LO / CO are returned to the
# caller, who must take them apart once and not share them.
#
# Idioms (DESIGN 9): helpers above callers; a match on a parameter before any destructuring let;
# no mutual recursion (a loop carries a record and a non-recursive step helper in its call).
import Base
import ./kernels.bend as K
import ./csvprod.bend as P

# ---- small helpers -------------------------------------------------------------------------------

def Ln.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# byte k (0..3) of a packed word
def Bt.of(+w: U32, +k: U32) -> U32:
  U32.and(U32.div(w, Ln.sel(U32.is_eq(k, 0), 1, Ln.sel(U32.is_eq(k, 1), 256, Ln.sel(U32.is_eq(k, 2), 65536, 16777216)))), 255)

def Bt.at.k(+p: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +w) = r
  (a, Bt.of(w, U32.and(p, 3)))

# byte p of a packed array (4 bytes per word, little endian)
def Bt.at(a: Array<U32>, +p: U32) -> Array<U32> & U32:
  Bt.at.k(p, Array.get(U32, a, U32.div(p, 4)))

def is_sp(+b: U32) -> Bool:
  Bool.or(U32.is_eq(b, 32), Bool.and(U32.is_ge(b, 9), U32.is_le(b, 13)))

# the dtype of a column: u32, i32, f32, bool, str by a per-region Dictionary (entries decoded once),
# str as one decoded String per row, skipped (an empty part)
type Ty is Data:
  TyU{}
  TyI{}
  TyF{}
  TyB{}
  TyS{}
  TyR{}
  TyN{}

# ---- the tokenizer -----------------------------------------------------------------------------------
# modes: field start, bare field, in quotes, just after a quote in a quoted field, CR after it.
# A bare field keeps its CRs; one CR right before the LF (or the end) that ends it is dropped,
# exactly the hub parser's CR-holding modes. fq bit 0: quoted, bit 1: holds a doubled quote.
# The loop is Tk.go2 (generated by bench/w6/gen_tk.py); at the end of the input the last record is
# closed by Tk.end (the helpers Tk.rec ... Tk.eof below: the reference parser's `fin.rows`).

type Md is Data:
  MS{}
  MB{}
  ME{}
  MQ{}
  MQC{}

type TK is Type:
  TK{m: Md, cr: U32, f: U32, r: U32, ln: U32, rl: U32, fs0: U32, qe: U32, esc: U32, rag: U32, rgn: U32, rej: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, lines: Array<U32>}

# the current field and its record end at p (lf: 1 for an LF, 0 for the end of the input).
# A blank record (one empty unquoted field) is skipped when w > 1; a record of another
# width is ragged (the first one's line and width are kept) and dropped.
def Tk.rec(+e: U32, +qf: U32, +p: U32, +lf: U32, +w: U32, st: TK) -> TK:
  match st:
    case TK{m, cr, +f, +r, +ln, +rl, +fs0, qe, esc, +rag, +rgn, rej, fs, fe, fq, lines}:
      +slot = U32.add(U32.mul(r, w), U32.min(f, U32.sub(w, 1)))
      +nf = U32.inc(f)
      +blank = Bool.and(U32.is_eq(nf, 1), Bool.and(U32.is_eq(qf, 0), U32.is_eq(e, fs0)))
      +skip = Bool.and(blank, U32.is_gt(w, 1))
      +keep = Bool.and(Bool.not(skip), U32.is_eq(nf, w))
      +ragd = Bool.and(Bool.not(skip), U32.is_ne(nf, w))
      +first = Bool.and(ragd, U32.is_eq(rag, 0))
      +ln2 = U32.add(ln, lf)
      TK{MS{}, 0, 0, U32.add(r, Bool.to_u32(keep)), ln2, U32.inc(ln2), U32.inc(p), qe, 0, Ln.sel(first, rl, rag), Ln.sel(first, nf, rgn), rej, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, e), Array.set(U32, fq, slot, qf), Array.set(U32, lines, r, rl)}

type CK is Data:
  KT{}
  KLf{}
  KCr{}
  KSep{}
  KQ{}
  KEnd{}

def Tk.cls.k(+lf: Bool, +cr: Bool, +sep: Bool, +q: Bool) -> CK:
  match lf:
    case True{}:
      KLf{}
    case False{}:
      match cr:
        case True{}:
          KCr{}
        case False{}:
          match sep:
            case True{}:
              KSep{}
            case False{}:
              match q:
                case True{}:
                  KQ{}
                case False{}:
                  KT{}

def Tk.cls(+b: U32, +sep: U32) -> CK:
  Tk.cls.k(U32.is_eq(b, 10), U32.is_eq(b, 13), U32.is_eq(b, sep), U32.is_eq(b, 34))

def Tk.rej(st: TK) -> TK:
  match st:
    case TK{m, cr, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines}:
      TK{m, cr, f, r, ln, rl, fs0, qe, esc, rag, rgn, 1, fs, fe, fq, lines}

def Tk.qf(+esc: U32) -> U32:
  U32.add(1, U32.mul(esc, 2))

# the closing-quote position and flags of the current quoted field
def Tk.qinfo(st: TK) -> U32 & U32 & TK:
  match st:
    case TK{m0, cr0, f, r, ln, rl, fs0, +qe, +esc, rag, rgn, rej, fs, fe, fq, lines}:
      (qe, Tk.qf(esc), TK{m0, cr0, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})

# the input ends in a quoted field's closing quote (or CR after it): the record ends there, no LF
def Tk.qend(+p: U32, +w: U32, r: U32 & U32 & TK) -> TK:
  (+qe, +qf, st) = r
  Tk.rec(qe, qf, p, 0, w, st)

def Tk.binfo(st: TK) -> U32 & TK:
  match st:
    case TK{m0, +cr0, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines}:
      (cr0, TK{m0, cr0, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})

def Tk.bend(+p: U32, +w: U32, +lf: U32, r: U32 & TK) -> TK:
  (+cr, st) = r
  Tk.rec(U32.sub(p, cr), 0, p, lf, w, st)

def Tk.mget(st: TK) -> TK & Md:
  match st:
    case TK{+m0, cr0, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines}:
      (TK{m0, cr0, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines}, m0)

# the packed array, the class of the byte at i (KEnd past the last byte) and i; one read per byte,
# the array handed back
type NX is Type:
  NX{a: Array<U32>, k: CK, i: U32}

def Tk.ck(end: Bool, +b: U32, +sep: U32) -> CK:
  match end:
    case True{}:
      KEnd{}
    case False{}:
      Tk.cls(b, sep)

def Tk.nx(+sep: U32, +n: U32, +i: U32, r: Array<U32> & U32) -> NX:
  (a, +x) = r
  NX{a, Tk.ck(U32.is_ge(i, n), Bt.of(x, U32.and(i, 3)), sep), i}

# a run of text bytes (none of LF, CR, the separator, a quote) is skipped by a tiny flat loop of
# its own: the main loop sees only the first byte after it (bare fields: a text byte keeps the mode)
def Tk.skipb(f: Nat, +sep: U32, +n: U32, sk: NX) -> NX:
  match f sk:
    case 0n other:
      other
    case 1n+p NX{a, KT{}, +i}:
      +j = U32.inc(i)
      Tk.skipb(p, sep, n, Tk.nx(sep, n, j, Array.get(U32, a, U32.div(j, 4))))
    case _ other:
      other

# inside quotes only a quote or an LF matters (CR, the separator and text are content)
def Tk.skipq(f: Nat, +sep: U32, +n: U32, sk: NX) -> NX:
  match f sk:
    case 0n other:
      other
    case _ NX{a, KQ{}, i}:
      NX{a, KQ{}, i}
    case _ NX{a, KLf{}, i}:
      NX{a, KLf{}, i}
    case _ NX{a, KEnd{}, i}:
      NX{a, KEnd{}, i}
    case 1n+p NX{a, k, +i}:
      +j = U32.inc(i)
      Tk.skipq(p, sep, n, Tk.nx(sep, n, j, Array.get(U32, a, U32.div(j, 4))))

# BEGIN GENERATED Tk.go2 (bench/w6/gen_tk.py writes this def: edit the generator, then run it)
def Tk.go2(f: Nat, m: Md, nx: NX, +cr: U32, +fi: U32, +r: U32, +ln: U32, +rl: U32, +fs0: U32, +qe: U32, +esc: U32, +rag: U32, +rgn: U32, +rej: U32, +w: U32, +sep: U32, +n: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, lines: Array<U32>) -> Array<U32> & TK:
  match f m nx:
    case 0n m0 NX{a, k, i}:
      (a, TK{m0, cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})
    case 1n+q m0 NX{a, KEnd{}, i}:
      (a, TK{m0, cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})
    case 1n+q MS{} NX{a, KLf{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      +nf = U32.inc(fi)
      +blank = Bool.and(U32.is_eq(nf, 1), U32.is_eq(i, fs0))
      +skip = Bool.and(blank, U32.is_gt(w, 1))
      +keep = Bool.and(Bool.not(skip), U32.is_eq(nf, w))
      +ragd = Bool.and(Bool.not(skip), U32.is_ne(nf, w))
      +first = Bool.and(ragd, U32.is_eq(rag, 0))
      +ln2 = U32.inc(ln)
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, 0, U32.add(r, Bool.to_u32(keep)), ln2, U32.inc(ln2), i1, qe, 0, Ln.sel(first, rl, rag), Ln.sel(first, nf, rgn), rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, i), Array.set(U32, fq, slot, 0), Array.set(U32, lines, r, rl))
    case 1n+q MS{} NX{a, KCr{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MB{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 1, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MS{} NX{a, KSep{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, U32.inc(fi), r, ln, rl, i1, qe, 0, rag, rgn, rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, i), Array.set(U32, fq, slot, 0), lines)
    case 1n+q MS{} NX{a, KQ{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, ME{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, fi, r, ln, rl, i1, qe, 0, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MS{} NX{a, KT{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MB{}, Tk.skipb(U32.to_nat(U32.sub(n, i1)), sep, n, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4)))), 0, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MB{} NX{a, KLf{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      +nf = U32.inc(fi)
      +blank = Bool.and(U32.is_eq(nf, 1), U32.is_eq(U32.sub(i, cr), fs0))
      +skip = Bool.and(blank, U32.is_gt(w, 1))
      +keep = Bool.and(Bool.not(skip), U32.is_eq(nf, w))
      +ragd = Bool.and(Bool.not(skip), U32.is_ne(nf, w))
      +first = Bool.and(ragd, U32.is_eq(rag, 0))
      +ln2 = U32.inc(ln)
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, 0, U32.add(r, Bool.to_u32(keep)), ln2, U32.inc(ln2), i1, qe, 0, Ln.sel(first, rl, rag), Ln.sel(first, nf, rgn), rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, U32.sub(i, cr)), Array.set(U32, fq, slot, 0), Array.set(U32, lines, r, rl))
    case 1n+q MB{} NX{a, KCr{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MB{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 1, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MB{} NX{a, KSep{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, U32.inc(fi), r, ln, rl, i1, qe, 0, rag, rgn, rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, i), Array.set(U32, fq, slot, 0), lines)
    case 1n+q MB{} NX{a, KQ{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MB{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, 1, w, sep, n, fs, fe, fq, lines)
    case 1n+q MB{} NX{a, KT{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MB{}, Tk.skipb(U32.to_nat(U32.sub(n, i1)), sep, n, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4)))), 0, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q ME{} NX{a, KQ{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MQ{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, fi, r, ln, rl, fs0, i, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q ME{} NX{a, KLf{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, ME{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, fi, r, U32.inc(ln), rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q ME{} NX{a, _, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, ME{}, Tk.skipq(U32.to_nat(U32.sub(n, i1)), sep, n, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4)))), 0, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MQ{} NX{a, KQ{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, ME{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, fi, r, ln, rl, fs0, qe, 1, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MQ{} NX{a, KLf{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      +nf = U32.inc(fi)
      +blank = Bool.and(U32.is_eq(nf, 1), Bool.and(U32.is_eq(U32.add(1, U32.mul(esc, 2)), 0), U32.is_eq(qe, fs0)))
      +skip = Bool.and(blank, U32.is_gt(w, 1))
      +keep = Bool.and(Bool.not(skip), U32.is_eq(nf, w))
      +ragd = Bool.and(Bool.not(skip), U32.is_ne(nf, w))
      +first = Bool.and(ragd, U32.is_eq(rag, 0))
      +ln2 = U32.inc(ln)
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, 0, U32.add(r, Bool.to_u32(keep)), ln2, U32.inc(ln2), i1, qe, 0, Ln.sel(first, rl, rag), Ln.sel(first, nf, rgn), rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, qe), Array.set(U32, fq, slot, U32.add(1, U32.mul(esc, 2))), Array.set(U32, lines, r, rl))
    case 1n+q MQ{} NX{a, KCr{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MQC{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, w, sep, n, fs, fe, fq, lines)
    case 1n+q MQ{} NX{a, KSep{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, U32.inc(fi), r, ln, rl, i1, qe, 0, rag, rgn, rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, qe), Array.set(U32, fq, slot, U32.add(1, U32.mul(esc, 2))), lines)
    case 1n+q MQ{} NX{a, KT{}, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MQ{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, 1, w, sep, n, fs, fe, fq, lines)
    case 1n+q MQC{} NX{a, KLf{}, +i}:
      +i1 = U32.inc(i)
      +slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))
      +nf = U32.inc(fi)
      +blank = Bool.and(U32.is_eq(nf, 1), Bool.and(U32.is_eq(U32.add(1, U32.mul(esc, 2)), 0), U32.is_eq(qe, fs0)))
      +skip = Bool.and(blank, U32.is_gt(w, 1))
      +keep = Bool.and(Bool.not(skip), U32.is_eq(nf, w))
      +ragd = Bool.and(Bool.not(skip), U32.is_ne(nf, w))
      +first = Bool.and(ragd, U32.is_eq(rag, 0))
      +ln2 = U32.inc(ln)
      Tk.go2(q, MS{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), 0, 0, U32.add(r, Bool.to_u32(keep)), ln2, U32.inc(ln2), i1, qe, 0, Ln.sel(first, rl, rag), Ln.sel(first, nf, rgn), rej, w, sep, n, Array.set(U32, fs, slot, fs0), Array.set(U32, fe, slot, qe), Array.set(U32, fq, slot, U32.add(1, U32.mul(esc, 2))), Array.set(U32, lines, r, rl))
    case 1n+q MQC{} NX{a, _, +i}:
      +i1 = U32.inc(i)
      Tk.go2(q, MQC{}, Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4))), cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, 1, w, sep, n, fs, fe, fq, lines)
# END GENERATED Tk.go2

def Tk.eof.f(more: Bool, +n: U32, +w: U32, st: TK) -> TK:
  match more:
    case True{}:
      Tk.rec(n, 0, n, 0, w, st)
    case False{}:
      st

def Tk.eof.s(+n: U32, +w: U32, st: TK) -> TK:
  match st:
    case TK{m0, cr0, +f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines}:
      Tk.eof.f(U32.is_gt(f, 0), n, w, TK{m0, cr0, f, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})

# the end of the input in the mode the last byte left
def Tk.eof(+n: U32, +w: U32, r: TK & Md) -> TK:
  (st, m) = r
  match m:
    case MS{}:
      Tk.eof.s(n, w, st)
    case MB{}:
      Tk.bend(n, w, 0, Tk.binfo(st))
    case ME{}:
      Tk.rej(st)
    case MQ{}:
      Tk.qend(n, w, Tk.qinfo(st))
    case MQC{}:
      Tk.qend(n, w, Tk.qinfo(st))

def Tk.end(fin: Bool, +n: U32, +w: U32, st: TK) -> TK:
  match fin:
    case True{}:
      Tk.eof(n, w, Tk.mget(st))
    case False{}:
      st

# ---- 3b. field access shared by the column loops -----------------------------------------------------

type SH is Type:
  SH{a: Array<U32>, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>}

type FR is Type:
  FR{sh: SH, s: U32, e: U32, qf: U32}

def Fd.k(a: Array<U32>, r1: Array<U32> & U32, r2: Array<U32> & U32, r3: Array<U32> & U32) -> FR:
  (fs, +s) = r1
  (fe, +e) = r2
  (fq, +qf) = r3
  FR{SH{a, fs, fe, fq}, s, e, qf}

def Fd.get(+slot: U32, sh: SH) -> FR:
  match sh:
    case SH{a, fs, fe, fq}:
      Fd.k(a, Array.get(U32, fs, slot), Array.get(U32, fe, slot), Array.get(U32, fq, slot))

# trimming (Char.is_space: 9..13 and 32, ASCII only, so bytes trim as code points do)
type TR is Type:
  TR{a: Array<U32>, s: U32, e: U32, go: Bool}

def Tr.l.chk(+s: U32, +e: U32, r: Array<U32> & U32) -> TR:
  (a, +b) = r
  TR{a, s, e, Bool.and(U32.is_lt(s, e), is_sp(b))}

def Tr.l(f: Nat, st: TR) -> TR:
  match f st:
    case _ TR{a, s, e, False{}}:
      TR{a, s, e, False{}}
    case 0n other:
      other
    case 1n+p TR{a, +s, +e, True{}}:
      Tr.l(p, Tr.l.chk(U32.inc(s), e, Bt.at(a, U32.inc(s))))

def Tr.r.chk(+s: U32, +e: U32, r: Array<U32> & U32) -> TR:
  (a, +b) = r
  TR{a, s, e, Bool.and(U32.is_lt(s, e), is_sp(b))}

def Tr.r(f: Nat, st: TR) -> TR:
  match f st:
    case _ TR{a, s, e, False{}}:
      TR{a, s, e, False{}}
    case 0n other:
      other
    case 1n+p TR{a, +s, +e, True{}}:
      Tr.r(p, Tr.r.chk(s, U32.sub(e, 1), Bt.at(a, U32.sub(e, 2))))

def Tr.both.k(st: TR) -> TR:
  match st:
    case TR{a, +s, +e, go}:
      Tr.r(U32.to_nat(U32.sub(e, s)), Tr.r.chk(s, e, Bt.at(a, U32.sub(e, 1))))

def Tr.both(+s: U32, +e: U32, a: Array<U32>) -> TR:
  Tr.both.k(Tr.l(U32.to_nat(U32.sub(e, s)), Tr.l.chk(s, e, Bt.at(a, s))))

# ---- UTF-8 decoding, byte for byte the runtime's io_str (invalid -> U+FFFD, the bad byte read
# again); esc: a doubled quote is one quote

type UD is Type:
  UD{a: Array<U32>, p: U32, need: U32, lo: U32, hi: U32, c: U32, out: String, done: Bool}

def Ud.lead(a: Array<U32>, +b: U32, +p: U32, out: String) -> UD:
  +need = Ln.sel(U32.is_lt(b, 224), 1, Ln.sel(U32.is_lt(b, 240), 2, 3))
  UD{a, U32.inc(p), need, Ln.sel(U32.is_eq(b, 224), 160, Ln.sel(U32.is_eq(b, 240), 144, 128)), Ln.sel(U32.is_eq(b, 237), 159, Ln.sel(U32.is_eq(b, 244), 143, 191)), U32.and(b, Ln.sel(U32.is_eq(need, 1), 31, Ln.sel(U32.is_eq(need, 2), 15, 7))), out, False{}}

def Ud.ascii(a: Array<U32>, +b: U32, +p: U32, +esc: U32, out: String) -> UD:
  UD{a, U32.add(p, Ln.sel(Bool.and(U32.is_eq(esc, 1), U32.is_eq(b, 34)), 2, 1)), 0, 128, 191, 0, SCon{Chr{b}, out}, False{}}

def Ud.hi(bad: Bool, a: Array<U32>, +b: U32, +p: U32, out: String) -> UD:
  match bad:
    case True{}:
      UD{a, U32.inc(p), 0, 128, 191, 0, SCon{Chr{65533}, out}, False{}}
    case False{}:
      Ud.lead(a, b, p, out)

def Ud.start.b(ascii: Bool, a: Array<U32>, +b: U32, +p: U32, +esc: U32, out: String) -> UD:
  match ascii:
    case True{}:
      Ud.ascii(a, b, p, esc, out)
    case False{}:
      Ud.hi(Bool.or(U32.is_lt(b, 194), U32.is_gt(b, 244)), a, b, p, out)

def Ud.start(end: Bool, a: Array<U32>, +b: U32, +p: U32, +esc: U32, out: String) -> UD:
  match end:
    case True{}:
      UD{a, p, 0, 128, 191, 0, out, True{}}
    case False{}:
      Ud.start.b(U32.is_lt(b, 128), a, b, p, esc, out)

def Ud.cont.k(last: Bool, a: Array<U32>, +p: U32, +n2: U32, +c2: U32, out: String) -> UD:
  match last:
    case True{}:
      UD{a, U32.inc(p), 0, 128, 191, 0, SCon{Chr{c2}, out}, False{}}
    case False{}:
      UD{a, U32.inc(p), n2, 128, 191, c2, out, False{}}

def Ud.cont(bad: Bool, a: Array<U32>, +b: U32, +p: U32, +need: U32, +c: U32, out: String) -> UD:
  match bad:
    case True{}:
      UD{a, p, 0, 128, 191, 0, SCon{Chr{65533}, out}, False{}}
    case False{}:
      Ud.cont.k(U32.is_eq(need, 1), a, p, U32.sub(need, 1), U32.add(U32.mul(c, 64), U32.and(b, 63)), out)

def Ud.step.m(cont: Bool, a: Array<U32>, +b: U32, +e: U32, +esc: U32, +p: U32, +need: U32, +lo: U32, +hi: U32, +c: U32, out: String) -> UD:
  match cont:
    case True{}:
      Ud.cont(Bool.or(U32.is_lt(b, lo), U32.is_gt(b, hi)), a, b, p, need, c, out)
    case False{}:
      Ud.start(U32.is_ge(p, e), a, b, p, esc, out)

def Ud.step.k(+e: U32, +esc: U32, +p: U32, +need: U32, +lo: U32, +hi: U32, +c: U32, out: String, r: Array<U32> & U32) -> UD:
  (a, +b) = r
  Ud.step.m(U32.is_gt(need, 0), a, b, e, esc, p, need, lo, hi, c, out)

def Ud.at.k(inb: Bool, a: Array<U32>, +p: U32) -> Array<U32> & U32:
  match inb:
    case True{}:
      Bt.at(a, p)
    case False{}:
      (a, 256)

def Ud.at(+e: U32, a: Array<U32>, +p: U32) -> Array<U32> & U32:
  Ud.at.k(U32.is_lt(p, e), a, p)

def Ud.go(f: Nat, +e: U32, +esc: U32, st: UD) -> Array<U32> & String:
  match f st:
    case _ UD{a, p, need, lo, hi, c, out, True{}}:
      (a, String.reverse(out))
    case 0n UD{a, p, need, lo, hi, c, out, done}:
      (a, String.reverse(out))
    case 1n+q UD{a, +p, +need, +lo, +hi, +c, out, False{}}:
      Ud.go(q, e, esc, Ud.step.k(e, esc, p, need, lo, hi, c, out, Ud.at(e, a, p)))

# the content [s, e) as a String
def Ud.str(+s: U32, +e: U32, +esc: U32, a: Array<U32>) -> Array<U32> & String:
  Ud.go(U32.to_nat(U32.add(U32.mul(U32.sub(e, s), 2), 2)), e, esc, UD{a, s, 0, 128, 191, 0, SNil{}, False{}})

# ---- 3c. typed field parsers ---------------------------------------------------------------------------

# a parsed field: value, state 0 null / 1 ok / 2 bad
type PV is Type:
  PV{a: Array<U32>, x: U32, st: U32}

type PF is Type:
  PF{a: Array<U32>, x: F32, st: U32}

# U32.read on [p, e): acc * 10 + (b - 48), ok while acc' / 10 == acc (U32.read's own test, so any
# non-digit byte fails as its code point does)
type PU is Type:
  PU{a: Array<U32>, p: U32, acc: U32, ok: Bool}

def Pu.step(+p: U32, +acc: U32, r: Array<U32> & U32) -> PU:
  (a, +b) = r
  +n2 = U32.add(U32.mul(acc, 10), U32.sub(b, 48))
  PU{a, U32.inc(p), n2, U32.is_eq(U32.div(n2, 10), acc)}

def Pu.go(f: Nat, st: PU) -> PV:
  match f st:
    case _ PU{a, p, acc, False{}}:
      PV{a, 0, 2}
    case 0n PU{a, p, acc, ok}:
      PV{a, acc, 1}
    case 1n+q PU{a, +p, +acc, True{}}:
      Pu.go(q, Pu.step(p, acc, Bt.at(a, p)))

def Pu.field.k(empty: Bool, +s: U32, +e: U32, a: Array<U32>) -> PV:
  match empty:
    case True{}:
      PV{a, 0, 0}
    case False{}:
      Pu.go(U32.to_nat(U32.sub(e, s)), PU{a, s, 0, True{}})

def Pu.field(tr: TR) -> PV:
  match tr:
    case TR{a, +s, +e, go}:
      Pu.field.k(U32.is_eq(s, e), s, e, a)

# i32 = I32.read of the trimmed text: an optional '-', then U32.read of the rest (digits only; an
# empty rest is bad, not null), then the bounds: a negative magnitude is at most 2^31, a positive
# one below it. A negative value is stored as two's complement bits; a bad cell holds 0.
def Pi.fin(+neg: Bool, pv: PV) -> PV:
  match pv:
    case PV{a, +x, +st}:
      +inr = Ln.sel(neg, Bool.to_u32(U32.is_le(x, 2147483648)), Bool.to_u32(U32.is_lt(x, 2147483648)))
      +okb = Bool.and(U32.is_eq(st, 1), U32.is_eq(inr, 1))
      PV{a, Ln.sel(okb, Ln.sel(neg, U32.sub(0, x), x), 0), Ln.sel(okb, 1, 2)}

# the rest [s, e) after the sign
def Pi.rest(+neg: Bool, +s: U32, +e: U32, a: Array<U32>, empty: Bool) -> PV:
  match empty:
    case True{}:
      PV{a, 0, 2}
    case False{}:
      Pi.fin(neg, Pu.go(U32.to_nat(U32.sub(e, s)), PU{a, s, 0, True{}}))

def Pi.sign(+s: U32, +e: U32, r: Array<U32> & U32) -> PV:
  (a, +b0) = r
  +neg = U32.is_eq(b0, 45)
  +s2 = U32.add(s, Bool.to_u32(neg))
  Pi.rest(neg, s2, e, a, U32.is_eq(s2, e))

def Pi.field.k(empty: Bool, +s: U32, +e: U32, a: Array<U32>) -> PV:
  match empty:
    case True{}:
      PV{a, 0, 0}
    case False{}:
      Pi.sign(s, e, Bt.at(a, s))

def Pi.field(tr: TR) -> PV:
  match tr:
    case TR{a, +s, +e, go}:
      Pi.field.k(U32.is_eq(s, e), s, e, a)

# bool: true / True -> 1, false / False -> 0 (trimmed, exactly)
type B5 is Type:
  B5{a: Array<U32>, b0: U32, b1: U32, b2: U32, b3: U32, b4: U32}

def Pb.k4(+b0: U32, +b1: U32, +b2: U32, +b3: U32, r4: Array<U32> & U32) -> B5:
  (a, +b4) = r4
  B5{a, b0, b1, b2, b3, b4}

def Pb.k3(+s: U32, +b0: U32, +b1: U32, +b2: U32, r3: Array<U32> & U32) -> B5:
  (a, +b3) = r3
  Pb.k4(b0, b1, b2, b3, Bt.at(a, U32.add(s, 4)))

def Pb.k2(+s: U32, +b0: U32, +b1: U32, r2: Array<U32> & U32) -> B5:
  (a, +b2) = r2
  Pb.k3(s, b0, b1, b2, Bt.at(a, U32.add(s, 3)))

def Pb.k1(+s: U32, +b0: U32, r1: Array<U32> & U32) -> B5:
  (a, +b1) = r1
  Pb.k2(s, b0, b1, Bt.at(a, U32.add(s, 2)))

def Pb.k0(+s: U32, r0: Array<U32> & U32) -> B5:
  (a, +b0) = r0
  Pb.k1(s, b0, Bt.at(a, U32.inc(s)))

def Pb.dec(+n: U32, b5: B5) -> PV:
  match b5:
    case B5{a, +b0, +b1, +b2, +b3, +b4}:
      +t = Bool.and(U32.is_eq(n, 4), Bool.and(Bool.or(U32.is_eq(b0, 116), U32.is_eq(b0, 84)), Bool.and(U32.is_eq(b1, 114), Bool.and(U32.is_eq(b2, 117), U32.is_eq(b3, 101)))))
      +f = Bool.and(U32.is_eq(n, 5), Bool.and(Bool.or(U32.is_eq(b0, 102), U32.is_eq(b0, 70)), Bool.and(U32.is_eq(b1, 97), Bool.and(U32.is_eq(b2, 108), Bool.and(U32.is_eq(b3, 115), U32.is_eq(b4, 101))))))
      PV{a, Bool.to_u32(t), Ln.sel(Bool.or(t, f), 1, 2)}

def Pb.field.k(empty: Bool, +n: U32, +s: U32, a: Array<U32>) -> PV:
  match empty:
    case True{}:
      PV{a, 0, 0}
    case False{}:
      Pb.dec(n, Pb.k0(s, Bt.at(a, s)))

def Pb.field(tr: TR) -> PV:
  match tr:
    case TR{a, +s, +e, go}:
      Pb.field.k(U32.is_eq(s, e), U32.sub(e, s), s, a)

# f32: the exact fast path [+-]digits[.digits] with mantissa M <= 2^24 and at most 10 fraction
# digits is ONE correctly rounded f32 division of two exact f32 values, which is the value strtof
# (F32.read) answers; anything else goes through F32.read on the decoded text (slow path)
type FS is Type:
  FS{a: Array<U32>, p: U32, m: U32, fd: U32, nd: U32, dot: U32, ok: Bool}

def Pf.step.k(+p: U32, +m: U32, +fd: U32, +nd: U32, +dot: U32, +ok: Bool, r: Array<U32> & U32) -> FS:
  (a, +b) = r
  +dig = Bool.and(U32.is_ge(b, 48), U32.is_le(b, 57))
  +isdot = U32.is_eq(b, 46)
  +dot2 = U32.add(dot, Bool.to_u32(isdot))
  FS{a, U32.inc(p), Ln.sel(dig, Ln.sel(U32.is_gt(m, 1677721), 16777217, U32.add(U32.mul(m, 10), U32.sub(b, 48))), m), U32.add(fd, Bool.to_u32(Bool.and(dig, U32.is_eq(dot, 1)))), U32.add(nd, Bool.to_u32(dig)), dot2, Bool.and(ok, Bool.and(Bool.or(dig, isdot), U32.is_le(dot2, 1)))}

def Pf.step(st: FS) -> FS:
  match st:
    case FS{a, +p, +m, +fd, +nd, +dot, +ok}:
      Pf.step.k(p, m, fd, nd, dot, ok, Bt.at(a, p))

def Pf.go(f: Nat, st: FS) -> FS:
  match f:
    case 0n:
      st
    case 1n+q:
      Pf.go(q, Pf.step(st))

def P10.go(f: Nat, x: F32) -> F32:
  match f:
    case 0n:
      x
    case 1n+p:
      P10.go(p, F32.mul(x, 10.0))

def Pf.neg(neg: Bool, x: F32) -> F32:
  match neg:
    case True{}:
      F32.neg(x)
    case False{}:
      x

def Pf.val(+neg: Bool, +m: U32, +fd: U32) -> F32:
  Pf.neg(neg, F32.div(U32.to_f32(m), P10.go(U32.to_nat(fd), 1.0)))

def Pf.slow.r(a: Array<U32>, m: Maybe<&2, F32>) -> PF:
  match m:
    case Some{x}:
      PF{a, x, 1}
    case None{}:
      PF{a, 0.0, 2}

def Pf.slow.k(r: Array<U32> & String) -> PF:
  (a, s) = r
  Pf.slow.r(a, F32.read(s))

def Pf.slow(+s: U32, +e: U32, +esc: U32, a: Array<U32>) -> PF:
  Pf.slow.k(Ud.str(s, e, esc, a))

def Pf.fin.k(fast: Bool, +neg: Bool, +m: U32, +fd: U32, +s: U32, +e: U32, +esc: U32, a: Array<U32>) -> PF:
  match fast:
    case True{}:
      PF{a, Pf.val(neg, m, fd), 1}
    case False{}:
      Pf.slow(s, e, esc, a)

def Pf.fin(+neg: Bool, +s: U32, +e: U32, +esc: U32, st: FS) -> PF:
  match st:
    case FS{a, p, +m, +fd, +nd, dot, +ok}:
      Pf.fin.k(Bool.and(ok, Bool.and(U32.is_gt(nd, 0), Bool.and(U32.is_le(m, 16777216), Bool.and(U32.is_le(fd, 10), U32.is_eq(esc, 0))))), neg, m, fd, s, e, esc, a)

def Pf.sign(+s: U32, +e: U32, +esc: U32, r: Array<U32> & U32) -> PF:
  (a, +b0) = r
  +neg = U32.is_eq(b0, 45)
  +sg = Bool.or(neg, U32.is_eq(b0, 43))
  +s2 = U32.add(s, Bool.to_u32(sg))
  Pf.fin(neg, s, e, esc, Pf.go(U32.to_nat(U32.sub(e, s2)), FS{a, s2, 0, 0, 0, 0, True{}}))

def Pf.field.k(empty: Bool, +s: U32, +e: U32, +esc: U32, a: Array<U32>) -> PF:
  match empty:
    case True{}:
      PF{a, 0.0, 0}
    case False{}:
      Pf.sign(s, e, esc, Bt.at(a, s))

def Pf.field(+esc: U32, tr: TR) -> PF:
  match tr:
    case TR{a, +s, +e, go}:
      Pf.field.k(U32.is_eq(s, e), s, e, esc, a)

# ---- the word / f32 column loops ---------------------------------------------------------------

type LW is Type:
  LW{sh: SH, a: Array<U32>, v: Array<U32>, nulls: U32, bad: U32}

type LF is Type:
  LF{sh: SH, a: Array<F32>, v: Array<U32>, nulls: U32, bad: U32}

def Lw.put(+r: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, out: Array<U32>, v: Array<U32>, +nulls: U32, +bad: U32, pv: PV) -> LW:
  match pv:
    case PV{a, +x, +st}:
      LW{SH{a, fs, fe, fq}, Array.set(U32, out, r, x), Array.set(U32, v, r, Bool.to_u32(U32.is_eq(st, 1))), U32.add(nulls, Bool.to_u32(U32.is_ne(st, 1))), Ln.sel(Bool.and(U32.is_eq(st, 2), U32.is_eq(bad, 0)), U32.inc(r), bad)}

def Lw.parse(t: Ty, tr: TR) -> PV:
  match t:
    case TyB{}:
      Pb.field(tr)
    case TyI{}:
      Pi.field(tr)
    case _:
      Pu.field(tr)

# u32 (TyU), i32 (TyI) or bool (TyB)
def Lw.cell(+t: Ty, +r: U32, out: Array<U32>, v: Array<U32>, +nulls: U32, +bad: U32, fr: FR) -> LW:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s, +e, qf}:
      Lw.put(r, fs, fe, fq, out, v, nulls, bad, Lw.parse(t, Tr.both(s, e, a)))

def Lw.go(f: Nat, +r: U32, +c: U32, +w: U32, +t: Ty, st: LW) -> LW:
  match f st:
    case 0n other:
      other
    case 1n+p LW{sh, out, v, +nulls, +bad}:
      Lw.go(p, U32.inc(r), c, w, t, Lw.cell(t, r, out, v, nulls, bad, Fd.get(U32.add(U32.mul(r, w), c), sh)))

def Lf.put(+r: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, out: Array<F32>, v: Array<U32>, +nulls: U32, +bad: U32, pv: PF) -> LF:
  match pv:
    case PF{a, x, +st}:
      LF{SH{a, fs, fe, fq}, Array.set(F32, out, r, x), Array.set(U32, v, r, Bool.to_u32(U32.is_eq(st, 1))), U32.add(nulls, Bool.to_u32(U32.is_ne(st, 1))), Ln.sel(Bool.and(U32.is_eq(st, 2), U32.is_eq(bad, 0)), U32.inc(r), bad)}

def Lf.cell(+r: U32, out: Array<F32>, v: Array<U32>, +nulls: U32, +bad: U32, fr: FR) -> LF:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s, +e, +qf}:
      Lf.put(r, fs, fe, fq, out, v, nulls, bad, Pf.field(U32.div(qf, 2), Tr.both(s, e, a)))

def Lf.go(f: Nat, +r: U32, +c: U32, +w: U32, st: LF) -> LF:
  match f st:
    case 0n other:
      other
    case 1n+p LF{sh, out, v, +nulls, +bad}:
      Lf.go(p, U32.inc(r), c, w, Lf.cell(r, out, v, nulls, bad, Fd.get(U32.add(U32.mul(r, w), c), sh)))

# ---- the Str column loop: a per-region coder keyed on byte ranges (FNV-1a over the content bytes,
# a doubled quote read as one; a hash hit compares the bytes of the representative row) ------------

type HB is Type:
  HB{a: Array<U32>, p: U32, h: U32, more: Bool}

def Hb.step.k(+p: U32, +e: U32, +esc: U32, +h: U32, r: Array<U32> & U32) -> HB:
  (a, +b) = r
  +p2 = U32.add(p, Ln.sel(Bool.and(U32.is_eq(esc, 1), U32.is_eq(b, 34)), 2, 1))
  HB{a, p2, U32.mul(U32.xor(h, b), 16777619), U32.is_lt(p2, e)}

def Hb.go(f: Nat, +e: U32, +esc: U32, st: HB) -> Array<U32> & U32:
  match f st:
    case _ HB{a, p, h, False{}}:
      (a, h)
    case 0n HB{a, p, h, more}:
      (a, h)
    case 1n+q HB{a, +p, +h, True{}}:
      Hb.go(q, e, esc, Hb.step.k(p, e, esc, h, Bt.at(a, p)))

# bytes [p, pe) (esc1) == bytes [q, qe) (esc2), read as content
type EQS is Type:
  EQS{a: Array<U32>, p: U32, q: U32, stop: Bool, same: Bool}

def Eb.look.y(+p: U32, +q: U32, +x: U32, +esc1: U32, +esc2: U32, r: Array<U32> & U32) -> EQS:
  (a, +y) = r
  EQS{a, U32.add(p, Ln.sel(Bool.and(U32.is_eq(esc1, 1), U32.is_eq(x, 34)), 2, 1)), U32.add(q, Ln.sel(Bool.and(U32.is_eq(esc2, 1), U32.is_eq(y, 34)), 2, 1)), U32.is_ne(x, y), U32.is_eq(x, y)}

def Eb.look.x(+p: U32, +q: U32, +esc1: U32, +esc2: U32, r: Array<U32> & U32) -> EQS:
  (a, +x) = r
  Eb.look.y(p, q, x, esc1, esc2, Bt.at(a, q))

def Eb.look.k(end: Bool, +both: Bool, +p: U32, +q: U32, +esc1: U32, +esc2: U32, a: Array<U32>) -> EQS:
  match end:
    case True{}:
      EQS{a, p, q, True{}, both}
    case False{}:
      Eb.look.x(p, q, esc1, esc2, Bt.at(a, p))

def Eb.look(+p: U32, +pe: U32, +q: U32, +qe: U32, +esc1: U32, +esc2: U32, a: Array<U32>) -> EQS:
  +ep = U32.is_ge(p, pe)
  +eq = U32.is_ge(q, qe)
  Eb.look.k(Bool.or(ep, eq), Bool.and(ep, eq), p, q, esc1, esc2, a)

def Eb.go(f: Nat, +pe: U32, +qe: U32, +esc1: U32, +esc2: U32, st: EQS) -> Array<U32> & Bool:
  match f st:
    case _ EQS{a, p, q, True{}, same}:
      (a, same)
    case 0n EQS{a, p, q, stop, same}:
      (a, same)
    case 1n+g EQS{a, +p, +q, False{}, same}:
      Eb.go(g, pe, qe, esc1, esc2, Eb.look(p, pe, q, qe, esc1, esc2, a))

# the coder's state: the shared arrays, the table, codes, validity, first rows of the entries
type LS is Type:
  LS{sh: SH, next: U32, nulls: U32, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, c: Array<U32>, v: Array<U32>, fr: Array<U32>}

type SK is Type:
  SK{sh: SH, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, more: Bool, emp: Bool, id: U32, j: U32}

def Sc.cmp.z(fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, r: Array<U32> & Bool) -> SH & Bool:
  (a, same) = r
  (SH{a, fs, fe, fq}, same)

# compare the current content [s, e) with the representative row's (on a hash hit)
def Sc.cmp.k(+s: U32, +e: U32, +esc: U32, fr: FR) -> SH & Bool:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s2, +e2, +q2}:
      Sc.cmp.z(fs, fe, fq, Eb.go(U32.to_nat(U32.add(U32.sub(e, s), 2)), e2, e, U32.div(q2, 2), esc, Eb.look(s2, e2, s, e, U32.div(q2, 2), esc, a)))

def Sc.cmp(hit: Bool, +rs: U32, +s: U32, +e: U32, +esc: U32, sh: SH) -> SH & Bool:
  match hit:
    case True{}:
      Sc.cmp.k(s, e, esc, Fd.get(rs, sh))
    case False{}:
      (sh, False{})

def Sc.look.d(+em: Bool, +j: U32, hs: Array<U32>, rp: Array<U32>, r3: Array<U32> & U32, rs: SH & Bool) -> SK:
  (ids, +id) = r3
  (sh, same) = rs
  SK{sh, hs, rp, ids, Bool.and(Bool.not(em), Bool.not(same)), em, id, j}

def Sc.look.c(+h: U32, +j: U32, +w: U32, +c: U32, +s: U32, +e: U32, +esc: U32, sh: SH, ids: Array<U32>, r1: Array<U32> & U32, r2: Array<U32> & U32) -> SK:
  (hs, +x) = r1
  (rp, +rr) = r2
  +em = U32.is_eq(rr, 0)
  Sc.look.d(em, j, hs, rp, Array.get(U32, ids, j), Sc.cmp(Bool.and(Bool.not(em), U32.is_eq(x, h)), U32.add(U32.mul(U32.sub(rr, 1), w), c), s, e, esc, sh))

def Sc.look(+h: U32, +j: U32, +w: U32, +c: U32, +s: U32, +e: U32, +esc: U32, sh: SH, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>) -> SK:
  Sc.look.c(h, j, w, c, s, e, esc, sh, ids, Array.get(U32, hs, j), Array.get(U32, rp, j))

def Sc.seek(f: Nat, sk: SK, +h: U32, +w: U32, +c: U32, +s: U32, +e: U32, +esc: U32, +mask: U32) -> SK:
  match f sk:
    case 0n other:
      other
    case _ SK{sh, hs, rp, ids, False{}, em, id, j}:
      SK{sh, hs, rp, ids, False{}, em, id, j}
    case 1n+p SK{sh, hs, rp, ids, True{}, em, id, +j}:
      Sc.seek(p, Sc.look(h, U32.and(U32.inc(j), mask), w, c, s, e, esc, sh, hs, rp, ids), h, w, c, s, e, esc, mask)

def Sc.put(+h: U32, +r: U32, +ok: U32, +next: U32, +nulls: U32, out: Array<U32>, v: Array<U32>, fr: Array<U32>, sk: SK) -> LS:
  match sk:
    case SK{sh, hs, rp, ids, more, True{}, id, +j}:
      LS{sh, U32.inc(next), nulls, Array.set(U32, hs, j, h), Array.set(U32, rp, j, U32.inc(r)), Array.set(U32, ids, j, next), Array.set(U32, out, r, next), Array.set(U32, v, r, ok), Array.set(U32, fr, next, r)}
    case SK{sh, hs, rp, ids, more, False{}, +id, j}:
      LS{sh, next, nulls, hs, rp, ids, Array.set(U32, out, r, id), Array.set(U32, v, r, ok), fr}

def Sc.slot(+h: U32, +b: Nat) -> U32:
  U32.shrn(U32.mul(h, 2654435769), Nat.sub(32n, b))

def Sc.cell.h(+r: U32, +w: U32, +c: U32, +b: Nat, +mask: U32, +fuel: Nat, +s: U32, +e: U32, +qf: U32, +next: U32, +nulls: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, v: Array<U32>, frr: Array<U32>, rh: Array<U32> & U32) -> LS:
  (a, +h) = rh
  +esc = U32.div(qf, 2)
  +ok = Bool.to_u32(Bool.or(U32.is_ne(qf, 0), U32.is_lt(s, e)))
  Sc.put(h, r, ok, next, U32.add(nulls, U32.sub(1, ok)), out, v, frr, Sc.seek(fuel, Sc.look(h, Sc.slot(h, b), w, c, s, e, esc, SH{a, fs, fe, fq}, hs, rp, ids), h, w, c, s, e, esc, mask))

def Sc.cell(+r: U32, +w: U32, +c: U32, +b: Nat, +mask: U32, +fuel: Nat, +next: U32, +nulls: U32, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, v: Array<U32>, frr: Array<U32>, fr: FR) -> LS:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s, +e, +qf}:
      Sc.cell.h(r, w, c, b, mask, fuel, s, e, qf, next, nulls, fs, fe, fq, hs, rp, ids, out, v, frr, Hb.go(U32.to_nat(U32.add(U32.sub(e, s), 1)), e, U32.div(qf, 2), HB{a, s, 2166136261, U32.is_lt(s, e)}))

def Sc.go(f: Nat, +r: U32, +c: U32, +w: U32, +b: Nat, +mask: U32, +fuel: Nat, st: LS) -> LS:
  match f st:
    case 0n other:
      other
    case 1n+p LS{sh, +next, +nulls, hs, rp, ids, out, v, frr}:
      Sc.go(p, U32.inc(r), c, w, b, mask, fuel, Sc.cell(r, w, c, b, mask, fuel, next, nulls, hs, rp, ids, out, v, frr, Fd.get(U32.add(U32.mul(r, w), c), sh)))

# the region's entries in local id order: the content of each entry's first row, decoded
type EN is Type:
  EN{sh: SH, fr: Array<U32>, ents: Array<String>}

def En.put(+id: U32, fr: Array<U32>, ents: Array<String>, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, r: Array<U32> & String) -> EN:
  (a, s) = r
  EN{SH{a, fs, fe, fq}, fr, Array.set(String, ents, id, s)}

def En.dec(+id: U32, fr: Array<U32>, ents: Array<String>, x: FR) -> EN:
  match x:
    case FR{SH{a, fs, fe, fq}, +s, +e, +qf}:
      En.put(id, fr, ents, fs, fe, fq, Ud.str(s, e, U32.div(qf, 2), a))

def En.row(+id: U32, +w: U32, +c: U32, sh: SH, ents: Array<String>, r: Array<U32> & U32) -> EN:
  (fr, +row) = r
  En.dec(id, fr, ents, Fd.get(U32.add(U32.mul(row, w), c), sh))

def En.go(f: Nat, +id: U32, +w: U32, +c: U32, st: EN) -> EN:
  match f st:
    case 0n other:
      other
    case 1n+p EN{sh, fr, ents}:
      En.go(p, U32.inc(id), w, c, En.row(id, w, c, sh, ents, Array.get(U32, fr, id)))

# ---- the raw string column loop: one decoded String per row ---------------------------------------

type LR is Type:
  LR{sh: SH, a: Array<String>, v: Array<U32>, nulls: U32}

def Rw.put(+r: U32, +ok: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, out: Array<String>, v: Array<U32>, +nulls: U32, rs: Array<U32> & String) -> LR:
  (a, s) = rs
  LR{SH{a, fs, fe, fq}, Array.set(String, out, r, s), Array.set(U32, v, r, ok), U32.add(nulls, U32.sub(1, ok))}

def Rw.cell(+r: U32, out: Array<String>, v: Array<U32>, +nulls: U32, fr: FR) -> LR:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s, +e, +qf}:
      Rw.put(r, Bool.to_u32(Bool.or(U32.is_ne(qf, 0), U32.is_lt(s, e))), fs, fe, fq, out, v, nulls, Ud.str(s, e, U32.div(qf, 2), a))

def Rw.go(f: Nat, +r: U32, +c: U32, +w: U32, st: LR) -> LR:
  match f st:
    case 0n other:
      other
    case 1n+p LR{sh, out, v, +nulls}:
      Rw.go(p, U32.inc(r), c, w, Rw.cell(r, out, v, nulls, Fd.get(U32.add(U32.mul(r, w), c), sh)))

# ---- a column of a region ----------------------------------------------------------------------------

# one column's part of a region (see the header comment)
type CO is Type:
  OW{a: Array<U32>, v: Array<U32>, nulls: U32, bad: U32, bl: U32, bt: String}
  OF{a: Array<F32>, v: Array<U32>, nulls: U32, bad: U32, bl: U32, bt: String}
  OS{c: Array<U32>, v: Array<U32>, nulls: U32, k: U32, ents: Array<String>, fr: Array<U32>}
  OR{a: Array<String>, v: Array<U32>, nulls: U32}

# a column finished: the shared arrays and the lines come back with it
type FC is Type:
  FC{sh: SH, lines: Array<U32>, co: CO}

# the first bad cell's line (lines[row]) and text, or none: the shared arrays come back
type BL is Type:
  BL{sh: SH, lines: Array<U32>, bl: U32, bt: String}

def Bd.mk.l(sh: SH, bt: String, r: Array<U32> & U32) -> BL:
  (lines, +bl) = r
  BL{sh, lines, bl, bt}

def Bd.mk.t(lines: Array<U32>, +row: U32, r: SH & String) -> BL:
  (sh, bt) = r
  Bd.mk.l(sh, bt, Array.get(U32, lines, row))

def Bd.text.k(fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, r: Array<U32> & String) -> SH & String:
  (a, s) = r
  (SH{a, fs, fe, fq}, s)

def Bd.text.f(fr: FR) -> SH & String:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s, +e, +qf}:
      Bd.text.k(fs, fe, fq, Ud.str(s, e, U32.div(qf, 2), a))

# the field at (row, column c)
def Bd.text(+slot: U32, sh: SH) -> SH & String:
  Bd.text.f(Fd.get(slot, sh))

def Bd.pick(has: Bool, +bad: U32, +c: U32, +w: U32, sh: SH, lines: Array<U32>) -> BL:
  match has:
    case True{}:
      Bd.mk.t(lines, U32.sub(bad, 1), Bd.text(U32.add(U32.mul(U32.sub(bad, 1), w), c), sh))
    case False{}:
      BL{sh, lines, 0, ""}

# a region's validity when it has no null: one slot holding 1 (every reader of a part's validity reads
# it per row with wrapping indices, so each row still reads 1), and the 2^d array is freed as the lane
# finishes, for the next lane to reuse, instead of living until the combine (bench/tpch: 13 columns
# x ~430 regions of lineitem, ~90 MB that was all ones)
def Col.vtrim(+nulls: U32, v: Array<U32>) -> Array<U32>:
  Bool.pick(Array<U32>, U32.is_zero(nulls), Array.new(U32, 0n, 1), v)

def Col.w.fin2(a: Array<U32>, v: Array<U32>, +nulls: U32, +bad: U32, bl: BL) -> FC:
  match bl:
    case BL{sh, lines, +l, bt}:
      FC{sh, lines, OW{a, Col.vtrim(nulls, v), nulls, bad, l, bt}}

def Col.w.fin(+c: U32, +w: U32, lines: Array<U32>, lw: LW) -> FC:
  match lw:
    case LW{sh, a, v, +nulls, +bad}:
      Col.w.fin2(a, v, nulls, bad, Bd.pick(U32.is_ne(bad, 0), bad, c, w, sh, lines))

def Col.f.fin2(a: Array<F32>, v: Array<U32>, +nulls: U32, +bad: U32, bl: BL) -> FC:
  match bl:
    case BL{sh, lines, +l, bt}:
      FC{sh, lines, OF{a, Col.vtrim(nulls, v), nulls, bad, l, bt}}

def Col.f.fin(+c: U32, +w: U32, lines: Array<U32>, lf: LF) -> FC:
  match lf:
    case LF{sh, a, v, +nulls, +bad}:
      Col.f.fin2(a, v, nulls, bad, Bd.pick(U32.is_ne(bad, 0), bad, c, w, sh, lines))

def Col.r.fin(lines: Array<U32>, lr: LR) -> FC:
  match lr:
    case LR{sh, a, v, +nulls}:
      FC{sh, lines, OR{a, Col.vtrim(nulls, v), nulls}}

def Col.s.fin3(sh: SH, lines: Array<U32>, c: Array<U32>, v: Array<U32>, +nulls: U32, +k: U32, ents: Array<String>, fr: Array<U32>) -> FC:
  FC{sh, lines, OS{c, Col.vtrim(nulls, v), nulls, k, ents, fr}}

def Col.s.fin2(lines: Array<U32>, c: Array<U32>, v: Array<U32>, +nulls: U32, +k: U32, en: EN) -> FC:
  match en:
    case EN{sh, fr, ents}:
      Col.s.fin3(sh, lines, c, v, nulls, k, ents, fr)

def Col.s.fin(+c: U32, +w: U32, lines: Array<U32>, ls: LS) -> FC:
  match ls:
    case LS{sh, +k, nulls, hs, rp, ids, out, v, fr}:
      Col.s.fin2(lines, out, v, nulls, k, En.go(U32.to_nat(k), 0, w, c, EN{sh, fr, Array.new(String, K.Kernel.depth_for(U32.max(k, 1)), "")}))

def Col.s.new(+nr: U32, +d: Nat, +c: U32, +w: U32, lines: Array<U32>, sh: SH) -> FC:
  +b = K.Kernel.depth_for(U32.max(U32.add(nr, nr), 2))
  +size = U32.shln(1, b)
  Col.s.fin(c, w, lines, Sc.go(U32.to_nat(nr), 0, c, w, b, U32.sub(size, 1), U32.to_nat(size), LS{sh, 0, 0, Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, d, 0), Array.new(U32, d, 0), Array.new(U32, d, 0)}))

def Col.one.k(t: Ty, +nr: U32, +d: Nat, +c: U32, +w: U32, lines: Array<U32>, sh: SH) -> FC:
  match t:
    case TyU{}:
      Col.w.fin(c, w, lines, Lw.go(U32.to_nat(nr), 0, c, w, TyU{}, LW{sh, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, 0}))
    case TyI{}:
      Col.w.fin(c, w, lines, Lw.go(U32.to_nat(nr), 0, c, w, TyI{}, LW{sh, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, 0}))
    case TyB{}:
      Col.w.fin(c, w, lines, Lw.go(U32.to_nat(nr), 0, c, w, TyB{}, LW{sh, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, 0}))
    case TyF{}:
      Col.f.fin(c, w, lines, Lf.go(U32.to_nat(nr), 0, c, w, LF{sh, Array.new(F32, d, 0.0), Array.new(U32, d, 0), 0, 0}))
    case TyS{}:
      Col.s.new(nr, d, c, w, lines, sh)
    case TyR{}:
      Col.r.fin(lines, Rw.go(U32.to_nat(nr), 0, c, w, LR{sh, Array.new(String, d, ""), Array.new(U32, d, 0), 0}))
    case TyN{}:
      FC{sh, lines, OW{Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), 0, 0, 0, ""}}

def Col.one(t: Ty, +nr: U32, +c: U32, +w: U32, lines: Array<U32>, sh: SH) -> FC:
  Col.one.k(t, nr, K.Kernel.depth_for(U32.max(nr, 1)), c, w, lines, sh)

# the columns so far (newest first) with the shared arrays
type CS is Type:
  CS{sh: SH, lines: Array<U32>, acc: List<&1, CO>}

def Cols.push(acc: List<&1, CO>, fc: FC) -> CS:
  match fc:
    case FC{sh, lines, co}:
      CS{sh, lines, co <> acc}

def Cols.step(t: Ty, +nr: U32, +c: U32, +w: U32, st: CS) -> CS:
  match st:
    case CS{sh, lines, acc}:
      Cols.push(acc, Col.one(t, nr, c, w, lines, sh))

# every column of the region, in order
def Cols.go(ts: List<&2, Ty>, +nr: U32, +c: U32, +w: U32, st: CS) -> CS:
  match ts:
    case Nil{}:
      st
    case t <> tt:
      Cols.go(tt, nr, U32.inc(c), w, Cols.step(t, nr, c, w, st))

# ---- a lane: one region ------------------------------------------------------------------------------

# rows, rejected, the first ragged record's line (0: none) and width, the rows' lines, the columns
type LO is Type:
  LO{n: U32, rej: U32, rag: U32, rgn: U32, lines: Array<U32>, cols: List<&1, CO>}

def Ln.fin(+n: U32, +rej: U32, +rag: U32, +rgn: U32, cs: CS) -> LO:
  match cs:
    case CS{sh, lines, acc}:
      LO{n, rej, rag, rgn, lines, List.reverse(&1, CO, acc)}

# a rejected region: nothing else is meaningful
def Ln.rejected(+rag: U32, +rgn: U32, lines: Array<U32>) -> LO:
  LO{0, 1, rag, rgn, lines, Nil{}}

# a tokenized region (W6.3): kept rows, rejected, the first ragged record (line, width), the shared
# arrays (the region's bytes and every field's range and flags) and the kept rows' lines. The typed
# loops (Ln.cols) or the classification (Ln.cls) read it; Ln.lane is Ln.tok then Ln.cols.
type TO is Type:
  TO{n: U32, rej: U32, rag: U32, rgn: U32, sh: SH, lines: Array<U32>}

def Ln.cols.k(rejd: Bool, +ts: List<&2, Ty>, +w: U32, +nr: U32, +rag: U32, +rgn: U32, sh: SH, lines: Array<U32>) -> LO:
  match rejd:
    case True{}:
      Ln.rejected(rag, rgn, lines)
    case False{}:
      Ln.fin(nr, 0, rag, rgn, Cols.go(ts, nr, 0, w, CS{sh, lines, Nil{}}))

# the typed columns of a tokenized region (ts: one Ty per column, w of them)
def Ln.cols(+ts: List<&2, Ty>, +w: U32, to: TO) -> LO:
  match to:
    case TO{+nr, +rej, +rag, +rgn, sh, lines}:
      Ln.cols.k(U32.is_ne(rej, 0), ts, w, nr, rag, rgn, sh, lines)

def Ln.to(r: Array<U32> & TK) -> TO:
  (a, st) = r
  match st:
    case TK{m, cr, f, +nr, ln, rl, fs0, qe, esc, +rag, +rgn, +rej, fs, fe, fq, lines}:
      TO{nr, rej, rag, rgn, SH{a, fs, fe, fq}, lines}

def Ln.end(+fin: U32, +n: U32, +w: U32, r: Array<U32> & TK) -> Array<U32> & TK:
  (a, st) = r
  (a, Tk.end(U32.is_eq(fin, 1), n, w, st))

# The tokenizer over one region. rows <= min(nt + 1, n / w + 1) (a kept record has w fields: at least
# w - 1 separators and a terminator), plus one slot: a dropped record (blank, ragged) writes at the
# next free row without keeping it, so the arrays never wrap.
def Ln.tok(+w: U32, +sep: U32, rg: P.Rg) -> TO:
  match rg:
    case P.Rg{a, +n, off, +line0, +nt, lfs, +fin}:
      +cap = U32.add(U32.min(U32.inc(nt), U32.inc(U32.div(n, w))), 1)
      +df = K.Kernel.depth_for(U32.max(U32.mul(cap, w), 1))
      +dl = K.Kernel.depth_for(cap)
      Ln.to(Ln.end(fin, n, w, Tk.go2(U32.to_nat(U32.inc(n)), MS{}, Tk.nx(sep, n, 0, Array.get(U32, a, 0)), 0, 0, 0, U32.sub(line0, 1), line0, 0, 0, 0, 0, 0, 0, w, sep, n, Array.new(U32, df, 0), Array.new(U32, df, 0), Array.new(U32, df, 0), Array.new(U32, dl, 0))))

# The lane of one region: the tokenizer, then one typed loop per column.
def Ln.lane(+ts: List<&2, Ty>, +w: U32, +sep: U32, rg: P.Rg) -> LO:
  Ln.cols(ts, w, Ln.tok(w, sep, rg))

# ---- classification (W6.3: inference, DESIGN.md 17.4.5) ------------------------------------------------
# Per column of a tokenized region: the first local row + 1 (0: none) whose cell does NOT fit u32, i32,
# f32, bool (a cell empty after trimming is a null and fits every dtype), and the first row whose cell
# has text after trimming. The field rules are the typed loops' own parsers (Pu, Pi, Pf, Pb), i.e.
# v0.1's Csv.ok / Csv.has.c; the reader turns them into v0.1's Csv.pick over the first infer_rows
# rows with the regions' row offsets (src/csv.bend, Csv.v2.ci.*).
type CL is Data:
  CL{fu: U32, fi: U32, ff: U32, fb: U32, fv: U32}

# the loop state (private, single constructor: cold)
type LC is Type:
  LC{sh: SH, fu: U32, fi: U32, ff: U32, fb: U32, fv: U32}

def Lc.first(+hit: Bool, +r: U32, +x: U32) -> U32:
  Ln.sel(Bool.and(hit, U32.is_eq(x, 0)), U32.inc(r), x)

def Lc.put(+r: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, +fu: U32, +fi: U32, +ff: U32, +fb: U32, +fv: U32, +su: U32, +si: U32, +sf: U32, pv: PV) -> LC:
  match pv:
    case PV{a, x, +sb}:
      LC{SH{a, fs, fe, fq}, Lc.first(U32.is_eq(su, 2), r, fu), Lc.first(U32.is_eq(si, 2), r, fi), Lc.first(U32.is_eq(sf, 2), r, ff), Lc.first(U32.is_eq(sb, 2), r, fb), Lc.first(U32.is_ne(su, 0), r, fv)}

def Lc.f(+r: U32, +s: U32, +e: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, +fu: U32, +fi: U32, +ff: U32, +fb: U32, +fv: U32, +su: U32, +si: U32, pf: PF) -> LC:
  match pf:
    case PF{a, x, +sf}:
      Lc.put(r, fs, fe, fq, fu, fi, ff, fb, fv, su, si, sf, Pb.field(TR{a, s, e, False{}}))

def Lc.i(+r: U32, +s: U32, +e: U32, +esc: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, +fu: U32, +fi: U32, +ff: U32, +fb: U32, +fv: U32, +su: U32, pv: PV) -> LC:
  match pv:
    case PV{a, x, +si}:
      Lc.f(r, s, e, fs, fe, fq, fu, fi, ff, fb, fv, su, si, Pf.field(esc, TR{a, s, e, False{}}))

def Lc.u(+r: U32, +s: U32, +e: U32, +esc: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, +fu: U32, +fi: U32, +ff: U32, +fb: U32, +fv: U32, pv: PV) -> LC:
  match pv:
    case PV{a, x, +su}:
      Lc.i(r, s, e, esc, fs, fe, fq, fu, fi, ff, fb, fv, su, Pi.field(TR{a, s, e, False{}}))

# the trimmed range of the cell: u32, then i32, f32, bool on it
def Lc.t(+r: U32, +esc: U32, fs: Array<U32>, fe: Array<U32>, fq: Array<U32>, +fu: U32, +fi: U32, +ff: U32, +fb: U32, +fv: U32, tr: TR) -> LC:
  match tr:
    case TR{a, +s, +e, go}:
      Lc.u(r, s, e, esc, fs, fe, fq, fu, fi, ff, fb, fv, Pu.field(TR{a, s, e, False{}}))

def Lc.cell(+r: U32, +fu: U32, +fi: U32, +ff: U32, +fb: U32, +fv: U32, fr: FR) -> LC:
  match fr:
    case FR{SH{a, fs, fe, fq}, +s, +e, +qf}:
      Lc.t(r, U32.div(qf, 2), fs, fe, fq, fu, fi, ff, fb, fv, Tr.both(s, e, a))

def Lc.go(f: Nat, +r: U32, +c: U32, +w: U32, st: LC) -> LC:
  match f st:
    case 0n other:
      other
    case 1n+p LC{sh, +fu, +fi, +ff, +fb, +fv}:
      Lc.go(p, U32.inc(r), c, w, Lc.cell(r, fu, fi, ff, fb, fv, Fd.get(U32.add(U32.mul(r, w), c), sh)))

# the columns' classes so far (newest first) with the shared arrays
type CC is Type:
  CC{sh: SH, acc: List<&1, CL>}

def Lc.push(acc: List<&1, CL>, lc: LC) -> CC:
  match lc:
    case LC{sh, +fu, +fi, +ff, +fb, +fv}:
      CC{sh, CL{fu, fi, ff, fb, fv} <> acc}

def Lc.col(+nr: U32, +c: U32, +w: U32, st: CC) -> CC:
  match st:
    case CC{sh, acc}:
      Lc.push(acc, Lc.go(U32.to_nat(nr), 0, c, w, LC{sh, 0, 0, 0, 0, 0}))

def Lc.cols(f: Nat, +nr: U32, +c: U32, +w: U32, st: CC) -> CC:
  match f:
    case 0n:
      st
    case 1n+p:
      Lc.cols(p, nr, U32.inc(c), w, Lc.col(nr, c, w, st))

# a tokenized region and its columns' classes (in column order)
type TC is Type:
  TC{to: TO, cl: List<&1, CL>}

def Ln.cls.k(+n: U32, +rej: U32, +rag: U32, +rgn: U32, lines: Array<U32>, cc: CC) -> TC:
  match cc:
    case CC{sh, acc}:
      TC{TO{n, rej, rag, rgn, sh, lines}, List.reverse(&1, CL, acc)}

# the classes of the w columns of a tokenized region (a rejected region classifies no row); the region
# comes back for the typed loops
def Ln.cls(+w: U32, to: TO) -> TC:
  match to:
    case TO{+n, +rej, +rag, +rgn, sh, lines}:
      Ln.cls.k(n, rej, rag, rgn, lines, Lc.cols(U32.to_nat(w), Ln.sel(U32.is_ne(rej, 0), 0, n), 0, w, CC{sh, Nil{}}))

# a region classified and handed back (its field arrays dropped): the forked inference pass of
# infer_rows = 0, which tokenizes again for the typed pass (17.4.5: two passes over the packed bytes,
# no second read)
type CR is Type:
  CR{rg: P.Rg, n: U32, cl: List<&1, CL>}

def Ln.clsr.k(+n: U32, off: U32, line0: U32, nt: U32, lfs: U32, fin: U32, tc: TC) -> CR:
  match tc:
    case TC{TO{+m, rej, rag, rgn, SH{a, fs, fe, fq}, lines}, cl}:
      CR{P.Rg{a, n, off, line0, nt, lfs, fin}, m, cl}

def Ln.clsr(+w: U32, +sep: U32, rg: P.Rg) -> CR:
  match rg:
    case P.Rg{a, +n, +off, +line0, +nt, +lfs, +fin}:
      Ln.clsr.k(n, off, line0, nt, lfs, fin, Ln.cls(w, Ln.tok(w, sep, P.Rg{a, n, off, line0, nt, lfs, fin})))
