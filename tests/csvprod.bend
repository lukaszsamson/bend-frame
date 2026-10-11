# W6.1: the CSV piece producer (src/csvprod.bend) against the v0.1 parser (src/csvparse.bend).
#
# Every adversarial file of tests/csvadv (bench/w6/gen_adv.py: quoted newlines in every record,
# doubled quotes at piece edges, CRLF split across pieces, multibyte UTF-8 split across pieces,
# a record longer than the piece, malformed quoting, ragged records, the empty file, blank lines,
# unterminated last records, invalid UTF-8) is read in pieces of 1, 2, 3, 4, 5, 7, 8, 13, 16, 31,
# 64, 97, 256, 4096 and 1048576 bytes, from offset 0 and (a second run) from the second record
# (the header step's answer). For a file the reference parser accepts, the regions must be EXACTLY
# those the lexical scan defines, derived from the reference's record starts: after each piece the
# region ends at the end of the last record that finished within the bytes read so far; every
# region start is a record start of the reference parser (physical line of its first byte, offset
# = the byte after the LF that ends the previous line), `nt` is the number of record ends inside,
# `lfs` its LF count, `line0` the first line. For every file (malformed too): regions tile
# [off0, size) with no gap, the lines chain (line0' = line0 + lfs), only the last region is
# final, the concatenated region bytes have the file's checksum, and the final quote parity is
# the parity of the quote bytes. Each line is `<case>: ok` when all 30 runs agree.
import Base
import ./../src/csvparse.bend as H
import ./../src/csvprod.bend as P
import ./../bench/w6/hx.bend as X
import ./../bench/w6/cases.bend as CS

# ---- what the reference parser says about the file ---------------------------------------------

# size, bytes, LF positions (ascending), quote bytes; ok: the reference accepts the file;
# starts: its records' start offsets, ends: the offsets where a record ENDS with its LF (the
# starts of the next records, and the size when the file ends with a record's LF)
type Fx is Data:
  Fx{size: U32, bs: List<&2, U32>, lf: List<&2, U32>, ok: Bool, starts: List<&2, U32>, ends: List<&2, U32>}

def Fx.lines(rs: List<&2, H.CsvRec>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case H.CsvRec{l, cs} <> t:
      l <> Fx.lines(t)

# the record ends: the starts after the first, then the size when the file ends with an LF
def Fx.ends.go(starts: List<&2, U32>, +size: U32, +last: U32) -> List<&2, U32>:
  match starts:
    case Nil{}:
      Bool.pick(List<&2, U32>, U32.is_eq(last, 10), size <> Nil{}, Nil{})
    case h <> t:
      h <> Fx.ends.go(t, size, last)

def Fx.ends(starts: List<&2, U32>, +size: U32, +last: U32) -> List<&2, U32>:
  match starts:
    case Nil{}:
      Nil{}
    case h <> t:
      Fx.ends.go(t, size, last)

def Fx.mk.q(+n: U32, bs: List<&2, U32>, lf: List<&2, U32>, +last: U32, +st: List<&2, U32>) -> Fx:
  Fx{n, bs, lf, True{}, st, Fx.ends(st, n, last)}

def Fx.mk.p(+n: U32, bs: List<&2, U32>, +lf: List<&2, U32>, +last: U32, +ls: List<&2, U32>) -> Fx:
  Fx.mk.q(n, bs, lf, last, X.Hx.offs(lf, ls))

def Fx.mk.k(+n: U32, bs: List<&2, U32>, lf: List<&2, U32>, +last: U32, ans: H.Ans) -> Fx:
  match ans:
    case H.Rejected{}:
      Fx{n, bs, lf, False{}, Nil{}, Nil{}}
    case H.Parsed{rs}:
      Fx.mk.p(n, bs, lf, last, Fx.lines(rs))

def Fx.mk(bs: List<&2, U32>, ans: H.Ans, sc: X.Sc) -> Fx:
  match sc:
    case X.Sc{+n, lf, qn, +last}:
      Fx.mk.k(n, bs, X.Hx.rev(lf), last, ans)

def Fx.load(+path: String, +sep: U32) -> IO(Fx):
  do IO<Fx>:
    +bs : List<&2, U32> <- X.Hx.bytes(path)
    txt : String <- X.Hx.text(path)
    return Fx.mk(bs, H.parse_sep(sep, txt), X.Hx.scan(bs, 0, Nil{}, 0, 0))


# ---- the expected regions ------------------------------------------------------------------------

# one region as the tests see it
type Rs is Data:
  Rs{off: U32, n: U32, line0: U32, nt: U32, lfs: U32, fin: U32}

def Rs.show(r: Rs) -> String:
  match r:
    case Rs{off, n, line0, nt, lfs, fin}:
      "[off " ++ U32.show(off) ++ " n " ++ U32.show(n) ++ " line " ++ U32.show(line0) ++ " nt " ++ U32.show(nt) ++ " lf " ++ U32.show(lfs) ++ " fin " ++ U32.show(fin) ++ "]"

def Rs.shows(xs: List<&2, Rs>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      Rs.show(h) ++ Rs.shows(t)

# the ends > x (ascending)
def Ex.gt.k(take: Bool, e: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match take:
    case True{}:
      e <> rest
    case False{}:
      rest

def Ex.gt(es: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      Ex.gt.k(U32.is_gt(e, x), e, Ex.gt(t, x))

# pop every end <= c: the rest, the last one popped (0: none), and whether the next one is <= c
type AD is Data:
  AD{es: List<&2, U32>, best: U32, go: Bool}

def Ex.adv.pick(+take: Bool, +e: U32, +t: List<&2, U32>, +best: U32) -> AD:
  AD{Bool.pick(List<&2, U32>, take, t, e <> t), Bool.pick(U32, take, e, best), take}

def Ex.adv.step(+c: U32, es: List<&2, U32>, +best: U32) -> AD:
  match es:
    case Nil{}:
      AD{Nil{}, best, False{}}
    case +e <> t:
      Ex.adv.pick(U32.is_le(e, c), e, t, best)

def Ex.adv(f: Nat, +c: U32, st: AD) -> AD:
  match f st:
    case 0n _:
      st
    case _ AD{es, best, False{}}:
      AD{es, best, False{}}
    case 1n+p AD{es, +best, True{}}:
      Ex.adv(p, c, Ex.adv.step(c, es, best))

# the cut search: bytes read so far c, the record ends not yet passed, the cuts (newest first)
type CU is Data:
  CU{c: U32, es: List<&2, U32>, cuts: List<&2, U32>, go: Bool}

# after the piece up to c2: the ends passed give a cut (the last), unless the file is read
def Ex.cuts.step(+c2: U32, +size: U32, +cuts: List<&2, U32>, ad: AD) -> CU:
  match ad:
    case AD{es, +best, go}:
      CU{c2, es, Bool.pick(List<&2, U32>, Bool.and(U32.is_ne(best, 0), U32.is_ne(c2, size)), best <> cuts, cuts), U32.is_ne(c2, size)}

def Ex.cuts(f: Nat, +piece: U32, +size: U32, st: CU) -> CU:
  match f st:
    case 0n _:
      st
    case _ CU{c, es, cuts, False{}}:
      CU{c, es, cuts, False{}}
    case 1n+p CU{+c, es, cuts, True{}}:
      Ex.cuts(p, piece, size, Ex.cuts.step(U32.min(U32.add(c, piece), size), size, cuts, Ex.adv(U32.to_nat(U32.add(size, 1)), U32.min(U32.add(c, piece), size), AD{es, 0, True{}})))

def Ex.cuts.fin(st: CU) -> List<&2, U32>:
  match st:
    case CU{c, es, cuts, go}:
      X.Hx.rev(cuts)

# the region ends: the cuts, then the size
def Ex.ends(cuts: List<&2, U32>, +size: U32) -> List<&2, U32>:
  match cuts:
    case Nil{}:
      size <> Nil{}
    case h <> t:
      h <> Ex.ends(t, size)

# the record ends in (s, e]
def Ex.cnt(es: List<&2, U32>, +s: U32, +e: U32, +n: U32) -> U32:
  match es:
    case Nil{}:
      n
    case +x <> t:
      Ex.cnt(t, s, e, U32.add(n, Bool.to_u32(Bool.and(U32.is_gt(x, s), U32.is_le(x, e)))))

# the region [s, e): its facts
def Ex.rg(+s: U32, +e: U32, +fin: U32, +lf: List<&2, U32>, es: List<&2, U32>) -> Rs:
  Rs{s, U32.sub(e, s), U32.inc(X.Hx.lfcount(lf, s, 0)), Ex.cnt(es, s, e, 0), U32.sub(X.Hx.lfcount(lf, e, 0), X.Hx.lfcount(lf, s, 0)), fin}

def Ex.zip(ss: List<&2, U32>, ee: List<&2, U32>, +lf: List<&2, U32>, +es: List<&2, U32>) -> List<&2, Rs>:
  match ss ee:
    case +s <> st +e <> Nil{}:
      Ex.rg(s, e, 1, lf, es) <> Nil{}
    case +s <> st +e <> et:
      Ex.rg(s, e, 0, lf, es) <> Ex.zip(st, et, lf, es)
    case _ _:
      Nil{}


def Ex.regions.k(+size: U32, +off0: U32, lf: List<&2, U32>, es: List<&2, U32>, +cuts: List<&2, U32>) -> List<&2, Rs>:
  Ex.zip(off0 <> cuts, Ex.ends(cuts, size), lf, es)

# the regions the lexical scan must make of fx from off0 with pieces of `piece` bytes
def Ex.regions(fx: Fx, +off0: U32, +piece: U32) -> List<&2, Rs>:
  match fx:
    case Fx{+size, bs, +lf, ok, starts, +ends}:
      Ex.regions.k(size, off0, lf, Ex.gt(ends, off0), Ex.cuts.fin(Ex.cuts(Nat.add(U32.to_nat(U32.div(size, piece)), 3n), piece, size, CU{off0, Ex.gt(ends, off0), Nil{}, True{}})))

# ---- the actual regions ----------------------------------------------------------------------------

# the checksum of the bytes of a region (FNV-1a, as Hx.lfold)
def Ac.fold.go(f: Nat, +i: U32, +h: U32, r: Array<U32> & U32) -> U32:
  match f:
    case 0n:
      (a, b) = r
      h
    case 1n+p:
      (a, +b) = r
      Ac.fold.go(p, U32.inc(i), U32.mul(U32.xor(h, b), 16777619), P.Pr.at(a, U32.inc(i)))

def Ac.fold(a: Array<U32>, +n: U32, +h: U32) -> U32:
  Ac.fold.go(U32.to_nat(n), 0, h, P.Pr.at(a, 0))

# the checksum so far and the regions (newest first)
type HA is Data:
  HA{h: U32, rs: List<&2, Rs>}

def Ac.one(rg: P.Rg, st: HA) -> HA:
  match rg:
    case P.Rg{a, +n, +off, +line0, +nt, +lfs, +fin}:
      match st:
        case HA{+h, rs}:
          HA{Ac.fold(a, n, h), Rs{off, n, line0, nt, lfs, fin} <> rs}

def Ac.go(regs: List<&1, P.Rg>, st: HA) -> HA:
  match regs:
    case Nil{}:
      st
    case rg <> t:
      Ac.go(t, Ac.one(rg, st))

# ---- the checks ---------------------------------------------------------------------------------------

# walking the regions: the next offset and line expected, everything agreed so far, the number of
# final regions, whether the last one is final
type TL is Data:
  TL{pos: U32, line: U32, ok: Bool, fins: U32, lastfin: U32}

def Ck.tile.one(r: Rs, st: TL) -> TL:
  match r st:
    case Rs{+off, +n, +line0, nt, +lfs, +fin} TL{+pos, +line, ok, +fins, lf}:
      TL{U32.add(off, n), U32.add(line0, lfs), Bool.and(ok, Bool.and(U32.is_eq(off, pos), U32.is_eq(line0, line))), U32.add(fins, fin), fin}

def Ck.tile(rs: List<&2, Rs>, st: TL) -> TL:
  match rs:
    case Nil{}:
      st
    case r <> t:
      Ck.tile(t, Ck.tile.one(r, st))

def Ck.tag(c: Bool, +t: String) -> String:
  Bool.pick(String, c, "", t ++ " ")

def Ck.tags(tl: TL, +size: U32, +line_end: U32) -> String:
  match tl:
    case TL{+pos, +line, +ok, +fins, +lastfin}:
      Ck.tag(Bool.and(ok, U32.is_eq(pos, size)), "tile") ++ Ck.tag(U32.is_eq(line, line_end), "lines") ++ Ck.tag(Bool.and(U32.is_eq(fins, 1), U32.is_eq(lastfin, 1)), "fin")

# the first region where the lists differ ("" when they are equal)
def Rs.same(x: Rs, y: Rs) -> Bool:
  match x y:
    case Rs{+a1, +a2, +a3, +a4, +a5, +a6} Rs{+b1, +b2, +b3, +b4, +b5, +b6}:
      Bool.and(Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), U32.is_eq(a3, b3))), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), U32.is_eq(a6, b6))))

def Rs.diff.k(same: Bool, +x: Rs, +y: Rs, +rest: String) -> String:
  match same:
    case True{}:
      rest
    case False{}:
      "region differs: want " ++ Rs.show(x) ++ " got " ++ Rs.show(y)

def Rs.diff(xs: List<&2, Rs>, ys: List<&2, Rs>) -> String:
  match xs ys:
    case Nil{} Nil{}:
      ""
    case +x <> xt +y <> yt:
      Rs.diff.k(Rs.same(x, y), x, y, Rs.diff(xt, yt))
    case Nil{} _:
      "fewer regions than expected"
    case _ Nil{}:
      "more regions than expected"

# an accepted file: the regions are exactly the expected ones
def Run.exact(ok: Bool, +tags: String, +want: List<&2, Rs>, +got: List<&2, Rs>) -> String:
  match ok:
    case True{}:
      tags ++ Rs.diff(want, got)
    case False{}:
      tags

def Run.v1(fx: Fx, +off0: U32, +odd: U32, +h: U32, +rs: List<&2, Rs>, want: List<&2, Rs>) -> String:
  match fx:
    case Fx{+size, +bs, +lf, ok, starts, ends}:
      Run.exact(ok, Ck.tag(U32.is_eq(h, X.Hx.lfold(bs, 0, off0, 2166136261)), "bytes") ++ Ck.tag(U32.is_eq(odd, U32.mod(X.Hx.qcount(bs, 0, off0, 0), 2)), "parity") ++ Ck.tags(Ck.tile(rs, TL{off0, U32.inc(X.Hx.lfcount(lf, off0, 0)), True{}, 0, 0}), size, U32.inc(X.Hx.lfcount(lf, size, 0))), want, rs)

def Run.v0(+fx: Fx, +off0: U32, +piece: U32, +odd: U32, ha: HA) -> String:
  match ha:
    case HA{+h, rs}:
      Run.v1(fx, off0, odd, h, List.reverse(&2, Rs, rs), Ex.regions(fx, off0, piece))

# the verdict of one run: "" when everything agrees
def Run.check(fx: Fx, +off0: U32, +piece: U32, o: P.PrOut) -> String:
  match o:
    case P.PrOk{nr, odd, regs}:
      Run.v0(fx, off0, piece, odd, Ac.go(regs, HA{2166136261, Nil{}}))
    case P.PrErr{code, msg}:
      "io error " ++ U32.show(code) ++ ": " ++ msg

# ---- running ------------------------------------------------------------------------------------------

# the line of offset x: 1 + the LFs before it
def Run.line(fx: Fx, +x: U32) -> U32:
  match fx:
    case Fx{size, bs, lf, ok, starts, ends}:
      U32.inc(X.Hx.lfcount(lf, x, 0))

def Run.one(+path: String, +fx: Fx, +off0: U32, +piece: U32) -> IO(String):
  do IO<String>:
    o : P.PrOut <- P.Pr.regions(path, off0, Run.line(fx, off0), piece)
    return Run.check(fx, off0, piece, o)

# the pieces still to run, the first failing verdict
type RP is Data:
  RP{ps: List<&2, U32>, v: String, go: Bool}

def Run.next(+ps: List<&2, U32>, +p: U32, +v: String) -> RP:
  Bool.pick(RP, String.is_empty(v), RP{ps, v, True{}}, RP{ps, "piece " ++ U32.show(p) ++ ": " ++ v, False{}})

def Run.loop(f: Nat, +path: String, +fx: Fx, +off0: U32, st: RP) -> IO(RP):
  match f st:
    case 0n _:
      IO.pure(RP, st)
    case _ RP{ps, v, False{}}:
      IO.pure(RP, RP{ps, v, False{}})
    case _ RP{Nil{}, v, True{}}:
      IO.pure(RP, RP{Nil{}, v, False{}})
    case 1n+p RP{+q <> t, v, True{}}:
      do IO<RP>:
        v2 : String <- Run.one(path, fx, off0, q)
        Run.loop(p, path, fx, off0, Run.next(t, q, v2))

def Run.all.k(rp: RP) -> String:
  match rp:
    case RP{ps, v, go}:
      v

# every piece size from off0
def Run.all(+path: String, +fx: Fx, +off0: U32) -> IO(String):
  do IO<String>:
    rp : RP <- Run.loop(20n, path, fx, off0, RP{X.Hx.pieces(), "", True{}})
    return Run.all.k(rp)

# the start of the second record (the header step's answer), 0 when there is none
def Run.second.k(starts: List<&2, U32>) -> U32:
  match starts:
    case Nil{}:
      0
    case h <> t:
      match t:
        case Nil{}:
          0
        case +s <> u:
          s

def Run.second(fx: Fx) -> U32:
  match fx:
    case Fx{size, bs, lf, ok, starts, ends}:
      Run.second.k(starts)

# the second run (off0 = the second record) only when there is one and the first passed
def Run.all.opt.k(skip: Bool, +path: String, +fx: Fx, +off1: U32) -> IO(String):
  match skip:
    case True{}:
      IO.pure(String, "")
    case False{}:
      Run.all(path, fx, off1)

def Run.all.opt(+path: String, +fx: Fx, +off1: U32, +v0: String) -> IO(String):
  Run.all.opt.k(U32.is_eq(off1, 0), path, fx, off1)

def Run.join(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_empty(a), Bool.pick(String, String.is_empty(b), "ok", "from record 2, " ++ b), "from offset 0, " ++ a)

def Run.two(+path: String, +fx: Fx, +off1: U32) -> IO(String):
  do IO<String>:
    +v0 : String <- Run.all(path, fx, 0)
    v1 : String <- Run.all.opt(path, fx, off1, v0)
    return Run.join(v0, v1)

def Case.run(path: String, +name: String, +fx: Fx) -> IO(String):
  do IO<String>:
    v : String <- Run.two(path, fx, Run.second(fx))
    return name ++ ": " ++ v

def Case.one.k(+name: String, +sep: U32) -> IO(String):
  do IO<String>:
    +path : String = "tests/csvadv/" ++ name ++ ".csv"
    +fx : Fx <- Fx.load(path, sep)
    Case.run(path, name, fx)

def Case.print(+s: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(s), IO.pure(Unit, Unit{}), IO.print(s))

# `only` (the first program argument, "" for every case) selects a case
def Case.one(+only: String, c: CS.Mf) -> IO(String):
  match c:
    case CS.Mf{+name, schema, hdr, +sep}:
      Bool.pick(IO(String), Bool.or(String.is_empty(only), String.eq(only, name)), Case.one.k(name, sep), IO.pure(String, ""))

def Case.loop(+only: String, cs: List<&2, CS.Mf>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> t:
      do IO<Unit>:
        s : String <- Case.one(only, c)
        Case.print(s)
        Case.loop(only, t)

# an IO error is a value
def Io.show(o: P.PrOut) -> String:
  match o:
    case P.PrOk{nr, odd, regs}:
      "ok"
    case P.PrErr{code, msg}:
      "io error " ++ U32.show(code) ++ ": " ++ msg

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
    o : P.PrOut <- P.Pr.regions("tests/csvadv/no_such_file.csv", 0, 1, 64)
    IO.print(Io.show(o))
#|quoted_nl: ok
#|quoted_nl_crlf: ok
#|quoted_nl_nofinal: ok
#|cr_soup: ok
#|cr_only_data: ok
#|crlf_plain: ok
#|utf8_typed: ok
#|utf8_bare: ok
#|long_records: ok
#|huge_record: ok
#|blanks_w2: ok
#|blanks_w1: ok
#|blanks_w1_str: ok
#|blanks_only: ok
#|lead_blank: ok
#|lead_blank_nohdr: ok
#|empty: ok
#|header_only: ok
#|header_only_nonl: ok
#|no_final_nl: ok
#|final_sep: ok
#|headerless: ok
#|bad_utf8: ok
#|mal_bare_quote_late: ok
#|mal_after_close: ok
#|mal_unclosed: ok
#|mal_unclosed_eof_q: ok
#|mal_cr_quote: ok
#|mal_closing_cr_text: ok
#|mal_and_ragged: ok
#|mal_in_second_half: ok
#|ragged_short: ok
#|ragged_long_first: ok
#|ragged_after_bad: ok
#|ragged_w1: ok
#|ragged_blank_ok: ok
#|bad_cols: ok
#|bad_cols_later_row: ok
#|bad_cols_earlier_other: ok
#|bad_quoted_text: ok
#|bad_i32_text: ok
#|f32_edges: ok
#|f32_one0: ok
#|f32_one1: ok
#|f32_one2: ok
#|f32_one3: ok
#|f32_one4: ok
#|f32_one5: ok
#|f32_one6: ok
#|f32_one7: ok
#|f32_one8: ok
#|f32_one9: ok
#|f32_one10: ok
#|f32_one11: ok
#|f32_one12: ok
#|f32_one13: ok
#|f32_one14: ok
#|f32_one15: ok
#|f32_one16: ok
#|f32_one17: ok
#|f32_random_fast: ok
#|u32_ok: ok
#|u32_bad0: ok
#|u32_bad1: ok
#|u32_bad2: ok
#|u32_bad3: ok
#|u32_bad4: ok
#|u32_bad5: ok
#|u32_bad6: ok
#|u32_bad7: ok
#|i32_ok: ok
#|u32_overflow: ok
#|u32_plus: ok
#|u32_sign: ok
#|u32_unicode_digit: ok
#|i32_edges: ok
#|i32_bad0: ok
#|i32_bad1: ok
#|i32_bad2: ok
#|i32_bad3: ok
#|i32_bad4: ok
#|i32_bad5: ok
#|i32_bad6: ok
#|i32_bad7: ok
#|i32_bad8: ok
#|i32_bad9: ok
#|bool_edges: ok
#|bool_bad: ok
#|bool_bad2: ok
#|bool_bad3: ok
#|escaped_numeric: ok
#|escaped_f32_bad: ok
#|nulls_all_types: ok
#|quote_edges: ok
#|fnv_collide: ok
#|fnv_collide_q: ok
#|wide: ok
#|tab_sep: ok
#|semicolon: ok
#|sep_dot: ok
#|sep_minus: ok
#|sep_pipe: ok
#|io error 2: No such file or directory
