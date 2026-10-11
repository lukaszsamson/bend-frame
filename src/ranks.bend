# src/ranks.bend -- lexical ranks of the distinct entries of a string column. DESIGN.md 17.3.2
# (D5, v0.2 W2.2).
#
#   Rk.words(+n, +d, +flip, a)  -> Array<String> & Array<U32>     (a, words)
#   Rk.dict(dict)               -> ST.Dict & Array<U32>            (dict, rank by code)
#   Rk.ranks(+k, +kd, +flip, a, fr, bl) -> RK{a, fr, rank}         (the stage itself)
#
# Rk.words is `Sort.str_words`: words[i] = rank(a[i]) xor flip for i < n, 0 beyond, where rank is
# the position of the row's string among the column's DISTINCT strings in code-point order, a
# prefix first (Base Map.to_list order = String.is_lt); the rows come back untouched (v0.1 dropped
# them). It runs the PACKED coder (src/hcode.bend Hc.code.pk, W2 pk ranks: first-appearance codes from
# 0; its one hashing walk copies each distinct key's code points into a flat array) and then the
# stage on the k entries, read from that flat array (no cons string is walked again; a hash hit of the
# coder compares flat words): ranks are computed per ENTRY and mapped to the rows by one gather
# (`word[row] = rank[code[row]]`; flip is folded into the k ranks, not the n words).
# Rk.dict is v0.1's `ST.Dict.ranks` (deleted by W2.3; tests/lib/v01str.bend): the same ranks of a Dictionary's k entries (rank[code]; slots >= k
# hold 0), the dictionary handed back.
#
# The stage (Rk.ranks), for k distinct entries `a[fr[e]]` with UTF-8 byte lengths bl[e] (bl is
# CONSUMED: the coder answers real lengths in HC.bl; Rk.dict computes them):
#  1. word offsets wo[e] = the prefix sums of ceil(bl[e] / 4);
#  2. PACK each entry once into big-endian U32 words of UTF-8 bytes (4 bytes per word, the last
#     word zero padded): UTF-8 byte order is code-point order, so comparing words compares strings
#     (for every U32 up to U+10FFFF, surrogates included, which encode in the same 3-byte form);
#     the walk also tracks the largest code point. FALLBACK: a code point above U+10FFFF (a Chr
#     can hold any U32) has no order-preserving 4-byte form: then the whole column is packed again
#     one code point per word (lengths = code point counts) and the same rounds run with 2 units
#     per round instead of 8 (unsigned word compare = code point compare);
#  3. RADIX REFINEMENT: round r stable-sorts every entry by (group, word 2r, word 2r + 1,
#     min(units left, upr)) with four `Radix.sort` calls (LSD: last key first; a digit that never
#     varies is skipped), then splits the groups (group = equal keys so far, id = its first
#     position). The last key puts a string before its extensions even when they continue with
#     U+0000 (padding and NUL compare equal, the remaining length does not). Distinct entries end
#     in singleton groups after ceil((LCP + 1) / upr) rounds (LCP: the longest common prefix of two
#     entries); the loop stops at the first round with no tie (and after mx / upr + 2 rounds
#     whatever happens: entries that are NOT distinct, never produced by the coder or a Dictionary,
#     would tie forever);
#  4. rank[perm[p]] = p xor flip (one scatter).
# Entries must be pairwise distinct (the coder's and a Dictionary's invariant): equal entries get
# distinct ranks in an unspecified order.
#
# Memory: pk = the entries' bytes / 4 words, wo, bl, gid, perm and the radix scratch: O(k) words,
# transient. No rank cache (no invalidation story); the stage is O(k x rounds) per request.
#
# Rk.ranks.pk (below) is the same stage over a packed coder's entries; Rk.ranks over strings stays
# for Rk.dict.
#
# Callers (W2.3): Sort.str_words / a Raw sort key (src/sort.bend: Rk.words, the key borrowed), a
# Dictionary sort key and Sort.dict_words, Dictionary min / max and comparisons between dictionaries
# (src/eval.bend: Rk.dict). `Radix.sort` comes from src/radix.bend (the single use is `Rx.sorted`).
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; pairs taken apart in the next
# helper's parameter; templates ~T.
import Base
import ./kernels.bend as K
import ./strs.bend as ST
import ./radix.bend as RD
import ./hcode.bend as H

# the stage's answer: the entries' rows, their ranks (2^kd slots: rank[e], 0 beyond k)
type RK is Type:
  RK{a: Array<String>, fr: Array<U32>, rank: Array<U32>}

def Rk.sel(+c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# ---- the lengths of the entries (when the caller has none) ----------------------------------------

type RLS is Type:
  RLS{a: Array<String>, fr: Array<U32>, bl: Array<U32>}

def Rl.put(+c: U32, bl: Array<U32>, r: Array<String> & U32, fr: Array<U32>) -> RLS:
  (a, +n) = r
  RLS{a, fr, Array.set(U32, bl, c, n)}

def Rl.str(~len: String -> U32, +c: U32, fr: Array<U32>, bl: Array<U32>, r: Array<String> & String) -> RLS:
  (a, s) = r
  Rl.put(c, bl, (a, len(s)), fr)

def Rl.row(~len: String -> U32, +c: U32, a: Array<String>, bl: Array<U32>, r: Array<U32> & U32) -> RLS:
  (fr, +row) = r
  Rl.str(~len, c, fr, bl, Array.get(String, a, row))

def Rl.go(~len: String -> U32, n: Nat, +c: U32, st: RLS) -> RLS:
  match n st:
    case 0n other:
      other
    case 1n+p RLS{a, fr, bl}:
      Rl.go(~len, p, U32.inc(c), Rl.row(~len, c, a, bl, Array.get(U32, fr, c)))

def Rl.cps(s: String, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{c, t}:
      Rl.cps(t, U32.inc(n))

# ---- word offsets ---------------------------------------------------------------------------------

# wo[e] = the first word of entry e, wo[k] = the total; units -> words is (x + wadd) >> wsh
type RW is Type:
  RW{tot: U32, mx: U32, bl: Array<U32>, wo: Array<U32>}

def Rw.go(n: Nat, +c: U32, +tot: U32, +mx: U32, +wadd: U32, +wsh: Nat, wo: Array<U32>, r: Array<U32> & U32) -> RW:
  match n:
    case 0n:
      (bl, x) = r
      RW{tot, mx, bl, Array.set(U32, wo, c, tot)}
    case 1n+p:
      (bl, +x) = r
      +j = U32.inc(c)
      Rw.go(p, j, U32.add(tot, U32.shrn(U32.add(x, wadd), wsh)), U32.max(mx, x), wadd, wsh, Array.set(U32, wo, c, tot), Array.get(U32, bl, j))

# ---- packing: UTF-8 bytes, big-endian, 4 per word ----------------------------------------------------
# State: the word buffer, the current word index, the partial word, the multiplier of the next
# byte (2^24, 2^16, 2^8, 1), the largest code point so far. Every byte rewrites its word (no flush
# step); a full word advances w and resets acc and m.

type PB is Type:
  PB{pk: Array<U32>, w: U32, acc: U32, m: U32, mx: U32}

def Pb.put(+b: U32, st: PB) -> PB:
  match st:
    case PB{pk, +w, +acc, +m, mx}:
      +acc2 = U32.add(acc, U32.mul(b, m))
      +fu = Bool.to_u32(U32.is_eq(m, 1))
      PB{Array.set(U32, pk, w, acc2), U32.add(w, fu), U32.mul(acc2, U32.sub(1, fu)), U32.or(U32.shrn(m, 8n), U32.mul(fu, 16777216)), mx}

# a continuation byte: 10xxxxxx of c >> sh
def Pb.cont(+c: U32, +sh: Nat) -> U32:
  U32.add(128, U32.and(U32.shrn(c, sh), 63))

# a four-byte character also records its code point (the largest wins): above U+10FFFF the packing
# is replaced by the fallback; one- to three-byte characters never are, so they skip the check
def Pb.wide(+c: U32, st: PB) -> PB:
  match st:
    case PB{pk, w, acc, m, +mx}:
      PB{pk, w, acc, m, U32.max(mx, c)}

def Pb.cp.k(+one: Bool, +two: Bool, +three: Bool, +c: U32, st: PB) -> PB:
  match one:
    case True{}:
      Pb.put(c, st)
    case False{}:
      match two:
        case True{}:
          Pb.put(Pb.cont(c, 0n), Pb.put(U32.add(192, U32.shrn(c, 6n)), st))
        case False{}:
          match three:
            case True{}:
              Pb.put(Pb.cont(c, 0n), Pb.put(Pb.cont(c, 6n), Pb.put(U32.add(224, U32.shrn(c, 12n)), st)))
            case False{}:
              Pb.wide(c, Pb.put(Pb.cont(c, 0n), Pb.put(Pb.cont(c, 6n), Pb.put(Pb.cont(c, 12n), Pb.put(U32.add(240, U32.shrn(c, 18n)), st)))))

def Pb.cp(+c: U32, st: PB) -> PB:
  Pb.cp.k(U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536), c, st)

def Str.u8(s: String, st: PB) -> PB:
  match s:
    case SNil{}:
      st
    case SCon{Chr{c}, t}:
      Str.u8(t, Pb.cp(c, st))

# the entries' walk: pk, the largest code point; the rows, offsets handed along
type RF is Type:
  RF{a: Array<String>, fr: Array<U32>, wo: Array<U32>, pk: Array<U32>, mx: U32}

def Rf.fin(a: Array<String>, fr: Array<U32>, wo: Array<U32>, pb: PB) -> RF:
  match pb:
    case PB{pk, w, acc, m, mx}:
      RF{a, fr, wo, pk, mx}

def Rf.s(fr: Array<U32>, pk: Array<U32>, +mx: U32, ro: Array<U32> & U32, r: Array<String> & String) -> RF:
  (wo, +w) = ro
  (a, s) = r
  Rf.fin(a, fr, wo, Str.u8(s, PB{pk, w, 0, 16777216, mx}))

def Rf.r(+c: U32, a: Array<String>, wo: Array<U32>, pk: Array<U32>, +mx: U32, r: Array<U32> & U32) -> RF:
  (fr, +row) = r
  Rf.s(fr, pk, mx, Array.get(U32, wo, c), Array.get(String, a, row))

def Rf.go(n: Nat, +c: U32, st: RF) -> RF:
  match n st:
    case 0n other:
      other
    case 1n+p RF{a, fr, wo, pk, +mx}:
      Rf.go(p, U32.inc(c), Rf.r(c, a, wo, pk, mx, Array.get(U32, fr, c)))

# the fallback packing: one code point per word
def Str.put(s: String, +p: U32, cps: Array<U32>) -> Array<U32>:
  match s:
    case SNil{}:
      cps
    case SCon{Chr{x}, t}:
      Str.put(t, U32.inc(p), Array.set(U32, cps, p, x))

def Rq.s(fr: Array<U32>, cps: Array<U32>, ro: Array<U32> & U32, r: Array<String> & String) -> RF:
  (wo, +p) = ro
  (a, s) = r
  RF{a, fr, wo, Str.put(s, p, cps), 0}

def Rq.r(+c: U32, a: Array<String>, wo: Array<U32>, cps: Array<U32>, r: Array<U32> & U32) -> RF:
  (fr, +row) = r
  Rq.s(fr, cps, Array.get(U32, wo, c), Array.get(String, a, row))

def Rq.go(n: Nat, +c: U32, st: RF) -> RF:
  match n st:
    case 0n other:
      other
    case 1n+p RF{a, fr, wo, cps, mx}:
      Rq.go(p, U32.inc(c), Rq.r(c, a, wo, cps, Array.get(U32, fr, c)))

# ---- the rounds ---------------------------------------------------------------------------------------
# upr = units (bytes, or code points in the fallback) per round = 2 words.

type RX is Type:
  RX{wo: Array<U32>, bl: Array<U32>, pk: Array<U32>, gid: Array<U32>, upr: U32}

type KK is Data:
  KG{}
  KW1{}
  KW2{}
  KL{}


# word j of entry e (0 past its end): wo[e], wo[e + 1], then pk[wo[e] + j] (an index past the end
# wraps: Array.get masks it)
def Rx.word.k(+j: U32, +o: U32, +o2: U32, bl: Array<U32>, gid: Array<U32>, +upr: U32, wo: Array<U32>, r: Array<U32> & U32) -> RX & U32:
  (pk, +x) = r
  (RX{wo, bl, pk, gid, upr}, U32.mul(x, Bool.to_u32(U32.is_lt(j, U32.sub(o2, o)))))

def Rx.word.b(+j: U32, +o: U32, bl: Array<U32>, gid: Array<U32>, +upr: U32, pk: Array<U32>, r: Array<U32> & U32) -> RX & U32:
  (wo, +o2) = r
  Rx.word.k(j, o, o2, bl, gid, upr, wo, Array.get(U32, pk, U32.add(o, j)))

def Rx.word.a(+e: U32, +j: U32, bl: Array<U32>, gid: Array<U32>, +upr: U32, pk: Array<U32>, r: Array<U32> & U32) -> RX & U32:
  (wo, +o) = r
  Rx.word.b(j, o, bl, gid, upr, pk, Array.get(U32, wo, U32.inc(e)))

def Rx.word(+e: U32, +j: U32, rx: RX) -> RX & U32:
  match rx:
    case RX{wo, bl, pk, gid, +upr}:
      Rx.word.a(e, j, bl, gid, upr, pk, Array.get(U32, wo, e))

# the units of entry e left in round r: min(max(bl[e] - r * upr, 0), upr)
def Rx.blen.k(wo: Array<U32>, pk: Array<U32>, gid: Array<U32>, +upr: U32, +r: U32, rb: Array<U32> & U32) -> RX & U32:
  (bl, +n) = rb
  +lo = U32.mul(r, upr)
  (RX{wo, bl, pk, gid, upr}, U32.min(U32.mul(U32.sub(n, lo), Bool.to_u32(U32.is_gt(n, lo))), upr))

def Rx.gid.k(wo: Array<U32>, bl: Array<U32>, pk: Array<U32>, +upr: U32, rg: Array<U32> & U32) -> RX & U32:
  (gid, +g) = rg
  (RX{wo, bl, pk, gid, upr}, g)

def Rx.key(kk: KK, +e: U32, +r: U32, rx: RX) -> RX & U32:
  match kk rx:
    case KG{} RX{wo, bl, pk, gid, +upr}:
      Rx.gid.k(wo, bl, pk, upr, Array.get(U32, gid, e))
    case KW1{} other:
      Rx.word(e, U32.mul(r, 2), other)
    case KW2{} other:
      Rx.word(e, U32.inc(U32.mul(r, 2)), other)
    case KL{} RX{wo, bl, pk, gid, +upr}:
      Rx.blen.k(wo, pk, gid, upr, r, Array.get(U32, bl, e))

type KS is Type:
  KS{rx: RX, ws: Array<U32>}

def Rx.keys.put(+p: U32, ws: Array<U32>, r: RX & U32) -> KS:
  (rx, +x) = r
  KS{rx, Array.set(U32, ws, p, x)}

# ws[p] = key of entry perm[p]
def Rx.keys(n: Nat, +p: U32, +kk: KK, +r: U32, st: KS, rp: Array<U32> & U32) -> KS & Array<U32>:
  match n st:
    case 0n other:
      (perm, e) = rp
      (other, perm)
    case 1n+q KS{rx, ws}:
      (perm, +e) = rp
      Rx.keys(q, U32.inc(p), kk, r, Rx.keys.put(p, ws, Rx.key(kk, e, r, rx)), Array.get(U32, perm, U32.inc(p)))

def Rx.sorted.k(rx: RX, r: Array<U32> & Array<U32>) -> RX & Array<U32>:
  (ws, perm) = r
  (rx, perm)

def Rx.sorted(+k: U32, +kd: Nat, r: KS & Array<U32>) -> RX & Array<U32>:
  (ks, perm) = r
  match ks:
    case KS{rx, ws}:
      Rx.sorted.k(rx, RD.Radix.sort(k, kd, (ws, perm)))

def Rx.by(+kk: KK, +k: U32, +kd: Nat, +r: U32, st: RX & Array<U32>) -> RX & Array<U32>:
  (rx, perm) = st
  Rx.sorted(k, kd, Rx.keys(U32.to_nat(k), 0, kk, r, KS{rx, Array.new(U32, kd, 0)}, Array.get(U32, perm, 0)))

# regroup: equal (group, w1, w2, left) neighbours stay together; new group id = its first position
type RG is Type:
  RG{rx: RX, ng: Array<U32>, pg: U32, p1: U32, p2: U32, pl: U32, start: U32, ties: U32}

def Rg.put(+p: U32, ng: Array<U32>, +e: U32, +pg: U32, +p1: U32, +p2: U32, +pl: U32, +start: U32, +ties: U32, +g: U32, +x1: U32, +x2: U32, rl: RX & U32) -> RG:
  (rx, +xl) = rl
  +same = Bool.and(U32.is_gt(p, 0), Bool.and(Bool.and(U32.is_eq(g, pg), U32.is_eq(x1, p1)), Bool.and(U32.is_eq(x2, p2), U32.is_eq(xl, pl))))
  +st2 = Rk.sel(same, start, p)
  RG{rx, Array.set(U32, ng, e, st2), g, x1, x2, xl, st2, U32.add(ties, Bool.to_u32(same))}

def Rg.w2(+p: U32, +r: U32, ng: Array<U32>, +e: U32, +pg: U32, +p1: U32, +p2: U32, +pl: U32, +start: U32, +ties: U32, +g: U32, +x1: U32, r2: RX & U32) -> RG:
  (rx, +x2) = r2
  Rg.put(p, ng, e, pg, p1, p2, pl, start, ties, g, x1, x2, Rx.key(KL{}, e, r, rx))

def Rg.w1(+p: U32, +r: U32, ng: Array<U32>, +e: U32, +pg: U32, +p1: U32, +p2: U32, +pl: U32, +start: U32, +ties: U32, +g: U32, r1: RX & U32) -> RG:
  (rx, +x1) = r1
  Rg.w2(p, r, ng, e, pg, p1, p2, pl, start, ties, g, x1, Rx.key(KW2{}, e, r, rx))

def Rg.g(+p: U32, +r: U32, ng: Array<U32>, +e: U32, +pg: U32, +p1: U32, +p2: U32, +pl: U32, +start: U32, +ties: U32, rg: RX & U32) -> RG:
  (rx, +g) = rg
  Rg.w1(p, r, ng, e, pg, p1, p2, pl, start, ties, g, Rx.key(KW1{}, e, r, rx))

def Rg.go(n: Nat, +p: U32, +r: U32, st: RG, rp: Array<U32> & U32) -> RG & Array<U32>:
  match n st:
    case 0n other:
      (perm, e) = rp
      (other, perm)
    case 1n+q RG{rx, ng, +pg, +p1, +p2, +pl, +start, +ties}:
      (perm, +e) = rp
      Rg.go(q, U32.inc(p), r, Rg.g(p, r, ng, e, pg, p1, p2, pl, start, ties, Rx.key(KG{}, e, r, rx)), Array.get(U32, perm, U32.inc(p)))

type RR is Type:
  RR{rx: RX, perm: Array<U32>, ties: U32, rounds: U32}

def Rg.fin(+rounds: U32, r: RG & Array<U32>) -> RR:
  (rg, perm) = r
  match rg:
    case RG{RX{wo, bl, pk, gid, upr}, ng, pg, p1, p2, pl, start, +ties}:
      RR{RX{wo, bl, pk, ng, upr}, perm, ties, U32.inc(rounds)}

def Rx.regroup(+k: U32, +kd: Nat, +r: U32, st: RX & Array<U32>) -> RR:
  (rx, perm) = st
  Rg.fin(r, Rg.go(U32.to_nat(k), 0, r, RG{rx, Array.new(U32, kd, 0), 0, 0, 0, 0, 0, 0}, Array.get(U32, perm, 0)))

def Rx.round(+k: U32, +kd: Nat, +r: U32, rx: RX, perm: Array<U32>) -> RR:
  Rx.regroup(k, kd, r, Rx.by(KG{}, k, kd, r, Rx.by(KW1{}, k, kd, r, Rx.by(KW2{}, k, kd, r, Rx.by(KL{}, k, kd, r, (rx, perm))))))

# a round only while some neighbours tie (afterwards the loop runs out its fuel doing nothing)
def Rx.round.if(go: Bool, +k: U32, +kd: Nat, +r: U32, rx: RX, perm: Array<U32>, +ties: U32, +rounds: U32) -> RR:
  match go:
    case True{}:
      Rx.round(k, kd, r, rx, perm)
    case False{}:
      RR{rx, perm, ties, rounds}

def Rx.loop(n: Nat, +r: U32, +k: U32, +kd: Nat, rr: RR) -> RR:
  match n rr:
    case 0n other:
      other
    case 1n+p RR{rx, perm, +ties, +rounds}:
      Rx.loop(p, U32.inc(r), k, kd, Rx.round.if(U32.is_ne(ties, 0), k, kd, r, rx, perm, ties, rounds))

# ---- ranks from the final order --------------------------------------------------------------------

# rk[perm[p]] = p xor flip
def Rk.go(n: Nat, +p: U32, +flip: U32, rk: Array<U32>, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (perm, x) = r
      rk
    case 1n+f:
      (perm, +x) = r
      +q = U32.inc(p)
      Rk.go(f, q, flip, Array.set(U32, rk, x, U32.xor(p, flip)), Array.get(U32, perm, q))

def Rk.fin(a: Array<String>, fr: Array<U32>, +k: U32, +kd: Nat, +flip: U32, rr: RR) -> RK:
  match rr:
    case RR{rx, perm, ties, rounds}:
      RK{a, fr, Rk.go(U32.to_nat(k), 0, flip, Array.new(U32, kd, 0), Array.get(U32, perm, 0))}

# the rounds over the packed entries (upr units per round, mx the longest entry in units); fewer
# than two entries need none
def Rk.run(+k: U32, +kd: Nat, +flip: U32, +upr: U32, +mx: U32, a: Array<String>, fr: Array<U32>, wo: Array<U32>, bl: Array<U32>, pk: Array<U32>) -> RK:
  Rk.fin(a, fr, k, kd, flip, Rx.loop(U32.to_nat(U32.mul(Bool.to_u32(U32.is_ge(k, 2)), U32.add(U32.div(mx, upr), 2))), 0, k, kd, RR{RX{wo, bl, pk, Array.new(U32, kd, 0), upr}, K.Kernel.iota(k, kd), 1, 0}))

# ---- the stage ----------------------------------------------------------------------------------------

# the fallback: the whole column one code point per word (the lengths are code point counts)
def Rk.wide.c(+k: U32, +kd: Nat, +flip: U32, +mx: U32, bl: Array<U32>, rf: RF) -> RK:
  match rf:
    case RF{a, fr, wo, pk, mx0}:
      Rk.run(k, kd, flip, 2, mx, a, fr, wo, bl, pk)

def Rk.wide.b(+k: U32, +kd: Nat, +flip: U32, a: Array<String>, fr: Array<U32>, rw: RW) -> RK:
  match rw:
    case RW{+tot, +mx, bl, wo}:
      Rk.wide.c(k, kd, flip, mx, bl, Rq.go(U32.to_nat(k), 0, RF{a, fr, wo, Array.new(U32, K.Kernel.depth_for(U32.inc(tot)), 0), 0}))

def Rk.wide.l(+k: U32, +kd: Nat, +flip: U32, +kd1: Nat, ls: RLS) -> RK:
  match ls:
    case RLS{a, fr, bl}:
      Rk.wide.b(k, kd, flip, a, fr, Rw.go(U32.to_nat(k), 0, 0, 0, 0, 0n, Array.new(U32, kd1, 0), Array.get(U32, bl, 0)))

def Rk.wide(+k: U32, +kd: Nat, +flip: U32, +kd1: Nat, a: Array<String>, fr: Array<U32>, bl: Array<U32>) -> RK:
  Rk.wide.l(k, kd, flip, kd1, Rl.go(~(s => Rl.cps(s, 0)), U32.to_nat(k), 0, RLS{a, fr, bl}))

# bytes (every code point <= U+10FFFF) or the fallback
def Rk.pk(+wide: Bool, +k: U32, +kd: Nat, +flip: U32, +kd1: Nat, +mx: U32, a: Array<String>, fr: Array<U32>, wo: Array<U32>, bl: Array<U32>, pk: Array<U32>) -> RK:
  match wide:
    case True{}:
      Rk.wide(k, kd, flip, kd1, a, fr, bl)
    case False{}:
      Rk.run(k, kd, flip, 8, mx, a, fr, wo, bl, pk)

def Rk.pack.b(+k: U32, +kd: Nat, +flip: U32, +kd1: Nat, +mx: U32, bl: Array<U32>, rf: RF) -> RK:
  match rf:
    case RF{a, fr, wo, pk, +cm}:
      Rk.pk(U32.is_gt(cm, 1114111), k, kd, flip, kd1, mx, a, fr, wo, bl, pk)

def Rk.pack(+k: U32, +kd: Nat, +flip: U32, +kd1: Nat, a: Array<String>, fr: Array<U32>, rw: RW) -> RK:
  match rw:
    case RW{+tot, +mx, bl, wo}:
      Rk.pack.b(k, kd, flip, kd1, mx, bl, Rf.go(U32.to_nat(k), 0, RF{a, fr, wo, Array.new(U32, K.Kernel.depth_for(U32.inc(tot)), 0), 0}))

# The ranks of k distinct entries: entry e is a[fr[e]], its UTF-8 byte length bl[e] (bl consumed).
# rank[e] = (its position among the entries in code-point order, a prefix first) xor flip, in an
# array of 2^kd slots (kd >= depth_for(k), >= 1 slot; slots >= k hold 0); a and fr come back.
def Rk.ranks(+k: U32, +kd: Nat, +flip: U32, a: Array<String>, fr: Array<U32>, bl: Array<U32>) -> RK:
  +kd1 = K.Kernel.depth_for(U32.inc(k))
  Rk.pack(k, kd, flip, kd1, a, fr, Rw.go(U32.to_nat(k), 0, 0, 0, 3, 2n, Array.new(U32, kd1, 0), Array.get(U32, bl, 0)))

# ---- the entry points ---------------------------------------------------------------------------------

# ---- the entries of the packed coder (W2 pk ranks) -------------------------------------------------------
# Hc.code.pk (src/hcode.bend) leaves each DISTINCT key's code points in one flat array, entries in id
# order: entry e = pk[po[e] .. po[e] + pl[e]). The stage needs the UTF-8 byte lengths and the big-endian
# packing of the entries, and takes both from that array: no cons string is walked after the coder's
# single hashing walk (the coder's hash hit compares flat words, never a representative row). The
# entries' first rows (fr) are not needed: the stage never looks at the rows again, so they are not
# derived (the coder's rows go straight back to the caller; Rk.run's `fr` slot is a pass-through).
#  pass A (Pa.*): per entry the byte length (a new array) and, over all entries, the largest code point;
#  then Rw.go (word offsets, as before) and, unless a code point exceeds U+10FFFF, pass B (Pq.*): the
#  entry's code points packed into the exact-size big-endian word array (Pb.*, as before);
#  FALLBACK (a code point above U+10FFFF): the code points already ARE the one-per-word form: the
#  offsets are Rw.go's prefix sums of the code point counts pl, pk is handed to the rounds as it is.

# the answer of an entry's code point loop: the array back, the byte count, the largest code point
type PI is Type:
  PI{pk: Array<U32>, b: U32, cm: U32}

# pass A, the spin loop over one entry's code points (n = its count, o = the index of the code point
# in r): bytes += UTF-8 length, cm = the running maximum; nothing is allocated per code point
def Pa.in(n: Nat, +o: U32, +b: U32, +cm: U32, r: Array<U32> & U32) -> PI:
  match n:
    case 0n:
      (pk, x) = r
      PI{pk, b, cm}
    case 1n+p:
      (pk, +c) = r
      +o2 = U32.inc(o)
      Pa.in(p, o2, U32.add(b, H.Hc.u8(c)), U32.max(cm, c), Array.get(U32, pk, o2))

type PA is Type:
  PA{po: Array<U32>, pl: Array<U32>, bl: Array<U32>, pk: Array<U32>, cm: U32}

def Pa.c(+e: U32, po: Array<U32>, pl: Array<U32>, bl: Array<U32>, pi: PI) -> PA:
  match pi:
    case PI{pk, +b, +cm}:
      PA{po, pl, Array.set(U32, bl, e, b), pk, cm}

def Pa.b(+e: U32, +o: U32, +cm: U32, po: Array<U32>, bl: Array<U32>, pk: Array<U32>, r: Array<U32> & U32) -> PA:
  (pl, +m) = r
  Pa.c(e, po, pl, bl, Pa.in(U32.to_nat(m), o, 0, cm, Array.get(U32, pk, o)))

def Pa.a(+e: U32, +cm: U32, pl: Array<U32>, bl: Array<U32>, pk: Array<U32>, r: Array<U32> & U32) -> PA:
  (po, +o) = r
  Pa.b(e, o, cm, po, bl, pk, Array.get(U32, pl, e))

# pass A's loop over the k entries (a spin loop over entries; one record per entry, none per code point)
def Pa.go(n: Nat, +e: U32, st: PA) -> PA:
  match n st:
    case 0n other:
      other
    case 1n+p PA{po, pl, bl, pk, +cm}:
      Pa.go(p, U32.inc(e), Pa.a(e, cm, pl, bl, pk, Array.get(U32, po, e)))

# pass B, the spin loop over one entry's code points: pack each (Pb.cp: 1 to 4 bytes) into the word
# buffer in the PB state; the source array rides along as the read-ahead pair
def Pq.in(n: Nat, +o: U32, st: PB, r: Array<U32> & U32) -> PB & Array<U32>:
  match n:
    case 0n:
      (pk, x) = r
      (st, pk)
    case 1n+p:
      (pk, +c) = r
      +o2 = U32.inc(o)
      Pq.in(p, o2, Pb.cp(c, st), Array.get(U32, pk, o2))

type PQ is Type:
  PQ{po: Array<U32>, pl: Array<U32>, wo: Array<U32>, pk: Array<U32>, out: Array<U32>}

def Pq.f(po: Array<U32>, pl: Array<U32>, wo: Array<U32>, r: PB & Array<U32>) -> PQ:
  (pb, pk) = r
  match pb:
    case PB{out, w, acc, m, mx}:
      PQ{po, pl, wo, pk, out}

def Pq.c(+o: U32, +m: U32, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, out: Array<U32>, r: Array<U32> & U32) -> PQ:
  (wo, +w) = r
  Pq.f(po, pl, wo, Pq.in(U32.to_nat(m), o, PB{out, w, 0, 16777216, 0}, Array.get(U32, pk, o)))

def Pq.b(+e: U32, +o: U32, po: Array<U32>, wo: Array<U32>, pk: Array<U32>, out: Array<U32>, r: Array<U32> & U32) -> PQ:
  (pl, +m) = r
  Pq.c(o, m, po, pl, pk, out, Array.get(U32, wo, e))

def Pq.a(+e: U32, pl: Array<U32>, wo: Array<U32>, pk: Array<U32>, out: Array<U32>, r: Array<U32> & U32) -> PQ:
  (po, +o) = r
  Pq.b(e, o, po, wo, pk, out, Array.get(U32, pl, e))

# pass B's loop over the k entries: entry e goes to out[wo[e] ..] (a spin loop over entries)
def Pq.go(n: Nat, +e: U32, st: PQ) -> PQ:
  match n st:
    case 0n other:
      other
    case 1n+p PQ{po, pl, wo, pk, out}:
      Pq.go(p, U32.inc(e), Pq.a(e, pl, wo, pk, out, Array.get(U32, po, e)))

# the packed words of the entries (RW: offsets, byte lengths) and the rounds over them
def Rk.pq.r(+k: U32, +kd: Nat, +flip: U32, +mx: U32, a: Array<String>, fr: Array<U32>, bl: Array<U32>, pq: PQ) -> RK:
  match pq:
    case PQ{po, pl, wo, pk, out}:
      Rk.run(k, kd, flip, 8, mx, a, fr, wo, bl, out)

def Rk.pq.b(+k: U32, +kd: Nat, +flip: U32, a: Array<String>, fr: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, rw: RW) -> RK:
  match rw:
    case RW{+tot, +mx, bl, wo}:
      Rk.pq.r(k, kd, flip, mx, a, fr, bl, Pq.go(U32.to_nat(k), 0, PQ{po, pl, wo, pk, Array.new(U32, K.Kernel.depth_for(U32.inc(tot)), 0)}))

# the fallback: the offsets are the prefix sums of the code point counts, the rounds take 2 words
def Rk.pw.b(+k: U32, +kd: Nat, +flip: U32, a: Array<String>, fr: Array<U32>, pk: Array<U32>, rw: RW) -> RK:
  match rw:
    case RW{+tot, +mx, pl, wo}:
      Rk.run(k, kd, flip, 2, mx, a, fr, wo, pl, pk)

def Rk.pw(+wide: Bool, +k: U32, +kd: Nat, +flip: U32, +kd1: Nat, a: Array<String>, fr: Array<U32>, po: Array<U32>, pl: Array<U32>, bl: Array<U32>, pk: Array<U32>) -> RK:
  match wide:
    case True{}:
      Rk.pw.b(k, kd, flip, a, fr, pk, Rw.go(U32.to_nat(k), 0, 0, 0, 0, 0n, Array.new(U32, kd1, 0), Array.get(U32, pl, 0)))
    case False{}:
      Rk.pq.b(k, kd, flip, a, fr, po, pl, pk, Rw.go(U32.to_nat(k), 0, 0, 0, 3, 2n, Array.new(U32, kd1, 0), Array.get(U32, bl, 0)))

def Rk.pa.r(+k: U32, +kd: Nat, +flip: U32, +kd1: Nat, a: Array<String>, fr: Array<U32>, pa: PA) -> RK:
  match pa:
    case PA{po, pl, bl, pk, +cm}:
      Rk.pw(U32.is_gt(cm, 1114111), k, kd, flip, kd1, a, fr, po, pl, bl, pk)

# The ranks of the k entries of a packed coder's table (k = next; po, pl, pk as Hc.code.pk answers;
# a, fr pass through): the same ranks as Rk.ranks over the entries' strings.
def Rk.ranks.pk(+k: U32, +kd: Nat, +flip: U32, a: Array<String>, fr: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>) -> RK:
  +kd1 = K.Kernel.depth_for(U32.inc(k))
  Rk.pa.r(k, kd, flip, kd1, a, fr, Pa.go(U32.to_nat(k), 0, PA{po, pl, Array.new(U32, kd, 0), pk, 0}))

# ---- the entry points ---------------------------------------------------------------------------------

# the words of the n rows: words[c] = rank[codes[c]] (the gather), the rows back
def Rk.words.g(a: Array<String>, r: Array<U32> & Array<U32>) -> Array<String> & Array<U32>:
  (w, codes) = r
  (a, w)

def Rk.words.r(+n: U32, +d: Nat, codes: Array<U32>, rk: RK) -> Array<String> & Array<U32>:
  match rk:
    case RK{a, fr, rank}:
      Rk.words.g(a, K.Kernel.gather(~U32, n, d, rank, codes, 0))

# the coder's table (hs, ix) is dropped; ix rides along as the stage's `fr` slot (unused)
def Rk.words.c(+n: U32, +d: Nat, +flip: U32, hj: H.HJ) -> Array<String> & Array<U32>:
  match hj:
    case H.HJ{+k, a, hs, ix, codes, po, pl, pk, cur, pd}:
      Rk.words.r(n, d, codes, Rk.ranks.pk(k, K.Kernel.depth_for(U32.max(k, 1)), flip, a, ix, po, pl, pk))

# Sort.str_words(n, d, flip, a) with the rows handed back: (a, words). The packed coder (Hc.code.pk:
# first-appearance ids from 0, the identity hash) and the rank stage over its flat entries.
def Rk.words(+n: U32, +d: Nat, +flip: U32, a: Array<String>) -> Array<String> & Array<U32>:
  Rk.words.c(n, d, flip, H.Hc.code.pk(~(h => h), n, d, a))

# v0.1's ST.Dict.ranks(dict) with the flat stage: (dict, rank by code), 2^dd slots
def Rk.dict.r(+k: U32, +dd: Nat, +b: Nat, slots: Array<ST.SSlot>, +tag: U32, rk: RK) -> ST.Dict & Array<U32>:
  match rk:
    case RK{strs, fr, rank}:
      (ST.Dict{k, dd, strs, b, slots, tag}, rank)

def Rk.dict.l(+k: U32, +dd: Nat, +b: Nat, slots: Array<ST.SSlot>, +tag: U32, ls: RLS) -> ST.Dict & Array<U32>:
  match ls:
    case RLS{strs, fr, bl}:
      Rk.dict.r(k, dd, b, slots, tag, Rk.ranks(k, dd, 0, strs, fr, bl))

def Rk.dict(d: ST.Dict) -> ST.Dict & Array<U32>:
  match d:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      Rk.dict.l(k, dd, b, slots, tag, Rl.go(~(s => H.Hc.blen(s, 0)), U32.to_nat(k), 0, RLS{strs, K.Kernel.iota(k, dd), Array.new(U32, dd, 0)}))
