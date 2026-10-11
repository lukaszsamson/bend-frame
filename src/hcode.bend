# src/hcode.bend -- the flat distinct-key coder for string columns. DESIGN.md 17.3.1 (D5, v0.2 W2.1).
#
#   Hc.code(~hash, +n, +d, +first, a) -> HC{next, a, hs, rp, ids, codes, fr, bl}
#
# Codes the first n rows of `a` (Array<String>, 2^d slots, d >= depth_for(n)) by first appearance:
#   codes[i] = first + (the number of distinct strings among rows 0..i-1 that differ from row i's
#              and first appeared before it), i.e. exactly v0.1 Sort.str_codes' codes (ids from `first`,
#              group_by 1, unique / ranks 0); rows >= n and slots >= next - first hold 0;
#   next     = first + the number of distinct strings (the next free id);
#   fr[e]    = the first row of entry e = id - first (the representative row; e < next - first);
#   bl[e]    = the UTF-8 byte length of entry e, from the SAME walk that hashes the row (the hash
#              template answers HB{h, b}; a template that does not count bytes answers b = 0 and
#              then bl is all 0: the rank stage, src/ranks.bend, needs real lengths);
#   a        = the rows, handed back untouched (borrow-and-return: the caller keeps ownership);
#   hs, rp, ids = the open-addressing table (hash, first row + 1, id), 2^b slots, handed back for a
#              caller that wants to probe it; a caller that does not simply drops them. (The join
#              probes Hc.code.pk's table instead, end of this file: W2.4 measured why.)
#
# The table: three Array<U32> of 2^b slots, b = ceil(log2(max(2n, 2))) (at most 24 at the row cap
# 2^23, DESIGN 15.8): hs[j] the key's hash, rp[j] its first row + 1 (0 = empty), ids[j] its id.
# NO string is stored: a probe compares the stored hash and walks the strings (the representative
# row rp[j] - 1 against the current row, a tail-recursive borrowed code-point walk with early exit)
# only on a hash HIT; a hash match never decides equality. Load <= 1/2 for any input (every row
# distinct at worst): presized once, never grown, never rehashed. Slot = the top b bits of
# h * 2654435769 (the same Fibonacci slot as ST.Ix.slot); linear probing, wrapping.
#
# Empty / null: "" is a key like any other (a Raw null slot holds "", so null rows get the code of
# "" and the caller applies validity afterwards, DESIGN 17.3.1). n = 0 answers next = first, touches
# no slot, allocates the tables of 2 slots and the three result arrays.
# Capacity: n <= 2^d and n <= 2^30 (the row cap is 2^23; the caller has checked it).
#
# Probe exhaustion: fuel 2^b. Unreachable: an empty slot exists while distinct keys <= n <= 2^(b-1).
# On exhaustion the probe answers the slot it stopped at, like ST.Ix.seek; correctness rests on the
# hypothesis "the probe for s stops at a slot that is empty or holds s" (LAWS.Probe's shape), stated
# for THIS table and not proven (tested-only, DESIGN 17.6).
#
# The hash is a TEMPLATE `~hash: String -> HB` so a test can instantiate a constant hash (every
# probe collides) and exercise the comparison path. Hc.hash = FNV-1a over the code points (the
# function ST.Dict uses: ST.Str.hash) plus the UTF-8 byte count, in one walk.
#
# Cost (every row walks its cons string once for the hash, a hit walks two more): the cons-string
# walk is inherent while rows are Array<String> (DESIGN 17.1.5: 2-4 ns per code point); the probe
# loop itself allocates nothing per row (the table state rides the spin loop's registers).
#
# Callers (W2.3): group_by keys and unique (src/groupby.bend Grp.enc.s / Grp.enc.sk: Hc.code.pk, ids
# + 1), Raw n_unique (src/eval.bend Eval.nu.str: Hc.code.pk, the entry count), the sort words of a
# Raw column (src/ranks.bend Rk.words: Hc.code.fnv, ids from 0, then the rank stage).
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; pairs taken apart in the next
# helper's parameter; templates ~T.
import Base
import ./kernels.bend as K
import ./strs.bend as ST

# a hash walk's answer: the hash and the UTF-8 byte length of the string (0 when not counted)
type HB is Data:
  HB{h: U32, b: U32}

# the result: see the header
type HC is Type:
  HC{next: U32, a: Array<String>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, codes: Array<U32>, fr: Array<U32>, bl: Array<U32>}

# a slot looked at: the tables back; more = probe on; emp = the slot is empty; id; the slot
type LK is Type:
  LK{a: Array<String>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, more: Bool, emp: Bool, id: U32, j: U32}

# ---- the hash walks --------------------------------------------------------------------------

# the UTF-8 length of code point c (1 to 4; a code point above U+10FFFF counts as 4: the rank
# stage detects those itself, DESIGN 17.3.2)
def Hc.u8(+c: U32) -> U32:
  U32.add(U32.add(1, Bool.to_u32(U32.is_ge(c, 128))), U32.add(Bool.to_u32(U32.is_ge(c, 2048)), Bool.to_u32(U32.is_ge(c, 65536))))

# FNV-1a over the code points and the byte count, one tail loop
def Hc.fnv(s: String, +h: U32, +b: U32) -> HB:
  match s:
    case SNil{}:
      HB{h, b}
    case SCon{Chr{+c}, t}:
      Hc.fnv(t, U32.mul(U32.xor(h, c), 16777619), U32.add(b, Hc.u8(c)))

# the default template: ST.Str.hash and the byte length
def Hc.hash(s: String) -> HB:
  Hc.fnv(s, 2166136261, 0)

# ST.Str.hash alone (b = 0): the coder without entry byte lengths
def Hc.hash.h(s: String) -> HB:
  HB{ST.Str.hash(s), 0}

# the byte length alone (tail loop)
def Hc.blen(s: String, +b: U32) -> U32:
  match s:
    case SNil{}:
      b
    case SCon{Chr{c}, t}:
      Hc.blen(t, U32.add(b, Hc.u8(c)))

# a constant hash with the true byte length: the forced-collision template of the tests
def Hc.hash.const(+h: U32, s: String) -> HB:
  HB{h, Hc.blen(s, 0)}

# ---- the probe -------------------------------------------------------------------------------

# tail-recursive code-point equality (ok: the prefix so far is equal)
def Hc.eq(x: String, y: String, ok: Bool) -> Bool:
  match x y ok:
    case SNil{} SNil{} k:
      k
    case SCon{Chr{c}, s} SCon{Chr{d}, t} True{}:
      Hc.eq(s, t, U32.is_eq(c, d))
    case _ _ _:
      False{}

def Hc.cmp.k(+s: String, r: Array<String> & String) -> Array<String> & Bool:
  (a, t) = r
  (a, Hc.eq(t, s, True{}))

# the representative row r against s, only on a hash hit
def Hc.cmp(hit: Bool, a: Array<String>, +r: U32, +s: String) -> Array<String> & Bool:
  match hit:
    case True{}:
      Hc.cmp.k(s, Array.get(String, a, r))
    case False{}:
      (a, False{})

def Hc.look.d(+e: Bool, +j: U32, hs: Array<U32>, rp: Array<U32>, r3: Array<U32> & U32, ra: Array<String> & Bool) -> LK:
  (ids, +id) = r3
  (a, same) = ra
  LK{a, hs, rp, ids, Bool.and(Bool.not(e), Bool.not(same)), e, id, j}

def Hc.look.c(+h: U32, +j: U32, +s: String, a: Array<String>, ids: Array<U32>, r1: Array<U32> & U32, r2: Array<U32> & U32) -> LK:
  (hs, +x) = r1
  (rp, +r) = r2
  +e = U32.is_eq(r, 0)
  Hc.look.d(e, j, hs, rp, Array.get(U32, ids, j), Hc.cmp(Bool.and(Bool.not(e), U32.is_eq(x, h)), a, U32.sub(r, 1), s))

# look at slot j
def Hc.look(+h: U32, +j: U32, +s: String, a: Array<String>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>) -> LK:
  Hc.look.c(h, j, s, a, ids, Array.get(U32, hs, j), Array.get(U32, rp, j))

# linear probing until an empty slot or the key (fuel 2^b: exhaustion is unreachable at load <= 1/2)
def Hc.seek(n: Nat, lk: LK, +h: U32, +s: String, +mask: U32) -> LK:
  match n lk:
    case 0n other:
      other
    case _ LK{a, hs, rp, ids, False{}, e, id, j}:
      LK{a, hs, rp, ids, False{}, e, id, j}
    case 1n+p LK{a, hs, rp, ids, True{}, e, id, +j}:
      Hc.seek(p, Hc.look(h, U32.and(U32.inc(j), mask), s, a, hs, rp, ids), h, s, mask)

# the row's code: a new entry (empty slot: the table, codes, first rows and byte lengths grow) or
# the matched entry's id
def Hc.put(+h: U32, +bn: U32, +i: U32, +first: U32, +next: U32, out: Array<U32>, fr: Array<U32>, bls: Array<U32>, lk: LK) -> HC:
  match lk:
    case LK{a, hs, rp, ids, more, True{}, id, +j}:
      +e = U32.sub(next, first)
      HC{U32.inc(next), a, Array.set(U32, hs, j, h), Array.set(U32, rp, j, U32.inc(i)), Array.set(U32, ids, j, next), Array.set(U32, out, i, next), Array.set(U32, fr, e, i), Array.set(U32, bls, e, bn)}
    case LK{a, hs, rp, ids, more, False{}, +id, j}:
      HC{next, a, hs, rp, ids, Array.set(U32, out, i, id), fr, bls}

def Hc.slot(+h: U32, +b: Nat) -> U32:
  U32.shrn(U32.mul(h, 2654435769), Nat.sub(32n, b))

def Hc.row.h(+i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, +next: U32, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>, bls: Array<U32>, +s: String, a: Array<String>, hb: HB) -> HC:
  match hb:
    case HB{+h, +bn}:
      Hc.put(h, bn, i, first, next, out, fr, bls, Hc.seek(fuel, Hc.look(h, Hc.slot(h, b), s, a, hs, rp, ids), h, s, mask))

def Hc.row.s(~hash: String -> HB, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, +next: U32, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>, bls: Array<U32>, r: Array<String> & String) -> HC:
  (a, +s) = r
  Hc.row.h(i, b, mask, fuel, first, next, hs, rp, ids, out, fr, bls, s, a, hash(s))

def Hc.row(~hash: String -> HB, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, st: HC) -> HC:
  match st:
    case HC{+next, a, hs, rp, ids, out, fr, bls}:
      Hc.row.s(~hash, i, b, mask, fuel, first, next, hs, rp, ids, out, fr, bls, Array.get(String, a, i))

def Hc.go(~hash: String -> HB, n: Nat, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, st: HC) -> HC:
  match n:
    case 0n:
      st
    case 1n+p:
      Hc.go(~hash, p, U32.inc(i), b, mask, fuel, first, Hc.row(~hash, i, b, mask, fuel, first, st))

# the coder (see the header). `d`: the depth of `a` (and of every per-row / per-entry result).
def Hc.code(~hash: String -> HB, +n: U32, +d: Nat, +first: U32, a: Array<String>) -> HC:
  +b = K.Kernel.depth_for(U32.max(U32.add(n, n), 2))
  +size = U32.shln(1, b)
  Hc.go(~hash, U32.to_nat(n), 0, b, U32.sub(size, 1), U32.to_nat(size), first, HC{first, a, Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, d, 0), Array.new(U32, d, 0), Array.new(U32, d, 0)})

# the coder with the default template (FNV-1a and byte lengths in one walk)
def Hc.code.fnv(+n: U32, +d: Nat, +first: U32, a: Array<String>) -> HC:
  Hc.code(~(s => Hc.hash(s)), n, d, first, a)

# the coder without byte lengths (ST.Str.hash only; bl is all 0): group_by / unique / n_unique need
# only the codes and the first rows, and skip the byte count of the walk (about 0.5-0.9 ns per code
# point, measured on the all-equal shape)
def Hc.code.h(+n: U32, +d: Nat, +first: U32, a: Array<String>) -> HC:
  Hc.code(~(s => Hc.hash.h(s)), n, d, first, a)

# ---- the packed coder and its lookup (W2.4: the join's string table) -----------------------------
#
#   Hc.code.pk(~mix, +n, +d, a) -> HJ{next, a, hs, ix, codes, po, pl, pk, cur, pd}
#   Hc.find.pk(~mix, +nb, +n, +d, hs, ix, po, pl, pk, q) -> HQ{q, hs, ix, po, pl, pk, out}
#
# Why not Hc.code + a lookup that compares against the representative row: in a frame.bend program
# String is a hot type, so each cell of a cons string costs dependent cache misses (its refcount
# redirect, then the cell), and a join's build strings sit wherever the parser's allocator put
# them. A hash hit of such a lookup walks the representative row at a random place: on the 1M
# distinct-key join (90 % hits) that walk was ~1.1 s of a 1.25 s probe (measured: the same probe
# without the walk took 0.14 s). A second, sequential packing walk after Hc.code cost 0.7 s more
# (the build strings are scattered: ~50 ns per code point). So the build walks each string ONCE,
# and that one walk hashes, counts AND copies the code points into one flat word array:
#
# Hc.code.pk codes the first n rows of a (Array<String>, 2^d slots) by first appearance from 0,
# exactly as Hc.code(.., first = 0) does (same codes, same next), and answers the table and the
# DISTINCT keys flat:
#   codes[i] = the id of row i (rows >= n hold 0); next = the number of distinct strings;
#   pk[po[e] .. po[e] + pl[e]) = the code points of entry e (its first row's string), entries
#              packed in id order; cur = the total, pk has 2^pd words (grown by doubling);
#   hs[j], ix[j] = the table (2^b slots, b as Hc.code): the key's hash, entry + 1 (0 = empty);
#   a comes back untouched (every row is walked once, borrowed).
# A row's code points are written at cur before its probe; a new key keeps them (cur moves on), a
# repeated one is overwritten by the next row. Equality on a hash hit is a FLAT compare of the
# row's code points (pk[cur ..], just written) with the entry's (counts first): no cons string is
# walked twice. Hc.find.pk looks the first n rows of q up in that table (the id, 2^32 - 1 when
# absent, rows >= n hold 0): q[i] is hashed and counted by one walk, then on a hash hit compared
# (a second walk of q[i], in cache) against pk[po[e] ..], with an end bound and early exit.
#
# Hash: FNV-1a over the code points (ST.Str.hash's function), computed by the walk, then passed
# through the template ~mix (the join: identity; a test: a constant, so every probe of the table
# collides and every hit is decided by the compare). The slot, probing, load <= 1/2, fuel 2^b and
# the exhaustion hypothesis are Hc.code's (above). The code-point total must fit a U32 (the cons
# strings would take ~24 bytes per code point first). Memory, transient: 8 bytes per table slot,
# 12 per row (codes, po, pl), 4 per code point of the distinct keys (+ the doubling's copy).
# Sequential: every loop below is a flat spin loop with nothing allocated per row or per code point
# (the pk growth allocates O(log) times).

# -- the walk: hash, count, copy

# a walk's answer: the hash, the next free word, pk (with its depth)
type PW is Type:
  PW{h: U32, o: U32, pd: Nat, pk: Array<U32>}

# a pk twice as large (the first 2^pd words copied)
def Hc.grow(+pd: Nat, pk: Array<U32>) -> Array<U32>:
  K.Kernel.copy_into(~U32, U32.shln(1, pd), 0, Array.new(U32, Nat.add(pd, 1n), 0), pk)

# FNV-1a over s and pk[o ..] = its code points (fits: o < 2^pd; else pk doubles first)
def Hc.pw(s: String, +h: U32, +o: U32, +pd: Nat, fits: Bool, pk: Array<U32>) -> PW:
  match s fits:
    case SNil{} _:
      PW{h, o, pd, pk}
    case SCon{Chr{+c}, t} True{}:
      +o2 = U32.inc(o)
      Hc.pw(t, U32.mul(U32.xor(h, c), 16777619), o2, pd, U32.is_lt(o2, U32.shln(1, pd)), Array.set(U32, pk, o, c))
    case SCon{Chr{+c}, t} False{}:
      +o2 = U32.inc(o)
      +pd2 = Nat.add(pd, 1n)
      Hc.pw(t, U32.mul(U32.xor(h, c), 16777619), o2, pd2, U32.is_lt(o2, U32.shln(1, pd2)), Array.set(U32, Hc.grow(pd, pk), o, c))

# s is used after the walk, so the walk borrows it (no take per cell); then it is dropped
def Hc.pw.z(w: PW, s: String) -> PW:
  w

# FNV-1a over the code points and their count (the probe side's walk; nothing written)
def Hc.fnvc(s: String, +h: U32, +n: U32) -> HB:
  match s:
    case SNil{}:
      HB{h, n}
    case SCon{Chr{+c}, t}:
      Hc.fnvc(t, U32.mul(U32.xor(h, c), 16777619), U32.inc(n))

# -- flat equality

# pk[x], pk[y]
type G2 is Type:
  G2{pk: Array<U32>, a: U32, b: U32}

def Hc.get2.l(+a: U32, r: Array<U32> & U32) -> G2:
  (pk, +b) = r
  G2{pk, a, b}

def Hc.get2.k(+y: U32, r: Array<U32> & U32) -> G2:
  (pk, +a) = r
  Hc.get2.l(a, Array.get(U32, pk, y))

def Hc.get2(pk: Array<U32>, +x: U32, +y: U32) -> G2:
  Hc.get2.k(y, Array.get(U32, pk, x))

# pk[x .. x + n) == pk[y .. y + n) (ok: equal so far; g = the words at x and y, read ahead)
def Hc.feq(n: Nat, +x: U32, +y: U32, ok: Bool, g: G2) -> Array<U32> & Bool:
  match n ok g:
    case _ False{} G2{pk, a, b}:
      (pk, False{})
    case 0n k G2{pk, a, b}:
      (pk, k)
    case 1n+p True{} G2{pk, +a, +b}:
      +x2 = U32.inc(x)
      +y2 = U32.inc(y)
      Hc.feq(p, x2, y2, U32.is_eq(a, b), Hc.get2(pk, x2, y2))

# s against pk[o .. e): code points equal and the same count (ok: equal so far; r = (pk, pk[o]))
def Hc.peq(s: String, +o: U32, +e: U32, ok: Bool, r: Array<U32> & U32) -> Array<U32> & Bool:
  match s ok:
    case SCon{Chr{+c}, t} True{}:
      (pk, +x) = r
      +o2 = U32.inc(o)
      Hc.peq(t, o2, e, Bool.and(U32.is_eq(c, x), U32.is_lt(o, e)), Array.get(U32, pk, o2))
    case SNil{} True{}:
      (pk, x) = r
      (pk, U32.is_eq(o, e))
    case _ _:
      (pk, x) = r
      (pk, False{})

# -- the table's probe (shared by the coder and the lookup)

# a compare's answer: the arrays back, equal?
type PC is Type:
  PC{po: Array<U32>, pl: Array<U32>, pk: Array<U32>, same: Bool}

def Hc.pc.f(po: Array<U32>, pl: Array<U32>, r: Array<U32> & Bool) -> PC:
  (pk, same) = r
  PC{po, pl, pk, same}

# the key to compare (fl, x, s): fl = True a packed row (the coder: pk[x .. x + len), s unused,
# ""), fl = False a cons string s (the lookup, x unused). Passed as three parameters, not as a sum
# type: a constructor holding s would take a reference to it (a refcount bump per probe row).
def Hc.pc.s(eq: Bool, fl: Bool, +o: U32, +l: U32, +x: U32, +s: String, po: Array<U32>, pl: Array<U32>, pk: Array<U32>) -> PC:
  match eq fl:
    case True{} True{}:
      Hc.pc.f(po, pl, Hc.feq(U32.to_nat(l), o, x, True{}, Hc.get2(pk, o, x)))
    case True{} False{}:
      Hc.pc.f(po, pl, Hc.peq(s, o, U32.add(o, l), True{}, Array.get(U32, pk, o)))
    case False{} _:
      PC{po, pl, pk, False{}}

def Hc.pc.l(+len: U32, fl: Bool, +x: U32, +s: String, pk: Array<U32>, r1: Array<U32> & U32, r2: Array<U32> & U32) -> PC:
  (po, +o) = r1
  (pl, +l) = r2
  Hc.pc.s(U32.is_eq(l, len), fl, o, l, x, s, po, pl, pk)

# entry e against the key, only on a hash hit: the counts first, then the code points
def Hc.pc(hit: Bool, fl: Bool, +e: U32, +len: U32, +x: U32, +s: String, po: Array<U32>, pl: Array<U32>, pk: Array<U32>) -> PC:
  match hit:
    case True{}:
      Hc.pc.l(len, fl, x, s, pk, Array.get(U32, po, e), Array.get(U32, pl, e))
    case False{}:
      PC{po, pl, pk, False{}}

# a slot looked at: the arrays back; more = probe on; emp = the slot is empty; the entry; the slot
type LP is Type:
  LP{hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, more: Bool, emp: Bool, e: U32, j: U32}

def Hc.lp.d(+emp: Bool, +j: U32, +e: U32, hs: Array<U32>, ix: Array<U32>, pc: PC) -> LP:
  match pc:
    case PC{po, pl, pk, +same}:
      LP{hs, ix, po, pl, pk, Bool.and(Bool.not(emp), Bool.not(same)), emp, e, j}

def Hc.lp.c(+h: U32, +len: U32, +j: U32, +fl: Bool, +x: U32, +s: String, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, r1: Array<U32> & U32, r2: Array<U32> & U32) -> LP:
  (hs, +hx) = r1
  (ix, +v) = r2
  +emp = U32.is_eq(v, 0)
  +e = U32.sub(v, 1)
  Hc.lp.d(emp, j, e, hs, ix, Hc.pc(Bool.and(Bool.not(emp), U32.is_eq(hx, h)), fl, e, len, x, s, po, pl, pk))

# look at slot j
def Hc.lp(+h: U32, +len: U32, +j: U32, +fl: Bool, +x: U32, +s: String, hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>) -> LP:
  Hc.lp.c(h, len, j, fl, x, s, po, pl, pk, Array.get(U32, hs, j), Array.get(U32, ix, j))

# linear probing until an empty slot or the key (fuel 2^b: exhaustion is unreachable at load <= 1/2)
def Hc.lp.seek(n: Nat, lp: LP, +h: U32, +len: U32, +fl: Bool, +x: U32, +s: String, +mask: U32) -> LP:
  match n lp:
    case 0n other:
      other
    case _ LP{hs, ix, po, pl, pk, False{}, emp, e, j}:
      LP{hs, ix, po, pl, pk, False{}, emp, e, j}
    case 1n+p LP{hs, ix, po, pl, pk, True{}, emp, e, +j}:
      Hc.lp.seek(p, Hc.lp(h, len, U32.and(U32.inc(j), mask), fl, x, s, hs, ix, po, pl, pk), h, len, fl, x, s, mask)

# -- the packed coder

# the coder's state / result (see the header)
type HJ is Type:
  HJ{next: U32, a: Array<String>, hs: Array<U32>, ix: Array<U32>, codes: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, cur: U32, pd: Nat}

# the row's code: a new entry (empty slot: its code points stay, at cur) or the matched entry's id
def Hc.jput(+h: U32, +len: U32, +i: U32, +next: U32, +cur: U32, +pd: Nat, a: Array<String>, codes: Array<U32>, lp: LP) -> HJ:
  match lp:
    case LP{hs, ix, po, pl, pk, more, True{}, e, +j}:
      HJ{U32.inc(next), a, Array.set(U32, hs, j, h), Array.set(U32, ix, j, U32.inc(next)), Array.set(U32, codes, i, next), Array.set(U32, po, next, cur), Array.set(U32, pl, next, len), pk, U32.add(cur, len), pd}
    case LP{hs, ix, po, pl, pk, more, False{}, +e, j}:
      HJ{next, a, hs, ix, Array.set(U32, codes, i, e), po, pl, pk, cur, pd}

def Hc.jrow.w(~mix: U32 -> U32, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, +next: U32, +cur: U32, a: Array<String>, hs: Array<U32>, ix: Array<U32>, codes: Array<U32>, po: Array<U32>, pl: Array<U32>, w: PW) -> HJ:
  match w:
    case PW{+h0, +o, +pd, pk}:
      +h = mix(h0)
      +len = U32.sub(o, cur)
      Hc.jput(h, len, i, next, cur, pd, a, codes, Hc.lp.seek(fuel, Hc.lp(h, len, Hc.slot(h, b), True{}, cur, "", hs, ix, po, pl, pk), h, len, True{}, cur, "", mask))

def Hc.jrow.s(~mix: U32 -> U32, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, +next: U32, +cur: U32, +pd: Nat, hs: Array<U32>, ix: Array<U32>, codes: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, r: Array<String> & String) -> HJ:
  (a, +s) = r
  Hc.jrow.w(~mix, i, b, mask, fuel, next, cur, a, hs, ix, codes, po, pl, Hc.pw.z(Hc.pw(s, 2166136261, cur, pd, U32.is_lt(cur, U32.shln(1, pd)), pk), s))

def Hc.jrow(~mix: U32 -> U32, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, st: HJ) -> HJ:
  match st:
    case HJ{+next, a, hs, ix, codes, po, pl, pk, +cur, +pd}:
      Hc.jrow.s(~mix, i, b, mask, fuel, next, cur, pd, hs, ix, codes, po, pl, pk, Array.get(String, a, i))

# the coder's loop (a spin loop)
def Hc.jgo(~mix: U32 -> U32, n: Nat, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, st: HJ) -> HJ:
  match n:
    case 0n:
      st
    case 1n+p:
      Hc.jgo(~mix, p, U32.inc(i), b, mask, fuel, Hc.jrow(~mix, i, b, mask, fuel, st))

# the packed coder (see the header); pk starts at 8 words per row (min 16) and doubles when full
def Hc.code.pk(~mix: U32 -> U32, +n: U32, +d: Nat, a: Array<String>) -> HJ:
  +b = K.Kernel.depth_for(U32.max(U32.add(n, n), 2))
  +size = U32.shln(1, b)
  +pd = K.Kernel.depth_for(U32.max(U32.shln(n, 3n), 16))
  Hc.jgo(~mix, U32.to_nat(n), 0, b, U32.sub(size, 1), U32.to_nat(size), HJ{0, a, Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, d, 0), Array.new(U32, d, 0), Array.new(U32, d, 0), Array.new(U32, pd, 0), 0, pd})

# -- the lookup

# the lookup's state: the probe rows, the table, the entries, the ids so far
type HQ is Type:
  HQ{q: Array<String>, hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, out: Array<U32>}

def Hc.fp.put(+i: U32, q: Array<String>, out: Array<U32>, lp: LP) -> HQ:
  match lp:
    case LP{hs, ix, po, pl, pk, more, +emp, +e, j}:
      HQ{q, hs, ix, po, pl, pk, Array.set(U32, out, i, Bool.pick(U32, emp, 4294967295, e))}

def Hc.fp.row.h(~mix: U32 -> U32, +i: U32, +bt: Nat, +mask: U32, +fuel: Nat, q: Array<String>, hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, out: Array<U32>, +s: String, hb: HB) -> HQ:
  match hb:
    case HB{+h0, +len}:
      +h = mix(h0)
      Hc.fp.put(i, q, out, Hc.lp.seek(fuel, Hc.lp(h, len, Hc.slot(h, bt), False{}, 0, s, hs, ix, po, pl, pk), h, len, False{}, 0, s, mask))

def Hc.fp.row.s(~mix: U32 -> U32, +i: U32, +bt: Nat, +mask: U32, +fuel: Nat, hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, out: Array<U32>, r: Array<String> & String) -> HQ:
  (q, +s) = r
  Hc.fp.row.h(~mix, i, bt, mask, fuel, q, hs, ix, po, pl, pk, out, s, Hc.fnvc(s, 2166136261, 0))

def Hc.fp.row(~mix: U32 -> U32, +i: U32, +bt: Nat, +mask: U32, +fuel: Nat, st: HQ) -> HQ:
  match st:
    case HQ{q, hs, ix, po, pl, pk, out}:
      Hc.fp.row.s(~mix, i, bt, mask, fuel, hs, ix, po, pl, pk, out, Array.get(String, q, i))

# the lookup's loop (a spin loop: the join's probe)
def Hc.fp.go(~mix: U32 -> U32, n: Nat, +i: U32, +bt: Nat, +mask: U32, +fuel: Nat, st: HQ) -> HQ:
  match n:
    case 0n:
      st
    case 1n+p:
      Hc.fp.go(~mix, p, U32.inc(i), bt, mask, fuel, Hc.fp.row(~mix, i, bt, mask, fuel, st))

# the lookup (see the header). nb: the n Hc.code.pk was given (it fixes the table size); d: the
# depth of q and out; ~mix: the coder's.
def Hc.find.pk(~mix: U32 -> U32, +nb: U32, +n: U32, +d: Nat, hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, q: Array<String>) -> HQ:
  +bt = K.Kernel.depth_for(U32.max(U32.add(nb, nb), 2))
  +size = U32.shln(1, bt)
  Hc.fp.go(~mix, U32.to_nat(n), 0, bt, U32.sub(size, 1), U32.to_nat(size), HQ{q, hs, ix, po, pl, pk, Array.new(U32, d, 0)})
