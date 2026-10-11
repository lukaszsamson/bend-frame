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
#              caller that wants to probe it (the join, W2.4); a caller that does not simply drops them.
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
# Callers (W2.3): group_by keys and unique (src/groupby.bend Grp.enc.s / Grp.enc.sk: Hc.code.h, ids
# from 1), Raw n_unique (src/eval.bend Eval.nu.str: Hc.code.h, the entry count), the sort words of a
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
