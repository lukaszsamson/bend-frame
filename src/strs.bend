# src/strs.bend -- the storage of a Str column: Raw or Dictionary (plans/M_01.txt section 5,
# DESIGN.md 14 M4).
#
#   SRaw{data}           data: Array<String>, one string per row (today's representation)
#   SDict{codes, dict}   codes: Array<U32>, one code per row, decoded through dict.strs
#
# The dtype stays Str; codes are internal: never a categorical dtype, a lexical rank or a
# globally meaningful id. Invariants of SDict (the Dictionary variant), next to the column's
# own (len <= 2^depth, validity):
#  * every code of a row < len is < dict.k (in range);
#  * strs[0] = "" always: code 0 is the EMPTY STRING, a value like any other entry, never a
#    null marker (null is validity, never a dictionary entry). A null row holds code 0, so a
#    null row decodes to "", exactly the Raw invariant "a null slot holds the dtype default";
#    `Strs.decode` is therefore a plain gather and decode(Dictionary) is the Raw column;
#  * the entries strs[0..k) are pairwise distinct (so equal codes <=> equal strings within
#    one dictionary), and index maps every entry to its code;
#  * tag is a fingerprint of the entries in code order (FNV-1a mix of each entry's hash):
#    equal dictionaries have equal tags; equal tags are VERIFIED entry by entry before codes
#    of two columns are compared directly (Bend has no global counter to hand out unique
#    ids, so a tag cannot be an identity).
#
# The index is an open-addressing table (FNV-1a + Fibonacci slot, linear probing, load <= 1/2,
# doubled when full), not Base's Map: a Map lookup per row costs ~3x a hash probe
# (IMPLEMENTING.md "M5 sort/groupby"), and the CSV reader codes every Str cell through it.
#
# Idioms (DESIGN.md section 9): helpers above callers; a match on a parameter comes before
# any destructuring let; pairs are taken apart in the next helper's parameter; templates ~T.
import Base
import ./kernels.bend as K

# an index slot: id = code + 1, 0 = an empty slot
type SSlot is Data:
  SSlot{key: String, id: U32}

# k entries in strs (2^dd slots), the index over 2^b slots, the fingerprint
type Dict is Type:
  Dict{k: U32, dd: Nat, strs: Array<String>, b: Nat, slots: Array<SSlot>, tag: U32}

type Strs is Type:
  SRaw{data: Array<String>}
  SDict{codes: Array<U32>, dict: Dict}

def Dict.miss() -> U32:
  4294967295

# ---- strings ------------------------------------------------------------------------------

# FNV-1a over the code points (tail recursive)
def Str.fnv(s: String, +h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{c}, t}:
      Str.fnv(t, U32.mul(U32.xor(h, c), 16777619))

def Str.hash(s: String) -> U32:
  Str.fnv(s, 2166136261)

# code-point equality (Base String.eq goes through String.cmp, which rebuilds both strings)
def Str.same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SCon{Chr{x}, s} SCon{Chr{y}, t}:
      Bool.and(U32.is_eq(x, y), Str.same(s, t))
    case _ _:
      False{}

# ---- the index ----------------------------------------------------------------------------

# the top b bits of h * golden (b >= 1)
def Ix.slot(+h: U32, +b: Nat) -> U32:
  U32.shrn(U32.mul(h, 2654435769), Nat.sub(32n, b))

# keep probing while the slot holds another key
def Ix.look(+s: String, r: Array<SSlot> & SSlot) -> Array<SSlot> & Bool:
  (t, x) = r
  match x:
    case SSlot{k, +id}:
      (t, Bool.and(U32.is_ne(id, 0), Bool.not(Str.same(k, s))))

# the slot holding s, or the empty slot where it would go
def Ix.seek.go(n: Nat, r: Array<SSlot> & Bool, +s: String, +mask: U32, +i: U32) -> Array<SSlot> & U32:
  match n r:
    case 0n Tuple{t, c}:
      (t, i)
    case _ Tuple{t, False{}}:
      (t, i)
    case 1n+p Tuple{t, True{}}:
      +j = U32.and(U32.inc(i), mask)
      Ix.seek.go(p, Ix.look(s, Array.get(SSlot, t, j)), s, mask, j)

def Ix.seek(+b: Nat, slots: Array<SSlot>, +h: U32, +s: String) -> Array<SSlot> & U32:
  +size = U32.shln(1, b)
  +i = Ix.slot(h, b)
  Ix.seek.go(U32.to_nat(size), Ix.look(s, Array.get(SSlot, slots, i)), s, U32.sub(size, 1), i)

# the id (code + 1, 0 = absent) at slot i
def Ix.id.k(r: Array<SSlot> & SSlot) -> Array<SSlot> & U32:
  (t, x) = r
  match x:
    case SSlot{k, id}:
      (t, id)

def Ix.id.at(+i: U32, r: Array<SSlot> & U32) -> U32 & U32 & Array<SSlot>:
  (t, id) = r
  (id, i, t)

def Ix.id(r: Array<SSlot> & U32) -> U32 & U32 & Array<SSlot>:
  (t, +i) = r
  Ix.id.at(i, Ix.id.k(Array.get(SSlot, t, i)))

def Ix.move.k(live: Bool, +key: String, +id: U32, r: Array<SSlot> & U32) -> Array<SSlot>:
  match live:
    case True{}:
      (t, +i) = r
      Array.set(SSlot, t, i, SSlot{key, id})
    case False{}:
      (t, i) = r
      t

# re-insert one old slot into the new table
def Ix.move(+b: Nat, nt: Array<SSlot>, x: SSlot) -> Array<SSlot>:
  match x:
    case SSlot{+key, +id}:
      Ix.move.k(U32.is_ne(id, 0), key, id, Ix.seek(b, nt, Str.hash(key), key))

def Ix.grow.go(n: Nat, +i: U32, +b: Nat, nt: Array<SSlot>, r: Array<SSlot> & SSlot) -> Array<SSlot>:
  match n:
    case 0n:
      (old, x) = r
      nt
    case 1n+p:
      (old, x) = r
      +j = U32.inc(i)
      Ix.grow.go(p, j, b, Ix.move(b, nt, x), Array.get(SSlot, old, j))

# the same keys in a table of 2^(b+1) slots
def Ix.grow(+b: Nat, slots: Array<SSlot>) -> Array<SSlot>:
  Ix.grow.go(U32.to_nat(U32.shln(1, b)), 0, Nat.add(b, 1n), Array.new(SSlot, Nat.add(b, 1n), SSlot{"", 0}), Array.get(SSlot, slots, 0))

# ---- the dictionary ---------------------------------------------------------------------------

def Dict.mix(+tag: U32, +h: U32) -> U32:
  U32.mul(U32.xor(tag, h), 16777619)

# strs with room for slot k (k <= 2^dd): doubled when full
def Dict.room(full: Bool, +dd: Nat, strs: Array<String>) -> Array<String>:
  match full:
    case True{}:
      ANode{strs, Array.new(String, dd, "")}
    case False{}:
      strs

def Dict.dd(+full: Bool, +dd: Nat) -> Nat:
  Bool.pick(Nat, full, Nat.add(dd, 1n), dd)

def Dict.fit.k(big: Bool, +k: U32, +dd: Nat, strs: Array<String>, +b: Nat, slots: Array<SSlot>, +tag: U32) -> Dict:
  match big:
    case True{}:
      Dict{k, dd, strs, Nat.add(b, 1n), Ix.grow(b, slots), tag}
    case False{}:
      Dict{k, dd, strs, b, slots, tag}

def Dict.fit(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, slots: Array<SSlot>, +tag: U32) -> Dict:
  +big = U32.is_gt(U32.add(k, k), U32.shln(1, b))
  Dict.fit.k(big, k, dd, strs, b, slots, tag)

# a new entry s with code k at slot i
def Dict.add(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, +tag: U32, +h: U32, +s: String, r: Array<SSlot> & U32) -> Dict:
  (t, +i) = r
  +full = U32.is_eq(k, U32.shln(1, dd))
  Dict.fit(U32.inc(k), Dict.dd(full, dd), Array.set(String, Dict.room(full, dd, strs), k, s), b, Array.set(SSlot, t, i, SSlot{s, U32.inc(k)}), Dict.mix(tag, h))

def Dict.code.p(isnew: Bool, +k: U32, +dd: Nat, strs: Array<String>, +b: Nat, +tag: U32, +h: U32, +s: String, t: Array<SSlot>, +i: U32, +id: U32) -> Dict & U32:
  match isnew:
    case True{}:
      (Dict.add(k, dd, strs, b, tag, h, s, (t, i)), k)
    case False{}:
      (Dict{k, dd, strs, b, t, tag}, U32.sub(id, 1))

def Dict.code.k(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, +tag: U32, +h: U32, +s: String, r: U32 & U32 & Array<SSlot>) -> Dict & U32:
  (+id, +i, t) = r
  Dict.code.p(U32.is_eq(id, 0), k, dd, strs, b, tag, h, s, t, i, id)

def Dict.code.h(d: Dict, +h: U32, +s: String) -> Dict & U32:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.code.k(k, dd, strs, b, tag, h, s, Ix.id(Ix.seek(b, slots, h, s)))

# the code of s, inserting it as a new entry when absent
def Dict.code(d: Dict, +s: String) -> Dict & U32:
  Dict.code.h(d, Str.hash(s), s)

def Dict.find.k(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, +tag: U32, r: U32 & U32 & Array<SSlot>) -> Dict & U32:
  (+id, i, t) = r
  (Dict{k, dd, strs, b, t, tag}, Bool.pick(U32, U32.is_eq(id, 0), Dict.miss(), U32.sub(id, 1)))

# the code of s, or Dict.miss() when s is not an entry
def Dict.find(d: Dict, +s: String) -> Dict & U32:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.find.k(k, dd, strs, b, tag, Ix.id(Ix.seek(b, slots, Str.hash(s), s)))

def Dict.zero() -> Dict:
  Dict{0, 0n, Array.new(String, 0n, ""), 2n, Array.new(SSlot, 2n, SSlot{"", 0}), 2166136261}

def Dict.fst(r: Dict & U32) -> Dict:
  (d, c) = r
  d

# the dictionary holding only "" (code 0)
def Dict.empty() -> Dict:
  Dict.fst(Dict.code(Dict.zero(), ""))

def Dict.size(d: Dict) -> Dict & U32:
  match d:
    case Dict{+k, dd, strs, b, slots, tag}:
      (Dict{k, dd, strs, b, slots, tag}, k)

def Dict.tag(d: Dict) -> Dict & U32:
  match d:
    case Dict{k, dd, strs, b, slots, +tag}:
      (Dict{k, dd, strs, b, slots, tag}, tag)

def Dict.get.k(+k: U32, +dd: Nat, +b: Nat, slots: Array<SSlot>, +tag: U32, r: Array<String> & String) -> Dict & String:
  (strs, s) = r
  (Dict{k, dd, strs, b, slots, tag}, s)

# the entry of code c
def Dict.get(d: Dict, +c: U32) -> Dict & String:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.get.k(k, dd, b, slots, tag, Array.get(String, strs, c))

def Dict.clone.k(+k: U32, +dd: Nat, +b: Nat, +tag: U32, ss: Array<String> & Array<String>, tt: Array<SSlot> & Array<SSlot>) -> Dict & Dict:
  (s1, s2) = ss
  (t1, t2) = tt
  (Dict{k, dd, s1, b, t1, tag}, Dict{k, dd, s2, b, t2, tag})

def Dict.clone(d: Dict) -> Dict & Dict:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.clone.k(k, dd, b, tag, Array.clone(String, strs), Array.clone(SSlot, slots))

# ---- whole-dictionary maps -----------------------------------------------------------------

def Dict.rc.op(ins: Bool, dst: Dict, +s: String) -> Dict & U32:
  match ins:
    case True{}:
      Dict.code(dst, s)
    case False{}:
      Dict.find(dst, s)

def Dict.rc.put(+c: U32, out: Array<U32>, r: Dict & U32) -> Dict & Array<U32>:
  (dst, x) = r
  (dst, Array.set(U32, out, c, x))

# out[c] = code of src entry c in dst (code_all: inserted when absent, else find: miss)
def Dict.rc.step(+ins: Bool, +c: U32, s: String, st: Dict & Array<U32>) -> Dict & Array<U32>:
  (dst, out) = st
  Dict.rc.put(c, out, Dict.rc.op(ins, dst, s))

def Dict.rc.go(n: Nat, +c: U32, +ins: Bool, st: Dict & Array<U32>, r: Array<String> & String) -> Array<String> & (Dict & Array<U32>):
  match n:
    case 0n:
      (strs, s) = r
      (strs, st)
    case 1n+p:
      (strs, s) = r
      +j = U32.inc(c)
      Dict.rc.go(p, j, ins, Dict.rc.step(ins, c, s, st), Array.get(String, strs, j))

def Dict.rc.fin2(src: Dict, st: Dict & Array<U32>) -> Dict & Dict & Array<U32>:
  (dst, m) = st
  (src, dst, m)

def Dict.rc.fin(+k: U32, +dd: Nat, +b: Nat, slots: Array<SSlot>, +tag: U32, r: Array<String> & (Dict & Array<U32>)) -> Dict & Dict & Array<U32>:
  (strs, st) = r
  Dict.rc.fin2(Dict{k, dd, strs, b, slots, tag}, st)

def Dict.rc(+ins: Bool, src: Dict, dst: Dict) -> Dict & Dict & Array<U32>:
  match src:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.rc.fin(k, dd, b, slots, tag, Dict.rc.go(U32.to_nat(k), 0, ins, (dst, Array.new(U32, dd, 0)), Array.get(String, strs, 0)))

# m[c] = the code in dst of src's entry c, Dict.miss() when dst lacks it (src, dst come back)
def Dict.recode(src: Dict, dst: Dict) -> Dict & Dict & Array<U32>:
  Dict.rc(False{}, src, dst)

# dst extended by every entry of src it lacks; m[c] = the code in the extended dst of src's
# entry c (src, the extended dst and m)
def Dict.merge(src: Dict, dst: Dict) -> Dict & Dict & Array<U32>:
  Dict.rc(True{}, src, dst)

# the entries in code order are the same (a, b come back)
def Dict.same.go(n: Nat, +c: U32, acc: Bool, ra: Array<String> & String, rb: Array<String> & String) -> Array<String> & Array<String> & Bool:
  match n:
    case 0n:
      (a, x) = ra
      (b, y) = rb
      (a, b, acc)
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(c)
      Dict.same.go(p, j, Bool.and(acc, Str.same(x, y)), Array.get(String, a, j), Array.get(String, b, j))

def Dict.same.fin(+k: U32, +dd: Nat, +b: Nat, ts: Array<SSlot>, +tag: U32, +k2: U32, +dd2: Nat, +b2: Nat, ts2: Array<SSlot>, +tag2: U32, r: Array<String> & Array<String> & Bool) -> Dict & Dict & Bool:
  (a, b3, ok) = r
  (Dict{k, dd, a, b, ts, tag}, Dict{k2, dd2, b3, b2, ts2, tag2}, ok)

def Dict.same.w(x: Dict, y: Dict) -> Dict & Dict & Bool:
  match x y:
    case Dict{+k, +dd, a, +b, ts, +tag} Dict{+k2, +dd2, a2, +b2, ts2, +tag2}:
      Dict.same.fin(k, dd, b, ts, tag, k2, dd2, b2, ts2, tag2, Dict.same.go(U32.to_nat(k), 0, True{}, Array.get(String, a, 0), Array.get(String, a2, 0)))

def Dict.same.v(go: Bool, x: Dict, y: Dict) -> Dict & Dict & Bool:
  match go:
    case True{}:
      Dict.same.w(x, y)
    case False{}:
      (x, y, False{})

def Dict.same.t(rx: Dict & U32, ry: Dict & U32) -> Dict & Dict & Bool:
  (x, +tx) = rx
  (y, +ty) = ry
  Dict.same.v(U32.is_eq(tx, ty), x, y)

def Dict.same.u(eq: Bool, x: Dict, y: Dict) -> Dict & Dict & Bool:
  match eq:
    case True{}:
      Dict.same.t(Dict.tag(x), Dict.tag(y))
    case False{}:
      (x, y, False{})

def Dict.same.k(rx: Dict & U32, ry: Dict & U32) -> Dict & Dict & Bool:
  (x, +kx) = rx
  (y, +ky) = ry
  Dict.same.u(U32.is_eq(kx, ky), x, y)

# equal sizes, equal tags, then every entry compared (the tag is only a fingerprint)
def Dict.same(x: Dict, y: Dict) -> Dict & Dict & Bool:
  Dict.same.k(Dict.size(x), Dict.size(y))

# ---- order -----------------------------------------------------------------------------------

# rank[c] = the position of entry c among the entries in String order (Base Map's crit-bit
# order: code points, a prefix first; Sort.str_words ranks Raw strings by the same Map)
def Dict.rk.ins(+c: U32, m: Map<&2, U32>, s: String) -> Map<&2, U32>:
  Map.set(&2, U32, m, s, c)

def Dict.rk.go(n: Nat, +c: U32, m: Map<&2, U32>, r: Array<String> & String) -> Array<String> & Map<&2, U32>:
  match n:
    case 0n:
      (strs, s) = r
      (strs, m)
    case 1n+p:
      (strs, s) = r
      +j = U32.inc(c)
      Dict.rk.go(p, j, Dict.rk.ins(c, m, s), Array.get(String, strs, j))

def Dict.rk.put(+pos: U32, rk: Array<U32>, kv: Sigma<&2, &2, String, _ => U32>) -> Array<U32>:
  (key, v) = kv
  Array.set(U32, rk, v, pos)

def Dict.rk.list(xs: List<&2, Sigma<&2, &2, String, _ => U32>>, +pos: U32, rk: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      rk
    case kv <> t:
      Dict.rk.list(t, U32.inc(pos), Dict.rk.put(pos, rk, kv))

def Dict.rk.fin(+k: U32, +dd: Nat, +b: Nat, slots: Array<SSlot>, +tag: U32, r: Array<String> & Map<&2, U32>) -> Dict & Array<U32>:
  (strs, m) = r
  (Dict{k, dd, strs, b, slots, tag}, Dict.rk.list(Map.to_list(&2, U32, m), 0, Array.new(U32, dd, 0)))

def Dict.ranks(d: Dict) -> Dict & Array<U32>:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.rk.fin(k, dd, b, slots, tag, Dict.rk.go(U32.to_nat(k), 0, Map.new(&2, U32), Array.get(String, strs, 0)))

# ---- Strs ------------------------------------------------------------------------------------

def Strs.is_dict(s: Strs) -> Strs & Bool:
  match s:
    case SRaw{a}:
      (SRaw{a}, False{})
    case SDict{c, d}:
      (SDict{c, d}, True{})

def Strs.fst(~T: Data, r: Array<T> & Array<U32>) -> Array<T>:
  (a, x) = r
  a

def Dict.decode(+n: U32, +d: Nat, codes: Array<U32>, dict: Dict) -> Array<String>:
  match dict:
    case Dict{k, dd, strs, b, slots, tag}:
      Strs.fst(~String, K.Kernel.gather(~String, n, d, strs, codes, ""))

# the rows as strings (2^d slots, n rows): a Raw column's array, a Dictionary's gathered
def Strs.decode(+n: U32, +d: Nat, s: Strs) -> Array<String>:
  match s:
    case SRaw{a}:
      a
    case SDict{codes, dict}:
      Dict.decode(n, d, codes, dict)

def Strs.get.r(r: Array<String> & String) -> Strs & String:
  (a, x) = r
  (SRaw{a}, x)

def Strs.get.d(codes: Array<U32>, r: Dict & String) -> Strs & String:
  (dict, x) = r
  (SDict{codes, dict}, x)

def Strs.get.c(dict: Dict, r: Array<U32> & U32) -> Strs & String:
  (codes, +c) = r
  Strs.get.d(codes, Dict.get(dict, c))

# the string of row i
def Strs.get(s: Strs, +i: U32) -> Strs & String:
  match s:
    case SRaw{a}:
      Strs.get.r(Array.get(String, a, i))
    case SDict{codes, dict}:
      Strs.get.c(dict, Array.get(U32, codes, i))

def Strs.clone.r(r: Array<String> & Array<String>) -> Strs & Strs:
  (a, b) = r
  (SRaw{a}, SRaw{b})

def Strs.clone.d(cc: Array<U32> & Array<U32>, dd: Dict & Dict) -> Strs & Strs:
  (c1, c2) = cc
  (d1, d2) = dd
  (SDict{c1, d1}, SDict{c2, d2})

def Strs.clone(s: Strs) -> Strs & Strs:
  match s:
    case SRaw{a}:
      Strs.clone.r(Array.clone(String, a))
    case SDict{codes, dict}:
      Strs.clone.d(Array.clone(U32, codes), Dict.clone(dict))

def Strs.out.r(r: Array<String> & Array<U32>) -> Strs & Array<U32>:
  (a, x) = r
  (SRaw{a}, x)

def Strs.out.d(dict: Dict, r: Array<U32> & Array<U32>) -> Strs & Array<U32>:
  (c, x) = r
  (SDict{c, dict}, x)

# rows perm[0..n) into 2^d slots (the dictionary moves along); perm comes back
def Strs.gather(s: Strs, perm: Array<U32>, +n: U32, +d: Nat) -> Strs & Array<U32>:
  match s:
    case SRaw{a}:
      Strs.out.r(K.Kernel.gather(~String, n, d, a, perm, ""))
    case SDict{codes, dict}:
      Strs.out.d(dict, K.Kernel.gather(~U32, n, d, codes, perm, 0))

# the first len rows where mask = 1 into 2^d slots; mask comes back
def Strs.compact(s: Strs, mask: Array<U32>, +len: U32, +d: Nat) -> Strs & Array<U32>:
  match s:
    case SRaw{a}:
      Strs.out.r(K.Kernel.compact_keep(~String, len, d, a, mask, ""))
    case SDict{codes, dict}:
      Strs.out.d(dict, K.Kernel.compact_keep(~U32, len, d, codes, mask, 0))

# null slots (mask word 0) back to the default: "" for Raw, code 0 (= "") for a Dictionary
def Strs.fix(+n: U32, s: Strs, m: Array<U32>) -> Strs & Array<U32>:
  match s:
    case SRaw{a}:
      Strs.out.r(K.Kernel.mask_data(~String, n, a, m, ""))
    case SDict{codes, dict}:
      Strs.out.d(dict, K.Kernel.mask_data(~U32, n, codes, m, 0))

def Dict.map.k(~U: Data, +n: U32, +d: Nat, codes: Array<U32>, +z: U, r: Dict & Array<U>) -> Array<U>:
  (dict, t) = r
  Strs.fst(~U, K.Kernel.gather(~U, n, d, t, codes, z))

def Dict.map.t2(~U: Data, ~f: String -> U, +k: U32, +dd: Nat, +b: Nat, slots: Array<SSlot>, +tag: U32, ss: Array<String> & Array<String>, +z: U) -> Dict & Array<U>:
  (s1, s2) = ss
  (Dict{k, dd, s1, b, slots, tag}, K.Kernel.map(~String, ~U, ~f, k, dd, s2, z))

def Dict.map.t(~U: Data, ~f: String -> U, d: Dict, +z: U) -> Dict & Array<U>:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.map.t2(~U, ~f, k, dd, b, slots, tag, Array.clone(String, strs), z)

# out[i] = f(row i) for i < n into 2^d slots: per row for Raw, per ENTRY for a Dictionary
# (then gathered by code: a string function runs once per distinct string). s is consumed.
def Strs.map(~U: Data, ~f: String -> U, +n: U32, +d: Nat, s: Strs, +z: U) -> Array<U>:
  match s:
    case SRaw{a}:
      K.Kernel.map(~String, ~U, ~f, n, d, a, z)
    case SDict{codes, dict}:
      Dict.map.k(~U, n, d, codes, z, Dict.map.t(~U, ~f, dict, z))

def Dict.mm.g(~U: Data, +n: U32, +d: Nat, cc: Array<U32> & Array<U32>, +z: U, r: Array<U> & Array<U32>) -> Array<U> & Array<U32>:
  (c1, c2) = cc
  (t, ok) = r
  (Strs.fst(~U, K.Kernel.gather(~U, n, d, t, c1, z)), Strs.fst(~U32, K.Kernel.gather(~U32, n, d, ok, c2, 0)))

def Dict.mm.t(~U: Data, ~f: String -> Maybe<&2, U>, d: Dict, +z: U) -> Array<U> & Array<U32>:
  match d:
    case Dict{+k, +dd, strs, b, slots, tag}:
      K.Kernel.map_maybe(~String, ~U, ~f, k, dd, strs, z)

# Kernel.map_maybe over the rows (per entry for a Dictionary); answers (out, ok)
def Strs.map_maybe(~U: Data, ~f: String -> Maybe<&2, U>, +n: U32, +d: Nat, s: Strs, +z: U) -> Array<U> & Array<U32>:
  match s:
    case SRaw{a}:
      K.Kernel.map_maybe(~String, ~U, ~f, n, d, a, z)
    case SDict{codes, dict}:
      Dict.mm.g(~U, n, d, Array.clone(U32, codes), z, Dict.mm.t(~U, ~f, dict, z))

# ---- encoding a Raw array -------------------------------------------------------------------

def Enc.put(+i: U32, out: Array<U32>, r: Dict & U32) -> Dict & Array<U32>:
  (dict, c) = r
  (dict, Array.set(U32, out, i, c))

def Enc.step(+i: U32, s: String, st: Dict & Array<U32>) -> Dict & Array<U32>:
  (dict, out) = st
  Enc.put(i, out, Dict.code(dict, s))

def Enc.go(n: Nat, +i: U32, st: Dict & Array<U32>, r: Array<String> & String) -> Dict & Array<U32>:
  match n:
    case 0n:
      (a, s) = r
      st
    case 1n+p:
      (a, s) = r
      +j = U32.inc(i)
      Enc.go(p, j, Enc.step(i, s, st), Array.get(String, a, j))

def Enc.fin(r: Dict & Array<U32>) -> Strs:
  (dict, codes) = r
  SDict{codes, dict}

# the Dictionary form of n rows (2^d slots): codes in first-appearance order after "" = 0;
# a Raw null slot holds "", so it gets code 0 as the invariant wants
def Strs.encode.raw(+n: U32, +d: Nat, a: Array<String>) -> Strs:
  Enc.fin(Enc.go(U32.to_nat(n), 0, (Dict.empty(), Array.new(U32, d, 0)), Array.get(String, a, 0)))

def Strs.encode(+n: U32, +d: Nat, s: Strs) -> Strs:
  match s:
    case SRaw{a}:
      Strs.encode.raw(n, d, a)
    case SDict{c, dict}:
      SDict{c, dict}

def Strs.raw(+n: U32, +d: Nat, s: Strs) -> Strs:
  SRaw{Strs.decode(n, d, s)}

# n rows of one string (a broadcast literal) as a Dictionary
def Strs.const.k(+d: Nat, r: Dict & U32) -> Strs:
  (dict, +c) = r
  SDict{Array.new(U32, d, c), dict}

def Strs.const(+d: Nat, +s: String) -> Strs:
  Strs.const.k(d, Dict.code(Dict.empty(), s))

# a copy of the entries (k of them in 2^dd slots); the dictionary comes back
type Ents is Type:
  Ents{k: U32, dd: Nat, strs: Array<String>}

def Dict.entries.k(+k: U32, +dd: Nat, +b: Nat, slots: Array<SSlot>, +tag: U32, ss: Array<String> & Array<String>) -> Dict & Ents:
  (s1, s2) = ss
  (Dict{k, dd, s1, b, slots, tag}, Ents{k, dd, s2})

def Dict.entries(d: Dict) -> Dict & Ents:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.entries.k(k, dd, b, slots, tag, Array.clone(String, strs))

def Dict.mp.t2(~P: Data, ~U: Data, ~f: P -> String -> U, +k: U32, +dd: Nat, +b: Nat, slots: Array<SSlot>, +tag: U32, ss: Array<String> & Array<String>, +p: P, +z: U) -> Dict & Array<U>:
  (s1, s2) = ss
  (Dict{k, dd, s1, b, slots, tag}, K.Kernel.map_p(~String, ~P, ~U, ~f, k, dd, s2, p, z))

def Dict.mp.t(~P: Data, ~U: Data, ~f: P -> String -> U, d: Dict, +p: P, +z: U) -> Dict & Array<U>:
  match d:
    case Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.mp.t2(~P, ~U, ~f, k, dd, b, slots, tag, Array.clone(String, strs), p, z)

# Kernel.map_p over the rows: out[i] = f(p, row i); per ENTRY for a Dictionary, then gathered
# by code (string predicates, is_in: once per distinct string). s is consumed.
def Strs.map_p(~P: Data, ~U: Data, ~f: P -> String -> U, +n: U32, +d: Nat, s: Strs, +p: P, +z: U) -> Array<U>:
  match s:
    case SRaw{a}:
      K.Kernel.map_p(~String, ~P, ~U, ~f, n, d, a, p, z)
    case SDict{codes, dict}:
      Dict.map.k(~U, n, d, codes, z, Dict.mp.t(~P, ~U, ~f, dict, p, z))
