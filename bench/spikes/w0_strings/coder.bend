# W0 spike T1/T2 (disposable): the distinct-key coder and lexical ranks after hash coding.
#   ~/.bend/bin/bend bench/spikes/w0_strings/coder.bend -o bench/spikes/w0_strings/build/coder
#   ./build/coder [--threads N] <shape> <n> <mode>
# shape: distinct ("k" + a scrambled u32: n distinct), prefix (a 31-char shared prefix + a
#        scrambled u32: n distinct), skew (half the rows in 8 hot keys, half distinct), equal
#        (one value), low (1000 distinct)
# mode:  old     Sort.str_codes_par (today's group_by/unique coder: Base Map, 8 forked blocks)
#        oldseq  Sort.str_codes (the same Map coder, one block)
#        new     Hc.code: presized flat open addressing over three Array<U32> (hash, rep+1, id)
#        rold    Sort.str_words (today's Raw sort words: Map coder + Map.to_list ranks)
#        rnew    Hc.code, then the k distinct entries as a flat code-point buffer, merge sort of
#                the entry indices, rank map, one gather (each stage timed)
#        rmap    Hc.code, then the k distinct entries ranked through Base Map (today's way of
#                ranking, on the distinct entries only)
# The keys are generated and walked once before the clock. stdout: one JSON line; chk is an
# FNV fold of the codes (code modes) or the words (rank modes): equal chk = equal output.
import Base
import ./../../../src/kernels.bend as K
import ./../../../src/strs.bend as ST
import ./../../../src/sort.bend as SO

# ---- keys -----------------------------------------------------------------------------------

type Shape is Data:
  ShD{}
  ShP{}
  ShS{}
  ShE{}
  ShL{}
  ShU{}

def Gen.h(+i: U32) -> U32:
  U32.mul(U32.add(i, 1), 2654435761)

def Gen.skew(hot: Bool, +h: U32) -> String:
  match hot:
    case True{}:
      "hot" ++ U32.show(U32.and(U32.shrn(h, 8n), 7))
    case False{}:
      "k" ++ U32.show(h)

# tricky code points for the order: NUL, 1- to 4-byte UTF-8 boundaries, prefixes of each other
def Gen.uni.b(+j: U32) -> String:
  Bool.pick(String, U32.is_eq(j, 0), "", Bool.pick(String, U32.is_eq(j, 1), SCon{Chr{0}, SNil{}}, Bool.pick(String, U32.is_eq(j, 2), "a", Bool.pick(String, U32.is_eq(j, 3), SCon{Chr{97}, SCon{Chr{0}, SNil{}}}, Bool.pick(String, U32.is_eq(j, 4), SCon{Chr{127}, SNil{}}, Bool.pick(String, U32.is_eq(j, 5), SCon{Chr{128}, SNil{}}, Bool.pick(String, U32.is_eq(j, 6), SCon{Chr{2047}, SNil{}}, Bool.pick(String, U32.is_eq(j, 7), SCon{Chr{2048}, SNil{}}, Bool.pick(String, U32.is_eq(j, 8), SCon{Chr{65535}, SNil{}}, Bool.pick(String, U32.is_eq(j, 9), SCon{Chr{65536}, SNil{}}, Bool.pick(String, U32.is_eq(j, 10), SCon{Chr{1114111}, SNil{}}, "\u{65e5}\u{672c}")))))))))))

def Gen.uni(+i: U32) -> String:
  Gen.uni.b(U32.mod(i, 12)) ++ Gen.uni.b(U32.mod(U32.div(i, 12), 12)) ++ Bool.pick(String, U32.is_eq(U32.mod(i, 5), 0), "", U32.show(U32.mod(i, 37)))

def Gen.key(sh: Shape, +i: U32) -> String:
  match sh:
    case ShD{}:
      "k" ++ U32.show(Gen.h(i))
    case ShP{}:
      "customer_segment_internal_code_" ++ U32.show(Gen.h(i))
    case ShS{}:
      Gen.skew(U32.is_eq(U32.and(Gen.h(i), 1), 0), Gen.h(i))
    case ShE{}:
      "all_rows_hold_this_one_value"
    case ShL{}:
      "v" ++ U32.show(U32.mod(Gen.h(i), 1000))
    case ShU{}:
      Gen.uni(i)

def Gen.go(n: Nat, +i: U32, +sh: Shape, a: Array<String>) -> Array<String>:
  match n:
    case 0n:
      a
    case 1n+p:
      Gen.go(p, U32.inc(i), sh, Array.set(String, a, i, Gen.key(sh, i)))

def Str.len(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      Str.len(t, U32.inc(acc))

def shape_of(+s: String) -> Shape:
  Bool.pick(Shape, String.eq(s, "prefix"), ShP{},
  Bool.pick(Shape, String.eq(s, "skew"), ShS{},
  Bool.pick(Shape, String.eq(s, "equal"), ShE{},
  Bool.pick(Shape, String.eq(s, "low"), ShL{}, Bool.pick(Shape, String.eq(s, "uni"), ShU{}, ShD{})))))

# ---- small helpers -----------------------------------------------------------------------------

def W(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def chk(+n: U32, a: Array<U32>) -> Array<U32> & U32:
  K.Kernel.fold(~U32, ~U32, ~(acc => c => U32.mul(U32.xor(acc, c), 16777619)), n, a, 2166136261)

# ---- T1: the coder -------------------------------------------------------------------------------
# Table of 2^b slots, b = log2ceil(2n) (load <= 1/2 even when every row is distinct, so a probe
# always ends at an empty slot or a match within 2^b steps): hs[j] = the key's FNV-1a hash,
# rp[j] = the first row holding it + 1 (0 = empty), ids[j] = its first-appearance id. No string
# is stored in the table: a hash hit compares the row against its representative row in place.
# fr[id - first] = the representative row of id (the entries, for the rank stage).

type HS is Type:
  HS{next: U32, a: Array<String>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>}

# a slot looked at: the tables back; more = probe on; emp = the slot is empty; id; the slot
type LK is Type:
  LK{a: Array<String>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, more: Bool, emp: Bool, id: U32, j: U32}

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

def Hc.look(+h: U32, +j: U32, +s: String, a: Array<String>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>) -> LK:
  Hc.look.c(h, j, s, a, ids, Array.get(U32, hs, j), Array.get(U32, rp, j))

# linear probing until an empty slot or the key (fuel 2^b: exhaustion is unreachable at load < 1)
def Hc.seek(n: Nat, lk: LK, +h: U32, +s: String, +mask: U32) -> LK:
  match n lk:
    case 0n other:
      other
    case _ LK{a, hs, rp, ids, False{}, e, id, j}:
      LK{a, hs, rp, ids, False{}, e, id, j}
    case 1n+p LK{a, hs, rp, ids, True{}, e, id, +j}:
      Hc.seek(p, Hc.look(h, U32.and(U32.inc(j), mask), s, a, hs, rp, ids), h, s, mask)

def Hc.put(+h: U32, +i: U32, +next: U32, +first: U32, out: Array<U32>, fr: Array<U32>, lk: LK) -> HS:
  match lk:
    case LK{a, hs, rp, ids, more, True{}, id, +j}:
      HS{U32.inc(next), a, Array.set(U32, hs, j, h), Array.set(U32, rp, j, U32.inc(i)), Array.set(U32, ids, j, next), Array.set(U32, out, i, next), Array.set(U32, fr, U32.sub(next, first), i)}
    case LK{a, hs, rp, ids, more, False{}, +id, j}:
      HS{next, a, hs, rp, ids, Array.set(U32, out, i, id), fr}

def Hc.slot(+h: U32, +b: Nat) -> U32:
  U32.shrn(U32.mul(h, 2654435769), Nat.sub(32n, b))

def Hc.row.s(+i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, +next: U32, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>, r: Array<String> & String) -> HS:
  (a, +s) = r
  +h = ST.Str.hash(s)
  Hc.put(h, i, next, first, out, fr, Hc.seek(fuel, Hc.look(h, Hc.slot(h, b), s, a, hs, rp, ids), h, s, mask))

def Hc.row(+i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, st: HS) -> HS:
  match st:
    case HS{+next, a, hs, rp, ids, out, fr}:
      Hc.row.s(i, b, mask, fuel, first, next, hs, rp, ids, out, fr, Array.get(String, a, i))

def Hc.go(n: Nat, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, +first: U32, st: HS) -> HS:
  match n:
    case 0n:
      st
    case 1n+p:
      Hc.go(p, U32.inc(i), b, mask, fuel, first, Hc.row(i, b, mask, fuel, first, st))

# out[i] = the first-appearance id of row i (ids from `first`), the rows back
def Hc.code(+n: U32, +d: Nat, +first: U32, a: Array<String>) -> HS:
  +b = K.Kernel.depth_for(U32.max(U32.add(n, n), 2))
  +size = U32.shln(1, b)
  Hc.go(U32.to_nat(n), 0, b, U32.sub(size, 1), U32.to_nat(size), first, HS{first, a, Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, d, 0), Array.new(U32, d, 0)})

# ---- T2: the distinct entries as a flat code-point buffer -----------------------------------------

type FB is Type:
  FB{tot: U32, a: Array<String>, fr: Array<U32>, off: Array<U32>}

def Fb.len.s(+c: U32, +tot: U32, fr: Array<U32>, off: Array<U32>, r: Array<String> & String) -> FB:
  (a, s) = r
  FB{U32.add(tot, Str.len(s, 0)), a, fr, Array.set(U32, off, c, tot)}

def Fb.len.r(+c: U32, +tot: U32, a: Array<String>, off: Array<U32>, r: Array<U32> & U32) -> FB:
  (fr, +row) = r
  Fb.len.s(c, tot, fr, off, Array.get(String, a, row))

def Fb.len(n: Nat, +c: U32, st: FB) -> FB:
  match n st:
    case 0n FB{+tot, a, fr, off}:
      FB{tot, a, fr, Array.set(U32, off, c, tot)}
    case 1n+p FB{+tot, a, fr, off}:
      Fb.len(p, U32.inc(c), Fb.len.r(c, tot, a, off, Array.get(U32, fr, c)))

def Str.put(s: String, +p: U32, cps: Array<U32>) -> Array<U32>:
  match s:
    case SNil{}:
      cps
    case SCon{Chr{x}, t}:
      Str.put(t, U32.inc(p), Array.set(U32, cps, p, x))

type FC is Type:
  FC{a: Array<String>, fr: Array<U32>, off: Array<U32>, cps: Array<U32>}

def Fc.s(fr: Array<U32>, cps: Array<U32>, ro: Array<U32> & U32, r: Array<String> & String) -> FC:
  (off, +p) = ro
  (a, s) = r
  FC{a, fr, off, Str.put(s, p, cps)}

def Fc.r(+c: U32, a: Array<String>, off: Array<U32>, cps: Array<U32>, r: Array<U32> & U32) -> FC:
  (fr, +row) = r
  Fc.s(fr, cps, Array.get(U32, off, c), Array.get(String, a, row))

def Fc.go(n: Nat, +c: U32, st: FC) -> FC:
  match n st:
    case 0n other:
      other
    case 1n+p FC{a, fr, off, cps}:
      Fc.go(p, U32.inc(c), Fc.r(c, a, off, cps, Array.get(U32, fr, c)))

# ---- T2: merge sort of entry indices, comparing in the flat buffer ------------------------------------

type CK is Type:
  CK{cps: Array<U32>, stop: Bool, le: Bool}

def Cmp.look.y(+ep: Bool, +eq: Bool, +x: U32, r: Array<U32> & U32) -> CK:
  (cps, +y) = r
  CK{cps, Bool.or(Bool.or(ep, eq), U32.is_ne(x, y)), Bool.or(ep, Bool.and(Bool.not(eq), U32.is_lt(x, y)))}

def Cmp.look.x(+ep: Bool, +eq: Bool, +q: U32, r: Array<U32> & U32) -> CK:
  (cps, +x) = r
  Cmp.look.y(ep, eq, x, Array.get(U32, cps, q))

def Cmp.look(+p: U32, +pe: U32, +q: U32, +qe: U32, cps: Array<U32>) -> CK:
  Cmp.look.x(U32.is_eq(p, pe), U32.is_eq(q, qe), q, Array.get(U32, cps, p))

# entry [p, pe) <= entry [q, qe) in code-point order, a prefix first
def Cmp.go(n: Nat, +p: U32, +pe: U32, +q: U32, +qe: U32, ck: CK) -> CK:
  match n ck:
    case 0n other:
      other
    case _ CK{cps, True{}, le}:
      CK{cps, True{}, le}
    case 1n+f CK{cps, False{}, le}:
      Cmp.go(f, U32.inc(p), pe, U32.inc(q), qe, Cmp.look(U32.inc(p), pe, U32.inc(q), qe, cps))

type CR is Type:
  CR{off: Array<U32>, cps: Array<U32>, le: Bool}

def Ms.cmp.e(off: Array<U32>, ck: CK) -> CR:
  match ck:
    case CK{cps, stop, le}:
      CR{off, cps, le}

def Ms.cmp.d(+fuel: Nat, +p: U32, +pe: U32, +q: U32, cps: Array<U32>, r: Array<U32> & U32) -> CR:
  (off, +qe) = r
  Ms.cmp.e(off, Cmp.go(fuel, p, pe, q, qe, Cmp.look(p, pe, q, qe, cps)))

def Ms.cmp.c(+fuel: Nat, +p: U32, +pe: U32, +y: U32, cps: Array<U32>, r: Array<U32> & U32) -> CR:
  (off, +q) = r
  Ms.cmp.d(fuel, p, pe, q, cps, Array.get(U32, off, U32.inc(y)))

def Ms.cmp.b(+fuel: Nat, +p: U32, +y: U32, cps: Array<U32>, r: Array<U32> & U32) -> CR:
  (off, +pe) = r
  Ms.cmp.c(fuel, p, pe, y, cps, Array.get(U32, off, y))

def Ms.cmp.a(+fuel: Nat, +x: U32, +y: U32, cps: Array<U32>, r: Array<U32> & U32) -> CR:
  (off, +p) = r
  Ms.cmp.b(fuel, p, y, cps, Array.get(U32, off, U32.inc(x)))

def Ms.cmp(both: Bool, +fuel: Nat, +x: U32, +y: U32, off: Array<U32>, cps: Array<U32>) -> CR:
  match both:
    case True{}:
      Ms.cmp.a(fuel, x, y, cps, Array.get(U32, off, x))
    case False{}:
      CR{off, cps, True{}}

type MP is Type:
  MP{i: U32, ie: U32, j: U32, je: U32, src: Array<U32>, dst: Array<U32>, off: Array<U32>, cps: Array<U32>}

# a new pair of runs once both runs of the last one are used up
def Ms.refill(+w: U32, +k: U32, mp: MP) -> MP:
  match mp:
    case MP{+i, +ie, +j, +je, src, dst, off, cps}:
      +done = Bool.and(U32.is_eq(i, ie), U32.is_eq(j, je))
      +nie = W(done, U32.min(U32.add(je, w), k), ie)
      MP{W(done, je, i), nie, W(done, nie, j), W(done, U32.min(U32.add(nie, w), k), je), src, dst, off, cps}

def Ms.put(+o: U32, +hasl: Bool, +i: U32, +ie: U32, +j: U32, +je: U32, +x: U32, +y: U32, src: Array<U32>, dst: Array<U32>, cr: CR) -> MP:
  match cr:
    case CR{off, cps, +lc}:
      +le = Bool.and(hasl, lc)
      MP{W(le, U32.inc(i), i), ie, W(le, j, U32.inc(j)), je, src, Array.set(U32, dst, o, W(le, x, y)), off, cps}

def Ms.step.y(+o: U32, +fuel: Nat, +i: U32, +ie: U32, +j: U32, +je: U32, +x: U32, dst: Array<U32>, off: Array<U32>, cps: Array<U32>, r: Array<U32> & U32) -> MP:
  (src, +y) = r
  +hasl = U32.is_lt(i, ie)
  +hasr = U32.is_lt(j, je)
  Ms.put(o, hasl, i, ie, j, je, x, y, src, dst, Ms.cmp(Bool.and(hasl, hasr), fuel, x, y, off, cps))

def Ms.step.x(+o: U32, +fuel: Nat, +i: U32, +ie: U32, +j: U32, +je: U32, dst: Array<U32>, off: Array<U32>, cps: Array<U32>, r: Array<U32> & U32) -> MP:
  (src, +x) = r
  Ms.step.y(o, fuel, i, ie, j, je, x, dst, off, cps, Array.get(U32, src, j))

def Ms.step(+o: U32, +fuel: Nat, mp: MP) -> MP:
  match mp:
    case MP{+i, +ie, +j, +je, src, dst, off, cps}:
      Ms.step.x(o, fuel, i, ie, j, je, dst, off, cps, Array.get(U32, src, i))

def Ms.go(n: Nat, +o: U32, +w: U32, +k: U32, +fuel: Nat, mp: MP) -> MP:
  match n:
    case 0n:
      mp
    case 1n+p:
      Ms.go(p, U32.inc(o), w, k, fuel, Ms.step(o, fuel, Ms.refill(w, k, mp)))

type MS is Type:
  MS{src: Array<U32>, dst: Array<U32>, off: Array<U32>, cps: Array<U32>}

def Ms.swap(mp: MP) -> MS:
  match mp:
    case MP{i, ie, j, je, src, dst, off, cps}:
      MS{dst, src, off, cps}

def Ms.pass(+w: U32, +k: U32, +fuel: Nat, ms: MS) -> MS:
  match ms:
    case MS{src, dst, off, cps}:
      Ms.swap(Ms.go(U32.to_nat(k), 0, w, k, fuel, MP{0, 0, 0, 0, src, dst, off, cps}))

def Ms.sort(n: Nat, go: Bool, +w: U32, +k: U32, +fuel: Nat, ms: MS) -> MS:
  match n go:
    case _ False{}:
      ms
    case 0n True{}:
      ms
    case 1n+p True{}:
      Ms.sort(p, U32.is_lt(U32.add(w, w), k), U32.add(w, w), k, fuel, Ms.pass(w, k, fuel, ms))

# rk[perm[p]] = p
def Rk.go(n: Nat, +p: U32, rk: Array<U32>, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (perm, x) = r
      rk
    case 1n+f:
      (perm, +x) = r
      Rk.go(f, U32.inc(p), Array.set(U32, rk, x, p), Array.get(U32, perm, U32.inc(p)))

# ---- T2 (alternative): ranks by radix refinement over packed UTF-8 ----------------------------------
# The k entries packed big-endian, 4 UTF-8 bytes per word (UTF-8 byte order is code point order).
# Round r sorts every entry stably by (group, word 2r, word 2r+1, min(bytes left, 8)) with four
# Radix.sort calls (LSD: last key first), then splits the groups; it stops when no two neighbours
# tie (distinct entries end in singleton groups). Rounds = (longest common prefix) / 8 + 1.

def U8.len(+c: U32) -> U32:
  W(U32.is_lt(c, 128), 1, W(U32.is_lt(c, 2048), 2, W(U32.is_lt(c, 65536), 3, 4)))

def Str.blen(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      Str.blen(t, U32.add(acc, U8.len(c)))

# pass 1: byte lengths and word offsets of the entries
type RB is Type:
  RB{tot: U32, mx: U32, a: Array<String>, fr: Array<U32>, bl: Array<U32>, wo: Array<U32>}

def Rb.s(+c: U32, +tot: U32, +mx: U32, fr: Array<U32>, bl: Array<U32>, wo: Array<U32>, r: Array<String> & String) -> RB:
  (a, s) = r
  +n = Str.blen(s, 0)
  RB{U32.add(tot, U32.div(U32.add(n, 3), 4)), U32.max(mx, n), a, fr, Array.set(U32, bl, c, n), Array.set(U32, wo, c, tot)}

def Rb.r(+c: U32, +tot: U32, +mx: U32, a: Array<String>, bl: Array<U32>, wo: Array<U32>, r: Array<U32> & U32) -> RB:
  (fr, +row) = r
  Rb.s(c, tot, mx, fr, bl, wo, Array.get(String, a, row))

def Rb.go(n: Nat, +c: U32, st: RB) -> RB:
  match n st:
    case 0n other:
      other
    case 1n+p RB{+tot, +mx, a, fr, bl, wo}:
      Rb.go(p, U32.inc(c), Rb.r(c, tot, mx, a, bl, wo, Array.get(U32, fr, c)))

# pass 2: the bytes, big-endian into words (every byte rewrites its word: no flush)
type PB is Type:
  PB{pk: Array<U32>, w: U32, acc: U32, j: U32}

def Pb.put(+b: U32, st: PB) -> PB:
  match st:
    case PB{pk, +w, +acc, +j}:
      +acc2 = U32.add(acc, U32.mul(b, W(U32.is_eq(j, 0), 16777216, W(U32.is_eq(j, 1), 65536, W(U32.is_eq(j, 2), 256, 1)))))
      +full = U32.is_eq(j, 3)
      PB{Array.set(U32, pk, w, acc2), U32.add(w, Bool.to_u32(full)), W(full, 0, acc2), U32.and(U32.inc(j), 3)}

def Pb.cont(+c: U32, +k: U32) -> U32:
  U32.add(128, U32.and(U32.div(c, k), 63))

def Pb.cp.k(+one: Bool, +two: Bool, +three: Bool, +c: U32, st: PB) -> PB:
  match one:
    case True{}:
      Pb.put(c, st)
    case False{}:
      match two:
        case True{}:
          Pb.put(Pb.cont(c, 1), Pb.put(U32.add(192, U32.div(c, 64)), st))
        case False{}:
          match three:
            case True{}:
              Pb.put(Pb.cont(c, 1), Pb.put(Pb.cont(c, 64), Pb.put(U32.add(224, U32.div(c, 4096)), st)))
            case False{}:
              Pb.put(Pb.cont(c, 1), Pb.put(Pb.cont(c, 64), Pb.put(Pb.cont(c, 4096), Pb.put(U32.add(240, U32.div(c, 262144)), st))))

def Pb.cp(+c: U32, st: PB) -> PB:
  Pb.cp.k(U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536), c, st)

def Str.u8(s: String, st: PB) -> PB:
  match s:
    case SNil{}:
      st
    case SCon{Chr{c}, t}:
      Str.u8(t, Pb.cp(c, st))

type RF is Type:
  RF{a: Array<String>, fr: Array<U32>, wo: Array<U32>, pk: Array<U32>}

def Rf.fin(a: Array<String>, fr: Array<U32>, wo: Array<U32>, pb: PB) -> RF:
  match pb:
    case PB{pk, w, acc, j}:
      RF{a, fr, wo, pk}

def Rf.s(fr: Array<U32>, pk: Array<U32>, ro: Array<U32> & U32, r: Array<String> & String) -> RF:
  (wo, +w) = ro
  (a, s) = r
  Rf.fin(a, fr, wo, Str.u8(s, PB{pk, w, 0, 0}))

def Rf.r(+c: U32, a: Array<String>, wo: Array<U32>, pk: Array<U32>, r: Array<U32> & U32) -> RF:
  (fr, +row) = r
  Rf.s(fr, pk, Array.get(U32, wo, c), Array.get(String, a, row))

def Rf.go(n: Nat, +c: U32, st: RF) -> RF:
  match n st:
    case 0n other:
      other
    case 1n+p RF{a, fr, wo, pk}:
      Rf.go(p, U32.inc(c), Rf.r(c, a, wo, pk, Array.get(U32, fr, c)))

# the rounds
type RX is Type:
  RX{wo: Array<U32>, bl: Array<U32>, pk: Array<U32>, gid: Array<U32>}

type KK is Data:
  KG{}
  KW1{}
  KW2{}
  KL{}

def Rx.word.k(+j: U32, +bl: U32, wo2: Array<U32>, bl2: Array<U32>, gid: Array<U32>, r: Array<U32> & U32) -> RX & U32:
  (pk2, +x) = r
  (RX{wo2, bl2, pk2, gid}, W(U32.is_lt(j, U32.div(U32.add(bl, 3), 4)), x, 0))

def Rx.word.b(+j: U32, pk: Array<U32>, gid: Array<U32>, ro: Array<U32> & U32, rb: Array<U32> & U32) -> RX & U32:
  (wo2, +o) = ro
  (bl3, +bl) = rb
  Rx.word.k(j, bl, wo2, bl3, gid, Array.get(U32, pk, U32.add(o, j)))

# word j of entry e (0 past its end)
def Rx.word(+e: U32, +j: U32, rx: RX) -> RX & U32:
  match rx:
    case RX{wo, bl, pk, gid}:
      Rx.word.b(j, pk, gid, Array.get(U32, wo, e), Array.get(U32, bl, e))

def Rx.blen.k(wo: Array<U32>, pk: Array<U32>, gid: Array<U32>, +r: U32, rb: Array<U32> & U32) -> RX & U32:
  (bl, +n) = rb
  +left = W(U32.is_gt(n, U32.mul(r, 8)), U32.sub(n, U32.mul(r, 8)), 0)
  (RX{wo, bl, pk, gid}, U32.min(left, 8))

def Rx.gid.k(wo: Array<U32>, bl: Array<U32>, pk: Array<U32>, rg: Array<U32> & U32) -> RX & U32:
  (gid, +g) = rg
  (RX{wo, bl, pk, gid}, g)

def Rx.key(kk: KK, +e: U32, +r: U32, rx: RX) -> RX & U32:
  match kk rx:
    case KG{} RX{wo, bl, pk, gid}:
      Rx.gid.k(wo, bl, pk, Array.get(U32, gid, e))
    case KW1{} other:
      Rx.word(e, U32.mul(r, 2), other)
    case KW2{} other:
      Rx.word(e, U32.inc(U32.mul(r, 2)), other)
    case KL{} RX{wo, bl, pk, gid}:
      Rx.blen.k(wo, pk, gid, r, Array.get(U32, bl, e))

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
      Rx.sorted.k(rx, SO.Radix.sort(k, kd, (ws, perm)))

def Rx.by(+kk: KK, +k: U32, +kd: Nat, +r: U32, st: RX & Array<U32>) -> RX & Array<U32>:
  (rx, perm) = st
  Rx.sorted(k, kd, Rx.keys(U32.to_nat(k), 0, kk, r, KS{rx, Array.new(U32, kd, 0)}, Array.get(U32, perm, 0)))

# regroup: equal (group, w1, w2, left) neighbours stay together; new group id = its first position
type RG is Type:
  RG{rx: RX, ng: Array<U32>, pg: U32, p1: U32, p2: U32, pl: U32, start: U32, ties: U32}

def Rg.put(+p: U32, ng: Array<U32>, +e: U32, +pg: U32, +p1: U32, +p2: U32, +pl: U32, +start: U32, +ties: U32, +g: U32, +x1: U32, +x2: U32, rl: RX & U32) -> RG:
  (rx, +xl) = rl
  +same = Bool.and(U32.is_gt(p, 0), Bool.and(Bool.and(U32.is_eq(g, pg), U32.is_eq(x1, p1)), Bool.and(U32.is_eq(x2, p2), U32.is_eq(xl, pl))))
  +st2 = W(same, start, p)
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
    case RG{RX{wo, bl, pk, gid}, ng, pg, p1, p2, pl, start, +ties}:
      RR{RX{wo, bl, pk, ng}, perm, ties, U32.inc(rounds)}

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

# ---- drivers ------------------------------------------------------------------------------------

def pr(+mode: String, +shape: String, +n: U32, +k: U32, +chars: U32, +ms: Nat, +x: U32, +extra: String) -> IO(Unit):
  IO.print("{\"spike\":\"coder\",\"mode\":\"" ++ mode ++ "\",\"shape\":\"" ++ shape ++ "\",\"n\":" ++ U32.show(n) ++ ",\"k\":" ++ U32.show(k) ++ ",\"chars\":" ++ U32.show(chars) ++ ",\"ms\":" ++ Nat.show(ms) ++ ",\"chk\":" ++ U32.show(x) ++ extra ++ "}")

# the length of row 0, read after the last clock: the rows stay alive until then (freeing 1M
# strings inside a timed region would be timed too)
def keep.k(r: Array<String> & String) -> U32:
  (a, s) = r
  Str.len(s, 0)

def keep(a: Array<String>) -> String:
  ",\"keep\":" ++ U32.show(keep.k(Array.get(String, a, 0)))

def fin.ck(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, +t1: Nat, +k: U32, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (codes, +x) = r
  pr(mode, shape, n, k, chars, Nat.sub(t1, t0), x, keep(a))

def fin.cs(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, +k: U32, a: Array<String>) -> IO(Unit):
  fin.ck(mode, shape, n, chars, t0, t1, k, a, chk(n, codes))

# old coders: (strings, codes, CS{map, next})
def run.old.k(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, r: Array<String> & Array<U32> & SO.CS) -> IO(Unit):
  (strs, codes, cs) = r
  match cs:
    case SO.CS{m, +k}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        fin.cs(mode, shape, n, chars, t0, t1, codes, k, strs)

def run.new.k(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, st: HS) -> IO(Unit):
  match st:
    case HS{+next, a, hs, rp, ids, out, fr}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        fin.cs(mode, shape, n, chars, t0, t1, out, next, a)

def run.rold.k(+shape: String, +n: U32, +chars: U32, +t0: Nat, w: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    fin.cs("rold", shape, n, chars, t0, t1, w, 0, Array.new(String, 0n, ""))

# rnew stages
def rnew.out(+shape: String, +n: U32, +chars: U32, +k: U32, +tot: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +t4: Nat, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (w, +x) = r
  pr("rnew", shape, n, k, chars, Nat.sub(t4, t0), x, keep(a) ++ ",\"code_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"flat_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"sort_ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ ",\"rank_ms\":" ++ Nat.show(Nat.sub(t4, t3)) ++ ",\"ent_chars\":" ++ U32.show(tot))

def rnew.fin(+shape: String, +n: U32, +chars: U32, +k: U32, +tot: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, a: Array<String>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (w, codes) = r
  do IO<Unit>:
    t4 : Nat <- IO.now()
    rnew.out(shape, n, chars, k, tot, t0, t1, t2, t3, t4, a, chk(n, w))

def rnew.rank(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +tot: U32, +t0: Nat, +t1: Nat, +t2: Nat, a: Array<String>, codes: Array<U32>, ms: MS) -> IO(Unit):
  match ms:
    case MS{perm, dst, off, cps}:
      do IO<Unit>:
        t3 : Nat <- IO.now()
        rnew.fin(shape, n, chars, k, tot, t0, t1, t2, t3, a, K.Kernel.gather(~U32, n, d, Rk.go(U32.to_nat(k), 0, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0), Array.get(U32, perm, 0)), codes, 0))

def rnew.sort(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, fc: FC, +tot: U32) -> IO(Unit):
  match fc:
    case FC{a, fr, off, cps}:
      +kd = K.Kernel.depth_for(U32.max(k, 1))
      do IO<Unit>:
        t2 : Nat <- IO.now()
        rnew.rank(shape, n, d, chars, k, tot, t0, t1, t2, a, codes, Ms.sort(32n, U32.is_lt(1, k), 1, k, U32.to_nat(U32.add(tot, 2)), MS{K.Kernel.iota(k, kd), Array.new(U32, kd, 0), off, cps}))

def rnew.flat(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, fb: FB) -> IO(Unit):
  match fb:
    case FB{+tot, a, fr, off}:
      rnew.sort(shape, n, d, chars, k, t0, t1, codes, Fc.go(U32.to_nat(k), 0, FC{a, fr, off, Array.new(U32, K.Kernel.depth_for(U32.max(tot, 1)), 0)}), tot)

def rnew.k(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, st: HS) -> IO(Unit):
  match st:
    case HS{+k, a, hs, rp, ids, out, fr}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        rnew.flat(shape, n, d, chars, k, t0, t1, out, Fb.len(U32.to_nat(k), 0, FB{0, a, fr, Array.new(U32, K.Kernel.depth_for(U32.inc(k)), 0)}))

# ---- T6: hashing every row, cons String vs a flat UTF-8 buffer (offsets + packed words) -----------

def T6.cons(+n: U32, a: Array<String>) -> Array<String> & U32:
  K.Kernel.fold(~String, ~U32, ~(acc => s => U32.xor(acc, ST.Str.hash(s))), n, a, 0)

# FNV-1a over the words [o, o + nw) (read-next)
def T6.fh(f: Nat, +o: U32, +h: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match f:
    case 0n:
      (pk, x) = r
      (pk, h)
    case 1n+p:
      (pk, +x) = r
      T6.fh(p, U32.inc(o), U32.mul(U32.xor(h, x), 16777619), Array.get(U32, pk, U32.inc(o)))

type T6S is Type:
  T6S{acc: U32, wo: Array<U32>, bl: Array<U32>, pk: Array<U32>}

def T6.row.k(+acc: U32, wo: Array<U32>, bl: Array<U32>, r: Array<U32> & U32) -> T6S:
  (pk, +h) = r
  T6S{U32.xor(acc, h), wo, bl, pk}

def T6.row.b(+acc: U32, pk: Array<U32>, ro: Array<U32> & U32, rb: Array<U32> & U32) -> T6S:
  (wo, +o) = ro
  (bl, +b) = rb
  T6.row.k(acc, wo, bl, T6.fh(U32.to_nat(U32.div(U32.add(b, 3), 4)), o, 2166136261, Array.get(U32, pk, o)))

def T6.flat(f: Nat, +i: U32, st: T6S) -> T6S:
  match f st:
    case 0n other:
      other
    case 1n+p T6S{+acc, wo, bl, pk}:
      T6.flat(p, U32.inc(i), T6.row.b(acc, pk, Array.get(U32, wo, i), Array.get(U32, bl, i)))

def t6.out(+shape: String, +n: U32, +chars: U32, +tot: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +hc: U32, a: Array<String>, st: T6S) -> IO(Unit):
  match st:
    case T6S{+hf, wo, bl, pk}:
      IO.print("{\"spike\":\"coder\",\"mode\":\"t6\",\"shape\":\"" ++ shape ++ "\",\"n\":" ++ U32.show(n) ++ ",\"chars\":" ++ U32.show(chars) ++ ",\"flat_words\":" ++ U32.show(tot) ++ ",\"cons_hash_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"flat_build_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"flat_hash_ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ keep(a) ++ ",\"chk\":" ++ U32.show(U32.xor(hc, hf)) ++ "}")

def t6.flat(+shape: String, +n: U32, +chars: U32, +tot: U32, +t0: Nat, +t1: Nat, +t2: Nat, +hc: U32, a: Array<String>, st: T6S) -> IO(Unit):
  match st:
    case T6S{+acc, wo, bl, pk}:
      do IO<Unit>:
        t3 : Nat <- IO.now()
        t6.out(shape, n, chars, tot, t0, t1, t2, t3, hc, a, T6S{acc, wo, bl, pk})

def t6.built(+shape: String, +n: U32, +chars: U32, +tot: U32, +t0: Nat, +t1: Nat, +hc: U32, bl: Array<U32>, rf: RF) -> IO(Unit):
  match rf:
    case RF{a, fr, wo, pk}:
      do IO<Unit>:
        t2 : Nat <- IO.now()
        t6.flat(shape, n, chars, tot, t0, t1, t2, hc, a, T6.flat(U32.to_nat(n), 0, T6S{0, wo, bl, pk}))

def t6.lens(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, +t1: Nat, +hc: U32, rb: RB) -> IO(Unit):
  match rb:
    case RB{+tot, mx, a, fr, bl, wo}:
      t6.built(shape, n, chars, tot, t0, t1, hc, bl, Rf.go(U32.to_nat(n), 0, RF{a, fr, wo, Array.new(U32, K.Kernel.depth_for(U32.inc(tot)), 0)}))

def t6.k(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, r: Array<String> & U32) -> IO(Unit):
  (a, +hc) = r
  do IO<Unit>:
    t1 : Nat <- IO.now()
    t6.lens(shape, n, d, chars, t0, t1, hc, Rb.go(U32.to_nat(n), 0, RB{0, 0, a, K.Kernel.iota(n, d), Array.new(U32, d, 0), Array.new(U32, d, 0)}))

# rrad stages: code, pack (UTF-8 words), radix refinement, rank + gather
def rrad.out(+shape: String, +n: U32, +chars: U32, +k: U32, +rounds: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +t4: Nat, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (w, +x) = r
  pr("rrad", shape, n, k, chars, Nat.sub(t4, t0), x, keep(a) ++ ",\"code_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"pack_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"sort_ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ ",\"rank_ms\":" ++ Nat.show(Nat.sub(t4, t3)) ++ ",\"rounds\":" ++ U32.show(rounds))

def rrad.fin(+shape: String, +n: U32, +chars: U32, +k: U32, +rounds: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, a: Array<String>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (w, codes) = r
  do IO<Unit>:
    t4 : Nat <- IO.now()
    rrad.out(shape, n, chars, k, rounds, t0, t1, t2, t3, t4, a, chk(n, w))

def rrad.rank(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, a: Array<String>, codes: Array<U32>, rr: RR) -> IO(Unit):
  match rr:
    case RR{rx, perm, ties, +rounds}:
      do IO<Unit>:
        t3 : Nat <- IO.now()
        rrad.fin(shape, n, chars, k, rounds, t0, t1, t2, t3, a, K.Kernel.gather(~U32, n, d, Rk.go(U32.to_nat(k), 0, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0), Array.get(U32, perm, 0)), codes, 0))

def rrad.sort(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +mx: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, bl: Array<U32>, rf: RF) -> IO(Unit):
  match rf:
    case RF{a, fr, wo, pk}:
      +kd = K.Kernel.depth_for(U32.max(k, 1))
      do IO<Unit>:
        t2 : Nat <- IO.now()
        rrad.rank(shape, n, d, chars, k, t0, t1, t2, a, codes, Rx.loop(U32.to_nat(U32.add(U32.div(mx, 8), 2)), 0, k, kd, RR{RX{wo, bl, pk, Array.new(U32, kd, 0)}, K.Kernel.iota(k, kd), 1, 0}))

def rrad.pack(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, rb: RB) -> IO(Unit):
  match rb:
    case RB{+tot, +mx, a, fr, bl, wo}:
      rrad.sort(shape, n, d, chars, k, mx, t0, t1, codes, bl, Rf.go(U32.to_nat(k), 0, RF{a, fr, wo, Array.new(U32, K.Kernel.depth_for(U32.inc(tot)), 0)}))

def rrad.k(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, st: HS) -> IO(Unit):
  match st:
    case HS{+k, a, hs, rp, ids, out, fr}:
      +kd1 = K.Kernel.depth_for(U32.inc(k))
      do IO<Unit>:
        t1 : Nat <- IO.now()
        rrad.pack(shape, n, d, chars, k, t0, t1, out, Rb.go(U32.to_nat(k), 0, RB{0, 0, a, fr, Array.new(U32, kd1, 0), Array.new(U32, kd1, 0)}))

# rmap: the k entries through Base Map (Sort.ranks.go over Map.to_list)
def Mp.ins.s(+c: U32, fr: Array<U32>, m: Map<&2, U32>, r: Array<String> & String) -> Array<String> & Array<U32> & Map<&2, U32>:
  (a, s) = r
  (a, fr, Map.set(&2, U32, m, s, c))

def Mp.ins.r(+c: U32, a: Array<String>, m: Map<&2, U32>, r: Array<U32> & U32) -> Array<String> & Array<U32> & Map<&2, U32>:
  (fr, +row) = r
  Mp.ins.s(c, fr, m, Array.get(String, a, row))

def Mp.go(n: Nat, +c: U32, st: Array<String> & Array<U32> & Map<&2, U32>) -> Array<String> & Array<U32> & Map<&2, U32>:
  match n:
    case 0n:
      st
    case 1n+p:
      (a, fr, m) = st
      Mp.go(p, U32.inc(c), Mp.ins.r(c, a, m, Array.get(U32, fr, c)))

def rmap.out(+shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (w, +x) = r
  pr("rmap", shape, n, k, chars, Nat.sub(t2, t0), x, keep(a) ++ ",\"code_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"mapsort_ms\":" ++ Nat.show(Nat.sub(t2, t1)))

def rmap.fin(+shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, a: Array<String>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (w, codes) = r
  do IO<Unit>:
    t2 : Nat <- IO.now()
    rmap.out(shape, n, chars, k, t0, t1, t2, a, chk(n, w))

def rmap.m(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, st: Array<String> & Array<U32> & Map<&2, U32>) -> IO(Unit):
  (a, fr, m) = st
  rmap.fin(shape, n, chars, k, t0, t1, a, K.Kernel.gather(~U32, n, d, SO.Sort.ranks.go(Map.to_list(&2, U32, m), 0, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0)), codes, 0))

def rmap.k(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, st: HS) -> IO(Unit):
  match st:
    case HS{+k, a, hs, rp, ids, out, fr}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        rmap.m(shape, n, d, chars, k, t0, t1, out, Mp.go(U32.to_nat(k), 0, (a, fr, Map.new(&2, U32))))

type Mode is Data:
  MOld{}
  MOldSeq{}
  MNew{}
  MROld{}
  MRNew{}
  MRMap{}
  MRRad{}
  MT6{}

def mode_of(+s: String) -> Mode:
  Bool.pick(Mode, String.eq(s, "oldseq"), MOldSeq{},
  Bool.pick(Mode, String.eq(s, "new"), MNew{},
  Bool.pick(Mode, String.eq(s, "rold"), MROld{},
  Bool.pick(Mode, String.eq(s, "rnew"), MRNew{},
  Bool.pick(Mode, String.eq(s, "rmap"), MRMap{}, Bool.pick(Mode, String.eq(s, "rrad"), MRRad{}, Bool.pick(Mode, String.eq(s, "t6"), MT6{}, MOld{})))))))

def run.mode(m: Mode, +mode: String, +shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, a: Array<String>) -> IO(Unit):
  match m:
    case MOld{}:
      run.old.k(mode, shape, n, chars, t0, SO.Sort.str_codes_par(n, d, 0, a))
    case MOldSeq{}:
      run.old.k(mode, shape, n, chars, t0, SO.Sort.str_codes(n, d, 0, a))
    case MNew{}:
      run.new.k(mode, shape, n, chars, t0, Hc.code(n, d, 0, a))
    case MROld{}:
      run.rold.k(shape, n, chars, t0, SO.Sort.str_words(n, d, 0, a))
    case MRNew{}:
      rnew.k(shape, n, d, chars, t0, Hc.code(n, d, 0, a))
    case MRMap{}:
      rmap.k(shape, n, d, chars, t0, Hc.code(n, d, 0, a))
    case MRRad{}:
      rrad.k(shape, n, d, chars, t0, Hc.code(n, d, 0, a))
    case MT6{}:
      t6.k(shape, n, d, chars, t0, T6.cons(n, a))

def run.go(+mode: String, +shape: String, +n: U32, +d: Nat, r: Array<String> & U32) -> IO(Unit):
  (a, +chars) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    run.mode(mode_of(mode), mode, shape, n, d, chars, t0, a)

def run(+shape: String, +n: U32, +mode: String) -> IO(Unit):
  +d = K.Kernel.depth_for(n)
  run.go(mode, shape, n, d, K.Kernel.fold(~String, ~U32, ~(acc => s => U32.add(acc, Str.len(s, 0))), n, Gen.go(U32.to_nat(n), 0, shape_of(shape), Array.new(String, d, "")), 0))

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      1000

def go(+xs: List<&2, String>) -> IO(Unit):
  run(nth(0n, xs, "distinct"), num(U32.read(nth(1n, xs, "1000"))), nth(2n, xs, "new"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
