# src/groupby.bend -- GroupBy.run. DESIGN.md 4.9.
#
# Algorithm (deviates from 4.9's per-row key strings, see DESIGN.md 14 M5):
#  1. type check keys and aggregations against the schema (first error wins),
#     then evaluate every key expression to a full column (Eval.full).
#  2. dictionary-encode each key column ONCE into dense U32 codes, null = 0:
#       bool  -> 0 null / 1 false / 2 true
#       u32 / i32 / f32 -> the order-preserving sort word (sort.bend; -0.0 =
#         0.0, every NaN one value); a value range < 2^20 is coded directly
#         (word - min + 1), a wider one by rank after a radix sort
#       str   -> a Map from string to first-appearance code (one Map lookup
#         per row: no per-row key strings, no concatenation)
#  3. combine the key codes left to right: g * k_c + c when the product of
#     the cardinalities is <= 2^22, then re-densified through a direct table;
#     otherwise the pairs are ranked by a radix sort. A final densify pass
#     numbers the groups in FIRST-APPEARANCE order and records each group's
#     first row (`first`).
#  4. key output columns = the key columns gathered at `first`; every
#     aggregation is one scatter over the rows into an n_groups accumulator
#     array (U32/I32 sums: wrapping word adds; F32 sum and every mean: the
#     Neumaier step with the non-finite guard of DESIGN.md 15.5.3, Grp.nm =
#     K.Kernel.nm.add, the rows of a group visited in ascending row order;
#     (seen, value) min/max with K.Kernel.fmin/fmax for f32, counts,
#     first/last row indices then a gather, n_unique by first occurrences of
#     (group, value) codes, the f32 codes being the 15.5.2 sort words). Results
#     equal Eval.agg applied to each group's rows in order, bit for bit.
#
# Output order: first appearance for maintain_order = True{} AND False{}
# (v1 does not use the flag; the contract of DESIGN.md 7 only promises first
# appearance when it is True{}).
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; pairs
# taken apart in the next helper's parameter; templates ~T: Data.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./schema.bend as S
import ./expr.bend as X
import ./eval.bend as V
import ./sort.bend as SO

# dense codes, every one < k
type Codes is Type:
  Codes{k: U32, c: Array<U32>}

# row -> group id, the number of groups, group -> its first row
type Groups is Type:
  Groups{ng: U32, gids: Array<U32>, first: Array<U32>}

type MM is Data:
  MM{mn: U32, mx: U32}

# accumulators: running sum s, Neumaier compensation c and valid count k (Grp.nm, for
# both f32 sum and mean); (seen, value)
type KS is Data:
  KS{s: F32, c: F32, k: U32}

type MW is Data:
  MW{seen: U32, m: U32}

type MF is Data:
  MF{seen: U32, m: F32}

type MS is Data:
  MS{seen: U32, m: String}

# key evaluation state
type GSt is Type:
  GSt{f: C.Frame, r: E.ResT(List<&1, C.Named>)}

# aggregation state: the frame, the groups, the output columns (newest first)
type ASt is Type:
  ASt{f: C.Frame, g: Groups, r: E.ResT(List<&1, C.Named>)}

def Grp.limit() -> U32:
  4194304

def Grp.range() -> U32:
  1048576

def Grp.bug(what: String) -> E.Err:
  E.InvalidOperation{"group_by: unexpected " ++ what}

# ---- small kernels ---------------------------------------------------------------------

# out[i] = f(k, a[i], b[i])
def Grp.zipk.go(~f: U32 -> U32 -> U32 -> U32, n: Nat, +i: U32, +k: U32, out: Array<U32>, ra: Array<U32> & U32, rb: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      out
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      Grp.zipk.go(~f, p, j, k, Array.set(U32, out, i, f(k, x, y)), Array.get(U32, a, j), Array.get(U32, b, j))

def Grp.zipk(~f: U32 -> U32 -> U32 -> U32, +n: U32, +d: Nat, +k: U32, a: Array<U32>, b: Array<U32>) -> Array<U32>:
  Grp.zipk.go(~f, U32.to_nat(n), 0, k, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, b, 0))

# acc[g[i]] = f(acc[g[i]], vals[i], mask[i]) for i < n; the gids come back.
# A 1-slot vals/mask array reads the same slot for every row (indices wrap).
def Grp.scat.put(~T: Data, ~A: Data, ~f: A -> T -> U32 -> A, x: T, v: U32, +g: U32, r: Array<A> & A) -> Array<A>:
  (acc, old) = r
  Array.set(A, acc, g, f(old, x, v))

def Grp.scat.go(~T: Data, ~A: Data, ~f: A -> T -> U32 -> A, n: Nat, +i: U32, acc: Array<A>, rg: Array<U32> & U32, rv: Array<T> & T, rm: Array<U32> & U32) -> Array<U32> & Array<A>:
  match n:
    case 0n:
      (gs, g) = rg
      (gs, acc)
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      (ms, v) = rm
      +j = U32.inc(i)
      Grp.scat.go(~T, ~A, ~f, p, j, Grp.scat.put(~T, ~A, ~f, x, v, g, Array.get(A, acc, g)), Array.get(U32, gs, j), Array.get(T, vs, j), Array.get(U32, ms, j))

def Grp.scat(~T: Data, ~A: Data, ~f: A -> T -> U32 -> A, +n: U32, gids: Array<U32>, vals: Array<T>, mask: Array<U32>, acc: Array<A>) -> Array<U32> & Array<A>:
  Grp.scat.go(~T, ~A, ~f, U32.to_nat(n), 0, acc, Array.get(U32, gids, 0), Array.get(T, vals, 0), Array.get(U32, mask, 0))

def Grp.fst(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

# null rows' codes := 0
def Grp.zero(+n: U32, w: Array<U32>, v: C.Valid) -> Array<U32>:
  match v:
    case C.AllValid{}:
      w
    case C.Mask{m}:
      Grp.fst(K.Kernel.mask_data(~U32, n, w, m, 0))

# ---- densify: codes -> groups in first-appearance order ---------------------------------

def Grp.dens.put(+i: U32, +next: U32, +x: U32, gids: Array<U32>, first: Array<U32>, rt: Array<U32> & U32) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  (table, +t) = rt
  +isnew = U32.is_zero(t)
  +id = Bool.pick(U32, isnew, next, U32.sub(t, 1))
  (U32.add(next, Bool.to_u32(isnew)), Array.set(U32, table, x, U32.inc(id)), Array.set(U32, gids, i, id), Array.set(U32, first, next, i))

def Grp.dens.go(n: Nat, +i: U32, st: U32 & Array<U32> & Array<U32> & Array<U32>, rc: Array<U32> & U32) -> Groups:
  match n:
    case 0n:
      (next, table, gids, first) = st
      Groups{next, gids, first}
    case 1n+p:
      (+next, table, gids, first) = st
      (c, +x) = rc
      +j = U32.inc(i)
      Grp.dens.go(p, j, Grp.dens.put(i, next, x, gids, first, Array.get(U32, table, x)), Array.get(U32, c, j))

# group ids in first-appearance order of the codes (< k); `first` has more
# than n_groups slots (a row that opens no group writes slot n_groups)
def Grp.densify(+n: U32, +d: Nat, +k: U32, c: Array<U32>) -> Groups:
  Grp.dens.go(U32.to_nat(n), 0, (0, Array.new(U32, K.Kernel.depth_for(k), 0), Array.new(U32, d, 0), Array.new(U32, K.Kernel.depth_for(U32.inc(n)), 0)), Array.get(U32, c, 0))

def Grp.to_codes(g: Groups) -> Codes:
  match g:
    case Groups{+ng, gids, first}:
      Codes{U32.max(ng, 1), gids}

# flags[i] = 1 when code c[i] occurs for the first time
def Grp.fo.put(+i: U32, +x: U32, flags: Array<U32>, rt: Array<U32> & U32) -> Array<U32> & Array<U32>:
  (table, t) = rt
  (Array.set(U32, table, x, 1), Array.set(U32, flags, i, U32.sub(1, t)))

def Grp.fo.go(n: Nat, +i: U32, st: Array<U32> & Array<U32>, rc: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (table, flags) = st
      flags
    case 1n+p:
      (table, flags) = st
      (c, +x) = rc
      +j = U32.inc(i)
      Grp.fo.go(p, j, Grp.fo.put(i, x, flags, Array.get(U32, table, x)), Array.get(U32, c, j))

def Grp.firstocc(+n: U32, +d: Nat, cd: Codes) -> Array<U32>:
  match cd:
    case Codes{k, c}:
      Grp.fo.go(U32.to_nat(n), 0, (Array.new(U32, K.Kernel.depth_for(k), 0), Array.new(U32, d, 0)), Array.get(U32, c, 0))

# ---- rank codes after a radix sort ---------------------------------------------------------

# codes[perm[j]] = number of value changes in ws[0..j]
def Grp.rank.go(n: Nat, +j: U32, +prev: U32, +rank: U32, codes: Array<U32>, rw: Array<U32> & U32, rp: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (codes, rank)
    case 1n+p:
      (ws, +x) = rw
      (perm, row) = rp
      +r = U32.add(rank, Bool.to_u32(U32.is_ne(x, prev)))
      +j2 = U32.inc(j)
      Grp.rank.go(p, j2, x, r, Array.set(U32, codes, row, r), Array.get(U32, ws, j2), Array.get(U32, perm, j2))

def Grp.rank.s(+n: U32, +d: Nat, perm: Array<U32>, r: Array<U32> & U32) -> Array<U32> & U32:
  (ws, +w0) = r
  Grp.rank.go(U32.to_nat(n), 0, w0, 0, Array.new(U32, d, 0), Array.get(U32, ws, 0), Array.get(U32, perm, 0))

def Grp.rank.c(+n: U32, +d: Nat, m: Array<U32>, r: Array<U32> & U32) -> Codes:
  (codes, rank) = r
  Codes{U32.add(rank, 2), Grp.zipk(~(k => c => v => U32.and(U32.inc(c), U32.sub(0, v))), n, d, 0, codes, m)}

def Grp.rank.b(+n: U32, +d: Nat, m: Array<U32>, st: Array<U32> & Array<U32>) -> Codes:
  (ws, perm) = st
  Grp.rank.c(n, d, m, Grp.rank.s(n, d, perm, Array.get(U32, ws, 0)))

# codes by rank of the words (valid rows 1.., null rows 0)
def Grp.rank(+n: U32, +d: Nat, w: Array<U32>, m: Array<U32>) -> Codes:
  Grp.rank.b(n, d, m, SO.Radix.sort(n, d, (w, K.Kernel.iota(n, d))))

# pairs (a[i], b[i]) ranked: radix by b, then stably by a, then count changes
def Grp.prank.go(n: Nat, +j: U32, +pa: U32, +pb: U32, +rank: U32, codes: Array<U32>, ra: Array<U32> & U32, rb: Array<U32> & U32, rp: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (codes, rank)
    case 1n+p:
      (xa, +x) = ra
      (xb, +y) = rb
      (perm, row) = rp
      +r = U32.add(rank, Bool.to_u32(Bool.or(U32.is_ne(x, pa), U32.is_ne(y, pb))))
      +j2 = U32.inc(j)
      Grp.prank.go(p, j2, x, y, r, Array.set(U32, codes, row, r), Array.get(U32, xa, j2), Array.get(U32, xb, j2), Array.get(U32, perm, j2))

def Grp.prank.fin(r: Array<U32> & U32) -> Codes:
  (codes, rank) = r
  Codes{U32.inc(rank), codes}

def Grp.prank.f(+n: U32, +d: Nat, perm: Array<U32>, ra: Array<U32> & U32, rb: Array<U32> & U32) -> Codes:
  (xa, +a0) = ra
  (xb, +b0) = rb
  Grp.prank.fin(Grp.prank.go(U32.to_nat(n), 0, a0, b0, 0, Array.new(U32, d, 0), Array.get(U32, xa, 0), Array.get(U32, xb, 0), Array.get(U32, perm, 0)))

def Grp.prank.e(+n: U32, +d: Nat, xa: Array<U32>, r: Array<U32> & Array<U32>) -> Codes:
  (xb, perm) = r
  Grp.prank.f(n, d, perm, Array.get(U32, xa, 0), Array.get(U32, xb, 0))

def Grp.prank.d(+n: U32, +d: Nat, b2: Array<U32>, st: Array<U32> & Array<U32>) -> Codes:
  (xa, perm) = st
  Grp.prank.e(n, d, xa, K.Kernel.gather(~U32, n, d, b2, perm, 0))

def Grp.prank.c(+n: U32, +d: Nat, a: Array<U32>, b2: Array<U32>, st: Array<U32> & Array<U32>) -> Codes:
  (xb, perm) = st
  Grp.prank.d(n, d, b2, SO.Radix.sort(n, d, K.Kernel.gather(~U32, n, d, a, perm, 0)))

def Grp.prank.b(+n: U32, +d: Nat, a: Array<U32>, bb: Array<U32> & Array<U32>) -> Codes:
  (b1, b2) = bb
  Grp.prank.c(n, d, a, b2, SO.Radix.sort(n, d, (b1, K.Kernel.iota(n, d))))

def Grp.prank(+n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Codes:
  Grp.prank.b(n, d, a, Array.clone(U32, b))

# ---- encode one column -----------------------------------------------------------------------

def Grp.mm.go(n: Nat, +i: U32, +mn: U32, +mx: U32, rw: Array<U32> & U32, rm: Array<U32> & U32) -> Array<U32> & Array<U32> & MM:
  match n:
    case 0n:
      (w, x) = rw
      (m, v) = rm
      (w, m, MM{mn, mx})
    case 1n+p:
      (w, +x) = rw
      (m, +v) = rm
      +j = U32.inc(i)
      Grp.mm.go(p, j, U32.min(mn, U32.or(x, U32.sub(v, 1))), U32.max(mx, U32.and(x, U32.sub(0, v))), Array.get(U32, w, j), Array.get(U32, m, j))

def Grp.enc.pick(allnull: Bool, small: Bool, +n: U32, +d: Nat, +mn: U32, +mx: U32, w: Array<U32>, m: Array<U32>) -> Codes:
  match allnull small:
    case True{} _:
      Codes{1, Array.new(U32, d, 0)}
    case False{} True{}:
      Codes{U32.add(U32.sub(mx, mn), 2), Grp.zipk(~(k => x => v => U32.and(U32.inc(U32.sub(x, k)), U32.sub(0, v))), n, d, mn, w, m)}
    case False{} False{}:
      Grp.rank(n, d, w, m)

def Grp.enc.mm(+n: U32, +d: Nat, r: Array<U32> & Array<U32> & MM) -> Codes:
  (w, m, mm) = r
  match mm:
    case MM{+mn, +mx}:
      Grp.enc.pick(U32.is_gt(mn, mx), U32.is_lt(U32.sub(mx, mn), Grp.range()), n, d, mn, mx, w, m)

# a word column (validity materialised to 2^d slots) to codes
def Grp.enc.num(+n: U32, +d: Nat, r: Array<U32> & C.Valid) -> Codes:
  (w, v) = r
  Grp.enc.mm(n, d, Grp.mm.go(U32.to_nat(n), 0, 4294967295, 0, Array.get(U32, w, 0), Array.get(U32, C.Valid.materialize(v, d), 0)))

def Grp.enc.str(+n: U32, v: C.Valid, r: Array<String> & Array<U32> & SO.CS) -> Codes:
  (strs, codes, cs) = r
  match cs:
    case SO.CS{m, k}:
      Codes{k, Grp.zero(n, codes, v)}

# dense codes of a column (null = 0); the column is consumed
def Grp.encode(c: C.Column) -> Codes:
  match c:
    case C.CBool{+n, d, v, x}:
      Codes{3, Grp.zero(n, SO.Sort.xmap(~U32, ~(w => U32.inc(w)), n, d, 0, x), v)}
    case C.CU32{+n, +d, v, x}:
      Grp.enc.num(n, d, SO.Sort.words(C.CU32{n, d, v, x}, False{}))
    case C.CI32{+n, +d, v, x}:
      Grp.enc.num(n, d, SO.Sort.words(C.CI32{n, d, v, x}, False{}))
    case C.CF32{+n, +d, v, x}:
      Grp.enc.num(n, d, SO.Sort.words(C.CF32{n, d, v, x}, False{}))
    case C.CStr{+n, +d, v, x}:
      Grp.enc.str(n, v, SO.Sort.str_codes_par(n, d, 1, x))

def Grp.enc.strk.b(+n: U32, +d: Nat, strs: Array<String>, +k: U32, r: Array<U32> & C.Valid) -> C.Column & Codes:
  (codes, v) = r
  (C.CStr{n, d, v, strs}, Codes{k, codes})

def Grp.enc.strk(+n: U32, +d: Nat, v: C.Valid, r: Array<String> & Array<U32> & SO.CS) -> C.Column & Codes:
  (strs, codes, cs) = r
  match cs:
    case SO.CS{m, +k}:
      Grp.enc.strk.b(n, d, strs, k, SO.Sort.words.z(n, codes, v))

def Grp.enc.cl(r: C.Column & C.Column) -> C.Column & Codes:
  (c1, c2) = r
  (c1, Grp.encode(c2))

# Grp.encode that hands the column back (strings are read in place, the
# other dtypes are cloned: one cheap word pass)
def Grp.encode_keep(c: C.Column) -> C.Column & Codes:
  match c:
    case C.CStr{+n, +d, v, x}:
      Grp.enc.strk(n, d, v, SO.Sort.str_codes_par(n, d, 1, x))
    case other:
      Grp.enc.cl(C.Column.clone(other))

def Grp.combine.b(small: Bool, +n: U32, +d: Nat, +kg: U32, +kc: U32, a: Array<U32>, b: Array<U32>) -> Codes:
  match small:
    case True{}:
      Grp.to_codes(Grp.densify(n, d, U32.mul(kg, kc), Grp.zipk(~(k => x => y => U32.add(U32.mul(x, k), y)), n, d, kc, a, b)))
    case False{}:
      Grp.prank(n, d, a, b)

# dense codes of the pairs (g, c)
def Grp.combine(+n: U32, +d: Nat, g: Codes, c: Codes) -> Codes:
  match g c:
    case Codes{+kg, a} Codes{+kc, b}:
      Grp.combine.b(U32.is_le(kg, U32.div(Grp.limit(), kc)), n, d, kg, kc, a, b)

# ---- accumulator steps ------------------------------------------------------------------------

def Grp.nm.k(+skip: Bool, +s: F32, +c: F32, k: U32, +v: U32, r: K.NS) -> KS:
  match r:
    case K.NS{s2, c2}:
      KS{Bool.pick(F32, skip, s, s2), Bool.pick(F32, skip, c, c2), U32.add(k, v)}

# the 15.5.3 step of Kernel.fsum (Neumaier, non-finite guard) on a group's state, the
# group_by f32 sum and every mean; unchanged when v = 0 (a null row)
def Grp.nm(acc: KS, +x: F32, +v: U32) -> KS:
  match acc:
    case KS{+s, +c, k}:
      Grp.nm.k(U32.is_zero(v), s, c, k, v, K.Kernel.nm.add(s, c, x))

def Grp.ks_s(a: KS) -> F32:
  match a:
    case KS{+s, +c, k}:
      K.Kernel.nm.result(s, c)

def Grp.ks_ok(a: KS) -> U32:
  match a:
    case KS{s, c, k}:
      Bool.to_u32(U32.is_ne(k, 0))

def Grp.ks_mean(a: KS) -> F32:
  match a:
    case KS{+s, +c, +k}:
      Bool.pick(F32, U32.is_zero(k), 0.0, F32.div(K.Kernel.nm.result(s, c), U32.to_f32(k)))

# (seen, value) steps: the first valid value, then op(value, x) (Eval's fold1)
def Grp.mw(~op: U32 -> U32 -> U32, acc: MW, +x: U32, +v: U32) -> MW:
  match acc:
    case MW{+s, +m}:
      MW{U32.or(s, v), Bool.pick(U32, U32.is_zero(v), m, Bool.pick(U32, U32.is_zero(s), x, op(m, x)))}

def Grp.mf(~op: F32 -> F32 -> F32, acc: MF, +x: F32, +v: U32) -> MF:
  match acc:
    case MF{+s, +m}:
      MF{U32.or(s, v), Bool.pick(F32, U32.is_zero(v), m, Bool.pick(F32, U32.is_zero(s), x, op(m, x)))}

def Grp.ms(~op: String -> String -> String, acc: MS, +x: String, +v: U32) -> MS:
  match acc:
    case MS{+s, +m}:
      MS{U32.or(s, v), Bool.pick(String, U32.is_zero(v), m, Bool.pick(String, U32.is_zero(s), x, op(m, x)))}

def Grp.mw.m(a: MW) -> U32:
  match a:
    case MW{s, m}:
      m

def Grp.mw.s(a: MW) -> U32:
  match a:
    case MW{s, m}:
      s

def Grp.mf.m(a: MF) -> F32:
  match a:
    case MF{s, m}:
      m

def Grp.mf.s(a: MF) -> U32:
  match a:
    case MF{s, m}:
      s

def Grp.ms.m(a: MS) -> String:
  match a:
    case MS{s, m}:
      m

def Grp.ms.s(a: MS) -> U32:
  match a:
    case MS{s, m}:
      s

def Grp.i2f(x: U32) -> F32:
  D.I32.to_f32(D.I32{x})

# ---- result columns ---------------------------------------------------------------------------

def Grp.valid.b(all: Bool, m: Array<U32>) -> C.Valid:
  match all:
    case True{}:
      C.AllValid{}
    case False{}:
      C.Mask{m}

def Grp.valid.a(+ng: U32, r: Array<U32> & U32) -> C.Valid:
  (m, c) = r
  Grp.valid.b(U32.is_eq(c, ng), m)

# a 0/1 mask of ng rows as a validity (AllValid when all ones)
def Grp.valid(+ng: U32, m: Array<U32>) -> C.Valid:
  Grp.valid.a(ng, K.Kernel.popcount(ng, m))

def Grp.wrap.w(t: D.DType, +ng: U32, +dg: Nat, first: Array<U32>, r: Array<U32> & Array<U32>) -> Groups & E.ResT(C.Column):
  (gids, acc) = r
  (Groups{ng, gids, first}, Done{C.Column.mk_w(t, ng, dg, C.AllValid{}, acc)})

def Grp.wrap.fsum(+ng: U32, +dg: Nat, first: Array<U32>, r: Array<U32> & Array<KS>) -> Groups & E.ResT(C.Column):
  (gids, acc) = r
  (Groups{ng, gids, first}, Done{C.CF32{ng, dg, C.AllValid{}, K.Kernel.map(~KS, ~F32, ~(a => Grp.ks_s(a)), ng, dg, acc, 0.0)}})

def Grp.wrap.mean.b(+ng: U32, +dg: Nat, first: Array<U32>, gids: Array<U32>, aa: Array<KS> & Array<KS>) -> Groups & E.ResT(C.Column):
  (a1, a2) = aa
  (Groups{ng, gids, first}, Done{C.CF32{ng, dg, Grp.valid(ng, K.Kernel.map(~KS, ~U32, ~(a => Grp.ks_ok(a)), ng, dg, a1, 0)), K.Kernel.map(~KS, ~F32, ~(a => Grp.ks_mean(a)), ng, dg, a2, 0.0)}})

def Grp.wrap.mean(+ng: U32, +dg: Nat, first: Array<U32>, r: Array<U32> & Array<KS>) -> Groups & E.ResT(C.Column):
  (gids, acc) = r
  Grp.wrap.mean.b(ng, dg, first, gids, Array.clone(KS, acc))

def Grp.wrap.mw.b(t: D.DType, +ng: U32, +dg: Nat, first: Array<U32>, gids: Array<U32>, aa: Array<MW> & Array<MW>) -> Groups & E.ResT(C.Column):
  (a1, a2) = aa
  (Groups{ng, gids, first}, Done{C.Column.mk_w(t, ng, dg, Grp.valid(ng, K.Kernel.map(~MW, ~U32, ~(a => Grp.mw.s(a)), ng, dg, a1, 0)), K.Kernel.map(~MW, ~U32, ~(a => Grp.mw.m(a)), ng, dg, a2, 0))})

def Grp.wrap.mw(t: D.DType, +ng: U32, +dg: Nat, first: Array<U32>, r: Array<U32> & Array<MW>) -> Groups & E.ResT(C.Column):
  (gids, acc) = r
  Grp.wrap.mw.b(t, ng, dg, first, gids, Array.clone(MW, acc))

def Grp.wrap.mf.b(+ng: U32, +dg: Nat, first: Array<U32>, gids: Array<U32>, aa: Array<MF> & Array<MF>) -> Groups & E.ResT(C.Column):
  (a1, a2) = aa
  (Groups{ng, gids, first}, Done{C.CF32{ng, dg, Grp.valid(ng, K.Kernel.map(~MF, ~U32, ~(a => Grp.mf.s(a)), ng, dg, a1, 0)), K.Kernel.map(~MF, ~F32, ~(a => Grp.mf.m(a)), ng, dg, a2, 0.0)}})

def Grp.wrap.mf(+ng: U32, +dg: Nat, first: Array<U32>, r: Array<U32> & Array<MF>) -> Groups & E.ResT(C.Column):
  (gids, acc) = r
  Grp.wrap.mf.b(ng, dg, first, gids, Array.clone(MF, acc))

def Grp.wrap.ms.b(+ng: U32, +dg: Nat, first: Array<U32>, gids: Array<U32>, aa: Array<MS> & Array<MS>) -> Groups & E.ResT(C.Column):
  (a1, a2) = aa
  (Groups{ng, gids, first}, Done{C.CStr{ng, dg, Grp.valid(ng, K.Kernel.map(~MS, ~U32, ~(a => Grp.ms.s(a)), ng, dg, a1, 0)), K.Kernel.map(~MS, ~String, ~(a => Grp.ms.m(a)), ng, dg, a2, "")}})

def Grp.wrap.ms(+ng: U32, +dg: Nat, first: Array<U32>, r: Array<U32> & Array<MS>) -> Groups & E.ResT(C.Column):
  (gids, acc) = r
  Grp.wrap.ms.b(ng, dg, first, gids, Array.clone(MS, acc))

def Grp.wrap.gather(+ng: U32, gids: Array<U32>, first: Array<U32>, r: C.Column & Array<U32>) -> Groups & E.ResT(C.Column):
  (c, idx) = r
  (Groups{ng, gids, first}, Done{c})

def Grp.wrap.err(+ng: U32, gids: Array<U32>, first: Array<U32>, e: E.Err) -> Groups & E.ResT(C.Column):
  (Groups{ng, gids, first}, Fail{e})

# ---- per-dtype aggregations (m: the validity, 1 slot of 1 when AllValid) ---------------------

def Grp.agg.w(op: X.AggOp, +t: D.DType, +n: U32, +ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, m: Array<U32>, x: Array<U32>) -> Groups & E.ResT(C.Column):
  match op t:
    case X.Sum{} _:
      Grp.wrap.w(t, ng, dg, first, Grp.scat(~U32, ~U32, ~(a => w => v => U32.add(a, U32.and(w, U32.sub(0, v)))), n, gids, x, m, Array.new(U32, dg, 0)))
    case X.Mean{} D.TI32{}:
      Grp.wrap.mean(ng, dg, first, Grp.scat(~U32, ~KS, ~(a => w => v => Grp.nm(a, Grp.i2f(w), v)), n, gids, x, m, Array.new(KS, dg, KS{0.0, 0.0, 0})))
    case X.Mean{} _:
      Grp.wrap.mean(ng, dg, first, Grp.scat(~U32, ~KS, ~(a => w => v => Grp.nm(a, U32.to_f32(w), v)), n, gids, x, m, Array.new(KS, dg, KS{0.0, 0.0, 0})))
    case X.Min{} D.TI32{}:
      Grp.wrap.mw(t, ng, dg, first, Grp.scat(~U32, ~MW, ~(a => w => v => Grp.mw(~(p => q => V.Eval.i32_min(p, q)), a, w, v)), n, gids, x, m, Array.new(MW, dg, MW{0, 0})))
    case X.Min{} _:
      Grp.wrap.mw(t, ng, dg, first, Grp.scat(~U32, ~MW, ~(a => w => v => Grp.mw(~(p => q => U32.min(p, q)), a, w, v)), n, gids, x, m, Array.new(MW, dg, MW{0, 0})))
    case X.Max{} D.TI32{}:
      Grp.wrap.mw(t, ng, dg, first, Grp.scat(~U32, ~MW, ~(a => w => v => Grp.mw(~(p => q => V.Eval.i32_max(p, q)), a, w, v)), n, gids, x, m, Array.new(MW, dg, MW{0, 0})))
    case X.Max{} _:
      Grp.wrap.mw(t, ng, dg, first, Grp.scat(~U32, ~MW, ~(a => w => v => Grp.mw(~(p => q => U32.max(p, q)), a, w, v)), n, gids, x, m, Array.new(MW, dg, MW{0, 0})))
    case _ _:
      Grp.wrap.err(ng, gids, first, Grp.bug("aggregation over a word column"))

def Grp.agg.f(op: X.AggOp, +n: U32, +ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, m: Array<U32>, x: Array<F32>) -> Groups & E.ResT(C.Column):
  match op:
    case X.Sum{}:
      Grp.wrap.fsum(ng, dg, first, Grp.scat(~F32, ~KS, ~(a => w => v => Grp.nm(a, w, v)), n, gids, x, m, Array.new(KS, dg, KS{0.0, 0.0, 0})))
    case X.Mean{}:
      Grp.wrap.mean(ng, dg, first, Grp.scat(~F32, ~KS, ~(a => w => v => Grp.nm(a, w, v)), n, gids, x, m, Array.new(KS, dg, KS{0.0, 0.0, 0})))
    case X.Min{}:
      Grp.wrap.mf(ng, dg, first, Grp.scat(~F32, ~MF, ~(a => w => v => Grp.mf(~(p => q => K.Kernel.fmin(p, q)), a, w, v)), n, gids, x, m, Array.new(MF, dg, MF{0, 0.0})))
    case X.Max{}:
      Grp.wrap.mf(ng, dg, first, Grp.scat(~F32, ~MF, ~(a => w => v => Grp.mf(~(p => q => K.Kernel.fmax(p, q)), a, w, v)), n, gids, x, m, Array.new(MF, dg, MF{0, 0.0})))

    case _:
      Grp.wrap.err(ng, gids, first, Grp.bug("aggregation over an f32 column"))

def Grp.agg.s(op: X.AggOp, +n: U32, +ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, m: Array<U32>, x: Array<String>) -> Groups & E.ResT(C.Column):
  match op:
    case X.Min{}:
      Grp.wrap.ms(ng, dg, first, Grp.scat(~String, ~MS, ~(a => w => v => Grp.ms(~(p => q => V.Eval.str_min(p, q)), a, w, v)), n, gids, x, m, Array.new(MS, dg, MS{0, ""})))
    case X.Max{}:
      Grp.wrap.ms(ng, dg, first, Grp.scat(~String, ~MS, ~(a => w => v => Grp.ms(~(p => q => V.Eval.str_max(p, q)), a, w, v)), n, gids, x, m, Array.new(MS, dg, MS{0, ""})))
    case _:
      Grp.wrap.err(ng, gids, first, Grp.bug("aggregation over a str column"))

# Sum / Mean / Min / Max by dtype
def Grp.agg.v(op: X.AggOp, +ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, c: C.Column) -> Groups & E.ResT(C.Column):
  match c:
    case C.CBool{n, d, v, x}:
      Grp.agg.w(op, D.TBool{}, n, ng, dg, gids, first, C.Valid.materialize(v, 0n), x)
    case C.CU32{n, d, v, x}:
      Grp.agg.w(op, D.TU32{}, n, ng, dg, gids, first, C.Valid.materialize(v, 0n), x)
    case C.CI32{n, d, v, x}:
      Grp.agg.w(op, D.TI32{}, n, ng, dg, gids, first, C.Valid.materialize(v, 0n), x)
    case C.CF32{n, d, v, x}:
      Grp.agg.f(op, n, ng, dg, gids, first, C.Valid.materialize(v, 0n), x)
    case C.CStr{n, d, v, x}:
      Grp.agg.s(op, n, ng, dg, gids, first, C.Valid.materialize(v, 0n), x)

# Len: rows per group
def Grp.agg.len(+ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, r: C.Column & U32) -> Groups & E.ResT(C.Column):
  (c, +n) = r
  Grp.wrap.w(D.TU32{}, ng, dg, first, Grp.scat(~U32, ~U32, ~(a => w => v => U32.add(a, v)), n, gids, Array.new(U32, 0n, 0), Array.new(U32, 0n, 1), Array.new(U32, dg, 0)))

# Count: valid rows per group
def Grp.agg.count.b(+n: U32, +ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, r: C.Column & C.Valid) -> Groups & E.ResT(C.Column):
  (c, v) = r
  Grp.wrap.w(D.TU32{}, ng, dg, first, Grp.scat(~U32, ~U32, ~(a => w => v => U32.add(a, v)), n, gids, Array.new(U32, 0n, 0), C.Valid.materialize(v, 0n), Array.new(U32, dg, 0)))

def Grp.agg.count(+ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, r: C.Column & U32) -> Groups & E.ResT(C.Column):
  (c, +n) = r
  Grp.agg.count.b(n, ng, dg, gids, first, C.Column.take_valid(c))

# Last: the group's last row (null or not), as Eval.agg Last over its rows
def Grp.agg.last.b(+ng: U32, first: Array<U32>, c: C.Column, r: Array<U32> & Array<U32>) -> Groups & E.ResT(C.Column):
  (g2, last) = r
  Grp.wrap.gather(ng, g2, first, C.Column.gather(c, last, ng))

def Grp.agg.last(+ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, r: C.Column & U32) -> Groups & E.ResT(C.Column):
  (c, +n) = r
  Grp.agg.last.b(ng, first, c, Grp.scat(~U32, ~U32, ~(a => w => v => w), n, gids, K.Kernel.iota(n, K.Kernel.depth_for(n)), Array.new(U32, 0n, 1), Array.new(U32, dg, 0)))

# First: the group's first row
def Grp.agg.first.b(+ng: U32, gids: Array<U32>, r: C.Column & Array<U32>) -> Groups & E.ResT(C.Column):
  (c, first) = r
  (Groups{ng, gids, first}, Done{c})

# NUnique: distinct (group, value) codes counted per group; null counts as
# one value (Eval.agg / Polars)
def Grp.agg.nu.b(+n: U32, +ng: U32, +dg: Nat, first: Array<U32>, c: C.Column, gg: Array<U32> & Array<U32>) -> Groups & E.ResT(C.Column):
  (g1, g2) = gg
  +d = K.Kernel.depth_for(n)
  Grp.wrap.w(D.TU32{}, ng, dg, first, Grp.scat(~U32, ~U32, ~(a => w => v => U32.add(a, w)), n, g1, Grp.firstocc(n, d, Grp.combine(n, d, Codes{U32.max(ng, 1), g2}, Grp.encode(c))), Array.new(U32, 0n, 1), Array.new(U32, dg, 0)))

def Grp.agg.nu(+ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, r: C.Column & U32) -> Groups & E.ResT(C.Column):
  (c, +n) = r
  Grp.agg.nu.b(n, ng, dg, first, c, Array.clone(U32, gids))

# one aggregation of a full column per group; the groups come back
def Grp.agg.op(op: X.AggOp, +ng: U32, +dg: Nat, gids: Array<U32>, first: Array<U32>, c: C.Column) -> Groups & E.ResT(C.Column):
  match op:
    case X.Len{}:
      Grp.agg.len(ng, dg, gids, first, C.Column.len(c))
    case X.Count{}:
      Grp.agg.count(ng, dg, gids, first, C.Column.len(c))
    case X.First{}:
      Grp.agg.first.b(ng, gids, C.Column.gather(c, first, ng))
    case X.Last{}:
      Grp.agg.last(ng, dg, gids, first, C.Column.len(c))
    case X.NUnique{}:
      Grp.agg.nu(ng, dg, gids, first, C.Column.len(c))
    case other:
      Grp.agg.v(other, ng, dg, gids, first, c)

def Grp.agg.go(op: X.AggOp, +ng: U32, gids: Array<U32>, first: Array<U32>, c: C.Column) -> Groups & E.ResT(C.Column):
  +dg = K.Kernel.depth_for(ng)
  Grp.agg.op(op, ng, dg, gids, first, c)

def Grp.agg(op: X.AggOp, g: Groups, c: C.Column) -> Groups & E.ResT(C.Column):
  match g:
    case Groups{ng, gids, first}:
      Grp.agg.go(op, ng, gids, first, c)

# ---- validation ---------------------------------------------------------------------------------

def Grp.chk.keys(ks: List<&2, X.Expr>) -> Maybe<&2, E.Err>:
  match ks:
    case Nil{}:
      None{}
    case +k <> t:
      Maybe.or(&2, E.Err, Bool.pick(Maybe<&2, E.Err>, X.Expr.is_agg(k), Some{E.InvalidOperation{"group_by key is an aggregation: " ++ X.Expr.show(k)}}, None{}), Grp.chk.keys(t))

def Grp.chk.split(+e: X.Expr, s: Maybe<&2, X.AggSplit>) -> Maybe<&2, E.Err>:
  match s:
    case None{}:
      Some{E.InvalidOperation{"agg expects an aggregation: " ++ X.Expr.show(e)}}
    case Some{X.AggSplit{op, inner}}:
      Bool.pick(Maybe<&2, E.Err>, X.Expr.is_agg(inner), Some{E.InvalidOperation{"nested aggregation in agg: " ++ X.Expr.show(e)}}, None{})

def Grp.chk.aggs(ags: List<&2, X.Expr>) -> Maybe<&2, E.Err>:
  match ags:
    case Nil{}:
      None{}
    case +a <> t:
      Maybe.or(&2, E.Err, Grp.chk.split(a, X.Expr.split_agg(a)), Grp.chk.aggs(t))

def Grp.chk.empty(ks: List<&2, X.Expr>) -> Maybe<&2, E.Err>:
  match ks:
    case Nil{}:
      Some{E.InvalidOperation{"group_by needs at least one key"}}
    case _:
      None{}

# type errors first (keys, then aggs), then the shape rules
def Grp.validate(+keys: List<&2, X.Expr>, +aggs: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  Maybe.or(&2, E.Err, V.Eval.check(keys, s), Maybe.or(&2, E.Err, V.Eval.check(aggs, s), Maybe.or(&2, E.Err, Grp.chk.empty(keys), Maybe.or(&2, E.Err, Grp.chk.keys(keys), Grp.chk.aggs(aggs)))))

# ---- keys ------------------------------------------------------------------------------------------

def Grp.key.add(+name: String, acc: List<&1, C.Named>, r: C.Frame & E.ResT(C.Column)) -> GSt:
  (f, rc) = r
  match rc:
    case Fail{e}:
      GSt{f, Fail{e}}
    case Done{c}:
      GSt{f, Done{C.Named{name, c} <> acc}}

def Grp.key.step(+e: X.Expr, st: GSt) -> GSt:
  match st:
    case GSt{f, Fail{err}}:
      GSt{f, Fail{err}}
    case GSt{f, Done{acc}}:
      Grp.key.add(X.Expr.name(e), acc, V.Eval.full(f, e))

# every key expression as a full column (newest first)
def Grp.keys(ks: List<&2, X.Expr>, st: GSt) -> GSt:
  match ks:
    case Nil{}:
      st
    case k <> t:
      Grp.keys(t, Grp.key.step(k, st))

def Grp.codes.add(+n: U32, +d: Nat, name: String, acc: List<&1, C.Named>, g: Codes, cc: C.Column & Codes) -> List<&1, C.Named> & Codes:
  (c1, cd) = cc
  (C.Named{name, c1} <> acc, Grp.combine(n, d, g, cd))

def Grp.codes.step(+n: U32, +d: Nat, name: String, col: C.Column, st: List<&1, C.Named> & Codes) -> List<&1, C.Named> & Codes:
  (acc, g) = st
  Grp.codes.add(n, d, name, acc, g, Grp.encode_keep(col))

# the combined codes of the key columns; the columns are given newest first
# (as Grp.keys leaves them) and come back in key order. Combining in reverse
# key order is fine: only the final densify fixes the group numbering.
def Grp.codes(cols: List<&1, C.Named>, +n: U32, +d: Nat, st: List<&1, C.Named> & Codes) -> List<&1, C.Named> & Codes:
  match cols:
    case Nil{}:
      st
    case C.Named{name, col} <> t:
      Grp.codes(t, n, d, Grp.codes.step(n, d, name, col, st))

# key output columns: each key column at its group's first row
def Grp.kout.add(name: String, acc: List<&1, C.Named>, +ng: U32, gids: Array<U32>, r: C.Column & Array<U32>) -> Groups & List<&1, C.Named>:
  (c, first) = r
  (Groups{ng, gids, first}, C.Named{name, c} <> acc)

def Grp.kout.step(name: String, col: C.Column, st: Groups & List<&1, C.Named>) -> Groups & List<&1, C.Named>:
  (g, acc) = st
  match g:
    case Groups{+ng, gids, first}:
      Grp.kout.add(name, acc, ng, gids, C.Column.gather(col, first, ng))

def Grp.kout(cols: List<&1, C.Named>, st: Groups & List<&1, C.Named>) -> Groups & List<&1, C.Named>:
  match cols:
    case Nil{}:
      st
    case C.Named{name, col} <> t:
      Grp.kout(t, Grp.kout.step(name, col, st))

# ---- aggregations ------------------------------------------------------------------------------------

def Grp.aout.put(+name: String, f: C.Frame, acc: List<&1, C.Named>, r: Groups & E.ResT(C.Column)) -> ASt:
  (g, rc) = r
  match rc:
    case Fail{e}:
      ASt{f, g, Fail{e}}
    case Done{c}:
      ASt{f, g, Done{C.Named{name, c} <> acc}}

def Grp.aout.full(op: X.AggOp, +name: String, g: Groups, acc: List<&1, C.Named>, r: C.Frame & E.ResT(C.Column)) -> ASt:
  (f, rc) = r
  match rc:
    case Fail{e}:
      ASt{f, g, Fail{e}}
    case Done{c}:
      Grp.aout.put(name, f, acc, Grp.agg(op, g, c))

def Grp.aout.lit.b(+name: String, f: C.Frame, acc: List<&1, C.Named>, c: C.Column, g: Groups) -> ASt:
  match g:
    case Groups{+ng, gids, first}:
      ASt{f, Groups{ng, gids, first}, Done{C.Named{name, V.Eval.bcast(c, ng)} <> acc}}

# a literal-only input (sum(lit 2)): the 1-row aggregation, repeated per group
def Grp.aout.lit(+name: String, g: Groups, acc: List<&1, C.Named>, r: C.Frame & E.ResT(C.Column)) -> ASt:
  (f, rc) = r
  match rc:
    case Fail{e}:
      ASt{f, g, Fail{e}}
    case Done{c}:
      Grp.aout.lit.b(name, f, acc, c, g)

def Grp.aout.kind(lit: Bool, +op: X.AggOp, +inner: X.Expr, +name: String, f: C.Frame, g: Groups, acc: List<&1, C.Named>) -> ASt:
  match lit:
    case True{}:
      Grp.aout.lit(name, g, acc, V.Eval.expr(f, X.Agg{op, inner}))
    case False{}:
      Grp.aout.full(op, name, g, acc, V.Eval.full(f, inner))

def Grp.is_klit(k: V.SKind) -> Bool:
  match k:
    case V.KLit{}:
      True{}
    case _:
      False{}

def Grp.is_len(op: X.AggOp) -> Bool:
  match op:
    case X.Len{}:
      True{}
    case _:
      False{}

def Grp.aout.split(+name: String, s: Maybe<&2, X.AggSplit>, f: C.Frame, g: Groups, acc: List<&1, C.Named>) -> ASt:
  match s:
    case None{}:
      ASt{f, g, Fail{Grp.bug("non-aggregation")}}
    case Some{X.AggSplit{+op, +inner}}:
      Grp.aout.kind(Bool.and(Grp.is_klit(V.Eval.kind(inner)), Bool.not(Grp.is_len(op))), op, inner, name, f, g, acc)

def Grp.aout.step(+e: X.Expr, st: ASt) -> ASt:
  match st:
    case ASt{f, g, Fail{err}}:
      ASt{f, g, Fail{err}}
    case ASt{f, g, Done{acc}}:
      Grp.aout.split(X.Expr.name(e), X.Expr.split_agg(e), f, g, acc)

def Grp.aout(ags: List<&2, X.Expr>, st: ASt) -> ASt:
  match ags:
    case Nil{}:
      st
    case a <> t:
      Grp.aout(t, Grp.aout.step(a, st))

# ---- entry point -----------------------------------------------------------------------------------------

def GroupBy.fin(st: ASt) -> E.ResT(C.Frame):
  match st:
    case ASt{f, g, Fail{e}}:
      Fail{e}
    case ASt{f, g, Done{acc}}:
      C.Frame.from_columns(List.reverse(&1, C.Named, acc))

def GroupBy.out.b(aggs: List<&2, X.Expr>, f: C.Frame, r: Groups & List<&1, C.Named>) -> E.ResT(C.Frame):
  (g, acc) = r
  GroupBy.fin(Grp.aout(aggs, ASt{f, g, Done{acc}}))

def GroupBy.out(aggs: List<&2, X.Expr>, f: C.Frame, kc: List<&1, C.Named>, g: Groups) -> E.ResT(C.Frame):
  GroupBy.out.b(aggs, f, Grp.kout(kc, (g, Nil{})))

def GroupBy.group(+n: U32, +d: Nat, aggs: List<&2, X.Expr>, f: C.Frame, r: List<&1, C.Named> & Codes) -> E.ResT(C.Frame):
  (kc, cd) = r
  match cd:
    case Codes{+k, c}:
      GroupBy.out(aggs, f, kc, Grp.densify(n, d, k, c))

def GroupBy.keyed.b(aggs: List<&2, X.Expr>, kc: List<&1, C.Named>, r: C.Frame & U32) -> E.ResT(C.Frame):
  (f, +n) = r
  +d = K.Kernel.depth_for(n)
  GroupBy.group(n, d, aggs, f, Grp.codes(kc, n, d, (Nil{}, Codes{1, Array.new(U32, d, 0)})))

def GroupBy.keyed(aggs: List<&2, X.Expr>, st: GSt) -> E.ResT(C.Frame):
  match st:
    case GSt{f, Fail{e}}:
      Fail{e}
    case GSt{f, Done{kc}}:
      GroupBy.keyed.b(aggs, kc, C.Frame.height(f))

def GroupBy.run.b(err: Maybe<&2, E.Err>, f: C.Frame, keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match err:
    case Some{e}:
      Fail{e}
    case None{}:
      GroupBy.keyed(aggs, Grp.keys(keys, GSt{f, Done{Nil{}}}))

# the row cap (DESIGN.md 15.8): ng <= the input height h, so h under the cap bounds every group
# array; checked after the type errors and before any key expression is evaluated or any array built
def GroupBy.run.h(err: Maybe<&2, E.Err>, +keys: List<&2, X.Expr>, +aggs: List<&2, X.Expr>, r: C.Frame & U32) -> E.ResT(C.Frame):
  (f, +h) = r
  GroupBy.run.b(Maybe.or(&2, E.Err, err, K.Kernel.check_rows(h)), f, keys, aggs)

def GroupBy.run.a(+keys: List<&2, X.Expr>, +aggs: List<&2, X.Expr>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, +s) = r
  GroupBy.run.h(Grp.validate(keys, aggs, s), keys, aggs, C.Frame.height(f))

# group the frame by the key expressions and aggregate: output = one row per
# distinct key tuple (null keys form one group), key columns (named
# Expr.name) then one column per aggregation (Expr.name). Each aggregation
# must be `Agg{op, e}` under at most Aliases with no aggregation inside `e`;
# per group it equals Eval.agg(op) over the group's rows in input order
# (`Agg{Len, _}` = group size; a literal-only `e` aggregates the literal once,
# Polars: sum(lit 2) = 2 per group). Groups come in first-appearance order
# (also when maintain_order = False{}; see DESIGN.md 14 M5). The frame is
# consumed.
def GroupBy.run(f: C.Frame, +keys: List<&2, X.Expr>, +aggs: List<&2, X.Expr>, maintain_order: Bool) -> E.ResT(C.Frame):
  GroupBy.run.a(keys, aggs, S.Frame.schema(f))
