# src/kernels.bend -- flat, sequential, template array loops. DESIGN.md 4.3.
# Idioms (DESIGN.md section 9): helpers above callers; every loop is a
# tail-recursive def with Nat fuel first and an index counter; a call's pair
# result is taken apart in the NEXT step's parameter (R3); templates ~T: Data
# (R5). Kernels consume their input arrays unless the signature hands them back.
import Base
import ./err.bend as E

# the least depth d with 2^d >= n (n >= 1); the exit test rides as a parameter
def Kernel.depth_for.go(f: Nat, +n: U32, +d: Nat, fits: Bool) -> Nat:
  match f fits:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+p False{}:
      Kernel.depth_for.go(p, n, 1n+d, U32.is_le(n, U32.shln(1, 1n+d)))

def Kernel.depth_for(+n: U32) -> Nat:
  Kernel.depth_for.go(32n, n, 0n, U32.is_le(n, 1))

# out[i] = f(a[i]) for i < n, consuming a; r is the NEXT read (a, a[i])
def Kernel.map.go(~T: Data, ~U: Data, ~f: T -> U, n: Nat, +i: U32, out: Array<U>, r: Array<T> & T) -> Array<U>:
  match n:
    case 0n:
      out
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Kernel.map.go(~T, ~U, ~f, p, j, Array.set(U, out, i, f(x)), Array.get(T, a, j))

def Kernel.map(~T: Data, ~U: Data, ~f: T -> U, +n: U32, +d: Nat, a: Array<T>, +z: U) -> Array<U>:
  Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z), Array.get(T, a, 0))

# out[i] = f(a[i], b[i]); ra, rb are the next reads
def Kernel.zip.go(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, n: Nat, +i: U32, out: Array<V>, ra: Array<T> & T, rb: Array<U> & U) -> Array<V>:
  match n:
    case 0n:
      out
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      Kernel.zip.go(~T, ~U, ~V, ~f, p, j, Array.set(V, out, i, f(x, y)), Array.get(T, a, j), Array.get(U, b, j))

def Kernel.zip(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, a: Array<T>, b: Array<U>, +z: V) -> Array<V>:
  Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0))

# acc = f(acc, a[i]) over i < n; the array comes back
def Kernel.fold.go(~T: Data, ~A: Data, ~f: A -> T -> A, n: Nat, +i: U32, acc: A, r: Array<T> & T) -> Array<T> & A:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Kernel.fold.go(~T, ~A, ~f, p, j, f(acc, x), Array.get(T, a, j))

def Kernel.fold(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, a: Array<T>, z: A) -> Array<T> & A:
  Kernel.fold.go(~T, ~A, ~f, U32.to_nat(n), 0, z, Array.get(T, a, 0))

# branch-free compaction: out[k] = a[i], k += mask[i]; answers (out, k)
def Kernel.compact.put(~T: Data, out: Array<T>, +k: U32, r: Array<T> & T) -> Array<T> & Array<T>:
  (a, x) = r
  (a, Array.set(T, out, k, x))

def Kernel.compact.go(~T: Data, n: Nat, +i: U32, +k: U32, ao: Array<T> & Array<T>, mi: Array<U32> & U32) -> Array<T> & U32:
  match n:
    case 0n:
      (a, out) = ao
      (out, k)
    case 1n+p:
      (a, out) = ao
      (mask, bit) = mi
      +j = U32.inc(i)
      Kernel.compact.go(~T, p, j, U32.add(k, bit), Kernel.compact.put(~T, out, k, Array.get(T, a, i)), Array.get(U32, mask, j))

def Kernel.compact(~T: Data, +n: U32, +d: Nat, a: Array<T>, mask: Array<U32>, +z: T) -> Array<T> & U32:
  Kernel.compact.go(~T, U32.to_nat(n), 0, 0, (a, Array.new(T, d, z)), Array.get(U32, mask, 0))

# Kernel.compact that hands the mask back instead of the count, so one mask
# can filter every buffer of a column (data, then validity) and every column
def Kernel.compact_keep.go(~T: Data, n: Nat, +i: U32, +k: U32, ao: Array<T> & Array<T>, mi: Array<U32> & U32) -> Array<T> & Array<U32>:
  match n:
    case 0n:
      (a, out) = ao
      (mask, bit) = mi
      (out, mask)
    case 1n+p:
      (a, out) = ao
      (mask, bit) = mi
      +j = U32.inc(i)
      Kernel.compact_keep.go(~T, p, j, U32.add(k, bit), Kernel.compact.put(~T, out, k, Array.get(T, a, i)), Array.get(U32, mask, j))

def Kernel.compact_keep(~T: Data, +n: U32, +d: Nat, a: Array<T>, mask: Array<U32>, +z: T) -> Array<T> & Array<U32>:
  Kernel.compact_keep.go(~T, U32.to_nat(n), 0, 0, (a, Array.new(T, d, z)), Array.get(U32, mask, 0))

# out[j] = src[perm[j]] for j < n; answers (out, perm)
def Kernel.gather.put(~T: Data, out: Array<T>, +j: U32, r: Array<T> & T) -> Array<T> & Array<T>:
  (src, x) = r
  (src, Array.set(T, out, j, x))

def Kernel.gather.go(~T: Data, n: Nat, +j: U32, so: Array<T> & Array<T>, r: Array<U32> & U32) -> Array<T> & Array<U32>:
  match n:
    case 0n:
      (src, out) = so
      (perm, i) = r
      (out, perm)
    case 1n+p:
      (src, out) = so
      (perm, i) = r
      +j2 = U32.inc(j)
      Kernel.gather.go(~T, p, j2, Kernel.gather.put(~T, out, j, Array.get(T, src, i)), Array.get(U32, perm, j2))

def Kernel.gather(~T: Data, +n: U32, +d: Nat, src: Array<T>, perm: Array<U32>, +z: T) -> Array<T> & Array<U32>:
  Kernel.gather.go(~T, U32.to_nat(n), 0, (src, Array.new(T, d, z)), Array.get(U32, perm, 0))

# acc[g[i]] = f(acc[g[i]], v[i]) for i < n: the scatter behind group_by
def Kernel.scatter.put(~T: Data, ~A: Data, ~f: A -> T -> A, +g: U32, x: T, r: Array<A> & A) -> Array<A>:
  (acc, old) = r
  Array.set(A, acc, g, f(old, x))

def Kernel.scatter.go(~T: Data, ~A: Data, ~f: A -> T -> A, n: Nat, +i: U32, acc: Array<A>, rg: Array<U32> & U32, rv: Array<T> & T) -> Array<A>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      Kernel.scatter.go(~T, ~A, ~f, p, j, Kernel.scatter.put(~T, ~A, ~f, g, x, Array.get(A, acc, g)), Array.get(U32, gs, j), Array.get(T, vs, j))

def Kernel.scatter(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, gids: Array<U32>, vals: Array<T>, acc: Array<A>) -> Array<A>:
  Kernel.scatter.go(~T, ~A, ~f, U32.to_nat(n), 0, acc, Array.get(U32, gids, 0), Array.get(T, vals, 0))

# a list into a fresh array of 2^depth_for(n) slots padded with z
def Kernel.fill.go(~T: Data, xs: List<&2, T>, +i: U32, a: Array<T>) -> Array<T>:
  match xs:
    case Nil{}:
      a
    case h <> t:
      Kernel.fill.go(~T, t, U32.inc(i), Array.set(T, a, i, h))

# the length of a list plus n, as a tail call (Base List.length is not one: it overflows the
# interpreter's stack on ~2^15 elements, NEW-2); wraps past 2^32 - 1 elements
def Kernel.count(~T: Data, xs: List<&2, T>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case h <> t:
      Kernel.count(~T, t, U32.inc(n))

def Kernel.from_list(~T: Data, +xs: List<&2, T>, +z: T) -> U32 & Array<T>:
  +n = Kernel.count(~T, xs, 0)
  (n, Kernel.fill.go(~T, xs, 0, Array.new(T, Kernel.depth_for(U32.max(n, 1)), z)))

# ---- extras (DESIGN.md 4.3 "Add:") ----------------------------------------------

# out[i] = off + i for i < n
def Kernel.iota.go(n: Nat, +i: U32, +off: U32, out: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      out
    case 1n+p:
      Kernel.iota.go(p, U32.inc(i), off, Array.set(U32, out, i, U32.add(off, i)))

def Kernel.iota_from(+n: U32, +d: Nat, +off: U32) -> Array<U32>:
  Kernel.iota.go(U32.to_nat(n), 0, off, Array.new(U32, d, 0))

# out[i] = i for i < n
def Kernel.iota(+n: U32, +d: Nat) -> Array<U32>:
  Kernel.iota_from(n, d, 0)

# 2^d slots of z
def Kernel.const(~T: Data, +d: Nat, +z: T) -> Array<T>:
  Array.new(T, d, z)

# the first n slots as a list, in order; the array comes back. The loop runs
# from the last slot to the first so consing yields ascending order.
def Kernel.to_list.go(~T: Data, n: Nat, +i: U32, acc: List<&2, T>, r: Array<T> & T) -> Array<T> & List<&2, T>:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      Kernel.to_list.go(~T, p, U32.sub(i, 1), x <> acc, Array.get(T, a, U32.sub(i, 1)))

def Kernel.to_list(~T: Data, +n: U32, a: Array<T>) -> Array<T> & List<&2, T>:
  Kernel.to_list.go(~T, U32.to_nat(n), U32.sub(n, 1), Nil{}, Array.get(T, a, U32.sub(n, 1)))

# elementwise boolean algebra over 0/1 words
def Kernel.mask_and(+n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32>:
  Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, a, b, 0)

def Kernel.mask_or(+n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32>:
  Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.or(x, y)), n, d, a, b, 0)

def Kernel.mask_not(+n: U32, +d: Nat, a: Array<U32>) -> Array<U32>:
  Kernel.map(~U32, ~U32, ~(x => U32.xor(x, 1)), n, d, a, 0)

# the number of set words among the first n; the mask comes back
def Kernel.popcount(+n: U32, mask: Array<U32>) -> Array<U32> & U32:
  Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, mask, 0)

# are the first n elements equal under eq? Both arrays are consumed.
def Kernel.all_eq.go(~T: Data, ~eq: T -> T -> Bool, n: Nat, +i: U32, acc: U32, ra: Array<T> & T, rb: Array<T> & T) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      Kernel.all_eq.go(~T, ~eq, p, j, U32.and(acc, Bool.to_u32(eq(x, y))), Array.get(T, a, j), Array.get(T, b, j))

def Kernel.all_eq(~T: Data, ~eq: T -> T -> Bool, +n: U32, a: Array<T>, b: Array<T>) -> Bool:
  U32.is_ne(Kernel.all_eq.go(~T, ~eq, U32.to_nat(n), 0, 1, Array.get(T, a, 0), Array.get(T, b, 0)), 0)

# the M7 knob: levels of ANode splitting for forked kernels (0 = flat loops)
def Kernel.fork_depth() -> Nat:
  0n

# ---- M2 extras (eval) -----------------------------------------------------------

# in place: a[i] := z where m[i] = 0, for i < n (null slots back to the dtype
# default); answers (a, m)
def Kernel.mask_data.go(~T: Data, n: Nat, +i: U32, +z: T, ra: Array<T> & T, rm: Array<U32> & U32) -> Array<T> & Array<U32>:
  match n:
    case 0n:
      (a, x) = ra
      (m, w) = rm
      (a, m)
    case 1n+p:
      (a, x) = ra
      (m, w) = rm
      +j = U32.inc(i)
      Kernel.mask_data.go(~T, p, j, z, Array.get(T, Array.set(T, a, i, Bool.pick(T, U32.is_ne(w, 0), x, z)), j), Array.get(U32, m, j))

def Kernel.mask_data(~T: Data, +n: U32, a: Array<T>, m: Array<U32>, +z: T) -> Array<T> & Array<U32>:
  Kernel.mask_data.go(~T, U32.to_nat(n), 0, z, Array.get(T, a, 0), Array.get(U32, m, 0))

# in place into a: a[i] := m[i] ? a[i] : b[i] for i < n (b consumed);
# answers (m, a)
def Kernel.choose.go(~T: Data, n: Nat, +i: U32, ra: Array<T> & T, rb: Array<T> & T, rm: Array<U32> & U32) -> Array<U32> & Array<T>:
  match n:
    case 0n:
      (a, x) = ra
      (b, y) = rb
      (m, w) = rm
      (m, a)
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      (m, w) = rm
      +j = U32.inc(i)
      Kernel.choose.go(~T, p, j, Array.get(T, Array.set(T, a, i, Bool.pick(T, U32.is_ne(w, 0), x, y)), j), Array.get(T, b, j), Array.get(U32, m, j))

def Kernel.choose(~T: Data, +n: U32, m: Array<U32>, a: Array<T>, b: Array<T>) -> Array<U32> & Array<T>:
  Kernel.choose.go(~T, U32.to_nat(n), 0, Array.get(T, a, 0), Array.get(T, b, 0), Array.get(U32, m, 0))

# ---- the F32 policy (DESIGN.md 15.5.2, 15.5.3): one relation, one accumulation ---------

# the total-order word of an f32 (15.5.2): -inf < .. < -0.0 = 0.0 < .. < +inf < NaN, every
# NaN (any payload, any sign) the largest word; negatives are bit-flipped, positives get the
# sign bit set. `x op y` over f32 (== != < <= > >=, sort, group_by, n_unique, join keys) is
# `U32 op` of these words. Sort.fword is this function.
def Kernel.fword.b(+b: U32) -> U32:
  +a = U32.and(b, 2147483647)
  Bool.pick(U32, U32.is_gt(a, 2139095040), 4294967295, Bool.pick(U32, U32.is_zero(a), 2147483648, Bool.pick(U32, U32.is_ge(b, 2147483648), U32.xor(b, 4294967295), U32.or(b, 2147483648))))

def Kernel.fword(x: F32) -> U32:
  Kernel.fword.b(F32.bits(x))

# finite: neither +-inf nor NaN (exponent bits not all ones)
def Kernel.is_finite(x: F32) -> Bool:
  U32.is_lt(U32.and(F32.bits(x), 2147483647), 2139095040)

def Kernel.is_nan(+x: F32) -> Bool:
  Bool.not(F32.is_eq(x, x))

# min / max (15.5.2 exceptions): NaN is skipped (both NaN -> NaN); a -0.0 / 0.0 tie gives
# -0.0 for min and 0.0 for max, whatever the order; otherwise IEEE `<`
def Kernel.fmin(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, Kernel.is_nan(a), b, Bool.pick(F32, Kernel.is_nan(b), a, Bool.pick(F32, F32.is_lt(a, b), a, Bool.pick(F32, F32.is_lt(b, a), b, Bool.pick(F32, U32.is_ge(F32.bits(a), 2147483648), a, b)))))

def Kernel.fmax(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, Kernel.is_nan(a), b, Bool.pick(F32, Kernel.is_nan(b), a, Bool.pick(F32, F32.is_lt(b, a), a, Bool.pick(F32, F32.is_lt(a, b), b, Bool.pick(F32, U32.is_ge(F32.bits(a), 2147483648), b, a)))))

# Neumaier accumulation with a non-finite guard (15.5.3): state (s, c), both f32
type NS is Data:
  NS{s: F32, c: F32}

# the compensation after t = s + x: Neumaier's term while t is finite, c unchanged once
# the partial sum is +-inf or NaN (c is never read again then)
def Kernel.nm.c(fin: Bool, +s: F32, +x: F32, +t: F32, +c: F32) -> F32:
  match fin:
    case True{}:
      F32.add(c, Bool.pick(F32, F32.is_ge(F32.abs(s), F32.abs(x)), F32.add(F32.sub(s, t), x), F32.add(F32.sub(x, t), s)))
    case False{}:
      c

# one step: the sum s, the compensation c, the next value x
def Kernel.nm.add(+s: F32, +c: F32, +x: F32) -> NS:
  +t = F32.add(s, x)
  NS{t, Kernel.nm.c(Kernel.is_finite(t), s, x, t, c)}

def Kernel.nm.step(acc: NS, +x: F32) -> NS:
  match acc:
    case NS{+s, +c}:
      Kernel.nm.add(s, c, x)

# the result: s + c while s is finite, s itself (+-inf or NaN) otherwise
def Kernel.nm.result(+s: F32, +c: F32) -> F32:
  Bool.pick(F32, Kernel.is_finite(s), F32.add(s, c), s)

def Kernel.nm.fin(acc: NS) -> F32:
  match acc:
    case NS{+s, +c}:
      Kernel.nm.result(s, c)

# the 15.5.3 sum of cv(a[i]) over i < n, in ascending i; a is consumed
def Kernel.fsum.go(~T: Data, ~cv: T -> F32, n: Nat, +i: U32, acc: NS, r: Array<T> & T) -> F32:
  match n:
    case 0n:
      Kernel.nm.fin(acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Kernel.fsum.go(~T, ~cv, p, j, Kernel.nm.step(acc, cv(x)), Array.get(T, a, j))

def Kernel.fsum(~T: Data, ~cv: T -> F32, +n: U32, a: Array<T>) -> F32:
  Kernel.fsum.go(~T, ~cv, U32.to_nat(n), 0, NS{0.0, 0.0}, Array.get(T, a, 0))

# the first i < n with a[i] != 0 and b[i] = 0, else n (a cell valid in a, null in b);
# a 1-slot array reads its one slot for every i. Both arrays are consumed.
def Kernel.first_drop.go(n: Nat, +i: U32, +m: U32, +acc: U32, ra: Array<U32> & U32, rb: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      Kernel.first_drop.go(p, j, m, Bool.pick(U32, Bool.and(U32.is_eq(acc, m), Bool.and(U32.is_ne(x, 0), U32.is_zero(y))), i, acc), Array.get(U32, a, j), Array.get(U32, b, j))

def Kernel.first_drop(+n: U32, a: Array<U32>, b: Array<U32>) -> U32:
  Kernel.first_drop.go(U32.to_nat(n), 0, n, n, Array.get(U32, a, 0), Array.get(U32, b, 0))

# out[i] = v and ok[i] = 1 where f(a[i]) = Some{v}, else z and 0; one pass
# over a (consumed); answers (out, ok), both of 2^d slots
def Kernel.map_maybe.put(~U: Data, +i: U32, +z: U, out: Array<U>, ok: Array<U32>, m: Maybe<&2, U>) -> Array<U> & Array<U32>:
  match m:
    case Some{v}:
      (Array.set(U, out, i, v), Array.set(U32, ok, i, 1))
    case None{}:
      (Array.set(U, out, i, z), Array.set(U32, ok, i, 0))

def Kernel.map_maybe.go(~T: Data, ~U: Data, ~f: T -> Maybe<&2, U>, n: Nat, +i: U32, +z: U, oo: Array<U> & Array<U32>, r: Array<T> & T) -> Array<U> & Array<U32>:
  match n:
    case 0n:
      oo
    case 1n+p:
      (out, ok) = oo
      (a, x) = r
      +j = U32.inc(i)
      Kernel.map_maybe.go(~T, ~U, ~f, p, j, z, Kernel.map_maybe.put(~U, i, z, out, ok, f(x)), Array.get(T, a, j))

def Kernel.map_maybe(~T: Data, ~U: Data, ~f: T -> Maybe<&2, U>, +n: U32, +d: Nat, a: Array<T>, +z: U) -> Array<U> & Array<U32>:
  Kernel.map_maybe.go(~T, ~U, ~f, U32.to_nat(n), 0, z, (Array.new(U, d, z), Array.new(U32, d, 0)), Array.get(T, a, 0))

# out[i] = v and ok[i] = 1 where f(a[i], b[i]) = Some{v}, else z and 0 (both consumed)
def Kernel.zip_maybe.go(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> Maybe<&2, V>, n: Nat, +i: U32, +z: V, oo: Array<V> & Array<U32>, ra: Array<T> & T, rb: Array<U> & U) -> Array<V> & Array<U32>:
  match n:
    case 0n:
      oo
    case 1n+p:
      (out, ok) = oo
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      Kernel.zip_maybe.go(~T, ~U, ~V, ~f, p, j, z, Kernel.map_maybe.put(~V, i, z, out, ok, f(x, y)), Array.get(T, a, j), Array.get(U, b, j))

def Kernel.zip_maybe(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> Maybe<&2, V>, +n: U32, +d: Nat, a: Array<T>, b: Array<U>, +z: V) -> Array<V> & Array<U32>:
  Kernel.zip_maybe.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, z, (Array.new(V, d, z), Array.new(U32, d, 0)), Array.get(T, a, 0), Array.get(U, b, 0))

# ---- row cap (DESIGN.md 15.8, B04-i) ---------------------------------------------------------------
# A frame holds at most 2^23 rows. Kernel.depth_for alone is not a guard: every path that
# allocates a height not bounded by an existing frame calls check_rows before allocating.

def Kernel.max_rows() -> U32:
  8388608

# check_rows with the cap as a parameter: the entry the tests use with a lowered cap
# (the error text names the cap it was given); check_rows is this at max_rows()
def Kernel.check_rows.cap(+cap: U32, +n: U32) -> Maybe<&2, E.Err>:
  Bool.pick(Maybe<&2, E.Err>, U32.is_gt(n, cap), Some{E.InvalidOperation{"too many rows: " ++ U32.show(n) ++ " exceeds " ++ U32.show(cap)}}, None{})

def Kernel.check_rows(+n: U32) -> Maybe<&2, E.Err>:
  Kernel.check_rows.cap(Kernel.max_rows(), n)

# ---- M3 (expressions): a map with a Data parameter ---------------------------------------

# out[i] = f(p, a[i]) for i < n, consuming a. `p` is a Data value every step sees: what a
# template lambda cannot capture (is_in's literal list, clip's bounds, a string pattern).
def Kernel.map_p.go(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, n: Nat, +i: U32, +p: P, out: Array<U>, r: Array<T> & T) -> Array<U>:
  match n:
    case 0n:
      out
    case 1n+q:
      (a, x) = r
      +j = U32.inc(i)
      Kernel.map_p.go(~T, ~P, ~U, ~f, q, j, p, Array.set(U, out, i, f(p, x)), Array.get(T, a, j))

def Kernel.map_p(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +n: U32, +d: Nat, a: Array<T>, +p: P, +z: U) -> Array<U>:
  Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0))
