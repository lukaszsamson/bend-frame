# src/kernels.bend -- flat, sequential, template array loops. DESIGN.md 4.3.
# Idioms (DESIGN.md section 9): helpers above callers; every loop is a
# tail-recursive def with Nat fuel first and an index counter; a call's pair
# result is taken apart in the NEXT step's parameter (R3); templates ~T: Data
# (R5). Kernels consume their input arrays unless the signature hands them back.
import Base

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

def Kernel.from_list(~T: Data, +xs: List<&2, T>, +z: T) -> U32 & Array<T>:
  +n = U32.from_nat(List.length(&2, T, xs))
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
