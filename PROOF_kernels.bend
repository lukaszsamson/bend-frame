# PROOF_kernels.bend -- proofs of LAWS.bend sections 5 and 5b (columns and
# kernels: array shape through Laws.slots, with the Sigma-witness pattern).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/plan.bend as P
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L

# =====================================================================================
# 5. Columns
# =====================================================================================

def Laws.head_len(c, n):
  match c:
    case C.CBool{len, depth, valid, data}:
      {==}
    case C.CU32{len, depth, valid, data}:
      {==}
    case C.CI32{len, depth, valid, data}:
      {==}
    case C.CF32{len, depth, valid, data}:
      {==}
    case C.CStr{len, depth, valid, data}:
      {==}

def Laws.head_dtype(c, n):
  match c:
    case C.CBool{len, depth, valid, data}:
      {==}
    case C.CU32{len, depth, valid, data}:
      {==}
    case C.CI32{len, depth, valid, data}:
      {==}
    case C.CF32{len, depth, valid, data}:
      {==}
    case C.CStr{len, depth, valid, data}:
      {==}

# =====================================================================================
# 5b. Kernels: array shape. Arrays are affine, so every lemma that rewrites one
# hands the rewritten array back as a witness (&b: Array<T> -> ...) beside
# the equation about it.
# =====================================================================================

# Array.size(xs) = (b, n) lifted to the node: size.node rebuilds ANode{b, ys}
def size_node(-T: Type, -xs: Array<T>, ys: Array<T>, w: &b: Array<T> -> &n: U32 -> {Array.size(T, xs) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32} & {Laws.slots(T, xs) == n : U32})
  -> &b2: Array<T> -> &n2: U32 -> {Array.size(T, ANode{xs, ys}) == (b2, n2) : Array<T> & U32} & {Laws.slots(T, b2) == n2 : U32} & {Laws.slots(T, ANode{xs, ys}) == n2 : U32}:
  (b, n0, eq, sl, sa) = w
  +n = n0
  (ANode{b, ys}, U32.shl(n), (%Equal.sym(Array<T> & U32, Array.size(T, xs), (b, n), eq) : {Array.size.node(T, ys, _) == (ANode{b, ys}, U32.shl(n)) : Array<T> & U32}; {==}), (%sl : {U32.shl(Laws.slots(T, b)) == U32.shl(_) : U32}; {==}), (%sa : {U32.shl(Laws.slots(T, xs)) == U32.shl(_) : U32}; {==}))

# Array.size(a) is (b, n): b is a handed back live, n the slots of both
def size_is(-T: Type, a: Array<T>) -> &b: Array<T> -> &n: U32 -> {Array.size(T, a) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32} & {Laws.slots(T, a) == n : U32}:
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1, {==}, {==}, {==})
    case ANode{xs, ys}:
      size_node(T, xs, ys, size_is(T, xs))

# the swap of the left half lifted to the node
def swap_lo(-T: Type, -xs: Array<T>, ys: Array<T>, -n: U32, -i: U32, -v: T, w: &c: Array<T> -> &o: T -> {Array.swap.go(T, xs, n, i, v, U32.is_lt(i, U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, xs) : U32})
  -> &c2: Array<T> -> &o2: T -> {Array.swap.lo(T, ys, Array.swap.go(T, xs, n, i, v, U32.is_lt(i, U32.shr(n)))) == (c2, o2) : Array<T> & T} & {Laws.slots(T, c2) == Laws.slots(T, ANode{xs, ys}) : U32}:
  (c, o, eq, sl) = w
  (ANode{c, ys}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, xs, n, i, v, U32.is_lt(i, U32.shr(n))), (c, o), eq) : {Array.swap.lo(T, ys, _) == (ANode{c, ys}, o) : Array<T> & T}; {==}), (%sl : {U32.shl(Laws.slots(T, c)) == U32.shl(_) : U32}; {==}))

# the swap of the right half lifted to the node (the slots are the left half's)
def swap_hi(-T: Type, xs: Array<T>, -ys: Array<T>, -n: U32, -j: U32, -v: T, w: &c: Array<T> -> &o: T -> {Array.swap.go(T, ys, n, j, v, U32.is_lt(j, U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, ys) : U32})
  -> &c2: Array<T> -> &o2: T -> {Array.swap.hi(T, xs, Array.swap.go(T, ys, n, j, v, U32.is_lt(j, U32.shr(n)))) == (c2, o2) : Array<T> & T} & {Laws.slots(T, c2) == Laws.slots(T, ANode{xs, ys}) : U32}:
  (c, o, eq, sl) = w
  (ANode{xs, c}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, ys, n, j, v, U32.is_lt(j, U32.shr(n))), (c, o), eq) : {Array.swap.hi(T, xs, _) == (ANode{xs, c}, o) : Array<T> & T}; {==}), {==})

# Array.swap.go answers (c, o) with c of a's slots
def swap_ex(-T: Type, a: Array<T>, +n: U32, +i: U32, v: T, z: Bool) -> &c: Array<T> -> &o: T -> {Array.swap.go(T, a, n, i, v, z) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, a) : U32}:
  match a z:
    case ALeaf{x} _:
      (ALeaf{v}, x, {==}, {==})
    case ANode{xs, ys} True{}:
      swap_lo(T, xs, ys, U32.shr(n), i, v, swap_ex(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))))
    case ANode{xs, ys} False{}:
      swap_hi(T, xs, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, swap_ex(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))

# Array.set(out, i, v) = set.fin(swap.at(i, v, size(out))): the size step (eq1)
# then the swap step (w) give the written array c, with out's slots k
def set_swap(-T: Type, -out: Array<T>, -b1: Array<T>, -n: U32, -i: U32, -v: T, -k: U32,
  eq1: {Array.size(T, out) == (b1, n) : Array<T> & U32}, sl1: {Laws.slots(T, b1) == n : U32}, sa1: {Laws.slots(T, out) == n : U32}, hk: {Laws.slots(T, out) == k : U32},
  w: &c: Array<T> -> &o: T -> {Array.swap.go(T, b1, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, b1) : U32})
  -> &b: Array<T> -> {Array.set(T, out, i, v) == b : Array<T>} & {Laws.slots(T, b) == k : U32}:
  (c, o, eq2, sl2) = w
  (c, (%Equal.sym(Array<T> & U32, Array.size(T, out), (b1, n), eq1) : {Array.set.fin(T, Array.swap.at(T, i, v, _)) == c : Array<T>}; %Equal.sym(Array<T> & T, Array.swap.go(T, b1, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))), (c, o), eq2) : {Array.set.fin(T, _) == c : Array<T>}; {==}), (%hk : {Laws.slots(T, c) == _ : U32}; %Equal.sym(U32, Laws.slots(T, out), n, sa1) : {Laws.slots(T, c) == _ : U32}; %sl1 : {Laws.slots(T, c) == _ : U32}; sl2))

def set_size(-T: Type, -out: Array<T>, +i: U32, v: T, -k: U32, hk: {Laws.slots(T, out) == k : U32}, w: &b1: Array<T> -> &n: U32 -> {Array.size(T, out) == (b1, n) : Array<T> & U32} & {Laws.slots(T, b1) == n : U32} & {Laws.slots(T, out) == n : U32})
  -> &b: Array<T> -> {Array.set(T, out, i, v) == b : Array<T>} & {Laws.slots(T, b) == k : U32}:
  (b1, n0, eq1, sl1, sa1) = w
  +n = n0
  set_swap(T, out, b1, n, i, v, k, eq1, sl1, sa1, hk, swap_ex(T, b1, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))

# Array.set keeps the slots: the written array is handed back live
def set_ex(-T: Type, out: Array<T>, +i: U32, v: T, -k: U32, hk: {Laws.slots(T, out) == k : U32}) -> &b: Array<T> -> {Array.set(T, out, i, v) == b : Array<T>} & {Laws.slots(T, b) == k : U32}:
  set_size(T, out, i, v, k, hk, size_is(T, out))

# one step of Kernel.map.go: the written array b replaces Array.set(out, i, f(x))
# and the induction hypothesis ih runs the remaining fuel over it
def map_step(~T: Data, ~U: Data, ~f: T -> U, -p: Nat, -j: U32, -out: Array<U>, -i: U32, -x: T, -k: U32, r2: Array<T> & T,
  w: &b: Array<U> -> {Array.set(U, out, i, f(x)) == b : Array<U>} & {Laws.slots(U, b) == k : U32},
  ih: @b: Array<U> -> @r: Array<T> & T -> {Laws.slots(U, b) == k : U32} -> {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, p, j, b, r)) == k : U32})
  -> {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, p, j, Array.set(U, out, i, f(x)), r2)) == k : U32}:
  (b, eq, sl) = w
  %Equal.sym(Array<U>, Array.set(U, out, i, f(x)), b, eq) : {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, p, j, _, r2)) == k : U32}
  ih(b, r2, sl)

# Kernel.map.go only ever writes into out: the slots stay k
def map_go_slots(~T: Data, ~U: Data, ~f: T -> U, fuel: Nat, +i: U32, out: Array<U>, r: Array<T> & T, +k: U32, hk: {Laws.slots(U, out) == k : U32}) -> {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, fuel, i, out, r)) == k : U32}:
  match fuel:
    case 0n:
      hk
    case 1n+p:
      (a, x) = r
      map_step(~T, ~U, ~f, p, U32.inc(i), out, i, x, k, Array.get(T, a, U32.inc(i)), set_ex(U, out, i, f(x), k, hk), b => r2 => h => map_go_slots(~T, ~U, ~f, p, U32.inc(i), b, r2, k, h))

# a fresh array of depth d has 2^d slots
def new_slots(-T: Data, d: Nat, -v: T) -> {Laws.slots(T, Array.new(T, d, v)) == U32.shln(1, d) : U32}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %new_slots(T, p, v) : {U32.shl(Laws.slots(T, Array.new(T, p, v))) == U32.shl(_) : U32}
      {==}

def Laws.mask_not_slots(n, d, a):
  map_go_slots(~U32, ~U32, ~(x => U32.xor(x, 1)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), U32.shln(1, d), new_slots(U32, d, 0))

# the same for Kernel.zip.go, which reads two arrays per step
def zip_step(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, -p: Nat, -j: U32, -out: Array<V>, -i: U32, -x: T, -y: U, -k: U32, ra2: Array<T> & T, rb2: Array<U> & U,
  w: &c: Array<V> -> {Array.set(V, out, i, f(x, y)) == c : Array<V>} & {Laws.slots(V, c) == k : U32},
  ih: @c: Array<V> -> @ra: Array<T> & T -> @rb: Array<U> & U -> {Laws.slots(V, c) == k : U32} -> {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, p, j, c, ra, rb)) == k : U32})
  -> {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, p, j, Array.set(V, out, i, f(x, y)), ra2, rb2)) == k : U32}:
  (c, eq, sl) = w
  %Equal.sym(Array<V>, Array.set(V, out, i, f(x, y)), c, eq) : {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, p, j, _, ra2, rb2)) == k : U32}
  ih(c, ra2, rb2, sl)

def zip_go_slots(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fuel: Nat, +i: U32, out: Array<V>, ra: Array<T> & T, rb: Array<U> & U, +k: U32, hk: {Laws.slots(V, out) == k : U32}) -> {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, fuel, i, out, ra, rb)) == k : U32}:
  match fuel:
    case 0n:
      hk
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      zip_step(~T, ~U, ~V, ~f, p, U32.inc(i), out, i, x, y, k, Array.get(T, a, U32.inc(i)), Array.get(U, b, U32.inc(i)), set_ex(V, out, i, f(x, y), k, hk), c => ra2 => rb2 => h => zip_go_slots(~T, ~U, ~V, ~f, p, U32.inc(i), c, ra2, rb2, k, h))

def Laws.mask_and_slots(n, d, a, b):
  zip_go_slots(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, b, 0), U32.shln(1, d), new_slots(U32, d, 0))

# the same for Kernel.iota.go, which reads nothing
def iota_step(-p: Nat, -j: U32, -out: Array<U32>, -i: U32, -off: U32, -k: U32,
  w: &b: Array<U32> -> {Array.set(U32, out, i, U32.add(off, i)) == b : Array<U32>} & {Laws.slots(U32, b) == k : U32},
  ih: @b: Array<U32> -> {Laws.slots(U32, b) == k : U32} -> {Laws.slots(U32, K.Kernel.iota.go(p, j, off, b)) == k : U32})
  -> {Laws.slots(U32, K.Kernel.iota.go(p, j, off, Array.set(U32, out, i, U32.add(off, i)))) == k : U32}:
  (b, eq, sl) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, i, U32.add(off, i)), b, eq) : {Laws.slots(U32, K.Kernel.iota.go(p, j, off, _)) == k : U32}
  ih(b, sl)

def iota_go_slots(fuel: Nat, +i: U32, +off: U32, out: Array<U32>, +k: U32, hk: {Laws.slots(U32, out) == k : U32}) -> {Laws.slots(U32, K.Kernel.iota.go(fuel, i, off, out)) == k : U32}:
  match fuel:
    case 0n:
      hk
    case 1n+p:
      iota_step(p, U32.inc(i), out, i, off, k, set_ex(U32, out, i, U32.add(off, i), k, hk), b => h => iota_go_slots(p, U32.inc(i), off, b, k, h))

def Laws.iota_slots(n, d, off):
  iota_go_slots(U32.to_nat(n), 0, off, Array.new(U32, d, 0), U32.shln(1, d), new_slots(U32, d, 0))
