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

# =====================================================================================
# 9. P0 well-formedness (LAWS.bend section 9)
# =====================================================================================

# min(n, a) <= b from a <= b: c1 = cmp(n, a), c2 = cmp(a, b) as parameters
def min_le_k(+x: Word(32n), +y: Word(32n), +w: Word(32n), c1: Cmp, c2: Cmp, e1: {Word.cmp(32n, x, y) == c1 : Cmp}, e2: {Word.cmp(32n, y, w) == c2 : Cmp}, h: {Cmp.is_le(c2) == True{} : Bool})
  -> {U32.is_le(Bool.pick(U32, Cmp.is_lt(c1), U32{x}, U32{y}), U32{w}) == True{} : Bool}:
  match c1 c2:
    case LT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(32n, x, w), LT{}, L.word_lt_trans(32n, x, y, w, e1, e2)) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      %L.word_cmp_eq(32n, y, w, e2) : {U32.is_le(U32{x}, U32{_}) == True{} : Bool}
      %Equal.sym(Cmp, Word.cmp(32n, x, y), LT{}, e1) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case LT{} GT{}:
      Empty.absurd({U32.is_le(U32{x}, U32{w}) == True{} : Bool}, L.false_true(h))
    case EQ{} _:
      %Equal.sym(Cmp, Word.cmp(32n, y, w), c2, e2) : {Cmp.is_le(_) == True{} : Bool}
      h
    case GT{} _:
      %Equal.sym(Cmp, Word.cmp(32n, y, w), c2, e2) : {Cmp.is_le(_) == True{} : Bool}
      h

def Laws.u32_min_le(n, a, b, h):
  match n a b:
    case U32{+x} U32{+y} U32{+w}:
      min_le_k(x, y, w, Word.cmp(32n, x, y), Word.cmp(32n, y, w), {==}, {==}, h)

def Laws.wf_new(T, d, z):
  match d:
    case 0n:
      Unit{}
    case 1n++p:
      (Laws.wf_new(T, p, z), Laws.wf_new(T, p, z))

def Laws.wf_new_words(bits, d, w, hw):
  match bits d:
    case True{} 0n:
      hw
    case False{} 0n:
      Unit{}
    case True{} 1n++p:
      (Laws.wf_new_words(True{}, p, w, hw), Laws.wf_new_words(True{}, p, w, hw))
    case False{} 1n++p:
      (Laws.wf_new_words(False{}, p, w, hw), Laws.wf_new_words(False{}, p, w, hw))

def Laws.wf_frame_empty():
  Unit{}

def Laws.wf_column_head(c, n, wf):
  match c:
    case C.CBool{+len, +depth, valid, data}:
      (hl, hv) = wf
      (Laws.u32_min_le(n, len, U32.shln(1, depth), hl), hv)
    case C.CU32{+len, +depth, valid, data}:
      (hl, hv) = wf
      (Laws.u32_min_le(n, len, U32.shln(1, depth), hl), hv)
    case C.CI32{+len, +depth, valid, data}:
      (hl, hv) = wf
      (Laws.u32_min_le(n, len, U32.shln(1, depth), hl), hv)
    case C.CF32{+len, +depth, valid, data}:
      (hl, hv) = wf
      (Laws.u32_min_le(n, len, U32.shln(1, depth), hl), hv)
    case C.CStr{+len, +depth, valid, data}:
      (hl, hv) = wf
      (Laws.u32_min_le(n, len, U32.shln(1, depth), hl), hv)

# a column of height h stays a column of height min(n, h) under head
def wf_colh_head(+h: U32, c: C.Column, +n: U32, hc: Laws.WFColumnH(h, c)) -> Laws.WFColumnH(U32.min(n, h), C.Column.head(c, n)):
  match c:
    case C.CBool{+len, depth, valid, data}:
      (hl, hw) = hc
      ((%Equal.sym(U32, len, h, hl) : {U32.min(n, _) == U32.min(n, h) : U32}; {==}), Laws.wf_column_head(C.CBool{len, depth, valid, data}, n, hw))
    case C.CU32{+len, depth, valid, data}:
      (hl, hw) = hc
      ((%Equal.sym(U32, len, h, hl) : {U32.min(n, _) == U32.min(n, h) : U32}; {==}), Laws.wf_column_head(C.CU32{len, depth, valid, data}, n, hw))
    case C.CI32{+len, depth, valid, data}:
      (hl, hw) = hc
      ((%Equal.sym(U32, len, h, hl) : {U32.min(n, _) == U32.min(n, h) : U32}; {==}), Laws.wf_column_head(C.CI32{len, depth, valid, data}, n, hw))
    case C.CF32{+len, depth, valid, data}:
      (hl, hw) = hc
      ((%Equal.sym(U32, len, h, hl) : {U32.min(n, _) == U32.min(n, h) : U32}; {==}), Laws.wf_column_head(C.CF32{len, depth, valid, data}, n, hw))
    case C.CStr{+len, depth, valid, data}:
      (hl, hw) = hc
      ((%Equal.sym(U32, len, h, hl) : {U32.min(n, _) == U32.min(n, h) : U32}; {==}), Laws.wf_column_head(C.CStr{len, depth, valid, data}, n, hw))

def wf_cols_head(+h: U32, cols: List<&1, C.Named>, +seen: List<&2, String>, +n: U32, wf: Laws.WFCols(h, cols, seen)) -> Laws.WFCols(U32.min(n, h), C.Cols.head(cols, n), seen):
  match cols:
    case Nil{}:
      Unit{}
    case C.Named{+nm, c} <> rest:
      (hn, hc, hrest) = wf
      (hn, wf_colh_head(h, c, n, hc), wf_cols_head(h, rest, nm <> seen, n, hrest))

def Laws.wf_frame_head(f, n, wf):
  match f:
    case C.Frame{+h, cols}:
      wf_cols_head(h, cols, Nil{}, n, wf)

# =====================================================================================
# 10. Buffer contents (LAWS.bend section 10): Array.get reads Laws.rd, Array.set
#     writes where rd reads, one step of gather / compact. Every lemma over an array
#     hands it back as a Sigma witness beside the equations (arrays are affine).
# =====================================================================================

# Array.size hands the array back unchanged, with its slot count as a Data witness
def size_same_node(-T: Type, -xs: Array<T>, ys: Array<T>, w: &b: Array<T> -> &n: U32 -> {b == xs : Array<T>} & {Array.size(T, xs) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32})
  -> &b2: Array<T> -> &n2: U32 -> {b2 == ANode{xs, ys} : Array<T>} & {Array.size(T, ANode{xs, ys}) == (b2, n2) : Array<T> & U32} & {Laws.slots(T, b2) == n2 : U32}:
  (b, n0, eb, es, sl) = w
  +n = n0
  (ANode{b, ys}, U32.shl(n), (%eb : {ANode{b, ys} == ANode{_, ys} : Array<T>}; {==}), (%Equal.sym(Array<T> & U32, Array.size(T, xs), (b, n), es) : {Array.size.node(T, ys, _) == (ANode{b, ys}, U32.shl(n)) : Array<T> & U32}; {==}), (%sl : {U32.shl(Laws.slots(T, b)) == U32.shl(_) : U32}; {==}))

def size_same(-T: Type, a: Array<T>) -> &b: Array<T> -> &n: U32 -> {b == a : Array<T>} & {Array.size(T, a) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32}:
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1, {==}, {==}, {==})
    case ANode{xs, ys}:
      size_same_node(T, xs, ys, size_same(T, xs))

# Array.get.go hands the array back and answers the cell rd models
def get_rd_lo(-T: Data, -xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, w: &x: T -> {Array.get.go(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))) == (xs, x) : Array<T> & T} & {x == Laws.rd(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))) : T})
  -> &x2: T -> {Array.get.go(T, ANode{xs, ys}, n, i, True{}) == (ANode{xs, ys}, x2) : Array<T> & T} & {x2 == Laws.rd(T, ANode{xs, ys}, n, i, True{}) : T}:
  (x, e1, e2) = w
  (x, (%Equal.sym(Array<T> & T, Array.get.go(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))), (xs, x), e1) : {Array.swap.lo(T, ys, _) == (ANode{xs, ys}, x) : Array<T> & T}; {==}), e2)

def get_rd_hi(-T: Data, -xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, w: &x: T -> {Array.get.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) == (ys, x) : Array<T> & T} & {x == Laws.rd(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) : T})
  -> &x2: T -> {Array.get.go(T, ANode{xs, ys}, n, i, False{}) == (ANode{xs, ys}, x2) : Array<T> & T} & {x2 == Laws.rd(T, ANode{xs, ys}, n, i, False{}) : T}:
  (x, e1, e2) = w
  (x, (%Equal.sym(Array<T> & T, Array.get.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), (ys, x), e1) : {Array.swap.hi(T, xs, _) == (ANode{xs, ys}, x) : Array<T> & T}; {==}), e2)

def get_rd(-T: Data, a: Array<T>, +n: U32, +i: U32, z: Bool) -> &x: T -> {Array.get.go(T, a, n, i, z) == (a, x) : Array<T> & T} & {x == Laws.rd(T, a, n, i, z) : T}:
  match a z:
    case ALeaf{+x} _:
      (x, {==}, {==})
    case ANode{xs, ys} True{}:
      get_rd_lo(T, xs, ys, n, i, get_rd(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))))
    case ANode{xs, ys} False{}:
      get_rd_hi(T, xs, ys, n, i, get_rd(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))

# Array.get through Array.size: b is a (eb) with n slots (es)
def get_at_k2(-T: Data, -a: Array<T>, -b: Array<T>, +i: U32, +n: U32, eb: {b == a : Array<T>}, +es: {Array.size(T, a) == (b, n) : Array<T> & U32},
  w: &x: T -> {Array.get.go(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (b, x) : Array<T> & T} & {x == Laws.rd(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) : T})
  -> &x2: T -> {Array.get(T, a, i) == (a, x2) : Array<T> & T} & {x2 == Laws.rd_at(T, a, i) : T}:
  (x, e1, e2) = w
  (x, (%Equal.sym(Array<T> & U32, Array.size(T, a), (b, n), es) : {Array.get.at(T, i, _) == (a, x) : Array<T> & T}; %eb : {Array.get.go(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (_, x) : Array<T> & T}; e1), (%Equal.sym(Array<T> & U32, Array.size(T, a), (b, n), es) : {x == Laws.rd_size(T, i, _) : T}; e2))

def get_at_k(-T: Data, -a: Array<T>, +i: U32, w: &b: Array<T> -> &n: U32 -> {b == a : Array<T>} & {Array.size(T, a) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32})
  -> &x: T -> {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T}:
  (b, n0, eb, es, sl) = w
  +n = n0
  get_at_k2(T, a, b, i, n, eb, es, get_rd(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))

# the cell Array.get answers, as a live witness (the array is consumed once)
def get_at_w(-T: Data, a: Array<T>, +i: U32) -> &x: T -> {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T}:
  get_at_k(T, a, i, size_same(T, a))

def get_pure_fin(-T: Data, -a: Array<T>, +i: U32, w: &x: T -> {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T}) -> {Array.get(T, a, i) == (a, Laws.rd_at(T, a, i)) : Array<T> & T}:
  (x, e1, e2) = w
  %e2 : {Array.get(T, a, i) == (a, _) : Array<T> & T}
  e1

def Laws.array_get_pure(T, a, i):
  get_pure_fin(T, a, i, get_at_w(T, a, i))

# Array.swap.go writes v where rd reads at the same (n, j, z); the written array keeps its slots
def swap_rd_lo(-T: Data, -xs: Array<T>, ys: Array<T>, +n: U32, +j: U32, +v: T, w: &c: Array<T> -> &o: T -> {Array.swap.go(T, xs, U32.shr(n), j, v, U32.is_lt(j, U32.shr(U32.shr(n)))) == (c, o) : Array<T> & T} & {Laws.rd(T, c, U32.shr(n), j, U32.is_lt(j, U32.shr(U32.shr(n)))) == v : T} & {Laws.slots(T, c) == Laws.slots(T, xs) : U32})
  -> &c2: Array<T> -> &o2: T -> {Array.swap.lo(T, ys, Array.swap.go(T, xs, U32.shr(n), j, v, U32.is_lt(j, U32.shr(U32.shr(n))))) == (c2, o2) : Array<T> & T} & {Laws.rd(T, c2, n, j, True{}) == v : T} & {Laws.slots(T, c2) == Laws.slots(T, ANode{xs, ys}) : U32}:
  (c, o, eq, hr, sl) = w
  (ANode{c, ys}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, xs, U32.shr(n), j, v, U32.is_lt(j, U32.shr(U32.shr(n)))), (c, o), eq) : {Array.swap.lo(T, ys, _) == (ANode{c, ys}, o) : Array<T> & T}; {==}), hr, (%sl : {U32.shl(Laws.slots(T, c)) == U32.shl(_) : U32}; {==}))

def swap_rd_hi(-T: Data, xs: Array<T>, -ys: Array<T>, +n: U32, +j: U32, +v: T, w: &c: Array<T> -> &o: T -> {Array.swap.go(T, ys, U32.shr(n), U32.sub(j, U32.shr(n)), v, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))) == (c, o) : Array<T> & T} & {Laws.rd(T, c, U32.shr(n), U32.sub(j, U32.shr(n)), U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))) == v : T} & {Laws.slots(T, c) == Laws.slots(T, ys) : U32})
  -> &c2: Array<T> -> &o2: T -> {Array.swap.hi(T, xs, Array.swap.go(T, ys, U32.shr(n), U32.sub(j, U32.shr(n)), v, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))) == (c2, o2) : Array<T> & T} & {Laws.rd(T, c2, n, j, False{}) == v : T} & {Laws.slots(T, c2) == Laws.slots(T, ANode{xs, ys}) : U32}:
  (c, o, eq, hr, sl) = w
  (ANode{xs, c}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, ys, U32.shr(n), U32.sub(j, U32.shr(n)), v, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))), (c, o), eq) : {Array.swap.hi(T, xs, _) == (ANode{xs, c}, o) : Array<T> & T}; {==}), hr, {==})

def swap_rd(-T: Data, a: Array<T>, +n: U32, +j: U32, +v: T, z: Bool) -> &c: Array<T> -> &o: T -> {Array.swap.go(T, a, n, j, v, z) == (c, o) : Array<T> & T} & {Laws.rd(T, c, n, j, z) == v : T} & {Laws.slots(T, c) == Laws.slots(T, a) : U32}:
  match a z:
    case ALeaf{x} _:
      (ALeaf{v}, x, {==}, {==}, {==})
    case ANode{xs, ys} True{}:
      swap_rd_lo(T, xs, ys, n, j, v, swap_rd(T, xs, U32.shr(n), j, v, U32.is_lt(j, U32.shr(U32.shr(n)))))
    case ANode{xs, ys} False{}:
      swap_rd_hi(T, xs, ys, n, j, v, swap_rd(T, ys, U32.shr(n), U32.sub(j, U32.shr(n)), v, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))))

# reading the written array c at i: its size is (c, n) again (c2 is c, n2 is n)
def set_get_k3(-T: Data, -c: Array<T>, +i: U32, +n: U32, +v: T,
  hr: {Laws.rd(T, c, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == v : T},
  slc: {Laws.slots(T, c) == n : U32},
  w: &c2: Array<T> -> &n2: U32 -> {c2 == c : Array<T>} & {Array.size(T, c) == (c2, n2) : Array<T> & U32} & {Laws.slots(T, c2) == n2 : U32})
  -> {Laws.rd_at(T, c, i) == v : T}:
  (c2, n2, ec2, es2, sl2) = w
  %Equal.sym(Array<T> & U32, Array.size(T, c), (c2, n2), es2) : {Laws.rd_size(T, i, _) == v : T}
  %sl2 : {Laws.rd(T, c2, _, U32.and(i, U32.sub(_, 1)), U32.is_lt(U32.and(i, U32.sub(_, 1)), U32.shr(_))) == v : T}
  %Equal.sym(Array<T>, c2, c, ec2) : {Laws.rd(T, _, Laws.slots(T, _), U32.and(i, U32.sub(Laws.slots(T, _), 1)), U32.is_lt(U32.and(i, U32.sub(Laws.slots(T, _), 1)), U32.shr(Laws.slots(T, _)))) == v : T}
  %Equal.sym(U32, Laws.slots(T, c), n, slc) : {Laws.rd(T, c, _, U32.and(i, U32.sub(_, 1)), U32.is_lt(U32.and(i, U32.sub(_, 1)), U32.shr(_))) == v : T}
  hr

def set_get_k2(-T: Data, -b: Array<T>, +i: U32, +n: U32, +v: T, slb: {Laws.slots(T, b) == n : U32},
  w: &c: Array<T> -> &o: T -> {Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.rd(T, c, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == v : T} & {Laws.slots(T, c) == Laws.slots(T, b) : U32})
  -> {Laws.rd_at(T, Array.set.fin(T, Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))), i) == v : T}:
  (c, o, eq, hr, slc) = w
  %Equal.sym(Array<T> & T, Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))), (c, o), eq) : {Laws.rd_at(T, Array.set.fin(T, _), i) == v : T}
  set_get_k3(T, c, i, n, v, hr, Equal.trans(U32, Laws.slots(T, c), Laws.slots(T, b), n, slc, slb), size_same(T, c))

def set_get_k1(-T: Data, -a: Array<T>, +i: U32, +v: T, w: &b: Array<T> -> &n: U32 -> {b == a : Array<T>} & {Array.size(T, a) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32})
  -> {Laws.rd_at(T, Array.set(T, a, i, v), i) == v : T}:
  (b, n0, eb, es, sl) = w
  +n = n0
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, n), es) : {Laws.rd_at(T, Array.set.fin(T, Array.swap.at(T, i, v, _)), i) == v : T}
  set_get_k2(T, b, i, n, v, sl, swap_rd(T, b, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))

def Laws.array_set_get(T, a, i, v):
  set_get_k1(T, a, i, v, size_same(T, a))

# ---- one step of the production kernels (U32 instance, see LAWS.bend section 10) ----

def gather_step_k(-src: Array<U32>, out: Array<U32>, -perm: Array<U32>, +j: U32, +i: U32,
  ws: &x: U32 -> {Array.get(U32, src, i) == (src, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, src, i) : U32},
  wp: &y: U32 -> {Array.get(U32, perm, U32.inc(j)) == (perm, y) : Array<U32> & U32} & {y == Laws.rd_at(U32, perm, U32.inc(j)) : U32})
  -> {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather.go(~U32, 1n, j, (src, out), (perm, i))), j) == Laws.rd_at(U32, src, i) : U32}:
  (x, e1, e2) = ws
  (y, f1, f2) = wp
  %Equal.sym(Array<U32> & U32, Array.get(U32, src, i), (src, x), e1) : {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather.go(~U32, 0n, U32.inc(j), K.Kernel.gather.put(~U32, out, j, _), Array.get(U32, perm, U32.inc(j)))), j) == Laws.rd_at(U32, src, i) : U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, perm, U32.inc(j)), (perm, y), f1) : {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather.go(~U32, 0n, U32.inc(j), K.Kernel.gather.put(~U32, out, j, (src, x)), _)), j) == Laws.rd_at(U32, src, i) : U32}
  %e2 : {Laws.rd_at(U32, Array.set(U32, out, j, x), j) == _ : U32}
  Laws.array_set_get(U32, out, j, x)

def Laws.gather_step(src, out, perm, j, i):
  gather_step_k(src, out, perm, j, i, get_at_w(U32, src, i), get_at_w(U32, perm, U32.inc(j)))

def compact_step_k(-a: Array<U32>, out: Array<U32>, mask: Array<U32>, +i: U32, +k: U32, +bit: U32,
  ws: &x: U32 -> {Array.get(U32, a, i) == (a, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, a, i) : U32})
  -> {Pair.snd(Array<U32>, U32, K.Kernel.compact.go(~U32, 1n, i, k, (a, out), (mask, bit))) == U32.add(k, bit) : U32}:
  (x, e1, e2) = ws
  %Equal.sym(Array<U32> & U32, Array.get(U32, a, i), (a, x), e1) : {Pair.snd(Array<U32>, U32, K.Kernel.compact.go(~U32, 0n, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~U32, out, k, _), Array.get(U32, mask, U32.inc(i)))) == U32.add(k, bit) : U32}
  {==}

def Laws.compact_step(a, out, mask, i, k, bit):
  compact_step_k(a, out, mask, i, k, bit, get_at_w(U32, a, i))

def compact_cell_k(-a: Array<U32>, out: Array<U32>, mask: Array<U32>, +i: U32, +k: U32, +bit: U32,
  ws: &x: U32 -> {Array.get(U32, a, i) == (a, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, a, i) : U32})
  -> {Laws.rd_at(U32, Pair.fst(Array<U32>, U32, K.Kernel.compact.go(~U32, 1n, i, k, (a, out), (mask, bit))), k) == Laws.rd_at(U32, a, i) : U32}:
  (x, e1, e2) = ws
  %Equal.sym(Array<U32> & U32, Array.get(U32, a, i), (a, x), e1) : {Laws.rd_at(U32, Pair.fst(Array<U32>, U32, K.Kernel.compact.go(~U32, 0n, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~U32, out, k, _), Array.get(U32, mask, U32.inc(i)))), k) == Laws.rd_at(U32, a, i) : U32}
  %e2 : {Laws.rd_at(U32, Array.set(U32, out, k, x), k) == _ : U32}
  Laws.array_set_get(U32, out, k, x)

def Laws.compact_step_cell(a, out, mask, i, k, bit):
  compact_cell_k(a, out, mask, i, k, bit, get_at_w(U32, a, i))
