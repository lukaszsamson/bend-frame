# PROOF_filtsel.bend -- proofs of LAWS.bend section 20 (v0.2 T4.3): the Filter + plain Select
# physical step (src/exec.bend Exec.fs / Exec.fc / Exec.run_phys) against Eval.filter then
# Exec.select (Frame.filter_mask then Frame.select_names) and against Exec.run_pure.
#
# Shape of the development (all TERM equalities; the robs law is their congruence):
#   * `ckw`: Kernel.compact_keep's result is (its output, the mask itself) (compact_keeps_mask's
#     loop, PC.cmask, at any element type); `colw`: so is Column.compact's (every constructor,
#     either validity, both string storages). With colw a compaction is a FUNCTION of (column, mask):
#     `cm` (the columns compacted one by one, the mask threaded) unfolds one column at a time.
#   * `cgo`: Frame.filter_mask's loop (Cols.compact.go) is the reversed `cm`; `fm`: filter_mask is
#     Frame{kept, cm(cols)}.
#   * `fgo`: Exec.fc's grouped loop is the same reversed `cm`: the compact3 / compact4 groups by the
#     kernels' simulation laws (PF.c3_sim / c4_sim, at the template instances the dispatch picks),
#     `pcl` (a rebuilt column is the compacted one), `fzw` (splitting a column and putting it back);
#     law fc_filter_mask.
#   * `tkc`: Cols.take over cm(cols) is cm over Cols.take(cols); `sel`: the select loop over the
#     filtered frame against the select loop over the unfiltered one; law select_filter_mask.
#   * Exec.fs against Eval.filter then Exec.select: both call Eval.filter.mask (one function: the F5
#     pred_count passes or the general predicate; v0.2 T4.4), so the law splits on its result once
#     (pr / pk) and needs nothing about the predicate (law filter_select_step); and the runner's
#     last two steps (laws filter_select_run_eq, filter_select_run).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/eval.bend as V
import ./src/plan.bend as P
import ./src/exec.bend as Q
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_contents.bend as PC
import ./PROOF_eval.bend as PV
import ./PROOF_exec.bend as PE
import ./PROOF_fused.bend as PF

# ---- the mask comes back: Kernel.compact_keep and Column.compact ----------------------------------

def peta(-A: Type, -B: Type, p: A & B) -> {p == (Pair.fst(A, B, p), Pair.snd(A, B, p)) : A & B}:
  match p:
    case (x, y):
      {==}

# the mask comes back (PC.cmask, compact_keeps_mask's loop, at any element type)
def ckm(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -m: Array<U32>, +z: T, a1: Array<T>, m1: Array<U32>, ea: {a1 == a : Array<T>}, em: {m1 == m : Array<U32>})
  -> {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)) == m : Array<U32>}:
  %ea : {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, _, m, z)) == m : Array<U32>}
  %em : {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a1, _, z)) == _ : Array<U32>}
  PC.cmask(~T, U32.to_nat(n), 0, 0, a1, Array.new(T, d, z), m1)

def ckw.k(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -m: Array<U32>, +z: T,
  +e1: {K.Kernel.compact_keep(~T, n, d, a, m, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z))) : Array<T> & Array<U32>},
  +e2: {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)) == m : Array<U32>})
  -> {K.Kernel.compact_keep(~T, n, d, a, m, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), m) : Array<T> & Array<U32>}:
  Equal.trans(Array<T> & Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z), (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z))), (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), m), e1, Equal.cong(Array<U32>, Array<T> & Array<U32>, s => (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), s), Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), m, e2))

# two live copies of an array (PC.clone_eq's result)
def CE(-T: Data, -a: Array<T>) -> Type:
  &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>}

def ckw.b(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -m: Array<U32>, +z: T, -a1: Array<T>, -m1: Array<U32>, ea: {a1 == a : Array<T>}, em: {m1 == m : Array<U32>}, wa: CE(T, a1), wm: CE(U32, m1))
  -> {K.Kernel.compact_keep(~T, n, d, a, m, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), m) : Array<T> & Array<U32>}:
  (a2, a3, +ea2, ea3) = wa
  (m2, m3, +em2, em3) = wm
  %ea : {K.Kernel.compact_keep(~T, n, d, _, m, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, _, m, z)), m) : Array<T> & Array<U32>}
  %em : {K.Kernel.compact_keep(~T, n, d, a1, _, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a1, _, z)), _) : Array<T> & Array<U32>}
  %ea2 : {K.Kernel.compact_keep(~T, n, d, _, m1, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, _, m1, z)), m1) : Array<T> & Array<U32>}
  %em2 : {K.Kernel.compact_keep(~T, n, d, a2, _, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a2, _, z)), _) : Array<T> & Array<U32>}
  ckw.k(~T, n, d, a2, m2, z, peta(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a2, m2, z)), ckm(~T, n, d, a2, m2, z, a3, m3, Equal.trans(Array<T>, a3, a1, a2, ea3, Equal.sym(Array<T>, a2, a1, ea2)), Equal.trans(Array<U32>, m3, m1, m2, em3, Equal.sym(Array<U32>, m2, m1, em2))))

# compact_keep answers (its output, the mask) at any element type; a and m are erased, the live
# copies a1 / m1 (equal to them) are spent
def ckw(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -m: Array<U32>, +z: T, a1: Array<T>, m1: Array<U32>, ea: {a1 == a : Array<T>}, em: {m1 == m : Array<U32>})
  -> {K.Kernel.compact_keep(~T, n, d, a, m, z) == (Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, n, d, a, m, z)), m) : Array<T> & Array<U32>}:
  ckw.b(~T, n, d, a, m, z, a1, m1, ea, em, PC.clone_eq(T, a1), PC.clone_eq(U32, m1))

# ---- Column.compact answers the mask itself ------------------------------------------------------------

def colw.ba(+len: U32, +dep: Nat, data: Array<U32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CBool{len, dep, C.AllValid{}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CBool{len, dep, C.AllValid{}, data}, m, kept)), m) : C.Column & Array<U32>}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m, {==}, {==})) : {C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TBool{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TBool{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.bm.k(+len: U32, +dep: Nat, v: Array<U32>, data: Array<U32>, -m: Array<U32>, +kept: U32, w: CE(U32, m))
  -> {C.Column.compact(C.CBool{len, dep, C.Mask{v}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CBool{len, dep, C.Mask{v}, data}, m, kept)), m) : C.Column & Array<U32>}:
  (m1, m2, e1, e2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0, v, m1, {==}, e1)) : {C.Column.compact.c(C.CBool{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_)) == (Pair.fst(C.Column, Array<U32>, C.Column.compact.c(C.CBool{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_))), m) : C.Column & Array<U32>}
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m2, {==}, e2)) : {C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.w(D.TBool{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.w(D.TBool{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.b(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CBool{len, dep, valid, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CBool{len, dep, valid, data}, m, kept)), m) : C.Column & Array<U32>}:
  match valid:
    case C.AllValid{}:
      colw.ba(len, dep, data, m, kept)
    case C.Mask{v}:
      colw.bm.k(len, dep, v, data, m, kept, PC.clone_eq(U32, m))

def colw.ua(+len: U32, +dep: Nat, data: Array<U32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CU32{len, dep, C.AllValid{}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CU32{len, dep, C.AllValid{}, data}, m, kept)), m) : C.Column & Array<U32>}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m, {==}, {==})) : {C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TU32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TU32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.um.k(+len: U32, +dep: Nat, v: Array<U32>, data: Array<U32>, -m: Array<U32>, +kept: U32, w: CE(U32, m))
  -> {C.Column.compact(C.CU32{len, dep, C.Mask{v}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CU32{len, dep, C.Mask{v}, data}, m, kept)), m) : C.Column & Array<U32>}:
  (m1, m2, e1, e2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0, v, m1, {==}, e1)) : {C.Column.compact.c(C.CU32{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_)) == (Pair.fst(C.Column, Array<U32>, C.Column.compact.c(C.CU32{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_))), m) : C.Column & Array<U32>}
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m2, {==}, e2)) : {C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.w(D.TU32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.w(D.TU32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.u(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CU32{len, dep, valid, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CU32{len, dep, valid, data}, m, kept)), m) : C.Column & Array<U32>}:
  match valid:
    case C.AllValid{}:
      colw.ua(len, dep, data, m, kept)
    case C.Mask{v}:
      colw.um.k(len, dep, v, data, m, kept, PC.clone_eq(U32, m))

def colw.ia(+len: U32, +dep: Nat, data: Array<U32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CI32{len, dep, C.AllValid{}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CI32{len, dep, C.AllValid{}, data}, m, kept)), m) : C.Column & Array<U32>}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m, {==}, {==})) : {C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TI32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TI32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.im.k(+len: U32, +dep: Nat, v: Array<U32>, data: Array<U32>, -m: Array<U32>, +kept: U32, w: CE(U32, m))
  -> {C.Column.compact(C.CI32{len, dep, C.Mask{v}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CI32{len, dep, C.Mask{v}, data}, m, kept)), m) : C.Column & Array<U32>}:
  (m1, m2, e1, e2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0, v, m1, {==}, e1)) : {C.Column.compact.c(C.CI32{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_)) == (Pair.fst(C.Column, Array<U32>, C.Column.compact.c(C.CI32{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_))), m) : C.Column & Array<U32>}
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m2, {==}, e2)) : {C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.w(D.TI32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.w(D.TI32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.i(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CI32{len, dep, valid, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CI32{len, dep, valid, data}, m, kept)), m) : C.Column & Array<U32>}:
  match valid:
    case C.AllValid{}:
      colw.ia(len, dep, data, m, kept)
    case C.Mask{v}:
      colw.im.k(len, dep, v, data, m, kept, PC.clone_eq(U32, m))

def colw.fa(+len: U32, +dep: Nat, data: Array<F32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CF32{len, dep, C.AllValid{}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CF32{len, dep, C.AllValid{}, data}, m, kept)), m) : C.Column & Array<U32>}:
  %Equal.sym(Array<F32> & Array<U32>, K.Kernel.compact_keep(~F32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0.0), (Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0.0)), m), ckw(~F32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0.0, data, m, {==}, {==})) : {C.Column.gather.d(C.AllValid{}, C.Column.out.f(kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.f(kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.fm.k(+len: U32, +dep: Nat, v: Array<U32>, data: Array<F32>, -m: Array<U32>, +kept: U32, w: CE(U32, m))
  -> {C.Column.compact(C.CF32{len, dep, C.Mask{v}, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CF32{len, dep, C.Mask{v}, data}, m, kept)), m) : C.Column & Array<U32>}:
  (m1, m2, e1, e2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0, v, m1, {==}, e1)) : {C.Column.compact.c(C.CF32{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_)) == (Pair.fst(C.Column, Array<U32>, C.Column.compact.c(C.CF32{len, dep, C.AllValid{}, data}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_))), m) : C.Column & Array<U32>}
  %Equal.sym(Array<F32> & Array<U32>, K.Kernel.compact_keep(~F32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0.0), (Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0.0)), m), ckw(~F32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0.0, data, m2, {==}, e2)) : {C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.f(kept, K.Kernel.depth_for(U32.add(kept, 1)), _)) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.f(kept, K.Kernel.depth_for(U32.add(kept, 1)), _))), m) : C.Column & Array<U32>}
  {==}

def colw.f(+len: U32, +dep: Nat, valid: C.Valid, data: Array<F32>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CF32{len, dep, valid, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CF32{len, dep, valid, data}, m, kept)), m) : C.Column & Array<U32>}:
  match valid:
    case C.AllValid{}:
      colw.fa(len, dep, data, m, kept)
    case C.Mask{v}:
      colw.fm.k(len, dep, v, data, m, kept, PC.clone_eq(U32, m))

def colw.ra(+len: U32, +dep: Nat, data: Array<String>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CStr{len, dep, C.AllValid{}, ST.SRaw{data}}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, C.AllValid{}, ST.SRaw{data}}, m, kept)), m) : C.Column & Array<U32>}:
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.compact_keep(~String, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, ""), (Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, "")), m), ckw(~String, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, "", data, m, {==}, {==})) : {C.Column.gather.d(C.AllValid{}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.r(_))) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.r(_)))), m) : C.Column & Array<U32>}
  {==}

def colw.rm.k(+len: U32, +dep: Nat, v: Array<U32>, data: Array<String>, -m: Array<U32>, +kept: U32, w: CE(U32, m))
  -> {C.Column.compact(C.CStr{len, dep, C.Mask{v}, ST.SRaw{data}}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, C.Mask{v}, ST.SRaw{data}}, m, kept)), m) : C.Column & Array<U32>}:
  (m1, m2, e1, e2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0, v, m1, {==}, e1)) : {C.Column.compact.c(C.CStr{len, dep, C.AllValid{}, ST.SRaw{data}}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_)) == (Pair.fst(C.Column, Array<U32>, C.Column.compact.c(C.CStr{len, dep, C.AllValid{}, ST.SRaw{data}}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_))), m) : C.Column & Array<U32>}
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.compact_keep(~String, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, ""), (Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, "")), m), ckw(~String, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, "", data, m2, {==}, e2)) : {C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.r(_))) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.r(_)))), m) : C.Column & Array<U32>}
  {==}

def colw.r(+len: U32, +dep: Nat, valid: C.Valid, data: Array<String>, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CStr{len, dep, valid, ST.SRaw{data}}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, valid, ST.SRaw{data}}, m, kept)), m) : C.Column & Array<U32>}:
  match valid:
    case C.AllValid{}:
      colw.ra(len, dep, data, m, kept)
    case C.Mask{v}:
      colw.rm.k(len, dep, v, data, m, kept, PC.clone_eq(U32, m))

def colw.da(+len: U32, +dep: Nat, data: Array<U32>, -dict: ST.Dict, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CStr{len, dep, C.AllValid{}, ST.SDict{data, dict}}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, C.AllValid{}, ST.SDict{data, dict}}, m, kept)), m) : C.Column & Array<U32>}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m, {==}, {==})) : {C.Column.gather.d(C.AllValid{}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.d(dict, _))) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.d(dict, _)))), m) : C.Column & Array<U32>}
  {==}

def colw.dm.k(+len: U32, +dep: Nat, v: Array<U32>, data: Array<U32>, -dict: ST.Dict, -m: Array<U32>, +kept: U32, w: CE(U32, m))
  -> {C.Column.compact(C.CStr{len, dep, C.Mask{v}, ST.SDict{data, dict}}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, C.Mask{v}, ST.SDict{data, dict}}, m, kept)), m) : C.Column & Array<U32>}:
  (m1, m2, e1, e2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0, v, m1, {==}, e1)) : {C.Column.compact.c(C.CStr{len, dep, C.AllValid{}, ST.SDict{data, dict}}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_)) == (Pair.fst(C.Column, Array<U32>, C.Column.compact.c(C.CStr{len, dep, C.AllValid{}, ST.SDict{data, dict}}, kept, K.Kernel.depth_for(U32.add(kept, 1)), C.Valid.compact.k(_))), m) : C.Column & Array<U32>}
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0)), m), ckw(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), data, m, 0, data, m2, {==}, e2)) : {C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.d(dict, _))) == (Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.Mask{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, len, K.Kernel.depth_for(U32.add(kept, 1)), v, m, 0))}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.d(dict, _)))), m) : C.Column & Array<U32>}
  {==}

def colw.d(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>, -dict: ST.Dict, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CStr{len, dep, valid, ST.SDict{data, dict}}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, valid, ST.SDict{data, dict}}, m, kept)), m) : C.Column & Array<U32>}:
  match valid:
    case C.AllValid{}:
      colw.da(len, dep, data, dict, m, kept)
    case C.Mask{v}:
      colw.dm.k(len, dep, v, data, dict, m, kept, PC.clone_eq(U32, m))

def colw.s(+len: U32, +dep: Nat, valid: C.Valid, data: ST.Strs, m: Array<U32>, +kept: U32)
  -> {C.Column.compact(C.CStr{len, dep, valid, data}, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(C.CStr{len, dep, valid, data}, m, kept)), m) : C.Column & Array<U32>}:
  match data:
    case ST.SRaw{a}:
      colw.r(len, dep, valid, a, m, kept)
    case ST.SDict{codes, dict}:
      colw.d(len, dep, valid, codes, dict, m, kept)

# Column.compact answers (the compacted column, the mask itself): every constructor, validity, storage
def colw.go(c: C.Column, m: Array<U32>, +kept: U32) -> {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}:
  match c:
    case C.CBool{+len, +dep, valid, data}:
      colw.b(len, dep, valid, data, m, kept)
    case C.CU32{+len, +dep, valid, data}:
      colw.u(len, dep, valid, data, m, kept)
    case C.CI32{+len, +dep, valid, data}:
      colw.i(len, dep, valid, data, m, kept)
    case C.CF32{+len, +dep, valid, data}:
      colw.f(len, dep, valid, data, m, kept)
    case C.CStr{+len, +dep, valid, data}:
      colw.s(len, dep, valid, data, m, kept)

# the same with c and m erased and live copies spent
def colw(-c: C.Column, -m: Array<U32>, +kept: U32, c1: C.Column, m1: Array<U32>, ec: {c1 == c : C.Column}, em: {m1 == m : Array<U32>}) -> {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}:
  %ec : {C.Column.compact(_, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept)), m) : C.Column & Array<U32>}
  %em : {C.Column.compact(c1, _, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, _, kept)), _) : C.Column & Array<U32>}
  colw.go(c1, m1, kept)

# ---- the compact3 / compact4 dispatch: one kernel loop IS one compact_keep per buffer ----------------

# what compact_keep makes of a buffer (Exec.c3 / c4's zero per element type)
def bk(b: Q.Buf, +n: U32, +d: Nat, m: Array<U32>) -> Q.Buf:
  match b:
    case Q.BU{a}:
      Q.BU{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a, m, 0))}
    case Q.BF{a}:
      Q.BF{Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, d, a, m, 0.0))}
    case Q.BS{a}:
      Q.BS{Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, n, d, a, m, ""))}

def c3c(~A: Data, ~B: Data, ~wa: Array<A> -> Q.Buf, ~wb: Array<B> -> Q.Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, a2: Array<B>, +z1: A, +z2: B, b3: Q.Buf)
  -> {Q.Exec.c3.c(~A, ~B, ~wa, ~wb, n, d, m, a1, a2, z1, z2, b3) == Q.F3{wa(Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1))), wb(Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2))), bk(b3, n, d, m), m} : Q.F3}:
  match b3:
    case Q.BU{a3}:
      Equal.cong(K.C3<A, B, U32>, Q.F3, r => Q.Exec.c3.k(~A, ~B, ~U32, ~wa, ~wb, ~(o => Q.Buf.u(o)), r), K.Kernel.compact3(~A, ~B, ~U32, n, d, m, a1, a2, a3, z1, z2, 0), K.C3{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a3, m, 0)), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, PF.c3_sim(~A, ~B, ~U32, U32.to_nat(n), 0, 0, Array.new(A, d, z1), Array.new(B, d, z2), Array.new(U32, d, 0), a1, a2, a3, m))
    case Q.BF{a3}:
      Equal.cong(K.C3<A, B, F32>, Q.F3, r => Q.Exec.c3.k(~A, ~B, ~F32, ~wa, ~wb, ~(o => Q.Buf.f(o)), r), K.Kernel.compact3(~A, ~B, ~F32, n, d, m, a1, a2, a3, z1, z2, 0.0), K.C3{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2)), Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, d, a3, m, 0.0)), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, PF.c3_sim(~A, ~B, ~F32, U32.to_nat(n), 0, 0, Array.new(A, d, z1), Array.new(B, d, z2), Array.new(F32, d, 0.0), a1, a2, a3, m))
    case Q.BS{a3}:
      Equal.cong(K.C3<A, B, String>, Q.F3, r => Q.Exec.c3.k(~A, ~B, ~String, ~wa, ~wb, ~(o => Q.Buf.s(o)), r), K.Kernel.compact3(~A, ~B, ~String, n, d, m, a1, a2, a3, z1, z2, ""), K.C3{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2)), Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, n, d, a3, m, "")), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, PF.c3_sim(~A, ~B, ~String, U32.to_nat(n), 0, 0, Array.new(A, d, z1), Array.new(B, d, z2), Array.new(String, d, ""), a1, a2, a3, m))

def c3b(~A: Data, ~wa: Array<A> -> Q.Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, +z1: A, b2: Q.Buf, b3: Q.Buf)
  -> {Q.Exec.c3.b(~A, ~wa, n, d, m, a1, z1, b2, b3) == Q.F3{wa(Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1))), bk(b2, n, d, m), bk(b3, n, d, m), m} : Q.F3}:
  match b2:
    case Q.BU{a2}:
      c3c(~A, ~U32, ~wa, ~(o => Q.Buf.u(o)), n, d, m, a1, a2, z1, 0, b3)
    case Q.BF{a2}:
      c3c(~A, ~F32, ~wa, ~(o => Q.Buf.f(o)), n, d, m, a1, a2, z1, 0.0, b3)
    case Q.BS{a2}:
      c3c(~A, ~String, ~wa, ~(o => Q.Buf.s(o)), n, d, m, a1, a2, z1, "", b3)

# Exec.c3 IS one compact_keep per buffer, the mask itself back (PF.c3_sim at the instance picked)
def c3t(+n: U32, +d: Nat, m: Array<U32>, b1: Q.Buf, b2: Q.Buf, b3: Q.Buf) -> {Q.Exec.c3(n, d, m, b1, b2, b3) == Q.F3{bk(b1, n, d, m), bk(b2, n, d, m), bk(b3, n, d, m), m} : Q.F3}:
  match b1:
    case Q.BU{a1}:
      c3b(~U32, ~(o => Q.Buf.u(o)), n, d, m, a1, 0, b2, b3)
    case Q.BF{a1}:
      c3b(~F32, ~(o => Q.Buf.f(o)), n, d, m, a1, 0.0, b2, b3)
    case Q.BS{a1}:
      c3b(~String, ~(o => Q.Buf.s(o)), n, d, m, a1, "", b2, b3)

def c4d(~A: Data, ~B: Data, ~C: Data, ~wa: Array<A> -> Q.Buf, ~wb: Array<B> -> Q.Buf, ~wc: Array<C> -> Q.Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, a2: Array<B>, a3: Array<C>, +z1: A, +z2: B, +z3: C, b4: Q.Buf)
  -> {Q.Exec.c4.d(~A, ~B, ~C, ~wa, ~wb, ~wc, n, d, m, a1, a2, a3, z1, z2, z3, b4) == Q.F4{wa(Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1))), wb(Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2))), wc(Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep(~C, n, d, a3, m, z3))), bk(b4, n, d, m), m} : Q.F4}:
  match b4:
    case Q.BU{a4}:
      Equal.cong(K.C4<A, B, C, U32>, Q.F4, r => Q.Exec.c4.k(~A, ~B, ~C, ~U32, ~wa, ~wb, ~wc, ~(o => Q.Buf.u(o)), r), K.Kernel.compact4(~A, ~B, ~C, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, 0), K.C4{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2)), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep(~C, n, d, a3, m, z3)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a4, m, 0)), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, PF.c4_sim(~A, ~B, ~C, ~U32, U32.to_nat(n), 0, 0, Array.new(A, d, z1), Array.new(B, d, z2), Array.new(C, d, z3), Array.new(U32, d, 0), a1, a2, a3, a4, m))
    case Q.BF{a4}:
      Equal.cong(K.C4<A, B, C, F32>, Q.F4, r => Q.Exec.c4.k(~A, ~B, ~C, ~F32, ~wa, ~wb, ~wc, ~(o => Q.Buf.f(o)), r), K.Kernel.compact4(~A, ~B, ~C, ~F32, n, d, m, a1, a2, a3, a4, z1, z2, z3, 0.0), K.C4{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2)), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep(~C, n, d, a3, m, z3)), Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, d, a4, m, 0.0)), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, PF.c4_sim(~A, ~B, ~C, ~F32, U32.to_nat(n), 0, 0, Array.new(A, d, z1), Array.new(B, d, z2), Array.new(C, d, z3), Array.new(F32, d, 0.0), a1, a2, a3, a4, m))
    case Q.BS{a4}:
      Equal.cong(K.C4<A, B, C, String>, Q.F4, r => Q.Exec.c4.k(~A, ~B, ~C, ~String, ~wa, ~wb, ~wc, ~(o => Q.Buf.s(o)), r), K.Kernel.compact4(~A, ~B, ~C, ~String, n, d, m, a1, a2, a3, a4, z1, z2, z3, ""), K.C4{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2)), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep(~C, n, d, a3, m, z3)), Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, n, d, a4, m, "")), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, PF.c4_sim(~A, ~B, ~C, ~String, U32.to_nat(n), 0, 0, Array.new(A, d, z1), Array.new(B, d, z2), Array.new(C, d, z3), Array.new(String, d, ""), a1, a2, a3, a4, m))

def c4c(~A: Data, ~B: Data, ~wa: Array<A> -> Q.Buf, ~wb: Array<B> -> Q.Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, a2: Array<B>, +z1: A, +z2: B, b3: Q.Buf, b4: Q.Buf)
  -> {Q.Exec.c4.c(~A, ~B, ~wa, ~wb, n, d, m, a1, a2, z1, z2, b3, b4) == Q.F4{wa(Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1))), wb(Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep(~B, n, d, a2, m, z2))), bk(b3, n, d, m), bk(b4, n, d, m), m} : Q.F4}:
  match b3:
    case Q.BU{a3}:
      c4d(~A, ~B, ~U32, ~wa, ~wb, ~(o => Q.Buf.u(o)), n, d, m, a1, a2, a3, z1, z2, 0, b4)
    case Q.BF{a3}:
      c4d(~A, ~B, ~F32, ~wa, ~wb, ~(o => Q.Buf.f(o)), n, d, m, a1, a2, a3, z1, z2, 0.0, b4)
    case Q.BS{a3}:
      c4d(~A, ~B, ~String, ~wa, ~wb, ~(o => Q.Buf.s(o)), n, d, m, a1, a2, a3, z1, z2, "", b4)

def c4b(~A: Data, ~wa: Array<A> -> Q.Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, +z1: A, b2: Q.Buf, b3: Q.Buf, b4: Q.Buf)
  -> {Q.Exec.c4.b(~A, ~wa, n, d, m, a1, z1, b2, b3, b4) == Q.F4{wa(Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep(~A, n, d, a1, m, z1))), bk(b2, n, d, m), bk(b3, n, d, m), bk(b4, n, d, m), m} : Q.F4}:
  match b2:
    case Q.BU{a2}:
      c4c(~A, ~U32, ~wa, ~(o => Q.Buf.u(o)), n, d, m, a1, a2, z1, 0, b3, b4)
    case Q.BF{a2}:
      c4c(~A, ~F32, ~wa, ~(o => Q.Buf.f(o)), n, d, m, a1, a2, z1, 0.0, b3, b4)
    case Q.BS{a2}:
      c4c(~A, ~String, ~wa, ~(o => Q.Buf.s(o)), n, d, m, a1, a2, z1, "", b3, b4)

# Exec.c4 IS one compact_keep per buffer, the mask itself back (PF.c4_sim)
def c4t(+n: U32, +d: Nat, m: Array<U32>, b1: Q.Buf, b2: Q.Buf, b3: Q.Buf, b4: Q.Buf) -> {Q.Exec.c4(n, d, m, b1, b2, b3, b4) == Q.F4{bk(b1, n, d, m), bk(b2, n, d, m), bk(b3, n, d, m), bk(b4, n, d, m), m} : Q.F4}:
  match b1:
    case Q.BU{a1}:
      c4b(~U32, ~(o => Q.Buf.u(o)), n, d, m, a1, 0, b2, b3, b4)
    case Q.BF{a1}:
      c4b(~F32, ~(o => Q.Buf.f(o)), n, d, m, a1, 0.0, b2, b3, b4)
    case Q.BS{a1}:
      c4b(~String, ~(o => Q.Buf.s(o)), n, d, m, a1, "", b2, b3, b4)

# ---- a rebuilt column IS the compacted one; splitting a column and putting it back -----------------

def pcl.sb(a: Array<U32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(Q.SB{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(Q.SB{}, Q.BU{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0)), m), ckw(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0, a, m, {==}, {==})) : {Q.Exec.mk(Q.SB{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TBool{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))) : C.Column}
  {==}

def pcl.su(a: Array<U32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(Q.SU{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(Q.SU{}, Q.BU{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0)), m), ckw(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0, a, m, {==}, {==})) : {Q.Exec.mk(Q.SU{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TU32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))) : C.Column}
  {==}

def pcl.si(a: Array<U32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(Q.SI{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(Q.SI{}, Q.BU{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0)), m), ckw(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0, a, m, {==}, {==})) : {Q.Exec.mk(Q.SI{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TI32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))) : C.Column}
  {==}

def pcl.sd(-dict: ST.Dict, a: Array<U32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(Q.SD{dict}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(Q.SD{dict}, Q.BU{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0)), m), ckw(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0, a, m, {==}, {==})) : {Q.Exec.mk(Q.SD{dict}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.d(dict, _)))) : C.Column}
  {==}

def pcl.sx(a: Array<U32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(Q.SX{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(Q.SX{}, Q.BU{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0), (Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0)), m), ckw(~U32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0, a, m, {==}, {==})) : {Q.Exec.mk(Q.SX{}, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.w(D.TU32{}, kept, K.Kernel.depth_for(U32.add(kept, 1)), _))) : C.Column}
  {==}

def pcl.f(-s: Q.Sh, a: Array<F32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(s, bk(Q.BF{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, Q.BF{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<F32> & Array<U32>, K.Kernel.compact_keep(~F32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0.0), (Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0.0)), m), ckw(~F32, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, 0.0, a, m, {==}, {==})) : {Q.Exec.mk(s, bk(Q.BF{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.f(kept, K.Kernel.depth_for(U32.add(kept, 1)), _))) : C.Column}
  {==}

def pcl.r(-s: Q.Sh, a: Array<String>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(s, bk(Q.BS{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, Q.BS{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.compact_keep(~String, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, ""), (Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, "")), m), ckw(~String, l, K.Kernel.depth_for(U32.add(kept, 1)), a, m, "", a, m, {==}, {==})) : {Q.Exec.mk(s, bk(Q.BS{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.gather.d(C.AllValid{}, C.Column.out.s(kept, K.Kernel.depth_for(U32.add(kept, 1)), ST.Strs.out.r(_)))) : C.Column}
  {==}

def pcl.u(s: Q.Sh, a: Array<U32>, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(s, bk(Q.BU{a}, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, Q.BU{a}, l, p, C.AllValid{}), m, kept)) : C.Column}:
  match s:
    case Q.SB{}:
      pcl.sb(a, l, p, m, kept)
    case Q.SU{}:
      pcl.su(a, l, p, m, kept)
    case Q.SI{}:
      pcl.si(a, l, p, m, kept)
    case Q.SD{dict}:
      pcl.sd(dict, a, l, p, m, kept)
    case Q.SX{}:
      pcl.sx(a, l, p, m, kept)

# a column rebuilt from its compacted buffer IS Column.compact's column (AllValid, any shell)
def pcl(s: Q.Sh, b: Q.Buf, +l: U32, +p: Nat, m: Array<U32>, +kept: U32) -> {Q.Exec.mk(s, bk(b, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, b, l, p, C.AllValid{}), m, kept)) : C.Column}:
  match b:
    case Q.BU{a}:
      pcl.u(s, a, l, p, m, kept)
    case Q.BF{a}:
      pcl.f(s, a, l, p, m, kept)
    case Q.BS{a}:
      pcl.r(s, a, l, p, m, kept)

def FZW(-c: C.Column) -> Type:
  &z: Q.Fz -> {Q.Exec.fz(c) == z : Q.Fz} & {Q.Exec.unfz(z) == c : C.Column}

def fzw.b(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>) -> FZW(C.CBool{len, dep, valid, data}):
  match valid:
    case C.AllValid{}:
      (Q.FzOk{len, dep, Q.SB{}, Q.BU{data}}, {==}, {==})
    case C.Mask{v}:
      (Q.FzNo{C.CBool{len, dep, C.Mask{v}, data}}, {==}, {==})

def fzw.u(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>) -> FZW(C.CU32{len, dep, valid, data}):
  match valid:
    case C.AllValid{}:
      (Q.FzOk{len, dep, Q.SU{}, Q.BU{data}}, {==}, {==})
    case C.Mask{v}:
      (Q.FzNo{C.CU32{len, dep, C.Mask{v}, data}}, {==}, {==})

def fzw.i(+len: U32, +dep: Nat, valid: C.Valid, data: Array<U32>) -> FZW(C.CI32{len, dep, valid, data}):
  match valid:
    case C.AllValid{}:
      (Q.FzOk{len, dep, Q.SI{}, Q.BU{data}}, {==}, {==})
    case C.Mask{v}:
      (Q.FzNo{C.CI32{len, dep, C.Mask{v}, data}}, {==}, {==})

def fzw.f(+len: U32, +dep: Nat, valid: C.Valid, data: Array<F32>) -> FZW(C.CF32{len, dep, valid, data}):
  match valid:
    case C.AllValid{}:
      (Q.FzOk{len, dep, Q.SX{}, Q.BF{data}}, {==}, {==})
    case C.Mask{v}:
      (Q.FzNo{C.CF32{len, dep, C.Mask{v}, data}}, {==}, {==})

def fzw.r(+len: U32, +dep: Nat, valid: C.Valid, a: Array<String>) -> FZW(C.CStr{len, dep, valid, ST.SRaw{a}}):
  match valid:
    case C.AllValid{}:
      (Q.FzOk{len, dep, Q.SX{}, Q.BS{a}}, {==}, {==})
    case C.Mask{v}:
      (Q.FzNo{C.CStr{len, dep, C.Mask{v}, ST.SRaw{a}}}, {==}, {==})

def fzw.d(+len: U32, +dep: Nat, valid: C.Valid, codes: Array<U32>, dict: ST.Dict) -> FZW(C.CStr{len, dep, valid, ST.SDict{codes, dict}}):
  match valid:
    case C.AllValid{}:
      (Q.FzOk{len, dep, Q.SD{dict}, Q.BU{codes}}, {==}, {==})
    case C.Mask{v}:
      (Q.FzNo{C.CStr{len, dep, C.Mask{v}, ST.SDict{codes, dict}}}, {==}, {==})

def fzw.s(+len: U32, +dep: Nat, valid: C.Valid, data: ST.Strs) -> FZW(C.CStr{len, dep, valid, data}):
  match data:
    case ST.SRaw{a}:
      fzw.r(len, dep, valid, a)
    case ST.SDict{codes, dict}:
      fzw.d(len, dep, valid, codes, dict)

# Exec.fz's split, live, and Exec.unfz puts the column back
def fzw(c: C.Column) -> FZW(c):
  match c:
    case C.CBool{+len, +dep, valid, data}:
      fzw.b(len, dep, valid, data)
    case C.CU32{+len, +dep, valid, data}:
      fzw.u(len, dep, valid, data)
    case C.CI32{+len, +dep, valid, data}:
      fzw.i(len, dep, valid, data)
    case C.CF32{+len, +dep, valid, data}:
      fzw.f(len, dep, valid, data)
    case C.CStr{+len, +dep, valid, data}:
      fzw.s(len, dep, valid, data)


# ---- copies (proof witnesses only) ---------------------------------------------------------------

def CE3(-T: Data, -a: Array<T>) -> Type:
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>}

def CE4(-T: Data, -a: Array<T>) -> Type:
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}

def CE5(-T: Data, -a: Array<T>) -> Type:
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> &a5: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>} & {a5 == a : Array<T>}

def ce3.k(-T: Data, -a: Array<T>, a1: Array<T>, +e1: {a1 == a : Array<T>}, -b: Array<T>, +eb: {b == a : Array<T>}, w: CE(T, b)) -> CE3(T, a):
  (b1, b2, eb1, eb2) = w
  (a1, b1, b2, e1, Equal.trans(Array<T>, b1, b, a, eb1, eb), Equal.trans(Array<T>, b2, b, a, eb2, eb))

def ce3.a(-T: Data, -a: Array<T>, w: CE(T, a)) -> CE3(T, a):
  (a1, b, e1, eb) = w
  ce3.k(T, a, a1, e1, b, eb, PC.clone_eq(T, b))

def ce3(-T: Data, a: Array<T>) -> CE3(T, a):
  ce3.a(T, a, PC.clone_eq(T, a))

def ce4.k(-T: Data, -a: Array<T>, a1: Array<T>, +e1: {a1 == a : Array<T>}, -b: Array<T>, +eb: {b == a : Array<T>}, w: CE3(T, b)) -> CE4(T, a):
  (b1, b2, b3, eb1, eb2, eb3) = w
  (a1, b1, b2, b3, e1, Equal.trans(Array<T>, b1, b, a, eb1, eb), Equal.trans(Array<T>, b2, b, a, eb2, eb), Equal.trans(Array<T>, b3, b, a, eb3, eb))

def ce4.a(-T: Data, -a: Array<T>, w: CE(T, a)) -> CE4(T, a):
  (a1, b, e1, eb) = w
  ce4.k(T, a, a1, e1, b, eb, ce3(T, b))

def ce4(-T: Data, a: Array<T>) -> CE4(T, a):
  ce4.a(T, a, PC.clone_eq(T, a))

def ce5.k(-T: Data, -a: Array<T>, a1: Array<T>, +e1: {a1 == a : Array<T>}, -b: Array<T>, +eb: {b == a : Array<T>}, w: CE4(T, b)) -> CE5(T, a):
  (b1, b2, b3, b4, eb1, eb2, eb3, eb4) = w
  (a1, b1, b2, b3, b4, e1, Equal.trans(Array<T>, b1, b, a, eb1, eb), Equal.trans(Array<T>, b2, b, a, eb2, eb), Equal.trans(Array<T>, b3, b, a, eb3, eb), Equal.trans(Array<T>, b4, b, a, eb4, eb))

def ce5.a(-T: Data, -a: Array<T>, w: CE(T, a)) -> CE5(T, a):
  (a1, b, e1, eb) = w
  ce5.k(T, a, a1, e1, b, eb, ce4(T, b))

def ce5(-T: Data, a: Array<T>) -> CE5(T, a):
  ce5.a(T, a, PC.clone_eq(T, a))

# two copies of a buffer
def BC(-b: Q.Buf) -> Type:
  &b1: Q.Buf -> &b2: Q.Buf -> {b1 == b : Q.Buf} & {b2 == b : Q.Buf}

def bclone.u(-a: Array<U32>, w: CE(U32, a)) -> BC(Q.BU{a}):
  (a1, a2, e1, e2) = w
  (Q.BU{a1}, Q.BU{a2}, Equal.cong(Array<U32>, Q.Buf, x => Q.BU{x}, a1, a, e1), Equal.cong(Array<U32>, Q.Buf, x => Q.BU{x}, a2, a, e2))

def bclone.f(-a: Array<F32>, w: CE(F32, a)) -> BC(Q.BF{a}):
  (a1, a2, e1, e2) = w
  (Q.BF{a1}, Q.BF{a2}, Equal.cong(Array<F32>, Q.Buf, x => Q.BF{x}, a1, a, e1), Equal.cong(Array<F32>, Q.Buf, x => Q.BF{x}, a2, a, e2))

def bclone.s(-a: Array<String>, w: CE(String, a)) -> BC(Q.BS{a}):
  (a1, a2, e1, e2) = w
  (Q.BS{a1}, Q.BS{a2}, Equal.cong(Array<String>, Q.Buf, x => Q.BS{x}, a1, a, e1), Equal.cong(Array<String>, Q.Buf, x => Q.BS{x}, a2, a, e2))

def bclone(b: Q.Buf) -> BC(b):
  match b:
    case Q.BU{a}:
      bclone.u(a, PC.clone_eq(U32, a))
    case Q.BF{a}:
      bclone.f(a, PC.clone_eq(F32, a))
    case Q.BS{a}:
      bclone.s(a, PC.clone_eq(String, a))

# ---- the steps of Frame.filter_mask's loop, with the mask back -----------------------------------------

def CW(-c: C.Column, -m: Array<U32>, +kept: U32) -> Type:
  {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}

# one Cols.compact.step: the compacted column on the accumulator, the mask itself back
def st1(-n: String, -c: C.Column, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, ec: CW(c, m, kept))
  -> {C.Cols.compact.step(n, kept, c, (m, acc)) == (m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  %Equal.sym(C.Column & Array<U32>, C.Column.compact(c, m, kept), (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m), ec) : {C.Cols.compact.add(n, acc, _) == (m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  {==}

def chain3(-n1: String, -c1: C.Column, -n2: String, -c2: C.Column, -n3: String, -c3: C.Column, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, e1: CW(c1, m, kept), e2: CW(c2, m, kept), e3: CW(c3, m, kept))
  -> {C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  %Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.step(n1, kept, c1, (m, acc)), (m, C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc), st1(n1, c1, m, acc, kept, e1)) : {C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, _)) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.step(n2, kept, c2, (m, C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc)), (m, C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc), st1(n2, c2, m, C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc, kept, e2)) : {C.Cols.compact.step(n3, kept, c3, _) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  st1(n3, c3, m, C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc, kept, e3)

def chain4(-n1: String, -c1: C.Column, -n2: String, -c2: C.Column, -n3: String, -c3: C.Column, -n4: String, -c4: C.Column, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, e1: CW(c1, m, kept), e2: CW(c2, m, kept), e3: CW(c3, m, kept), e4: CW(c4, m, kept))
  -> {C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc))))) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(c4, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  %Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))), (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc), chain3(n1, c1, n2, c2, n3, c3, m, acc, kept, e1, e2, e3)) : {C.Cols.compact.step(n4, kept, c4, _) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(c4, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  st1(n4, c4, m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc, kept, e4)

def one3.k(-n1: String, y1: Q.Fz, -n2: String, y2: Q.Fz, -n3: String, y3: Q.Fz, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, w: CE3(U32, m))
  -> {Q.Exec.fc.one(n3, kept, y3, Q.Exec.fc.one(n2, kept, y2, Q.Exec.fc.one(n1, kept, y1, (m, acc)))) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  (m1, m2, m3, e1, e2, e3) = w
  chain3(n1, Q.Exec.unfz(y1), n2, Q.Exec.unfz(y2), n3, Q.Exec.unfz(y3), m, acc, kept, colw(Q.Exec.unfz(y1), m, kept, Q.Exec.unfz(y1), m1, {==}, e1), colw(Q.Exec.unfz(y2), m, kept, Q.Exec.unfz(y2), m2, {==}, e2), colw(Q.Exec.unfz(y3), m, kept, Q.Exec.unfz(y3), m3, {==}, e3))

# 3 columns one by one (Exec.fc.one = Cols.compact.step on the column put back)
def one3(-n1: String, y1: Q.Fz, -n2: String, y2: Q.Fz, -n3: String, y3: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.one(n3, kept, y3, Q.Exec.fc.one(n2, kept, y2, Q.Exec.fc.one(n1, kept, y1, (m, acc)))) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  one3.k(n1, y1, n2, y2, n3, y3, m, acc, kept, ce3(U32, m))

def one4.k(-n1: String, y1: Q.Fz, -n2: String, y2: Q.Fz, -n3: String, y3: Q.Fz, -n4: String, y4: Q.Fz, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, w: CE4(U32, m))
  -> {Q.Exec.fc.one(n4, kept, y4, Q.Exec.fc.one(n3, kept, y3, Q.Exec.fc.one(n2, kept, y2, Q.Exec.fc.one(n1, kept, y1, (m, acc))))) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  (m1, m2, m3, m4, e1, e2, e3, e4) = w
  chain4(n1, Q.Exec.unfz(y1), n2, Q.Exec.unfz(y2), n3, Q.Exec.unfz(y3), n4, Q.Exec.unfz(y4), m, acc, kept, colw(Q.Exec.unfz(y1), m, kept, Q.Exec.unfz(y1), m1, {==}, e1), colw(Q.Exec.unfz(y2), m, kept, Q.Exec.unfz(y2), m2, {==}, e2), colw(Q.Exec.unfz(y3), m, kept, Q.Exec.unfz(y3), m3, {==}, e3), colw(Q.Exec.unfz(y4), m, kept, Q.Exec.unfz(y4), m4, {==}, e4))

# 4 columns one by one (Exec.fc.one = Cols.compact.step on the column put back)
def one4(-n1: String, y1: Q.Fz, -n2: String, y2: Q.Fz, -n3: String, y3: Q.Fz, -n4: String, y4: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.one(n4, kept, y4, Q.Exec.fc.one(n3, kept, y3, Q.Exec.fc.one(n2, kept, y2, Q.Exec.fc.one(n1, kept, y1, (m, acc))))) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(y1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  one4.k(n1, y1, n2, y2, n3, y3, n4, y4, m, acc, kept, ce4(U32, m))

def pclw(s: Q.Sh, -b: Q.Buf, b1: Q.Buf, eb: {b1 == b : Q.Buf}, +l: U32, +p: Nat, -m: Array<U32>, m1: Array<U32>, em: {m1 == m : Array<U32>}, +kept: U32)
  -> {Q.Exec.mk(s, bk(b, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, b, l, p, C.AllValid{}), m, kept)) : C.Column}:
  %eb : {Q.Exec.mk(s, bk(_, l, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, _, l, p, C.AllValid{}), m, kept)) : C.Column}
  %em : {Q.Exec.mk(s, bk(b1, l, K.Kernel.depth_for(U32.add(kept, 1)), _), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{}) == Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.mk(s, b1, l, p, C.AllValid{}), _, kept)) : C.Column}
  pcl(s, b1, l, p, m1, kept)

def c3w(+n: U32, +d: Nat, -m: Array<U32>, m1: Array<U32>, em: {m1 == m : Array<U32>}, -b1: Q.Buf, -b2: Q.Buf, -b3: Q.Buf, x1: Q.Buf, x2: Q.Buf, x3: Q.Buf, e1: {x1 == b1 : Q.Buf}, e2: {x2 == b2 : Q.Buf}, e3: {x3 == b3 : Q.Buf})
  -> {Q.Exec.c3(n, d, m, b1, b2, b3) == Q.F3{bk(b1, n, d, m), bk(b2, n, d, m), bk(b3, n, d, m), m} : Q.F3}:
  %e1 : {Q.Exec.c3(n, d, m, _, b2, b3) == Q.F3{bk(_, n, d, m), bk(b2, n, d, m), bk(b3, n, d, m), m} : Q.F3}
  %e2 : {Q.Exec.c3(n, d, m, x1, _, b3) == Q.F3{bk(x1, n, d, m), bk(_, n, d, m), bk(b3, n, d, m), m} : Q.F3}
  %e3 : {Q.Exec.c3(n, d, m, x1, x2, _) == Q.F3{bk(x1, n, d, m), bk(x2, n, d, m), bk(_, n, d, m), m} : Q.F3}
  %em : {Q.Exec.c3(n, d, _, x1, x2, x3) == Q.F3{bk(x1, n, d, _), bk(x2, n, d, _), bk(x3, n, d, _), _} : Q.F3}
  c3t(n, d, m1, x1, x2, x3)

def c4w(+n: U32, +d: Nat, -m: Array<U32>, m1: Array<U32>, em: {m1 == m : Array<U32>}, -b1: Q.Buf, -b2: Q.Buf, -b3: Q.Buf, -b4: Q.Buf, x1: Q.Buf, x2: Q.Buf, x3: Q.Buf, x4: Q.Buf, e1: {x1 == b1 : Q.Buf}, e2: {x2 == b2 : Q.Buf}, e3: {x3 == b3 : Q.Buf}, e4: {x4 == b4 : Q.Buf})
  -> {Q.Exec.c4(n, d, m, b1, b2, b3, b4) == Q.F4{bk(b1, n, d, m), bk(b2, n, d, m), bk(b3, n, d, m), bk(b4, n, d, m), m} : Q.F4}:
  %e1 : {Q.Exec.c4(n, d, m, _, b2, b3, b4) == Q.F4{bk(_, n, d, m), bk(b2, n, d, m), bk(b3, n, d, m), bk(b4, n, d, m), m} : Q.F4}
  %e2 : {Q.Exec.c4(n, d, m, x1, _, b3, b4) == Q.F4{bk(x1, n, d, m), bk(_, n, d, m), bk(b3, n, d, m), bk(b4, n, d, m), m} : Q.F4}
  %e3 : {Q.Exec.c4(n, d, m, x1, x2, _, b4) == Q.F4{bk(x1, n, d, m), bk(x2, n, d, m), bk(_, n, d, m), bk(b4, n, d, m), m} : Q.F4}
  %e4 : {Q.Exec.c4(n, d, m, x1, x2, x3, _) == Q.F4{bk(x1, n, d, m), bk(x2, n, d, m), bk(x3, n, d, m), bk(_, n, d, m), m} : Q.F4}
  %em : {Q.Exec.c4(n, d, _, x1, x2, x3, x4) == Q.F4{bk(x1, n, d, _), bk(x2, n, d, _), bk(x3, n, d, _), bk(x4, n, d, _), _} : Q.F4}
  c4t(n, d, m1, x1, x2, x3, x4)

def s3.f.k(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, -b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, -b2: Q.Buf, -n3: String, +l3: U32, +p3: Nat, s3: Q.Sh, -b3: Q.Buf, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, +e12: {l1 == l2 : U32}, +e13: {l1 == l3 : U32}, wb1: BC(b1), wb2: BC(b2), wb3: BC(b3), wm: CE4(U32, m))
  -> {Q.Exec.fc.k3(n1, s1, n2, s2, n3, s3, kept, K.Kernel.depth_for(U32.add(kept, 1)), acc, Q.Exec.c3(l1, K.Kernel.depth_for(U32.add(kept, 1)), m, b1, b2, b3)) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  (b1a, b1b, eb1a, eb1b) = wb1
  (b2a, b2b, eb2a, eb2b) = wb2
  (b3a, b3b, eb3a, eb3b) = wb3
  (m1, m2, m3, m4, em1, em2, em3, em4) = wm
  %Equal.sym(Q.F3, Q.Exec.c3(l1, K.Kernel.depth_for(U32.add(kept, 1)), m, b1, b2, b3), Q.F3{bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), bk(b2, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), bk(b3, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), m}, c3w(l1, K.Kernel.depth_for(U32.add(kept, 1)), m, m4, em4, b1, b2, b3, b1a, b2a, b3a, eb1a, eb2a, eb3a)) : {Q.Exec.fc.k3(n1, s1, n2, s2, n3, s3, kept, K.Kernel.depth_for(U32.add(kept, 1)), acc, _) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(U32, l1, l2, e12) : {(m, C.Named{n3, Q.Exec.mk(s3, bk(b3, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, _, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(U32, l1, l3, e13) : {(m, C.Named{n3, Q.Exec.mk(s3, bk(b3, _, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s1, b1, b1b, eb1b, l1, p1, m, m1, em1, kept) : {(m, C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, _} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s2, b2, b2b, eb2b, l2, p2, m, m2, em2, kept) : {(m, C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, _} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s3, b3, b3b, eb3b, l3, p3, m, m3, em3, kept) : {(m, C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n3, _} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) : Array<U32> & List<&1, C.Named>}
  {==}

def s3.t(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, b2: Q.Buf, -n3: String, +l3: U32, +p3: Nat, s3: Q.Sh, b3: Q.Buf, ok: Bool, +eok: {Bool.and(U32.is_eq(l1, l2), U32.is_eq(l1, l3)) == ok : Bool}, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.t3(ok, n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match ok:
    case True{}:
      s3.f.k(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, m, acc, kept, PV.u32_eq_sound(l1, l2, L.and_left(U32.is_eq(l1, l2), U32.is_eq(l1, l3), eok)), PV.u32_eq_sound(l1, l3, L.and_right(U32.is_eq(l1, l2), U32.is_eq(l1, l3), eok)), bclone(b1), bclone(b2), bclone(b3), ce4(U32, m))
    case False{}:
      one3(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, Q.FzOk{l3, p3, s3, b3}, m, acc, kept)

def s3.l3(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, b2: Q.Buf, -n3: String, z3: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s3(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, z3, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z3:
    case Q.FzOk{+l3, +p3, s3, b3}:
      s3.t(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, Bool.and(U32.is_eq(l1, l2), U32.is_eq(l1, l3)), {==}, m, acc, kept)
    case Q.FzNo{c3}:
      one3(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, Q.FzNo{c3}, m, acc, kept)

def s3.l2(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, z2: Q.Fz, -n3: String, z3: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s3(n1, Q.FzOk{l1, p1, s1, b1}, n2, z2, n3, z3, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z2:
    case Q.FzOk{+l2, +p2, s2, b2}:
      s3.l3(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, z3, m, acc, kept)
    case Q.FzNo{c2}:
      one3(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzNo{c2}, n3, z3, m, acc, kept)

def s3(-n1: String, z1: Q.Fz, -n2: String, z2: Q.Fz, -n3: String, z3: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s3(n1, z1, n2, z2, n3, z3, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z1:
    case Q.FzOk{+l1, +p1, s1, b1}:
      s3.l2(n1, l1, p1, s1, b1, n2, z2, n3, z3, m, acc, kept)
    case Q.FzNo{c1}:
      one3(n1, Q.FzNo{c1}, n2, z2, n3, z3, m, acc, kept)

def s4.f.k(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, -b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, -b2: Q.Buf, -n3: String, +l3: U32, +p3: Nat, s3: Q.Sh, -b3: Q.Buf, -n4: String, +l4: U32, +p4: Nat, s4: Q.Sh, -b4: Q.Buf, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, +e12: {l1 == l2 : U32}, +e13: {l1 == l3 : U32}, +e14: {l1 == l4 : U32}, wb1: BC(b1), wb2: BC(b2), wb3: BC(b3), wb4: BC(b4), wm: CE5(U32, m))
  -> {Q.Exec.fc.k4(n1, s1, n2, s2, n3, s3, n4, s4, kept, K.Kernel.depth_for(U32.add(kept, 1)), acc, Q.Exec.c4(l1, K.Kernel.depth_for(U32.add(kept, 1)), m, b1, b2, b3, b4)) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  (b1a, b1b, eb1a, eb1b) = wb1
  (b2a, b2b, eb2a, eb2b) = wb2
  (b3a, b3b, eb3a, eb3b) = wb3
  (b4a, b4b, eb4a, eb4b) = wb4
  (m1, m2, m3, m4, m5, em1, em2, em3, em4, em5) = wm
  %Equal.sym(Q.F4, Q.Exec.c4(l1, K.Kernel.depth_for(U32.add(kept, 1)), m, b1, b2, b3, b4), Q.F4{bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), bk(b2, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), bk(b3, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), bk(b4, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), m}, c4w(l1, K.Kernel.depth_for(U32.add(kept, 1)), m, m5, em5, b1, b2, b3, b4, b1a, b2a, b3a, b4a, eb1a, eb2a, eb3a, eb4a)) : {Q.Exec.fc.k4(n1, s1, n2, s2, n3, s3, n4, s4, kept, K.Kernel.depth_for(U32.add(kept, 1)), acc, _) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(U32, l1, l2, e12) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, _, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(U32, l1, l3, e13) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, _, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(U32, l1, l4, e14) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, _, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s1, b1, b1b, eb1b, l1, p1, m, m1, em1, kept) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, l4, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, _} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s2, b2, b2b, eb2b, l2, p2, m, m2, em2, kept) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, l4, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, _} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s3, b3, b3b, eb3b, l3, p3, m, m3, em3, kept) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, l4, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, _} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) : Array<U32> & List<&1, C.Named>}
  %pclw(s4, b4, b4b, eb4b, l4, p4, m, m4, em4, kept) : {(m, C.Named{n4, Q.Exec.mk(s4, bk(b4, l4, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) == (m, C.Named{n4, _} <> C.Named{n3, Q.Exec.mk(s3, bk(b3, l3, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n2, Q.Exec.mk(s2, bk(b2, l2, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> C.Named{n1, Q.Exec.mk(s1, bk(b1, l1, K.Kernel.depth_for(U32.add(kept, 1)), m), kept, K.Kernel.depth_for(U32.add(kept, 1)), C.AllValid{})} <> acc) : Array<U32> & List<&1, C.Named>}
  {==}

def s4.t(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, b2: Q.Buf, -n3: String, +l3: U32, +p3: Nat, s3: Q.Sh, b3: Q.Buf, -n4: String, +l4: U32, +p4: Nat, s4: Q.Sh, b4: Q.Buf, ok: Bool, +eok: {Bool.and(U32.is_eq(l1, l2), Bool.and(U32.is_eq(l1, l3), U32.is_eq(l1, l4))) == ok : Bool}, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.t4(ok, n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, n4, l4, p4, s4, b4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l4, p4, s4, b4}), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match ok:
    case True{}:
      s4.f.k(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, n4, l4, p4, s4, b4, m, acc, kept, PV.u32_eq_sound(l1, l2, L.and_left(U32.is_eq(l1, l2), Bool.and(U32.is_eq(l1, l3), U32.is_eq(l1, l4)), eok)), PV.u32_eq_sound(l1, l3, L.and_left(U32.is_eq(l1, l3), U32.is_eq(l1, l4), L.and_right(U32.is_eq(l1, l2), Bool.and(U32.is_eq(l1, l3), U32.is_eq(l1, l4)), eok))), PV.u32_eq_sound(l1, l4, L.and_right(U32.is_eq(l1, l3), U32.is_eq(l1, l4), L.and_right(U32.is_eq(l1, l2), Bool.and(U32.is_eq(l1, l3), U32.is_eq(l1, l4)), eok))), bclone(b1), bclone(b2), bclone(b3), bclone(b4), ce5(U32, m))
    case False{}:
      one4(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, Q.FzOk{l3, p3, s3, b3}, n4, Q.FzOk{l4, p4, s4, b4}, m, acc, kept)

def s4.l4(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, b2: Q.Buf, -n3: String, +l3: U32, +p3: Nat, s3: Q.Sh, b3: Q.Buf, -n4: String, z4: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s4(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, Q.FzOk{l3, p3, s3, b3}, n4, z4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l3, p3, s3, b3}), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z4:
    case Q.FzOk{+l4, +p4, s4, b4}:
      s4.t(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, n4, l4, p4, s4, b4, Bool.and(U32.is_eq(l1, l2), Bool.and(U32.is_eq(l1, l3), U32.is_eq(l1, l4))), {==}, m, acc, kept)
    case Q.FzNo{c4}:
      one4(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, Q.FzOk{l3, p3, s3, b3}, n4, Q.FzNo{c4}, m, acc, kept)

def s4.l3(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, +l2: U32, +p2: Nat, s2: Q.Sh, b2: Q.Buf, -n3: String, z3: Q.Fz, -n4: String, z4: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s4(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, z3, n4, z4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l2, p2, s2, b2}), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z3:
    case Q.FzOk{+l3, +p3, s3, b3}:
      s4.l4(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, n4, z4, m, acc, kept)
    case Q.FzNo{c3}:
      one4(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzOk{l2, p2, s2, b2}, n3, Q.FzNo{c3}, n4, z4, m, acc, kept)

def s4.l2(-n1: String, +l1: U32, +p1: Nat, s1: Q.Sh, b1: Q.Buf, -n2: String, z2: Q.Fz, -n3: String, z3: Q.Fz, -n4: String, z4: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s4(n1, Q.FzOk{l1, p1, s1, b1}, n2, z2, n3, z3, n4, z4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(Q.FzOk{l1, p1, s1, b1}), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z2:
    case Q.FzOk{+l2, +p2, s2, b2}:
      s4.l3(n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, z3, n4, z4, m, acc, kept)
    case Q.FzNo{c2}:
      one4(n1, Q.FzOk{l1, p1, s1, b1}, n2, Q.FzNo{c2}, n3, z3, n4, z4, m, acc, kept)

def s4(-n1: String, z1: Q.Fz, -n2: String, z2: Q.Fz, -n3: String, z3: Q.Fz, -n4: String, z4: Q.Fz, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s4(n1, z1, n2, z2, n3, z3, n4, z4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}:
  match z1:
    case Q.FzOk{+l1, +p1, s1, b1}:
      s4.l2(n1, l1, p1, s1, b1, n2, z2, n3, z3, n4, z4, m, acc, kept)
    case Q.FzNo{c1}:
      one4(n1, Q.FzNo{c1}, n2, z2, n3, z3, n4, z4, m, acc, kept)


def CE6(-T: Data, -a: Array<T>) -> Type:
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> &a5: Array<T> -> &a6: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>} & {a5 == a : Array<T>} & {a6 == a : Array<T>}

def ce6.k(-T: Data, -a: Array<T>, a1: Array<T>, +e1: {a1 == a : Array<T>}, -b: Array<T>, +eb: {b == a : Array<T>}, w: CE5(T, b)) -> CE6(T, a):
  (b1, b2, b3, b4, b5, eb1, eb2, eb3, eb4, eb5) = w
  (a1, b1, b2, b3, b4, b5, e1, Equal.trans(Array<T>, b1, b, a, eb1, eb), Equal.trans(Array<T>, b2, b, a, eb2, eb), Equal.trans(Array<T>, b3, b, a, eb3, eb), Equal.trans(Array<T>, b4, b, a, eb4, eb), Equal.trans(Array<T>, b5, b, a, eb5, eb))

def ce6.a(-T: Data, -a: Array<T>, w: CE(T, a)) -> CE6(T, a):
  (a1, b, e1, eb) = w
  ce6.k(T, a, a1, e1, b, eb, ce5(T, b))

def ce6(-T: Data, a: Array<T>) -> CE6(T, a):
  ce6.a(T, a, PC.clone_eq(T, a))

# FZW of a column from a live copy of it
def fzwe(-c: C.Column, c1: C.Column, e: {c1 == c : C.Column}) -> FZW(c):
  %e : FZW(_)
  fzw(c1)

def fg3.b(-n1: String, -c1: C.Column, -n2: String, -c2: C.Column, -n3: String, -c3: C.Column, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, cb1: C.Column, +eb1: {cb1 == c1 : C.Column}, w1: FZW(c1), cb2: C.Column, +eb2: {cb2 == c2 : C.Column}, w2: FZW(c2), cb3: C.Column, +eb3: {cb3 == c3 : C.Column}, w3: FZW(c3), wm: CE4(U32, m))
  -> {Q.Exec.fc.s3(n1, Q.Exec.fz(c1), n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}:
  (z1, efz1, eun1) = w1
  (z2, efz2, eun2) = w2
  (z3, efz3, eun3) = w3
  (m1, m2, m3, m4, +em1, em2, em3, em4) = wm
  %Equal.sym(Q.Fz, Q.Exec.fz(c1), z1, efz1) : {Q.Exec.fc.s3(n1, _, n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Q.Fz, Q.Exec.fz(c2), z2, efz2) : {Q.Exec.fc.s3(n1, z1, n2, _, n3, Q.Exec.fz(c3), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Q.Fz, Q.Exec.fz(c3), z3, efz3) : {Q.Exec.fc.s3(n1, z1, n2, z2, n3, _, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}
  %em1 : {Q.Exec.fc.s3(n1, z1, n2, z2, n3, z3, kept, K.Kernel.depth_for(U32.add(kept, 1)), (_, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32> & List<&1, C.Named>, Q.Exec.fc.s3(n1, z1, n2, z2, n3, z3, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m1, acc)), (m1, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m1, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m1, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m1, kept))} <> acc), s3(n1, z1, n2, z2, n3, z3, m1, acc, kept)) : {_ == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32>, m1, m, em1) : {(_, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), _, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), _, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), _, kept))} <> acc) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))), (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc), chain3(n1, c1, n2, c2, n3, c3, m, acc, kept, colw(c1, m, kept, cb1, m2, eb1, em2), colw(c2, m, kept, cb2, m3, eb2, em3), colw(c3, m, kept, cb3, m4, eb3, em4))) : {(m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) == _ : Array<U32> & List<&1, C.Named>}
  %eun1 : {(m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %eun2 : {(m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  %eun3 : {(m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) == (m, C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc) : Array<U32> & List<&1, C.Named>}
  {==}

def fg3.a(-n1: String, -c1: C.Column, -n2: String, -c2: C.Column, -n3: String, -c3: C.Column, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, wc1: PV.CloneW(c1), wc2: PV.CloneW(c2), wc3: PV.CloneW(c3))
  -> {Q.Exec.fc.s3(n1, Q.Exec.fz(c1), n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}:
  (ca1, cb1, ecl1, eca1, ecb1) = wc1
  (ca2, cb2, ecl2, eca2, ecb2) = wc2
  (ca3, cb3, ecl3, eca3, ecb3) = wc3
  fg3.b(n1, c1, n2, c2, n3, c3, m, acc, kept, cb1, ecb1, fzwe(c1, ca1, eca1), cb2, ecb2, fzwe(c2, ca2, eca2), cb3, ecb3, fzwe(c3, ca3, eca3), ce4(U32, m))

def fg3(-n1: String, c1: C.Column, -n2: String, c2: C.Column, -n3: String, c3: C.Column, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32)
  -> {Q.Exec.fc.s3(n1, Q.Exec.fz(c1), n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))) : Array<U32> & List<&1, C.Named>}:
  fg3.a(n1, c1, n2, c2, n3, c3, m, acc, kept, PV.clone_w(c1), PV.clone_w(c2), PV.clone_w(c3))

def fg4.b(-n1: String, -c1: C.Column, -n2: String, -c2: C.Column, -n3: String, -c3: C.Column, -n4: String, -c4: C.Column, -rest: List<&1, C.Named>, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, cb1: C.Column, +eb1: {cb1 == c1 : C.Column}, w1: FZW(c1), cb2: C.Column, +eb2: {cb2 == c2 : C.Column}, w2: FZW(c2), cb3: C.Column, +eb3: {cb3 == c3 : C.Column}, w3: FZW(c3), cb4: C.Column, +eb4: {cb4 == c4 : C.Column}, w4: FZW(c4), wm: CE6(U32, m), ih: @ma: Array<U32> -> @-a2: List<&1, C.Named> -> {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (ma, a2)) == C.Cols.compact.go(rest, kept, (ma, a2)) : Array<U32> & List<&1, C.Named>})
  -> {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, Q.Exec.fz(c1), n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), n4, Q.Exec.fz(c4), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}:
  (z1, efz1, eun1) = w1
  (z2, efz2, eun2) = w2
  (z3, efz3, eun3) = w3
  (z4, efz4, eun4) = w4
  (m1, m2, m3, m4, m5, m6, +em1, em2, em3, em4, em5, em6) = wm
  %Equal.sym(Q.Fz, Q.Exec.fz(c1), z1, efz1) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, _, n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), n4, Q.Exec.fz(c4), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Q.Fz, Q.Exec.fz(c2), z2, efz2) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, z1, n2, _, n3, Q.Exec.fz(c3), n4, Q.Exec.fz(c4), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Q.Fz, Q.Exec.fz(c3), z3, efz3) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, z1, n2, z2, n3, _, n4, Q.Exec.fz(c4), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Q.Fz, Q.Exec.fz(c4), z4, efz4) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, z1, n2, z2, n3, z3, n4, _, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %em1 : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, z1, n2, z2, n3, z3, n4, z4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (_, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32> & List<&1, C.Named>, Q.Exec.fc.s4(n1, z1, n2, z2, n3, z3, n4, z4, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m1, acc)), (m1, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m1, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m1, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m1, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m1, kept))} <> acc), s4(n1, z1, n2, z2, n3, z3, n4, z4, m1, acc, kept)) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), _) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32>, m1, m, em1) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (_, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), _, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), _, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), _, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), _, kept))} <> acc)) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}
  %Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc))))), (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(c4, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(c1, m, kept))} <> acc), chain4(n1, c1, n2, c2, n3, c3, n4, c4, m, acc, kept, colw(c1, m, kept, cb1, m2, eb1, em2), colw(c2, m, kept, cb2, m3, eb2, em3), colw(c3, m, kept, cb3, m4, eb3, em4), colw(c4, m, kept, cb4, m5, eb4, em5))) : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) == C.Cols.compact.go(rest, kept, _) : Array<U32> & List<&1, C.Named>}
  %eun1 : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) == C.Cols.compact.go(rest, kept, (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(c4, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(c2, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> acc)) : Array<U32> & List<&1, C.Named>}
  %eun2 : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) == C.Cols.compact.go(rest, kept, (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(c4, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(c3, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) : Array<U32> & List<&1, C.Named>}
  %eun3 : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) == C.Cols.compact.go(rest, kept, (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(c4, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) : Array<U32> & List<&1, C.Named>}
  %eun4 : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) == C.Cols.compact.go(rest, kept, (m, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(_, m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) : Array<U32> & List<&1, C.Named>}
  %em6 : {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (_, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) == C.Cols.compact.go(rest, kept, (_, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)) : Array<U32> & List<&1, C.Named>}
  ih(m6, C.Named{n4, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z4), m, kept))} <> C.Named{n3, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z3), m, kept))} <> C.Named{n2, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z2), m, kept))} <> C.Named{n1, Pair.fst(C.Column, Array<U32>, C.Column.compact(Q.Exec.unfz(z1), m, kept))} <> acc)

def fg4.a(-n1: String, -c1: C.Column, -n2: String, -c2: C.Column, -n3: String, -c3: C.Column, -n4: String, -c4: C.Column, -rest: List<&1, C.Named>, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, wc1: PV.CloneW(c1), wc2: PV.CloneW(c2), wc3: PV.CloneW(c3), wc4: PV.CloneW(c4), ih: @ma: Array<U32> -> @-a2: List<&1, C.Named> -> {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (ma, a2)) == C.Cols.compact.go(rest, kept, (ma, a2)) : Array<U32> & List<&1, C.Named>})
  -> {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, Q.Exec.fz(c1), n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), n4, Q.Exec.fz(c4), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}:
  (ca1, cb1, ecl1, eca1, ecb1) = wc1
  (ca2, cb2, ecl2, eca2, ecb2) = wc2
  (ca3, cb3, ecl3, eca3, ecb3) = wc3
  (ca4, cb4, ecl4, eca4, ecb4) = wc4
  fg4.b(n1, c1, n2, c2, n3, c3, n4, c4, rest, m, acc, kept, cb1, ecb1, fzwe(c1, ca1, eca1), cb2, ecb2, fzwe(c2, ca2, eca2), cb3, ecb3, fzwe(c3, ca3, eca3), cb4, ecb4, fzwe(c4, ca4, eca4), ce6(U32, m), ih)

def fg4(-n1: String, c1: C.Column, -n2: String, c2: C.Column, -n3: String, c3: C.Column, -n4: String, c4: C.Column, -rest: List<&1, C.Named>, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, ih: @ma: Array<U32> -> @-a2: List<&1, C.Named> -> {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), (ma, a2)) == C.Cols.compact.go(rest, kept, (ma, a2)) : Array<U32> & List<&1, C.Named>})
  -> {Q.Exec.fc.go(rest, kept, K.Kernel.depth_for(U32.add(kept, 1)), Q.Exec.fc.s4(n1, Q.Exec.fz(c1), n2, Q.Exec.fz(c2), n3, Q.Exec.fz(c3), n4, Q.Exec.fz(c4), kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc))) == C.Cols.compact.go(rest, kept, C.Cols.compact.step(n4, kept, c4, C.Cols.compact.step(n3, kept, c3, C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, (m, acc)))))) : Array<U32> & List<&1, C.Named>}:
  fg4.a(n1, c1, n2, c2, n3, c3, n4, c4, rest, m, acc, kept, PV.clone_w(c1), PV.clone_w(c2), PV.clone_w(c3), PV.clone_w(c4), ih)

# Exec.fc's grouped loop IS Frame.filter_mask's loop (Cols.compact.go), for every column list
def fgo(cols: List<&1, C.Named>, m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32) -> {Q.Exec.fc.go(cols, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, acc)) == C.Cols.compact.go(cols, kept, (m, acc)) : Array<U32> & List<&1, C.Named>}:
  match cols:
    case Nil{}:
      {==}
    case C.Named{n1, c1} <> Nil{}:
      {==}
    case C.Named{n1, c1} <> C.Named{n2, c2} <> Nil{}:
      {==}
    case C.Named{+n1, c1} <> C.Named{+n2, c2} <> C.Named{+n3, c3} <> Nil{}:
      fg3(n1, c1, n2, c2, n3, c3, m, acc, kept)
    case C.Named{+n1, c1} <> C.Named{+n2, c2} <> C.Named{+n3, c3} <> C.Named{+n4, c4} <> rest:
      fg4(n1, c1, n2, c2, n3, c3, n4, c4, rest, m, acc, kept, ma => a2 => fgo(rest, ma, a2, kept))

def Laws.fc_filter_mask(g, m, kept):
  match g:
    case C.Frame{h, cols}:
      Equal.cong(Array<U32> & List<&1, C.Named>, C.Frame, r => C.Frame.filter_mask.k(kept, r), Q.Exec.fc.go(cols, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, Nil{})), C.Cols.compact.go(cols, kept, (m, Nil{})), fgo(cols, m, Nil{}, kept))

# ---- Frame.filter_mask as a function of the columns: cm ---------------------------------------------
#
# cm(cols, m) compacts the columns one by one (Column.compact), the mask threaded from the LAST column
# to the first (a self-recursion that destructures only parameters); with colw every mask is m itself,
# so cm's columns are Column.compact(c, m, kept)'s, one per input column, names unchanged (cmu).

def cm.h(n: String, l: List<&1, C.Named>, r: C.Column & Array<U32>) -> List<&1, C.Named> & Array<U32>:
  (c2, m2) = r
  (C.Named{n, c2} <> l, m2)

def cm.g(n: String, c: C.Column, +kept: U32, r: List<&1, C.Named> & Array<U32>) -> List<&1, C.Named> & Array<U32>:
  (l, m) = r
  cm.h(n, l, C.Column.compact(c, m, kept))

def cm(cols: List<&1, C.Named>, m: Array<U32>, +kept: U32) -> List<&1, C.Named> & Array<U32>:
  match cols:
    case Nil{}:
      (Nil{}, m)
    case C.Named{n, c} <> rest:
      cm.g(n, c, kept, cm(rest, m, kept))

# the columns of cm
def cml(cols: List<&1, C.Named>, m: Array<U32>, +kept: U32) -> List<&1, C.Named>:
  Pair.fst(List<&1, C.Named>, Array<U32>, cm(cols, m, kept))

# cm answers its columns and the mask itself
def CMW(-cols: List<&1, C.Named>, -m: Array<U32>, +kept: U32) -> Type:
  {cm(cols, m, kept) == (cml(cols, m, kept), m) : List<&1, C.Named> & Array<U32>}

def cmw_cons(-n: String, -c: C.Column, -l: List<&1, C.Named>, -m: Array<U32>, +kept: U32, ec: CW(c, m, kept), el: CMW(l, m, kept)) -> CMW(C.Named{n, c} <> l, m, kept):
  %Equal.sym(List<&1, C.Named> & Array<U32>, cm(l, m, kept), (cml(l, m, kept), m), el) : {cm.g(n, c, kept, _) == (Pair.fst(List<&1, C.Named>, Array<U32>, cm.g(n, c, kept, _)), m) : List<&1, C.Named> & Array<U32>}
  %Equal.sym(C.Column & Array<U32>, C.Column.compact(c, m, kept), (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m), ec) : {cm.h(n, cml(l, m, kept), _) == (Pair.fst(List<&1, C.Named>, Array<U32>, cm.h(n, cml(l, m, kept), _)), m) : List<&1, C.Named> & Array<U32>}
  {==}

# one column of cm
def cmu(-n: String, -c: C.Column, -l: List<&1, C.Named>, -m: Array<U32>, +kept: U32, ec: CW(c, m, kept), el: CMW(l, m, kept))
  -> {cml(C.Named{n, c} <> l, m, kept) == C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(l, m, kept) : List<&1, C.Named>}:
  %Equal.sym(List<&1, C.Named> & Array<U32>, cm(l, m, kept), (cml(l, m, kept), m), el) : {Pair.fst(List<&1, C.Named>, Array<U32>, cm.g(n, c, kept, _)) == C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(l, m, kept) : List<&1, C.Named>}
  %Equal.sym(C.Column & Array<U32>, C.Column.compact(c, m, kept), (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m), ec) : {Pair.fst(List<&1, C.Named>, Array<U32>, cm.h(n, cml(l, m, kept), _)) == C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(l, m, kept) : List<&1, C.Named>}
  {==}

# a live copy equal to m, made from another (the transitivity every clone needs)
def etr(-a: Array<U32>, -b: Array<U32>, -m: Array<U32>, e1: {a == b : Array<U32>}, e2: {b == m : Array<U32>}) -> {a == m : Array<U32>}:
  Equal.trans(Array<U32>, a, b, m, e1, e2)

# ---- Frame.filter_mask's loop is the reversed cm ---------------------------------------------------

def CGO(-cols: List<&1, C.Named>, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32) -> Type:
  {C.Cols.compact.go(cols, kept, (m, acc)) == (m, List.reverse.go(&1, C.Named, cml(cols, m, kept), acc)) : Array<U32> & List<&1, C.Named>} & CMW(cols, m, kept)

def cgo.j(-n: String, -c: C.Column, -rest: List<&1, C.Named>, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}, ih1: {C.Cols.compact.go(rest, kept, (m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc)) == (m, List.reverse.go(&1, C.Named, cml(rest, m, kept), C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc)) : Array<U32> & List<&1, C.Named>}, +ih2: {cm(rest, m, kept) == (cml(rest, m, kept), m) : List<&1, C.Named> & Array<U32>}) -> CGO(C.Named{n, c} <> rest, m, acc, kept):
  ((%Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.step(n, kept, c, (m, acc)), (m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc), st1(n, c, m, acc, kept, ec)) : {C.Cols.compact.go(rest, kept, _) == (m, List.reverse.go(&1, C.Named, cml(C.Named{n, c} <> rest, m, kept), acc)) : Array<U32> & List<&1, C.Named>}; %Equal.sym(List<&1, C.Named>, cml(C.Named{n, c} <> rest, m, kept), C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(rest, m, kept), cmu(n, c, rest, m, kept, ec, ih2)) : {C.Cols.compact.go(rest, kept, (m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc)) == (m, List.reverse.go(&1, C.Named, _, acc)) : Array<U32> & List<&1, C.Named>}; ih1), cmw_cons(n, c, rest, m, kept, ec, ih2))

def cgo.k(-n: String, -c: C.Column, -rest: List<&1, C.Named>, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}, ih: CGO(rest, m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc, kept)) -> CGO(C.Named{n, c} <> rest, m, acc, kept):
  (ih1, ih2) = ih
  cgo.j(n, c, rest, m, acc, kept, ec, ih1, ih2)

def cgo.c(n: String, c: C.Column, -rest: List<&1, C.Named>, -m: Array<U32>, -acc: List<&1, C.Named>, +kept: U32, w: CE(U32, m), ih: @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> CGO(rest, m, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc, kept)) -> CGO(C.Named{n, c} <> rest, m, acc, kept):
  (m1, m2, e1, e2) = w
  cgo.k(n, c, rest, m, acc, kept, colw(c, m, kept, c, m1, {==}, e1), ih(m2, e2))

# Frame.filter_mask's loop is the reversed cm, and cm answers the mask (m erased, a live copy mm spent)
def cgo(cols: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, -acc: List<&1, C.Named>, +kept: U32) -> CGO(cols, m, acc, kept):
  match cols:
    case Nil{}:
      ({==}, {==})
    case C.Named{n, c} <> rest:
      cgo.c(n, c, rest, m, acc, kept, (%em : CE(U32, _); PC.clone_eq(U32, mm)), m2 => e2 => cgo(rest, m, m2, e2, C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> acc, kept))

# ---- cm commutes with List.reverse; filter_mask is Frame{kept, cm} ------------------------------------

def RCM(-xs: List<&1, C.Named>, -ys: List<&1, C.Named>, -m: Array<U32>, +kept: U32) -> Type:
  {List.reverse.go(&1, C.Named, cml(xs, m, kept), cml(ys, m, kept)) == cml(List.reverse.go(&1, C.Named, xs, ys), m, kept) : List<&1, C.Named>} & CMW(xs, m, kept)

def rcm.j(-n: String, -c: C.Column, -t: List<&1, C.Named>, -ys: List<&1, C.Named>, -m: Array<U32>, +kept: U32,
  +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>},
  +hy: {cm(ys, m, kept) == (cml(ys, m, kept), m) : List<&1, C.Named> & Array<U32>},
  r1: {List.reverse.go(&1, C.Named, cml(t, m, kept), cml(C.Named{n, c} <> ys, m, kept)) == cml(List.reverse.go(&1, C.Named, t, C.Named{n, c} <> ys), m, kept) : List<&1, C.Named>},
  +r2: {cm(t, m, kept) == (cml(t, m, kept), m) : List<&1, C.Named> & Array<U32>})
  -> RCM(C.Named{n, c} <> t, ys, m, kept):
  ((%Equal.sym(List<&1, C.Named>, cml(C.Named{n, c} <> t, m, kept), C.Named{n, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(t, m, kept), cmu(n, c, t, m, kept, ec, r2)) : {List.reverse.go(&1, C.Named, _, cml(ys, m, kept)) == cml(List.reverse.go(&1, C.Named, t, C.Named{n, c} <> ys), m, kept) : List<&1, C.Named>}; %cmu(n, c, ys, m, kept, ec, hy) : {List.reverse.go(&1, C.Named, cml(t, m, kept), _) == cml(List.reverse.go(&1, C.Named, t, C.Named{n, c} <> ys), m, kept) : List<&1, C.Named>}; r1), cmw_cons(n, c, t, m, kept, ec, r2))

def rcm.k2(-n: String, -c: C.Column, -t: List<&1, C.Named>, -ys: List<&1, C.Named>, -m: Array<U32>, +kept: U32,
  +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>},
  +hy: {cm(ys, m, kept) == (cml(ys, m, kept), m) : List<&1, C.Named> & Array<U32>},
  r: RCM(t, C.Named{n, c} <> ys, m, kept))
  -> RCM(C.Named{n, c} <> t, ys, m, kept):
  (r1, r2) = r
  rcm.j(n, c, t, ys, m, kept, ec, hy, r1, r2)

def rcm.k(-n: String, -c: C.Column, -t: List<&1, C.Named>, -ys: List<&1, C.Named>, -m: Array<U32>, +kept: U32,
  +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>},
  +hy: {cm(ys, m, kept) == (cml(ys, m, kept), m) : List<&1, C.Named> & Array<U32>},
  ih: @h2: {cm(C.Named{n, c} <> ys, m, kept) == (cml(C.Named{n, c} <> ys, m, kept), m) : List<&1, C.Named> & Array<U32>} -> RCM(t, C.Named{n, c} <> ys, m, kept))
  -> RCM(C.Named{n, c} <> t, ys, m, kept):
  rcm.k2(n, c, t, ys, m, kept, ec, hy, ih(cmw_cons(n, c, ys, m, kept, ec, hy)))

def rcm.c(n: String, c: C.Column, -t: List<&1, C.Named>, -ys: List<&1, C.Named>, -m: Array<U32>, +kept: U32, +hy: {cm(ys, m, kept) == (cml(ys, m, kept), m) : List<&1, C.Named> & Array<U32>}, w: CE(U32, m),
  ih: @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> @h2: {cm(C.Named{n, c} <> ys, m, kept) == (cml(C.Named{n, c} <> ys, m, kept), m) : List<&1, C.Named> & Array<U32>} -> RCM(t, C.Named{n, c} <> ys, m, kept))
  -> RCM(C.Named{n, c} <> t, ys, m, kept):
  (m1, m2, e1, e2) = w
  rcm.k(n, c, t, ys, m, kept, colw(c, m, kept, c, m1, {==}, e1), hy, h2 => ih(m2, e2, h2))

# reverse.go(cm xs, cm ys) is cm(reverse.go(xs, ys)) (given ys's mask comes back), and cm(xs) answers the mask
def rcm(xs: List<&1, C.Named>, -ys: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32, +hy: {cm(ys, m, kept) == (cml(ys, m, kept), m) : List<&1, C.Named> & Array<U32>}) -> RCM(xs, ys, m, kept):
  match xs:
    case Nil{}:
      ({==}, {==})
    case C.Named{n, c} <> t:
      rcm.c(n, c, t, ys, m, kept, hy, (%em : CE(U32, _); PC.clone_eq(U32, mm)), m2 => e2 => h2 => rcm(t, C.Named{n, c} <> ys, m, m2, e2, kept, h2))

# reversing twice (the accumulator form)
def rr(xs: List<&1, C.Named>, -a: List<&1, C.Named>) -> {List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, xs, a), Nil{}) == List.reverse.go(&1, C.Named, a, xs) : List<&1, C.Named>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rr(t, h <> a)

# two live copies of a column list (proof witnesses: PROOF_sorthead's cols_dup, which imports this file)
def LD(-cols: List<&1, C.Named>) -> Type:
  &a: List<&1, C.Named> -> &b: List<&1, C.Named> -> {a == cols : List<&1, C.Named>} & {b == cols : List<&1, C.Named>}

def ldup.k(+nm: String, -c: C.Column, -rest: List<&1, C.Named>, wc: PV.CloneW(c), wr: LD(rest)) -> LD(C.Named{nm, c} <> rest):
  (c1, c2, ecl, e1, e2) = wc
  (r1, r2, er1, er2) = wr
  (C.Named{nm, c1} <> r1, C.Named{nm, c2} <> r2, (%er1 : {C.Named{nm, c1} <> r1 == C.Named{nm, c} <> _ : List<&1, C.Named>}; %e1 : {C.Named{nm, c1} <> r1 == C.Named{nm, _} <> r1 : List<&1, C.Named>}; {==}), (%er2 : {C.Named{nm, c2} <> r2 == C.Named{nm, c} <> _ : List<&1, C.Named>}; %e2 : {C.Named{nm, c2} <> r2 == C.Named{nm, _} <> r2 : List<&1, C.Named>}; {==}))

def ldup(cols: List<&1, C.Named>) -> LD(cols):
  match cols:
    case Nil{}:
      (Nil{}, Nil{}, {==}, {==})
    case C.Named{+nm, c} <> rest:
      ldup.k(nm, c, rest, PV.clone_w(c), ldup(rest))

def FM(+h: U32, -cols: List<&1, C.Named>, -m: Array<U32>, +kept: U32) -> Type:
  {C.Frame.filter_mask(C.Frame{h, cols}, m, kept) == C.Frame{kept, cml(cols, m, kept)} : C.Frame}

def fm.b(+h: U32, -cols: List<&1, C.Named>, -m: Array<U32>, +kept: U32,
  g1: {C.Cols.compact.go(cols, kept, (m, Nil{})) == (m, List.reverse.go(&1, C.Named, cml(cols, m, kept), Nil{})) : Array<U32> & List<&1, C.Named>},
  q1: {List.reverse.go(&1, C.Named, cml(cols, m, kept), Nil{}) == cml(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept) : List<&1, C.Named>},
  q2: {List.reverse.go(&1, C.Named, cml(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept), Nil{}) == cml(List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, cols, Nil{}), Nil{}), m, kept) : List<&1, C.Named>},
  q3: {List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, cols, Nil{}), Nil{}) == cols : List<&1, C.Named>})
  -> FM(h, cols, m, kept):
  %Equal.sym(Array<U32> & List<&1, C.Named>, C.Cols.compact.go(cols, kept, (m, Nil{})), (m, List.reverse.go(&1, C.Named, cml(cols, m, kept), Nil{})), g1) : {C.Frame.filter_mask.k(kept, _) == C.Frame{kept, cml(cols, m, kept)} : C.Frame}
  %Equal.sym(List<&1, C.Named>, List.reverse.go(&1, C.Named, cml(cols, m, kept), Nil{}), cml(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept), q1) : {C.Frame{kept, List.reverse.go(&1, C.Named, _, Nil{})} == C.Frame{kept, cml(cols, m, kept)} : C.Frame}
  %Equal.sym(List<&1, C.Named>, List.reverse.go(&1, C.Named, cml(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept), Nil{}), cml(List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, cols, Nil{}), Nil{}), m, kept), q2) : {C.Frame{kept, _} == C.Frame{kept, cml(cols, m, kept)} : C.Frame}
  %Equal.sym(List<&1, C.Named>, List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, cols, Nil{}), Nil{}), cols, q3) : {C.Frame{kept, cml(_, m, kept)} == C.Frame{kept, cml(cols, m, kept)} : C.Frame}
  {==}

# the lemmas about the live copies, rewritten to the erased originals
def rcmw(-xs: List<&1, C.Named>, x1: List<&1, C.Named>, ex: {x1 == xs : List<&1, C.Named>}, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32) -> RCM(xs, Nil{}, m, kept):
  %ex : RCM(_, Nil{}, m, kept)
  rcm(x1, Nil{}, m, mm, em, kept, {==})

def rrw(-xs: List<&1, C.Named>, x1: List<&1, C.Named>, ex: {x1 == xs : List<&1, C.Named>}) -> {List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, xs, Nil{}), Nil{}) == xs : List<&1, C.Named>}:
  %ex : {List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, _, Nil{}), Nil{}) == _ : List<&1, C.Named>}
  rr(x1, Nil{})

def cgow(-xs: List<&1, C.Named>, x1: List<&1, C.Named>, ex: {x1 == xs : List<&1, C.Named>}, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32) -> CGO(xs, m, Nil{}, kept):
  %ex : CGO(_, m, Nil{}, kept)
  cgo(x1, m, mm, em, Nil{}, kept)

def fm.a(+h: U32, -cols: List<&1, C.Named>, -m: Array<U32>, +kept: U32, w1: LD(cols), w2: LD(cols), wm: CE3(U32, m)) -> FM(h, cols, m, kept):
  (a1, a2, ea1, ea2) = w1
  (b1, b2, eb1, eb2) = w2
  (m1, m2, m3, em1, em2, em3) = wm
  fm.b(h, cols, m, kept, Pair.fst({C.Cols.compact.go(cols, kept, (m, Nil{})) == (m, List.reverse.go(&1, C.Named, cml(cols, m, kept), Nil{})) : Array<U32> & List<&1, C.Named>}, CMW(cols, m, kept), cgow(cols, a1, ea1, m, m1, em1, kept)), Pair.fst({List.reverse.go(&1, C.Named, cml(cols, m, kept), Nil{}) == cml(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept) : List<&1, C.Named>}, CMW(cols, m, kept), rcmw(cols, a2, ea2, m, m2, em2, kept)), Pair.fst({List.reverse.go(&1, C.Named, cml(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept), Nil{}) == cml(List.reverse.go(&1, C.Named, List.reverse.go(&1, C.Named, cols, Nil{}), Nil{}), m, kept) : List<&1, C.Named>}, CMW(List.reverse.go(&1, C.Named, cols, Nil{}), m, kept), rcmw(List.reverse.go(&1, C.Named, cols, Nil{}), List.reverse.go(&1, C.Named, b1, Nil{}), Equal.cong(List<&1, C.Named>, List<&1, C.Named>, x => List.reverse.go(&1, C.Named, x, Nil{}), b1, cols, eb1), m, m3, em3, kept)), rrw(cols, b2, eb2))

def fm.c(+h: U32, -cols: List<&1, C.Named>, -m: Array<U32>, +kept: U32, w: LD(cols), wm: CE3(U32, m)) -> FM(h, cols, m, kept):
  (x, y, ex, ey) = w
  fm.a(h, cols, m, kept, (%ex : LD(_); ldup(x)), (%ey : LD(_); ldup(y)), wm)

# Frame.filter_mask IS Frame{kept, cm(cols)} (m erased, a live copy spent)
def fm(+h: U32, cols: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32) -> FM(h, cols, m, kept):
  fm.c(h, cols, m, kept, ldup(cols), (%em : CE3(U32, _); ce3(U32, mm)))

# ---- Cols.take over cm(cols) is cm over Cols.take(cols) -------------------------------------------

# a Maybe column compacted
def mmc(mc: Maybe<&1, C.Column>, m: Array<U32>, +kept: U32) -> Maybe<&1, C.Column>:
  match mc:
    case None{}:
      None{}
    case Some{c}:
      Some{Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))}

def TK(-cols: List<&1, C.Named>, -m: Array<U32>, +nm: String, +kept: U32) -> Type:
  &r: List<&1, C.Named> -> &mc: Maybe<&1, C.Column> -> {C.Cols.take(cols, nm) == (r, mc) : List<&1, C.Named> & Maybe<&1, C.Column>} & {C.Cols.take(cml(cols, m, kept), nm) == (cml(r, m, kept), mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>} & CMW(cols, m, kept) & CMW(r, m, kept)

def tkc.t(+nm: String, +nn: String, -c: C.Column, ca: C.Column, +eca: {ca == c : C.Column}, -rest: List<&1, C.Named>, r: List<&1, C.Named>, mc: Maybe<&1, C.Column>, b: Bool, +eb: {String.eq(nm, nn) == b : Bool}, -m: Array<U32>, +kept: U32,
  t1: {C.Cols.take(rest, nm) == (r, mc) : List<&1, C.Named> & Maybe<&1, C.Column>}, t2: {C.Cols.take(cml(rest, m, kept), nm) == (cml(r, m, kept), mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}, +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}, +w1: {cm(rest, m, kept) == (cml(rest, m, kept), m) : List<&1, C.Named> & Array<U32>}, +w2: {cm(r, m, kept) == (cml(r, m, kept), m) : List<&1, C.Named> & Array<U32>})
  -> TK(C.Named{nn, c} <> rest, m, nm, kept):
  match b:
    case True{}:
      (r, Some{ca}, (%Equal.sym(Bool, String.eq(nm, nn), True{}, eb) : {C.Cols.take.k(_, nn, c, C.Cols.take(rest, nm)) == (r, Some{ca}) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.take(rest, nm), (r, mc), t1) : {C.Cols.take.k(True{}, nn, c, _) == (r, Some{ca}) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(C.Column, ca, c, eca) : {(r, Some{c}) == (r, Some{_}) : List<&1, C.Named> & Maybe<&1, C.Column>}; {==}), (%Equal.sym(List<&1, C.Named>, cml(C.Named{nn, c} <> rest, m, kept), C.Named{nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(rest, m, kept), cmu(nn, c, rest, m, kept, ec, w1)) : {C.Cols.take(_, nm) == (cml(r, m, kept), mmc(Some{ca}, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(Bool, String.eq(nm, nn), True{}, eb) : {C.Cols.take.k(_, nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), C.Cols.take(cml(rest, m, kept), nm)) == (cml(r, m, kept), mmc(Some{ca}, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.take(cml(rest, m, kept), nm), (cml(r, m, kept), mmc(mc, m, kept)), t2) : {C.Cols.take.k(True{}, nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), _) == (cml(r, m, kept), mmc(Some{ca}, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(C.Column, ca, c, eca) : {C.Cols.take.k(True{}, nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), (cml(r, m, kept), mmc(mc, m, kept))) == (cml(r, m, kept), mmc(Some{_}, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; {==}), cmw_cons(nn, c, rest, m, kept, ec, w1), w2)
    case False{}:
      (C.Named{nn, ca} <> r, mc, (%Equal.sym(Bool, String.eq(nm, nn), False{}, eb) : {C.Cols.take.k(_, nn, c, C.Cols.take(rest, nm)) == (C.Named{nn, ca} <> r, mc) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.take(rest, nm), (r, mc), t1) : {C.Cols.take.k(False{}, nn, c, _) == (C.Named{nn, ca} <> r, mc) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(C.Column, ca, c, eca) : {(C.Named{nn, c} <> r, mc) == (C.Named{nn, _} <> r, mc) : List<&1, C.Named> & Maybe<&1, C.Column>}; {==}), (%Equal.sym(List<&1, C.Named>, cml(C.Named{nn, c} <> rest, m, kept), C.Named{nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(rest, m, kept), cmu(nn, c, rest, m, kept, ec, w1)) : {C.Cols.take(_, nm) == (cml(C.Named{nn, ca} <> r, m, kept), mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(Bool, String.eq(nm, nn), False{}, eb) : {C.Cols.take.k(_, nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), C.Cols.take(cml(rest, m, kept), nm)) == (cml(C.Named{nn, ca} <> r, m, kept), mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.take(cml(rest, m, kept), nm), (cml(r, m, kept), mmc(mc, m, kept)), t2) : {C.Cols.take.k(False{}, nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), _) == (cml(C.Named{nn, ca} <> r, m, kept), mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; %Equal.sym(C.Column, ca, c, eca) : {C.Cols.take.k(False{}, nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), (cml(r, m, kept), mmc(mc, m, kept))) == (cml(C.Named{nn, _} <> r, m, kept), mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; (%Equal.sym(List<&1, C.Named>, cml(C.Named{nn, c} <> r, m, kept), C.Named{nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(r, m, kept), cmu(nn, c, r, m, kept, ec, w2)) : {(C.Named{nn, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(r, m, kept), mmc(mc, m, kept)) == (_, mmc(mc, m, kept)) : List<&1, C.Named> & Maybe<&1, C.Column>}; {==})), cmw_cons(nn, c, rest, m, kept, ec, w1), (%Equal.sym(C.Column, ca, c, eca) : CMW(C.Named{nn, _} <> r, m, kept); cmw_cons(nn, c, r, m, kept, ec, w2)))

def tkc.j(+nm: String, +nn: String, -c: C.Column, ca: C.Column, +eca: {ca == c : C.Column}, -rest: List<&1, C.Named>, -m: Array<U32>, +kept: U32, +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}, ih: TK(rest, m, nm, kept)) -> TK(C.Named{nn, c} <> rest, m, nm, kept):
  (r, mc, t1, t2, w1, w2) = ih
  tkc.t(nm, nn, c, ca, eca, rest, r, mc, String.eq(nm, nn), {==}, m, kept, t1, t2, ec, w1, w2)

def tkc.c(+nm: String, +nn: String, -c: C.Column, -rest: List<&1, C.Named>, -m: Array<U32>, +kept: U32, wc: PV.CloneW(c), w: CE(U32, m), ih: @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> TK(rest, m, nm, kept)) -> TK(C.Named{nn, c} <> rest, m, nm, kept):
  (ca, cb, ecl, eca, ecb) = wc
  (m1, m2, e1, e2) = w
  tkc.j(nm, nn, c, ca, eca, rest, m, kept, colw(c, m, kept, cb, m1, ecb, e1), ih(m2, e2))

# Cols.take over the compacted columns: the same split, the found column compacted (live witnesses)
def tkc(cols: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +nm: String, +kept: U32) -> TK(cols, m, nm, kept):
  match cols:
    case Nil{}:
      (Nil{}, None{}, {==}, {==}, {==}, {==})
    case C.Named{+nn, c} <> rest:
      tkc.c(nm, nn, c, rest, m, kept, PV.clone_w(c), (%em : CE(U32, _); PC.clone_eq(U32, mm)), m2 => e2 => tkc(rest, m, m2, e2, nm, kept))


# ---- the select loop over the filtered frame against the one over the unfiltered frame -------------

# a failed select loop stays failed
def sgf(ns: List<&2, String>, -e: E.Err) -> {C.Frame.select.go(ns, Fail{e}) == Fail{e} : E.ResT(C.Frame & List<&1, C.Named>)}:
  match ns:
    case Nil{}:
      {==}
    case n <> t:
      sgf(t, e)

def SELT(-ns: List<&2, String>, +h: U32, -cols: List<&1, C.Named>, -acc: List<&1, C.Named>, -m: Array<U32>, +kept: U32) -> Type:
  {C.Frame.select.fin(C.Frame.select.go(ns, Done{(C.Frame{kept, cml(cols, m, kept)}, cml(acc, m, kept))})) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(ns, Done{(C.Frame{h, cols}, acc)})), m, kept) : E.ResT(C.Frame)}

def sel.nil.b(+h: U32, -acc: List<&1, C.Named>, -m: Array<U32>, +kept: U32, q: {List.reverse.go(&1, C.Named, cml(acc, m, kept), Nil{}) == cml(List.reverse.go(&1, C.Named, acc, Nil{}), m, kept) : List<&1, C.Named>}, f: FM(h, List.reverse.go(&1, C.Named, acc, Nil{}), m, kept))
  -> {Done{C.Frame{kept, List.reverse.go(&1, C.Named, cml(acc, m, kept), Nil{})}} == Done{C.Frame.filter_mask(C.Frame{h, List.reverse.go(&1, C.Named, acc, Nil{})}, m, kept)} : E.ResT(C.Frame)}:
  %Equal.sym(C.Frame, C.Frame.filter_mask(C.Frame{h, List.reverse.go(&1, C.Named, acc, Nil{})}, m, kept), C.Frame{kept, cml(List.reverse.go(&1, C.Named, acc, Nil{}), m, kept)}, f) : {Done{C.Frame{kept, List.reverse.go(&1, C.Named, cml(acc, m, kept), Nil{})}} == Done{_} : E.ResT(C.Frame)}
  %q : {Done{C.Frame{kept, List.reverse.go(&1, C.Named, cml(acc, m, kept), Nil{})}} == Done{C.Frame{kept, _}} : E.ResT(C.Frame)}
  {==}

def sel.nil(+h: U32, -cols: List<&1, C.Named>, -acc: List<&1, C.Named>, -m: Array<U32>, +kept: U32, w: LD(acc), wm: CE(U32, m)) -> SELT(Nil{}, h, cols, acc, m, kept):
  (a1, a2, ea1, ea2) = w
  (m1, m2, em1, em2) = wm
  sel.nil.b(h, acc, m, kept, Pair.fst({List.reverse.go(&1, C.Named, cml(acc, m, kept), Nil{}) == cml(List.reverse.go(&1, C.Named, acc, Nil{}), m, kept) : List<&1, C.Named>}, CMW(acc, m, kept), rcmw(acc, a1, ea1, m, m1, em1, kept)), (%Equal.cong(List<&1, C.Named>, List<&1, C.Named>, x => List.reverse.go(&1, C.Named, x, Nil{}), a2, acc, ea2) : FM(h, _, m, kept); fm(h, List.reverse.go(&1, C.Named, a2, Nil{}), m, m2, em2, kept)))

def sel.some.k(+nm: String, +t: List<&2, String>, +h: U32, -cols: List<&1, C.Named>, r: List<&1, C.Named>, -c: C.Column, ca: C.Column, -acc: List<&1, C.Named>, a: List<&1, C.Named>, +ea: {a == acc : List<&1, C.Named>}, -m: Array<U32>, m1: Array<U32>, em1: {m1 == m : Array<U32>}, +kept: U32, +ec: {C.Column.compact(c, m, kept) == (Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept)), m) : C.Column & Array<U32>}, +ha: {cm(acc, m, kept) == (cml(acc, m, kept), m) : List<&1, C.Named> & Array<U32>}, +eca: {ca == c : C.Column}, ih: @r2: List<&1, C.Named> -> @a2: List<&1, C.Named> -> @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> @ha2: {cm(a2, m, kept) == (cml(a2, m, kept), m) : List<&1, C.Named> & Array<U32>} -> SELT(t, h, r2, a2, m, kept))
  -> {C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{kept, cml(r, m, kept)}, C.Named{nm, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(acc, m, kept))})) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{h, r}, C.Named{nm, c} <> acc)})), m, kept) : E.ResT(C.Frame)}:
  %cmu(nm, c, acc, m, kept, ec, ha) : {C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{kept, cml(r, m, kept)}, _)})) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{h, r}, C.Named{nm, c} <> acc)})), m, kept) : E.ResT(C.Frame)}
  %ea : {C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{kept, cml(r, m, kept)}, cml(C.Named{nm, c} <> _, m, kept))})) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{h, r}, C.Named{nm, c} <> _)})), m, kept) : E.ResT(C.Frame)}
  %eca : {C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{kept, cml(r, m, kept)}, cml(C.Named{nm, _} <> a, m, kept))})) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{h, r}, C.Named{nm, _} <> a)})), m, kept) : E.ResT(C.Frame)}
  ih(r, C.Named{nm, ca} <> a, m1, em1, (%Equal.sym(C.Column, ca, c, eca) : {cm(C.Named{nm, _} <> a, m, kept) == (cml(C.Named{nm, _} <> a, m, kept), m) : List<&1, C.Named> & Array<U32>}; %Equal.sym(List<&1, C.Named>, a, acc, ea) : {cm(C.Named{nm, c} <> _, m, kept) == (cml(C.Named{nm, c} <> _, m, kept), m) : List<&1, C.Named> & Array<U32>}; cmw_cons(nm, c, acc, m, kept, ec, ha)))

def sel.some(+nm: String, +t: List<&2, String>, +h: U32, -cols: List<&1, C.Named>, r: List<&1, C.Named>, -c: C.Column, acc: List<&1, C.Named>, -m: Array<U32>, +kept: U32, +ha: {cm(acc, m, kept) == (cml(acc, m, kept), m) : List<&1, C.Named> & Array<U32>}, wc: PV.CloneW(c), wm: CE(U32, m), ih: @r2: List<&1, C.Named> -> @a2: List<&1, C.Named> -> @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> @ha2: {cm(a2, m, kept) == (cml(a2, m, kept), m) : List<&1, C.Named> & Array<U32>} -> SELT(t, h, r2, a2, m, kept))
  -> {C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{kept, cml(r, m, kept)}, C.Named{nm, Pair.fst(C.Column, Array<U32>, C.Column.compact(c, m, kept))} <> cml(acc, m, kept))})) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, Done{(C.Frame{h, r}, C.Named{nm, c} <> acc)})), m, kept) : E.ResT(C.Frame)}:
  (ca, cb, ecl, eca, ecb) = wc
  (m1, m2, em1, em2) = wm
  sel.some.k(nm, t, h, cols, r, c, ca, acc, acc, {==}, m, m1, em1, kept, colw(c, m, kept, cb, m2, ecb, em2), ha, eca, ih)

def sel.mc(+nm: String, +t: List<&2, String>, +h: U32, -cols: List<&1, C.Named>, r: List<&1, C.Named>, mc: Maybe<&1, C.Column>, acc: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32, +ha: {cm(acc, m, kept) == (cml(acc, m, kept), m) : List<&1, C.Named> & Array<U32>}, ih: @r2: List<&1, C.Named> -> @a2: List<&1, C.Named> -> @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> @ha2: {cm(a2, m, kept) == (cml(a2, m, kept), m) : List<&1, C.Named> & Array<U32>} -> SELT(t, h, r2, a2, m, kept))
  -> {C.Frame.select.fin(C.Frame.select.go(t, C.Frame.select.add(nm, cml(acc, m, kept), (C.Frame{kept, cml(r, m, kept)}, mmc(mc, m, kept))))) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, C.Frame.select.add(nm, acc, (C.Frame{h, r}, mc)))), m, kept) : E.ResT(C.Frame)}:
  match mc:
    case None{}:
      (%Equal.sym(E.ResT(C.Frame & List<&1, C.Named>), C.Frame.select.go(t, Fail{E.ColumnNotFound{nm}}), Fail{E.ColumnNotFound{nm}}, sgf(t, E.ColumnNotFound{nm})) : {C.Frame.select.fin(_) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, Fail{E.ColumnNotFound{nm}})), m, kept) : E.ResT(C.Frame)}; %Equal.sym(E.ResT(C.Frame & List<&1, C.Named>), C.Frame.select.go(t, Fail{E.ColumnNotFound{nm}}), Fail{E.ColumnNotFound{nm}}, sgf(t, E.ColumnNotFound{nm})) : {C.Frame.select.fin(Fail{E.ColumnNotFound{nm}}) == Laws.fmres(C.Frame.select.fin(_), m, kept) : E.ResT(C.Frame)}; {==})
    case Some{c}:
      sel.some(nm, t, h, cols, r, c, acc, m, kept, ha, PV.clone_w(c), (%em : CE(U32, _); PC.clone_eq(U32, mm)), ih)

def sel.tk(+nm: String, +t: List<&2, String>, +h: U32, -cols: List<&1, C.Named>, acc: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32, +ha: {cm(acc, m, kept) == (cml(acc, m, kept), m) : List<&1, C.Named> & Array<U32>}, w: TK(cols, m, nm, kept), ih: @r2: List<&1, C.Named> -> @a2: List<&1, C.Named> -> @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> @ha2: {cm(a2, m, kept) == (cml(a2, m, kept), m) : List<&1, C.Named> & Array<U32>} -> SELT(t, h, r2, a2, m, kept))
  -> SELT(nm <> t, h, cols, acc, m, kept):
  (r, mc, t1, t2, w1, w2) = w
  %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.take(cml(cols, m, kept), nm), (cml(r, m, kept), mmc(mc, m, kept)), t2) : {C.Frame.select.fin(C.Frame.select.go(t, C.Frame.select.add(nm, cml(acc, m, kept), C.Frame.take.k(kept, _)))) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(nm <> t, Done{(C.Frame{h, cols}, acc)})), m, kept) : E.ResT(C.Frame)}
  %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.take(cols, nm), (r, mc), t1) : {C.Frame.select.fin(C.Frame.select.go(t, C.Frame.select.add(nm, cml(acc, m, kept), (C.Frame{kept, cml(r, m, kept)}, mmc(mc, m, kept))))) == Laws.fmres(C.Frame.select.fin(C.Frame.select.go(t, C.Frame.select.add(nm, acc, C.Frame.take.k(h, _)))), m, kept) : E.ResT(C.Frame)}
  sel.mc(nm, t, h, cols, r, mc, acc, m, mm, em, kept, ha, ih)

def sel.c(+nm: String, +t: List<&2, String>, +h: U32, cols: List<&1, C.Named>, acc: List<&1, C.Named>, -m: Array<U32>, +kept: U32, +ha: {cm(acc, m, kept) == (cml(acc, m, kept), m) : List<&1, C.Named> & Array<U32>}, wm: CE(U32, m), ih: @r2: List<&1, C.Named> -> @a2: List<&1, C.Named> -> @mm: Array<U32> -> @em: {mm == m : Array<U32>} -> @ha2: {cm(a2, m, kept) == (cml(a2, m, kept), m) : List<&1, C.Named> & Array<U32>} -> SELT(t, h, r2, a2, m, kept))
  -> SELT(nm <> t, h, cols, acc, m, kept):
  (m1, m2, em1, em2) = wm
  sel.tk(nm, t, h, cols, acc, m, m2, em2, kept, ha, tkc(cols, m, m1, em1, nm, kept), ih)

# the select loop over Frame{kept, cm(cols)} with cm(acc) IS fmres of the loop over Frame{h, cols} with acc
def sel(ns: List<&2, String>, +h: U32, cols: List<&1, C.Named>, acc: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32, +ha: {cm(acc, m, kept) == (cml(acc, m, kept), m) : List<&1, C.Named> & Array<U32>}) -> SELT(ns, h, cols, acc, m, kept):
  match ns:
    case Nil{}:
      sel.nil(h, cols, acc, m, kept, ldup(acc), (%em : CE(U32, _); PC.clone_eq(U32, mm)))
    case +nm <> +t:
      sel.c(nm, t, h, cols, acc, m, kept, ha, (%em : CE(U32, _); PC.clone_eq(U32, mm)), r2 => a2 => m2 => e2 => h2 => sel(t, h, r2, a2, m, m2, e2, kept, h2))

def sfm.d(+ns: List<&2, String>, d: Maybe<&2, String>, +ed: {C.Names.dup(ns, Nil{}, None{}) == d : Maybe<&2, String>}, +h: U32, cols: List<&1, C.Named>, -m: Array<U32>, mm: Array<U32>, em: {mm == m : Array<U32>}, +kept: U32)
  -> {C.Frame.select_names(C.Frame{kept, cml(cols, m, kept)}, ns) == Laws.fmres(C.Frame.select_names(C.Frame{h, cols}, ns), m, kept) : E.ResT(C.Frame)}:
  match d:
    case Some{n}:
      (%Equal.sym(Maybe<&2, String>, C.Names.dup(ns, Nil{}, None{}), Some{n}, ed) : {C.Frame.select_names.a(_, C.Frame{kept, cml(cols, m, kept)}, ns) == Laws.fmres(C.Frame.select_names.a(_, C.Frame{h, cols}, ns), m, kept) : E.ResT(C.Frame)}; {==})
    case None{}:
      (%Equal.sym(Maybe<&2, String>, C.Names.dup(ns, Nil{}, None{}), None{}, ed) : {C.Frame.select_names.a(_, C.Frame{kept, cml(cols, m, kept)}, ns) == Laws.fmres(C.Frame.select_names.a(_, C.Frame{h, cols}, ns), m, kept) : E.ResT(C.Frame)}; sel(ns, h, cols, Nil{}, m, mm, em, kept, {==}))

def sfm.k(+h: U32, -cols: List<&1, C.Named>, -m: Array<U32>, +kept: U32, +ns: List<&2, String>, w: LD(cols), wm: CE(U32, m))
  -> {C.Frame.select_names(C.Frame.filter_mask(C.Frame{h, cols}, m, kept), ns) == Laws.fmres(C.Frame.select_names(C.Frame{h, cols}, ns), m, kept) : E.ResT(C.Frame)}:
  (c1, c2, ec1, ec2) = w
  (m1, m2, em1, em2) = wm
  %Equal.sym(C.Frame, C.Frame.filter_mask(C.Frame{h, cols}, m, kept), C.Frame{kept, cml(cols, m, kept)}, (%ec1 : FM(h, _, m, kept); fm(h, c1, m, m1, em1, kept))) : {C.Frame.select_names(_, ns) == Laws.fmres(C.Frame.select_names(C.Frame{h, cols}, ns), m, kept) : E.ResT(C.Frame)}
  %ec2 : {C.Frame.select_names(C.Frame{kept, cml(_, m, kept)}, ns) == Laws.fmres(C.Frame.select_names(C.Frame{h, _}, ns), m, kept) : E.ResT(C.Frame)}
  sfm.d(ns, C.Names.dup(ns, Nil{}, None{}), {==}, h, c2, m, m2, em2, kept)

def Laws.select_filter_mask(f, m, kept, ns):
  match f:
    case C.Frame{+h, cols}:
      sfm.k(h, cols, m, kept, ns, ldup(cols), PC.clone_eq(U32, m))


# ---- the step: Exec.fs.r .. q against Eval.filter.r .. q over one mask result ---------------------------

def FD(-f: C.Frame) -> Type:
  &a: C.Frame -> &b: C.Frame -> {a == f : C.Frame} & {b == f : C.Frame}

def fdup.k(+h: U32, -cols: List<&1, C.Named>, w: LD(cols)) -> FD(C.Frame{h, cols}):
  (c1, c2, e1, e2) = w
  (C.Frame{h, c1}, C.Frame{h, c2}, (%e1 : {C.Frame{h, c1} == C.Frame{h, _} : C.Frame}; {==}), (%e2 : {C.Frame{h, c2} == C.Frame{h, _} : C.Frame}; {==}))

def fdup(f: C.Frame) -> FD(f):
  match f:
    case C.Frame{+h, cols}:
      fdup.k(h, cols, ldup(cols))

# Exec.fs.cmp IS fmres with Exec.fc (law fc_filter_mask)
def pcmp(r: E.ResT(C.Frame), m: Array<U32>, +kept: U32) -> {Q.Exec.fs.cmp(r, m, kept) == Laws.fmres(r, m, kept) : E.ResT(C.Frame)}:
  match r:
    case Fail{e}:
      {==}
    case Done{g}:
      Equal.cong(C.Frame, E.ResT(C.Frame), x => Done{x}, Q.Exec.fc(g, m, kept), C.Frame.filter_mask(g, m, kept), Laws.fc_filter_mask(g, m, kept))

def pq.k(-f: C.Frame, -m: Array<U32>, +kept: U32, +ns: List<&2, String>, w: FD(f), wm: CE(U32, m))
  -> {Q.Exec.fs.cmp(C.Frame.select_names(f, ns), m, kept) == C.Frame.select_names(C.Frame.filter_mask(f, m, kept), ns) : E.ResT(C.Frame)}:
  (f1, f2, ef1, ef2) = w
  (m1, m2, em1, em2) = wm
  Equal.trans(E.ResT(C.Frame), Q.Exec.fs.cmp(C.Frame.select_names(f, ns), m, kept), Laws.fmres(C.Frame.select_names(f, ns), m, kept), C.Frame.select_names(C.Frame.filter_mask(f, m, kept), ns), (%ef1 : {Q.Exec.fs.cmp(C.Frame.select_names(_, ns), m, kept) == Laws.fmres(C.Frame.select_names(_, ns), m, kept) : E.ResT(C.Frame)}; %em1 : {Q.Exec.fs.cmp(C.Frame.select_names(f1, ns), _, kept) == Laws.fmres(C.Frame.select_names(f1, ns), _, kept) : E.ResT(C.Frame)}; pcmp(C.Frame.select_names(f1, ns), m1, kept)), Equal.sym(E.ResT(C.Frame), C.Frame.select_names(C.Frame.filter_mask(f, m, kept), ns), Laws.fmres(C.Frame.select_names(f, ns), m, kept), (%ef2 : {C.Frame.select_names(C.Frame.filter_mask(_, m, kept), ns) == Laws.fmres(C.Frame.select_names(_, ns), m, kept) : E.ResT(C.Frame)}; %em2 : {C.Frame.select_names(C.Frame.filter_mask(f2, _, kept), ns) == Laws.fmres(C.Frame.select_names(f2, ns), _, kept) : E.ResT(C.Frame)}; Laws.select_filter_mask(f2, m2, kept, ns))))

def pq(f: C.Frame, +es: List<&2, X.Expr>, r: Array<U32> & U32, +hp: {Q.Exec.plain(es) == True{} : Bool}) -> {Q.Exec.fs.q(f, es, r) == Laws.fsres(V.Eval.filter.q(f, r), es) : E.ResT(C.Frame)}:
  match r:
    case (m, +kept):
      (%Equal.sym(Bool, Q.Exec.plain(es), True{}, hp) : {Q.Exec.fs.cmp(C.Frame.select_names(f, V.Eval.names(es)), m, kept) == Q.Exec.select.k(_, C.Frame.filter_mask(f, m, kept), es) : E.ResT(C.Frame)}; pq.k(f, m, kept, V.Eval.names(es), fdup(f), PC.clone_eq(U32, m)))

# Exec.fs.k / Exec.fs.r against Eval.filter.k / Eval.filter.r: one split on the mask result, then pq
def pk(+es: List<&2, X.Expr>, x: C.Frame & (Array<U32> & U32), +hp: {Q.Exec.plain(es) == True{} : Bool}) -> {Q.Exec.fs.k(es, x) == Laws.fsres(V.Eval.filter.k(x), es) : E.ResT(C.Frame)}:
  match x:
    case (f, r):
      pq(f, es, r, hp)

def pr(+es: List<&2, X.Expr>, r: E.ResT(C.Frame & (Array<U32> & U32)), +hp: {Q.Exec.plain(es) == True{} : Bool}) -> {Q.Exec.fs.r(es, r) == Laws.fsres(V.Eval.filter.r(r), es) : E.ResT(C.Frame)}:
  match r:
    case Fail{e}:
      {==}
    case Done{x}:
      pk(es, x, hp)

# Exec.fs and Eval.filter share the mask computation (V.Eval.filter.mask, the F5 passes or the
# general predicate): the law holds for EVERY mask result, so it needs nothing about the predicate
def Laws.filter_select_step(f, pred, es, hp):
  pr(es, V.Eval.filter.mask(f, pred), hp)

# ---- the runner ---------------------------------------------------------------------------------------

def loop_app(w: List<&2, Q.Instr>, +b: List<&2, Q.Instr>, -st: Q.St) -> {Q.Exec.loop(List.append(&2, Q.Instr, w, b), st) == Q.Exec.loop(b, Q.Exec.loop(w, st)) : Q.St}:
  match w:
    case Nil{}:
      {==}
    case i <> t:
      loop_app(t, b, Q.Exec.step(i, st))

def mark_nil(+a: List<&2, Q.Instr>) -> {Q.Exec.mark(a) == Laws.markw(a, Nil{}) : List<&2, Q.Instr>}:
  %PE.app_nil(a) : {Q.Exec.mark(_) == Laws.markw(a, Nil{}) : List<&2, Q.Instr>}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, a, Nil{})), List.append(&2, Q.Instr, Laws.markw(a, Nil{}), Q.Exec.mark(Nil{})), PE.mark_app(a, Nil{})) : {_ == Laws.markw(a, Nil{}) : List<&2, Q.Instr>}
  PE.app_nil(Laws.markw(a, Nil{}))

# the ISelect step after any filter result
def fs_tail(-env: P.Env, -t: List<&1, C.Frame>, +es: List<&2, X.Expr>, rr: E.ResT(C.Frame)) -> {Q.Exec.fin(Q.St{env, Q.Exec.push(Laws.fsres(rr, es), t)}) == Q.Exec.fin(Q.Exec.step.r(Q.ISelect{es}, env, Q.Exec.push(rr, t))) : E.ResT(C.Frame)}:
  match rr:
    case Fail{e}:
      {==}
    case Done{g}:
      {==}

def fs_f(-env: P.Env, -t: List<&1, C.Frame>, -f: C.Frame, +pred: X.Expr, +es: List<&2, X.Expr>, +hp: {Q.Exec.plain(es) == True{} : Bool}, w: FD(f))
  -> {Q.Exec.fin(Q.St{env, Q.Exec.push(Q.Exec.fs(f, pred, es), t)}) == Q.Exec.fin(Q.Exec.step.r(Q.ISelect{es}, env, Q.Exec.push(V.Eval.filter(f, pred), t))) : E.ResT(C.Frame)}:
  (f1, f2, ef1, ef2) = w
  %Equal.sym(E.ResT(C.Frame), Q.Exec.fs(f, pred, es), Laws.fsres(V.Eval.filter(f, pred), es), (%ef1 : {Q.Exec.fs(_, pred, es) == Laws.fsres(V.Eval.filter(_, pred), es) : E.ResT(C.Frame)}; Laws.filter_select_step(f1, pred, es, hp))) : {Q.Exec.fin(Q.St{env, Q.Exec.push(_, t)}) == Q.Exec.fin(Q.Exec.step.r(Q.ISelect{es}, env, Q.Exec.push(V.Eval.filter(f, pred), t))) : E.ResT(C.Frame)}
  %ef2 : {Q.Exec.fin(Q.St{env, Q.Exec.push(Laws.fsres(V.Eval.filter(_, pred), es), t)}) == Q.Exec.fin(Q.Exec.step.r(Q.ISelect{es}, env, Q.Exec.push(V.Eval.filter(_, pred), t))) : E.ResT(C.Frame)}
  fs_tail(env, t, es, V.Eval.filter(f2, pred))

def fs_s(+pred: X.Expr, +es: List<&2, X.Expr>, +hp: {Q.Exec.plain(es) == True{} : Bool}, -env: P.Env, stack: List<&1, C.Frame>)
  -> {Q.Exec.fin(Q.St{env, Q.Exec.fsel.s(pred, es, stack)}) == Q.Exec.fin(Q.Exec.step(Q.ISelect{es}, Q.St{env, Q.Exec.unary.pop(Q.IFilter{pred}, stack)})) : E.ResT(C.Frame)}:
  match stack:
    case Nil{}:
      {==}
    case f <> t:
      fs_f(env, t, f, pred, es, hp, fdup(f))

def fs_r(+pred: X.Expr, +es: List<&2, X.Expr>, +hp: {Q.Exec.plain(es) == True{} : Bool}, -env: P.Env, r: E.ResT(List<&1, C.Frame>))
  -> {Q.Exec.fin(Q.Exec.fsel.r(pred, es, env, r)) == Q.Exec.fin(Q.Exec.step(Q.ISelect{es}, Q.Exec.step.r(Q.IFilter{pred}, env, r))) : E.ResT(C.Frame)}:
  match r:
    case Fail{e}:
      {==}
    case Done{stack}:
      fs_s(pred, es, hp, env, stack)

# Exec.fsel against IFilter then ISelect, from any runner state
def fs_k(+pred: X.Expr, +es: List<&2, X.Expr>, +hp: {Q.Exec.plain(es) == True{} : Bool}, st: Q.St) -> {Q.Exec.fin(Q.Exec.fsel(pred, es, st)) == Q.Exec.fin(Q.Exec.step(Q.ISelect{es}, Q.Exec.step(Q.IFilter{pred}, st))) : E.ResT(C.Frame)}:
  match st:
    case Q.St{env, r}:
      fs_r(pred, es, hp, env, r)

def fsr.t(+es: List<&2, X.Expr>, +pred: X.Expr, +x: P.Plan, env: P.Env, +hp: {Q.Exec.plain(es) == True{} : Bool})
  -> {Q.Exec.fin(Q.Exec.fsel(pred, es, Q.Exec.loop(Q.Exec.mark(Q.Exec.compile(x, Nil{})), Q.St{env, Done{Nil{}}}))) == Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(Q.Exec.compile(x, Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})), Q.St{env, Done{Nil{}}})) : E.ResT(C.Frame)}:
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(Q.Exec.compile(x, Nil{})), Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), mark_nil(Q.Exec.compile(x, Nil{}))) : {Q.Exec.fin(Q.Exec.fsel(pred, es, Q.Exec.loop(_, Q.St{env, Done{Nil{}}}))) == Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(Q.Exec.compile(x, Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})), Q.St{env, Done{Nil{}}})) : E.ResT(C.Frame)}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IFilter{pred} <> Q.ISelect{es} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{pred} <> Q.ISelect{es} <> Nil{}), PE.compile_app(x, Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})) : {Q.Exec.fin(Q.Exec.fsel(pred, es, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))) == Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(_), Q.St{env, Done{Nil{}}})) : E.ResT(C.Frame)}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})), List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), Q.IFilter{pred} <> Q.ISelect{es} <> Nil{}), Q.Exec.mark(Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})), PE.mark_app(Q.Exec.compile(x, Nil{}), Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})) : {Q.Exec.fin(Q.Exec.fsel(pred, es, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))) == Q.Exec.fin(Q.Exec.loop(_, Q.St{env, Done{Nil{}}})) : E.ResT(C.Frame)}
  %PE.markw_ext(Q.Exec.compile(x, Nil{}), Nil{}, Q.IFilter{pred} <> Q.ISelect{es} <> Nil{}, {==}) : {Q.Exec.fin(Q.Exec.fsel(pred, es, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))) == Q.Exec.fin(Q.Exec.loop(List.append(&2, Q.Instr, _, Q.Exec.mark(Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})), Q.St{env, Done{Nil{}}})) : E.ResT(C.Frame)}
  %Equal.sym(Q.St, Q.Exec.loop(List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.Exec.mark(Q.IFilter{pred} <> Q.ISelect{es} <> Nil{})), Q.St{env, Done{Nil{}}}), Q.Exec.loop(Q.Exec.mark(Q.IFilter{pred} <> Q.ISelect{es} <> Nil{}), Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}})), loop_app(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.Exec.mark(Q.IFilter{pred} <> Q.ISelect{es} <> Nil{}), Q.St{env, Done{Nil{}}})) : {Q.Exec.fin(Q.Exec.fsel(pred, es, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))) == Q.Exec.fin(_) : E.ResT(C.Frame)}
  fs_k(pred, es, hp, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))

def fsr.p(+es: List<&2, X.Expr>, +pred: X.Expr, +x: P.Plan, env: P.Env, b: Bool, +eb: {Q.Exec.plain(es) == b : Bool})
  -> {Q.Exec.run_phys(P.Select{es, P.Filter{pred, x}}, env) == Q.Exec.run_pure(P.Select{es, P.Filter{pred, x}}, env) : E.ResT(C.Frame)}:
  match b:
    case True{}:
      (%Equal.sym(Bool, Q.Exec.plain(es), True{}, eb) : {Q.Exec.run_phys.f(_, es, pred, x, env) == Q.Exec.run_pure(P.Select{es, P.Filter{pred, x}}, env) : E.ResT(C.Frame)}; fsr.t(es, pred, x, env, eb))
    case False{}:
      (%Equal.sym(Bool, Q.Exec.plain(es), False{}, eb) : {Q.Exec.run_phys.f(_, es, pred, x, env) == Q.Exec.run_pure(P.Select{es, P.Filter{pred, x}}, env) : E.ResT(C.Frame)}; {==})

def Laws.filter_select_run_eq(es, pred, x, env):
  fsr.p(es, pred, x, env, Q.Exec.plain(es), {==})

def Laws.filter_select_run(es, pred, x, env, k):
  Equal.cong(E.ResT(C.Frame), Laws.RObs, r => Laws.robs(r, k), Q.Exec.run_phys(P.Select{es, P.Filter{pred, x}}, env), Q.Exec.run_pure(P.Select{es, P.Filter{pred, x}}, env), Laws.filter_select_run_eq(es, pred, x, env))
