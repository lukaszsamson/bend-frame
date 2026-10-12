# PROOF_peep.bend -- proofs of LAWS.bend section 19 (v0.2 T4.2, DESIGN.md 16.3 F1-F5): the fused
# evaluator's column-level operations equal the unfused operations they replace, and the peephole
# pass fires on its windows.
#
# Shape of every proof: the production operation, applied to columns of known constructors, unfolds
# by computation down to the kernel call; the only stuck terms are the length test U32.is_eq(n, n)
# (rewritten with PV.u32_eq_refl) and the kernel loops, which PROOF_fused's template lemmas turn
# into the unfused kernels (zb_sim / mpb_sim: the same loop, the operands handed back) or into cells
# (mpb_cell, zb_cell, zv_unfused, pco_cell). The rewrites name the intermediate term the goal reduces
# to (`%e : P` with P the goal at that point), so each proof is a few lines of rewriting followed by
# reflexivity or a cell lemma.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/expr.bend as X
import ./src/eval.bend as V
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B
import ./PROOF_contents.bend as PC
import ./PROOF_eval.bend as PV
import ./PROOF_inplace.bend as PI
import ./PROOF_fused.bend as PF

# ---- F2 dense: the fused zip IS Eval.bin's zip ------------------------------------------------------

def Laws.peep_f2_dense(n, d, d2, a, b):
  %Equal.sym(Bool, U32.is_eq(n, n), True{}, PV.u32_eq_refl(n)) : {V.Eval.fz.z2.a(X.Add{}, V.PNone{}, V.PNone{}, _, (C.CU32{n, d, C.AllValid{}, a}, D.TU32{}), (C.CU32{n, d2, C.AllValid{}, b}, D.TU32{})) == V.Z2R{Some{C.CU32{n, d, C.AllValid{}, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0)}}, C.CU32{n, d, C.AllValid{}, a}, C.CU32{n, d2, C.AllValid{}, b}} : V.Z2R}
  %Equal.sym(K.ZB<U32, U32, U32>, K.Kernel.zipb(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0), K.ZB{K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0), a, b}, PF.zb_sim(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), U32.to_nat(n), 0, Array.new(U32, d, 0), a, b)) : {V.Eval.fz.z2.e(False{}, False{}, C.AllValid{}, C.AllValid{}, V.Eval.fz.zr.ww(D.TU32{}, D.TU32{}, n, d, n, d2, V.Eval.fz.zw.b(~U32, ~U32, D.TU32{}, n, d, _))) == V.Z2R{Some{C.CU32{n, d, C.AllValid{}, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0)}}, C.CU32{n, d, C.AllValid{}, a}, C.CU32{n, d2, C.AllValid{}, b}} : V.Z2R}
  {==}

# ---- F1: the literal as map_pb's scalar against Eval.bin over the broadcast column -----------------

def Laws.peep_f1_back(n, d, a, lit):
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.map_pb(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), (K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), a), PF.mpb_sim(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), U32.to_nat(n), 0, lit, Array.new(U32, d, 0), a)) : {V.Eval.fz.z1.e(False{}, C.AllValid{}, V.Eval.fz.l.w(D.TU32{}, n, d, V.Eval.fz.lw.m(~U32, D.TBool{}, n, d, _))) == V.Z1R{Some{C.CBool{n, d, C.AllValid{}, K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0)}}, C.CU32{n, d, C.AllValid{}, a}} : V.Z1R}
  {==}

# map_pb's answer as (map_p's output, a), stated over a from a clone a1 == a
def pf1_sim(+n: U32, +d: Nat, -a: Array<U32>, +lit: U32, a1: Array<U32>, e1: {a1 == a : Array<U32>})
  -> {K.Kernel.map_pb(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0) == (K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), a) : Array<U32> & Array<U32>}:
  %e1 : {K.Kernel.map_pb(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, _, lit, 0) == (K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, _, lit, 0), _) : Array<U32> & Array<U32>}
  PF.mpb_sim(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), U32.to_nat(n), 0, lit, Array.new(U32, d, 0), a1)

# the map_p cell against the zip over the broadcast (any depth df: it reads lit everywhere)
def pf1_cell(+n: U32, +d: Nat, +df: Nat, -a: Array<U32>, +lit: U32, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  a2: Array<U32>, e2: {a2 == a : Array<U32>}, a3: Array<U32>, e3: {a3 == a : Array<U32>})
  -> {Laws.rd_at(U32, K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), k) == Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, df, lit), 0), k) : U32}:
  Equal.trans(U32, Laws.rd_at(U32, K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), k), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, a, k), lit)), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, df, lit), 0), k),
    (%e2 : {Laws.rd_at(U32, K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, _, lit, 0), k) == Bool.to_u32(U32.is_gt(Laws.rd_at(U32, _, k), lit)) : U32}; PF.mp_cell(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), d, n, a2, lit, 0, k, fits, hk)),
    Equal.sym(U32, Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, df, lit), 0), k), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, a, k), lit)),
      (%e3 : {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, _, Array.new(U32, df, lit), 0), k) == Bool.to_u32(U32.is_gt(Laws.rd_at(U32, _, k), lit)) : U32};
       %PF.rd_at_new(U32, df, lit, k) : {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a3, Array.new(U32, df, lit), 0), k) == Bool.to_u32(U32.is_gt(Laws.rd_at(U32, a3, k), _)) : U32};
       PC.zip_cell(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), d, n, a3, Array.new(U32, df, lit), 0, k, fits, hk))))

def pf1_m(+n: U32, +d: Nat, -a: Array<U32>, +lit: U32, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &a1: Array<U32> -> &a2: Array<U32> -> &a3: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>} & {a3 == a : Array<U32>})
  -> {Laws.ccell(Laws.z1_col(V.Eval.fz.z1(X.Gt{}, D.SU32{lit}, False{}, V.PNone{}, C.CU32{n, d, C.AllValid{}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Gt{}, C.CU32{n, d, C.AllValid{}, a}, V.Eval.const_col(D.SU32{lit}, D.TU32{}, n))), k) : D.Scalar}:
  (a1, a2, a3, e1, e2, e3) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.map_pb(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), (K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), a), pf1_sim(n, d, a, lit, a1, e1)) : {Laws.ccell(Laws.z1_col(V.Eval.fz.z1.e(False{}, C.AllValid{}, V.Eval.fz.l.w(D.TU32{}, n, d, V.Eval.fz.lw.m(~U32, D.TBool{}, n, d, _)))), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Gt{}, C.CU32{n, d, C.AllValid{}, a}, V.Eval.const_col(D.SU32{lit}, D.TU32{}, n))), k) : D.Scalar}
  Equal.cong(U32, D.Scalar, x => D.SBool{U32.is_ne(x, 0)}, Laws.rd_at(U32, K.Kernel.map_p(~U32, ~U32, ~U32, ~(q => x => Bool.to_u32(U32.is_gt(x, q))), n, d, a, lit, 0), k), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, K.Kernel.depth_for(n), lit), 0), k), pf1_cell(n, d, K.Kernel.depth_for(n), a, lit, k, fits, hk, a2, e2, a3, e3))

def Laws.peep_f1(n, d, a, lit, k, fits, hk):
  pf1_m(n, d, a, lit, k, fits, hk, PF.clone3(U32, a))

def pf1l_sim(+n: U32, +d: Nat, -a: Array<F32>, +lit: F32, a1: Array<F32>, e1: {a1 == a : Array<F32>})
  -> {K.Kernel.map_pb(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0) == (K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0), a) : Array<F32> & Array<F32>}:
  %e1 : {K.Kernel.map_pb(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, _, lit, 0.0) == (K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, _, lit, 0.0), _) : Array<F32> & Array<F32>}
  PF.mpb_sim(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), U32.to_nat(n), 0, lit, Array.new(F32, d, 0.0), a1)

# the map_p cell `lit - a[k]` against the zip of the broadcast (depth df, the output's) and a
def pf1l_cell(+n: U32, +d: Nat, +df: Nat, -a: Array<F32>, +lit: F32, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +fitsf: {U32.is_le(n, U32.shln(1, df)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  a2: Array<F32>, e2: {a2 == a : Array<F32>}, a3: Array<F32>, e3: {a3 == a : Array<F32>})
  -> {Laws.rd_at(F32, K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0), k) == Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, df, Array.new(F32, df, lit), a, 0.0), k) : F32}:
  Equal.trans(F32, Laws.rd_at(F32, K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0), k), F32.sub(lit, Laws.rd_at(F32, a, k)), Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, df, Array.new(F32, df, lit), a, 0.0), k),
    (%e2 : {Laws.rd_at(F32, K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, _, lit, 0.0), k) == F32.sub(lit, Laws.rd_at(F32, _, k)) : F32}; PF.mp_cell(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), d, n, a2, lit, 0.0, k, fits, hk)),
    Equal.sym(F32, Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, df, Array.new(F32, df, lit), a, 0.0), k), F32.sub(lit, Laws.rd_at(F32, a, k)),
      (%e3 : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, df, Array.new(F32, df, lit), _, 0.0), k) == F32.sub(lit, Laws.rd_at(F32, _, k)) : F32};
       %PF.rd_at_new(F32, df, lit, k) : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, df, Array.new(F32, df, lit), a3, 0.0), k) == F32.sub(_, Laws.rd_at(F32, a3, k)) : F32};
       PC.zip_cell(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), df, n, Array.new(F32, df, lit), a3, 0.0, k, fitsf, hk))))

def pf1l_m(+n: U32, +d: Nat, -a: Array<F32>, +lit: F32, +k: U32, +h31: {U32.is_le(n, U32.shln(1, 31n)) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &a1: Array<F32> -> &a2: Array<F32> -> &a3: Array<F32> -> {a1 == a : Array<F32>} & {a2 == a : Array<F32>} & {a3 == a : Array<F32>})
  -> {Laws.ccell(Laws.z1_col(V.Eval.fz.z1(X.Sub{}, D.SF32{lit}, True{}, V.PNone{}, C.CF32{n, d, C.AllValid{}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Sub{}, V.Eval.const_col(D.SF32{lit}, D.TF32{}, n), C.CF32{n, d, C.AllValid{}, a})), k) : D.Scalar}:
  (a1, a2, a3, e1, e2, e3) = w
  %Equal.sym(Array<F32> & Array<F32>, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0), (K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0), a), pf1l_sim(n, d, a, lit, a1, e1)) : {Laws.ccell(Laws.z1_col(V.Eval.fz.z1.e(False{}, C.AllValid{}, V.Eval.fz.l.f(n, d, V.Eval.fz.lf.m(n, d, _)))), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Sub{}, V.Eval.const_col(D.SF32{lit}, D.TF32{}, n), C.CF32{n, d, C.AllValid{}, a})), k) : D.Scalar}
  Equal.cong(F32, D.Scalar, x => D.SF32{x}, Laws.rd_at(F32, K.Kernel.map_p(~F32, ~F32, ~F32, ~(q => x => F32.sub(q, x)), n, d, a, lit, 0.0), k), Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, K.Kernel.depth_for(n), Array.new(F32, K.Kernel.depth_for(n), lit), a, 0.0), k), pf1l_cell(n, d, K.Kernel.depth_for(n), a, lit, k, fits, Laws.depth_for_fits(n, h31), hk, a2, e2, a3, e3))

def Laws.peep_f1_left(n, d, a, lit, k, h31, fits, hk):
  pf1l_m(n, d, a, lit, k, h31, fits, hk, PF.clone3(F32, a))

# ---- F2 masked: zipv's value output under mask_and, the columns back ------------------------------------

def Laws.peep_f2_mask_back(n, d, d2, a, ma, b, mb):
  %Equal.sym(Bool, U32.is_eq(n, n), True{}, PV.u32_eq_refl(n)) : {V.Eval.fz.z2.a(X.Add{}, V.PNone{}, V.PNone{}, _, (C.CU32{n, d, C.Mask{ma}, a}, D.TU32{}), (C.CU32{n, d2, C.Mask{mb}, b}, D.TU32{})) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}
  %Equal.sym(K.ZV<U32, U32, U32>, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0), K.ZV{Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), K.Kernel.mask_and(n, d, ma, mb), a, ma, b, mb}, Laws.zipv_valid(d, n, a, ma, b, mb, 0)) : {V.Eval.fz.z2.e(False{}, False{}, C.AllValid{}, C.AllValid{}, V.Eval.fz.zr.ww(D.TU32{}, D.TU32{}, n, d, n, d2, V.Eval.fz.zw.v(~U32, ~U32, D.TU32{}, n, d, True{}, True{}, _))) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}
  {==}

# ---- F3: a fallible cast does not fire ------------------------------------------------------------------

def Laws.peep_f3_strict(op, n, d, v, x, n2, d2, vb, b):
  {==}

# ---- F4 ----------------------------------------------------------------------------------------------------

def Laws.peep_f4(n, d, m, a):
  {==}

# post-review B1: F4 resets the null slots (Eval.fix = Kernel.mask_data in place); the fused fill's
# cell at k is the reset buffer's, which mask_data_cell's witness (PI.MDW) gives: the slot where the mask
# word is set, 0 where it is 0
def pf4n_k(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +k: U32, +hm: {Laws.rd_at(U32, m, k) == 0 : U32}, w: PI.MDW(~U32, n, d, a, m, 0, k))
  -> {Laws.ccell(Laws.z0_col(V.Eval.fz.z0(V.PFill{D.SU32{0}}, C.CU32{n, d, C.Mask{m}, a})), k) == D.SU32{0} : D.Scalar}:
  (o, mb, emd, emb, wfo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, a, m, 0), (o, mb), emd) : {Laws.ccell(C.Column.set_valid(V.Eval.fix.w2(D.TU32{}, n, d, _), C.AllValid{}), k) == D.SU32{0} : D.Scalar}
  Equal.cong(U32, D.Scalar, q => D.SU32{q}, Laws.rd_at(U32, o, k), 0,
    Equal.trans(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, d, o, k), 0, Laws.rd_at_wf(U32, d, o, k, wfo),
      Equal.trans(U32, Laws.rdN(U32, d, o, k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0), 0, cell,
        (%Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, a, k), 0) == 0 : U32}; {==}))))

def Laws.peep_f4_not_noop(n, d, m, a, k, wf, fits, hk, hm):
  ((%Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SU32{Laws.rd_at(U32, a, k)}, D.SNull{}) == D.SNull{} : D.Scalar}; {==}),
   pf4n_k(n, d, m, a, k, hm, PI.mask_data_w(~U32, n, d, a, m, 0, k, wf, fits, hk)))

# F4 on a borrowed column: the masked copy is Kernel.zipb's loop over the data and the mask, which IS
# Kernel.zip's with both operands handed back (PF.zb_sim)
def Laws.peep_f4_borrow(n, d, m, a):
  %Equal.sym(K.ZB<U32, U32, U32>, K.Kernel.zipb.go(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, m, 0)), K.ZB{K.Kernel.zip.go(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, m, 0)), a, m}, PF.zb_sim(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), U32.to_nat(n), 0, Array.new(U32, d, 0), a, m)) : {V.Eval.fz.dm.w(D.TU32{}, n, d, _) == V.Z1R{Some{C.CU32{n, d, C.AllValid{}, K.Kernel.zip(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0)}}, C.CU32{n, d, C.Mask{m}, a}} : V.Z1R}
  {==}

def Laws.peep_f4_other(lit, n, d, v, a, h):
  %Equal.sym(Bool, U32.is_zero(lit), False{}, h) : {V.Eval.fz.z0.b(_, C.CU32{n, d, v, a}) == V.Z0R{False{}, C.CU32{n, d, v, a}} : V.Z0R}
  {==}

# ---- the peephole pass ---------------------------------------------------------------------------------------

def Laws.fuse_lit_right(out, n, v, ty, op, rest, h):
  %Equal.sym(Bool, V.Eval.fz.op_ok(op), True{}, h) : {V.Eval.fz.p2(_, out, V.ORef{n, False{}}, V.PNone{}, V.ICol{n} <> Nil{}, v, ty, op, rest) == V.FzS{V.IFz{V.Z1{op, v, False{}, V.ORef{n, False{}}, V.PNone{}}, V.ICol{n} <> V.IConst{v, ty} <> V.IBin{op} <> Nil{}} <> out, rest} : V.FzS}
  {==}

def Laws.fuse_lit_left(out, n, v, ty, op, rest, h):
  %Equal.sym(Bool, V.Eval.fz.op_ok(op), True{}, h) : {V.Eval.fz.p3.go(_, out, v, ty, V.ORef{n, False{}}, V.PNone{}, V.ICol{n} <> Nil{}, op, rest) == V.FzS{V.IFz{V.Z1{op, v, True{}, V.ORef{n, False{}}, V.PNone{}}, V.IConst{v, ty} <> V.ICol{n} <> V.IBin{op} <> Nil{}} <> out, rest} : V.FzS}
  {==}

def Laws.fuse_two(out, na, nb, op, rest, h, hn):
  %Equal.sym(Bool, String.eq(na, nb), False{}, hn) : {V.Eval.fz.p1.go(Bool.and(Bool.not(_), V.Eval.fz.op_ok(op)), out, V.ORef{na, False{}}, V.PNone{}, V.ICol{na} <> Nil{}, V.ORef{nb, True{}}, V.PNone{}, V.IMove{nb} <> Nil{}, op, rest) == V.FzS{V.IFz{V.Z2{op, V.ORef{na, False{}}, V.PNone{}, V.ORef{nb, True{}}, V.PNone{}}, V.ICol{na} <> V.IMove{nb} <> V.IBin{op} <> Nil{}} <> out, rest} : V.FzS}
  %Equal.sym(Bool, V.Eval.fz.op_ok(op), True{}, h) : {V.Eval.fz.p1.go(_, out, V.ORef{na, False{}}, V.PNone{}, V.ICol{na} <> Nil{}, V.ORef{nb, True{}}, V.PNone{}, V.IMove{nb} <> Nil{}, op, rest) == V.FzS{V.IFz{V.Z2{op, V.ORef{na, False{}}, V.PNone{}, V.ORef{nb, True{}}, V.PNone{}}, V.ICol{na} <> V.IMove{nb} <> V.IBin{op} <> Nil{}} <> out, rest} : V.FzS}
  {==}

def Laws.fuse_fill(out, n, v, ty, rest):
  {==}

def Laws.fuse_kleene(out, rest):
  {==}

def Laws.fuse_same(out, n, op, rest):
  %Equal.sym(Bool, String.eq(n, n), True{}, Laws.str_eq_refl(n)) : {V.Eval.fz.p1.go(Bool.and(Bool.not(_), V.Eval.fz.op_ok(op)), out, V.ORef{n, False{}}, V.PNone{}, V.ICol{n} <> Nil{}, V.ORef{n, True{}}, V.PNone{}, V.IMove{n} <> Nil{}, op, rest) == V.FzS{V.ICol{n} <> out, V.IMove{n} <> V.IBin{op} <> rest} : V.FzS}
  {==}

# ---- F3: the cast inside the zip ------------------------------------------------------------------------

def Laws.peep_f3_back(n, d, d2, a, b):
  %Equal.sym(Bool, U32.is_eq(n, n), True{}, PV.u32_eq_refl(n)) : {V.Eval.fz.z2.a(X.Mul{}, V.PCast{D.TF32{}}, V.PNone{}, _, (C.CU32{n, d, C.AllValid{}, a}, D.TU32{}), (C.CF32{n, d2, C.AllValid{}, b}, D.TF32{})) == V.Z2R{Some{C.CF32{n, d, C.AllValid{}, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, 0.0))}}, C.CU32{n, d, C.AllValid{}, a}, C.CF32{n, d2, C.AllValid{}, b}} : V.Z2R}
  %Equal.sym(K.ZB<U32, F32, F32>, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, 0.0), K.ZB{K.Kernel.zip(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, 0.0), a, b}, PF.zb_sim(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), U32.to_nat(n), 0, Array.new(F32, d, 0.0), a, b)) : {V.Eval.fz.z2.e(False{}, False{}, C.AllValid{}, C.AllValid{}, V.Eval.fz.zr.wf(D.TU32{}, n, d, n, d2, V.Eval.fz.zf.b(~U32, ~F32, n, d, _))) == V.Z2R{Some{C.CF32{n, d, C.AllValid{}, Laws.zb_o(U32, F32, F32, _)}}, C.CU32{n, d, C.AllValid{}, a}, C.CF32{n, d2, C.AllValid{}, b}} : V.Z2R}
  {==}

def pf3_m(+n: U32, +d: Nat, +d2: Nat, -a: Array<U32>, -b: Array<F32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wa: &a1: Array<U32> -> &a2: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>}, wb: &b1: Array<F32> -> &b2: Array<F32> -> {b1 == b : Array<F32>} & {b2 == b : Array<F32>})
  -> {Laws.ccell(Laws.z2_col(V.Eval.fz.z2(X.Mul{}, V.PCast{D.TF32{}}, V.PNone{}, C.CU32{n, d, C.AllValid{}, a}, C.CF32{n, d2, C.AllValid{}, b})), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Mul{}, Laws.res_col(V.Eval.cast(D.TF32{}, C.CU32{n, d, C.AllValid{}, a})), C.CF32{n, d2, C.AllValid{}, b})), k) : D.Scalar}:
  (a1, a2, ea1, ea2) = wa
  (b1, b2, eb1, eb2) = wb
  %Equal.sym(V.Z2R, V.Eval.fz.z2(X.Mul{}, V.PCast{D.TF32{}}, V.PNone{}, C.CU32{n, d, C.AllValid{}, a}, C.CF32{n, d2, C.AllValid{}, b}), V.Z2R{Some{C.CF32{n, d, C.AllValid{}, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, 0.0))}}, C.CU32{n, d, C.AllValid{}, a}, C.CF32{n, d2, C.AllValid{}, b}},
    (%ea1 : {V.Eval.fz.z2(X.Mul{}, V.PCast{D.TF32{}}, V.PNone{}, C.CU32{n, d, C.AllValid{}, _}, C.CF32{n, d2, C.AllValid{}, b}) == V.Z2R{Some{C.CF32{n, d, C.AllValid{}, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, _, b, 0.0))}}, C.CU32{n, d, C.AllValid{}, _}, C.CF32{n, d2, C.AllValid{}, b}} : V.Z2R};
     %eb1 : {V.Eval.fz.z2(X.Mul{}, V.PCast{D.TF32{}}, V.PNone{}, C.CU32{n, d, C.AllValid{}, a1}, C.CF32{n, d2, C.AllValid{}, _}) == V.Z2R{Some{C.CF32{n, d, C.AllValid{}, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a1, _, 0.0))}}, C.CU32{n, d, C.AllValid{}, a1}, C.CF32{n, d2, C.AllValid{}, _}} : V.Z2R};
     Laws.peep_f3_back(n, d, d2, a1, b1))) : {Laws.ccell(Laws.z2_col(_), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Mul{}, Laws.res_col(V.Eval.cast(D.TF32{}, C.CU32{n, d, C.AllValid{}, a})), C.CF32{n, d2, C.AllValid{}, b})), k) : D.Scalar}
  Equal.cong(F32, D.Scalar, x => D.SF32{x}, Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, 0.0)), k), Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a, 0.0), b, 0.0), k),
    (%ea2 : {Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, _, b, 0.0)), k) == Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, _, 0.0), b, 0.0), k) : F32};
     %eb2 : {Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a2, _, 0.0)), k) == Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a2, 0.0), _, 0.0), k) : F32};
     Laws.zipb_cast_cell(d, n, a2, b2, 0.0, k, fits, hk)))

def Laws.peep_f3(n, d, d2, a, b, k, fits, hk):
  pf3_m(n, d, d2, a, b, k, fits, hk, PC.clone_eq(U32, a), PC.clone_eq(F32, b))

# ---- four clones of one array ---------------------------------------------------------------------------

def c4_j(-T: Data, -a: Array<T>, -b1: Array<T>, -b2: Array<T>, +e1: {b1 == a : Array<T>}, +e2: {b2 == a : Array<T>},
  w1: &c1: Array<T> -> &c2: Array<T> -> {c1 == b1 : Array<T>} & {c2 == b1 : Array<T>}, w2: &c3: Array<T> -> &c4: Array<T> -> {c3 == b2 : Array<T>} & {c4 == b2 : Array<T>})
  -> &x1: Array<T> -> &x2: Array<T> -> &x3: Array<T> -> &x4: Array<T> -> {x1 == a : Array<T>} & {x2 == a : Array<T>} & {x3 == a : Array<T>} & {x4 == a : Array<T>}:
  (c1, c2, f1, f2) = w1
  (c3, c4, f3, f4) = w2
  (c1, c2, c3, c4, Equal.trans(Array<T>, c1, b1, a, f1, e1), Equal.trans(Array<T>, c2, b1, a, f2, e1), Equal.trans(Array<T>, c3, b2, a, f3, e2), Equal.trans(Array<T>, c4, b2, a, f4, e2))

def c4_k(-T: Data, -a: Array<T>, w: &b1: Array<T> -> &b2: Array<T> -> {b1 == a : Array<T>} & {b2 == a : Array<T>})
  -> &x1: Array<T> -> &x2: Array<T> -> &x3: Array<T> -> &x4: Array<T> -> {x1 == a : Array<T>} & {x2 == a : Array<T>} & {x3 == a : Array<T>} & {x4 == a : Array<T>}:
  (b1, b2, +e1, +e2) = w
  c4_j(T, a, b1, b2, e1, e2, PC.clone_eq(T, b1), PC.clone_eq(T, b2))

def clone4(-T: Data, a: Array<T>) -> &x1: Array<T> -> &x2: Array<T> -> &x3: Array<T> -> &x4: Array<T> -> {x1 == a : Array<T>} & {x2 == a : Array<T>} & {x3 == a : Array<T>} & {x4 == a : Array<T>}:
  c4_k(T, a, PC.clone_eq(T, a))

# ---- F5: q1's pass ---------------------------------------------------------------------------------------

def Laws.peep_f5_back(n, d, ok, q, lit):
  %Equal.sym(K.PC<U32, U32>, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones()), K.PC{Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), ok, V.Eval.fz.ones(), q, V.Eval.fz.ones()}, Laws.pred_count_keeps(d, n, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())) : {V.Eval.f5.rw(D.TU32{}, n, d, False{}, _) == V.F5R{True{}, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}} : V.F5R}
  {==}

# peep_f5_back over the originals from clones
def pf5_back(+n: U32, +d: Nat, -ok: Array<U32>, -q: Array<U32>, +lit: U32, ok1: Array<U32>, e1: {ok1 == ok : Array<U32>}, q1: Array<U32>, e2: {q1 == q : Array<U32>})
  -> {V.Eval.f5.c(X.Gt{}, ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit}) == V.F5R{True{}, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}} : V.F5R}:
  %e1 : {V.Eval.f5.c(X.Gt{}, _, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit}) == V.F5R{True{}, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, _, V.Eval.fz.ones(), q, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, _, V.Eval.fz.ones(), q, V.Eval.fz.ones())), _, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}} : V.F5R}
  %e2 : {V.Eval.f5.c(X.Gt{}, ok1, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, _}, D.SU32{lit}) == V.F5R{True{}, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok1, V.Eval.fz.ones(), _, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok1, V.Eval.fz.ones(), _, V.Eval.fz.ones())), ok1, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, _}} : V.F5R}
  Laws.peep_f5_back(n, d, ok1, q1, lit)

def pf5_count(+n: U32, +d: Nat, -ok: Array<U32>, -q: Array<U32>, +lit: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  wo: &o1: Array<U32> -> &o2: Array<U32> -> {o1 == ok : Array<U32>} & {o2 == ok : Array<U32>}, wq: &q1: Array<U32> -> &q2: Array<U32> -> {q1 == q : Array<U32>} & {q2 == q : Array<U32>})
  -> {Laws.f5r_k(V.Eval.f5.c(X.Gt{}, ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit})) == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.f5r_m(V.Eval.f5.c(X.Gt{}, ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit})))) : U32}:
  (o1, o2, eo1, eo2) = wo
  (q1, q2, eq1, eq2) = wq
  %Equal.sym(V.F5R, V.Eval.f5.c(X.Gt{}, ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit}), V.F5R{True{}, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}}, pf5_back(n, d, ok, q, lit, o1, eo1, q1, eq1)) : {Laws.f5r_k(_) == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.f5r_m(_))) : U32}
  %eo2 : {Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, _, V.Eval.fz.ones(), q, V.Eval.fz.ones())) == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, _, V.Eval.fz.ones(), q, V.Eval.fz.ones())))) : U32}
  %eq2 : {Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, o2, V.Eval.fz.ones(), _, V.Eval.fz.ones())) == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, o2, V.Eval.fz.ones(), _, V.Eval.fz.ones())))) : U32}
  Laws.pred_count_count(d, n, lit, o2, V.Eval.fz.ones(), q2, V.Eval.fz.ones(), fits)

def Laws.peep_f5_count(n, d, ok, q, lit, fits):
  pf5_count(n, d, ok, q, lit, fits, PC.clone_eq(U32, ok), PC.clone_eq(U32, q))

# the fused mask cell: pred_count_cell, the ones array read as 1
def pf5_pcc(+n: U32, +d: Nat, -ok: Array<U32>, -q: Array<U32>, +lit: U32, +i: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hi: {U32.is_lt(i, n) == True{} : Bool}, ok2: Array<U32>, e1: {ok2 == ok : Array<U32>}, q2: Array<U32>, e2: {q2 == q : Array<U32>})
  -> {Laws.rd_at(U32, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), i) == U32.and(Laws.rd_at(U32, ok, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))) : U32}:
  %e1 : {Laws.rd_at(U32, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, _, V.Eval.fz.ones(), q, V.Eval.fz.ones())), i) == U32.and(Laws.rd_at(U32, _, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))) : U32}
  %e2 : {Laws.rd_at(U32, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok2, V.Eval.fz.ones(), _, V.Eval.fz.ones())), i) == U32.and(Laws.rd_at(U32, ok2, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, _, i), lit))) : U32}
  Equal.trans(U32, Laws.rd_at(U32, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok2, V.Eval.fz.ones(), q2, V.Eval.fz.ones())), i), Bool.pick(U32, U32.is_ne(U32.and(Laws.rd_at(U32, V.Eval.fz.ones(), i), Laws.rd_at(U32, V.Eval.fz.ones(), i)), 0), U32.and(Laws.rd_at(U32, ok2, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q2, i), lit))), 0), U32.and(Laws.rd_at(U32, ok2, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q2, i), lit))),
    Laws.pred_count_cell(d, n, lit, ok2, V.Eval.fz.ones(), q2, V.Eval.fz.ones(), i, fits, hi),
    (%Equal.sym(U32, Laws.rd_at(U32, Array.new(U32, 0n, 1), i), 1, PF.rd_at_new(U32, 0n, 1, i)) : {Bool.pick(U32, U32.is_ne(U32.and(_, _), 0), U32.and(Laws.rd_at(U32, ok2, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q2, i), lit))), 0) == U32.and(Laws.rd_at(U32, ok2, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q2, i), lit))) : U32}; {==}))

# the unfused mask cell: the And zip over ok and the Gt zip over q and the broadcast
def pf5_unf(+n: U32, +d: Nat, +df: Nat, -ok: Array<U32>, -q: Array<U32>, +lit: U32, +i: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hi: {U32.is_lt(i, n) == True{} : Bool}, ok3: Array<U32>, e3: {ok3 == ok : Array<U32>}, q3: Array<U32>, +e4: {q3 == q : Array<U32>}, q4: Array<U32>, +e5: {q4 == q : Array<U32>})
  -> {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, ok, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q, Array.new(U32, df, lit), 0), 0), i) == U32.and(Laws.rd_at(U32, ok, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))) : U32}:
  %e3 : {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, _, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q, Array.new(U32, df, lit), 0), 0), i) == U32.and(Laws.rd_at(U32, _, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))) : U32}
  %e4 : {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, ok3, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, _, Array.new(U32, df, lit), 0), 0), i) == U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, ok3, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q3, Array.new(U32, df, lit), 0), 0), i), U32.and(Laws.rd_at(U32, ok3, i), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q3, Array.new(U32, df, lit), 0), i)), PC.zip_cell(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), d, n, ok3, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q3, Array.new(U32, df, lit), 0), 0, i, fits, hi)) : {_ == U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))) : U32}
  %e5 : {U32.and(Laws.rd_at(U32, ok3, i), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q3, Array.new(U32, df, lit), 0), i)) == U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, _, i), lit))) : U32}
  %Equal.trans(Array<U32>, q4, q, q3, e5, Equal.sym(Array<U32>, q3, q, e4)) : {U32.and(Laws.rd_at(U32, ok3, i), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, _, Array.new(U32, df, lit), 0), i)) == U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q4, i), lit))) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q4, Array.new(U32, df, lit), 0), i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q4, i), Laws.rd_at(U32, Array.new(U32, df, lit), i))), PC.zip_cell(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), d, n, q4, Array.new(U32, df, lit), 0, i, fits, hi)) : {U32.and(Laws.rd_at(U32, ok3, i), _) == U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q4, i), lit))) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, Array.new(U32, df, lit), i), lit, PF.rd_at_new(U32, df, lit, i)) : {U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q4, i), _))) == U32.and(Laws.rd_at(U32, ok3, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q4, i), lit))) : U32}
  {==}

def pf5_cell(+n: U32, +d: Nat, -ok: Array<U32>, -q: Array<U32>, +lit: U32, +i: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hi: {U32.is_lt(i, n) == True{} : Bool},
  wo: &o1: Array<U32> -> &o2: Array<U32> -> &o3: Array<U32> -> {o1 == ok : Array<U32>} & {o2 == ok : Array<U32>} & {o3 == ok : Array<U32>},
  wq: &q1: Array<U32> -> &q2: Array<U32> -> &q3: Array<U32> -> &q4: Array<U32> -> {q1 == q : Array<U32>} & {q2 == q : Array<U32>} & {q3 == q : Array<U32>} & {q4 == q : Array<U32>})
  -> {Laws.rd_at(U32, Laws.f5r_m(V.Eval.f5.c(X.Gt{}, ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit})), i) == Laws.rd_at(U32, Pair.fst(Array<U32>, U32, V.Eval.pred(Laws.res_col(V.Eval.bin(X.And{}, C.CBool{n, d, C.AllValid{}, ok}, Laws.res_col(V.Eval.bin(X.Gt{}, C.CU32{n, d, C.AllValid{}, q}, V.Eval.const_col(D.SU32{lit}, D.TU32{}, n))))))), i) : U32}:
  (o1, o2, o3, eo1, eo2, eo3) = wo
  (q1, q2, q3, q4, eq1, eq2, eq3, eq4) = wq
  %Equal.sym(V.F5R, V.Eval.f5.c(X.Gt{}, ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}, D.SU32{lit}), V.F5R{True{}, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), Laws.pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), ok, V.Eval.fz.ones(), C.CU32{n, d, C.AllValid{}, q}}, pf5_back(n, d, ok, q, lit, o1, eo1, q1, eq1)) : {Laws.rd_at(U32, Laws.f5r_m(_), i) == Laws.rd_at(U32, Pair.fst(Array<U32>, U32, V.Eval.pred(Laws.res_col(V.Eval.bin(X.And{}, C.CBool{n, d, C.AllValid{}, ok}, Laws.res_col(V.Eval.bin(X.Gt{}, C.CU32{n, d, C.AllValid{}, q}, V.Eval.const_col(D.SU32{lit}, D.TU32{}, n))))))), i) : U32}
  Equal.trans(U32, Laws.rd_at(U32, Laws.pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, ok, V.Eval.fz.ones(), q, V.Eval.fz.ones())), i), U32.and(Laws.rd_at(U32, ok, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, ok, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q, Array.new(U32, K.Kernel.depth_for(n), lit), 0), 0), i),
    pf5_pcc(n, d, ok, q, lit, i, fits, hi, o2, eo2, q2, eq2),
    Equal.sym(U32, Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, ok, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, q, Array.new(U32, K.Kernel.depth_for(n), lit), 0), 0), i), U32.and(Laws.rd_at(U32, ok, i), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, q, i), lit))),
      pf5_unf(n, d, K.Kernel.depth_for(n), ok, q, lit, i, fits, hi, o3, eo3, q3, eq3, q4, eq4)))

def Laws.peep_f5_cell(n, d, ok, q, lit, i, fits, hi):
  pf5_cell(n, d, ok, q, lit, i, fits, hi, PF.clone3(U32, ok), clone4(U32, q))

# ---- F4 against Eval.fill: both cells are the slot where the mask word is set, 0 where it is 0 ----------
# Post-review B1: F4 resets the null slots itself (owned: Kernel.mask_data in place; borrowed: one masked
# copy), so the fused cell no longer needs the P0 hypothesis v0.2 stated (the null slot at k holds the
# default). Eval.fill's cell is Kernel.choose's against the broadcast 0 (PI.CHW); the owned fill's is
# Kernel.mask_data's (PI.MDW); the borrowed fill's is Kernel.zipb's (PF.zb_cell). Each witness consumes
# its own clone of the buffers (and of the data buffer's well-formedness: wfa_clone).

# two copies of a well-formed array, each with its own well-formedness
def CloneA(-T: Data, +d: Nat, -a: Array<T>) -> Type:
  &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & Laws.WFArray(T, d, a1) & Laws.WFArray(T, d, a2)

def wfa_clone_node(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>, wx: CloneA(T, p, xs), wy: CloneA(T, p, ys)) -> CloneA(T, 1n+p, ANode{xs, ys}):
  (x1, x2, ex1, ex2, wx1, wx2) = wx
  (y1, y2, ey1, ey2, wy1, wy2) = wy
  (ANode{x1, y1}, ANode{x2, y2}, (%ey1 : {ANode{x1, y1} == ANode{xs, _} : Array<T>}; %ex1 : {ANode{x1, y1} == ANode{_, y1} : Array<T>}; {==}), (%ey2 : {ANode{x2, y2} == ANode{xs, _} : Array<T>}; %ex2 : {ANode{x2, y2} == ANode{_, y2} : Array<T>}; {==}), (wx1, wy1), (wx2, wy2))

def wfa_clone(-T: Data, d: Nat, a: Array<T>, w: Laws.WFArray(T, d, a)) -> CloneA(T, d, a):
  match d a:
    case 0n ALeaf{+x}:
      (ALeaf{x}, ALeaf{x}, {==}, {==}, Unit{}, Unit{})
    case 1n++p ANode{xs, ys}:
      (wl, wr) = w
      wfa_clone_node(T, p, xs, ys, wfa_clone(T, p, xs, wl), wfa_clone(T, p, ys, wr))
    case 0n ANode{xs, ys}:
      Empty.absurd(CloneA(T, 0n, ANode{xs, ys}), w)
    case 1n+p ALeaf{x}:
      Empty.absurd(CloneA(T, 1n+p, ALeaf{x}), w)

def pf4_k(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +k: U32, w1: PI.MDW(~U32, n, d, a, m, 0, k), w2: PI.CHW(~U32, n, d, m, a, Array.new(U32, K.Kernel.depth_for(n), 0), k))
  -> {Laws.ccell(Laws.z0_col(V.Eval.fz.z0(V.PFill{D.SU32{0}}, C.CU32{n, d, C.Mask{m}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.fill(C.CU32{n, d, C.Mask{m}, a}, V.Eval.const_col(D.SU32{0}, D.TU32{}, n))), k) : D.Scalar}:
  (o1, mb1, emd, emb1, wfo1, cell1) = w1
  (mb2, o2, ech, emb2, wfo2, cell2) = w2
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, a, m, 0), (o1, mb1), emd) : {Laws.ccell(C.Column.set_valid(V.Eval.fix.w2(D.TU32{}, n, d, _), C.AllValid{}), k) == Laws.ccell(Laws.res_col(V.Eval.fill(C.CU32{n, d, C.Mask{m}, a}, V.Eval.const_col(D.SU32{0}, D.TU32{}, n))), k) : D.Scalar}
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.choose(~U32, n, m, a, Array.new(U32, K.Kernel.depth_for(n), 0)), (mb2, o2), ech) : {Laws.ccell(C.CU32{n, d, C.AllValid{}, o1}, k) == Laws.ccell(Laws.res_col(V.Eval.fill.w(D.TU32{}, n, d, V.Eval.fill.t2(~U32, n, d, C.AllValid{}, _))), k) : D.Scalar}
  Equal.cong(U32, D.Scalar, q => D.SU32{q}, Laws.rd_at(U32, o1, k), Laws.rd_at(U32, o2, k),
    (%Equal.sym(U32, Laws.rd_at(U32, o1, k), Laws.rdN(U32, d, o1, k), Laws.rd_at_wf(U32, d, o1, k, wfo1)) : {_ == Laws.rd_at(U32, o2, k) : U32};
     %Equal.sym(U32, Laws.rdN(U32, d, o1, k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0), cell1) : {_ == Laws.rd_at(U32, o2, k) : U32};
     %Equal.sym(U32, Laws.rd_at(U32, o2, k), Laws.rdN(U32, d, o2, k), Laws.rd_at_wf(U32, d, o2, k, wfo2)) : {Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) == _ : U32};
     %Equal.sym(U32, Laws.rdN(U32, d, o2, k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), Laws.rd_at(U32, Array.new(U32, K.Kernel.depth_for(n), 0), k)), cell2) : {Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) == _ : U32};
     %Equal.sym(U32, Laws.rd_at(U32, Array.new(U32, K.Kernel.depth_for(n), 0), k), 0, PF.rd_at_new(U32, K.Kernel.depth_for(n), 0, k)) : {Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), _) : U32};
     {==}))

def pf4_c(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wa: CloneA(U32, d, a), wm: &m1: Array<U32> -> &m2: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>})
  -> {Laws.ccell(Laws.z0_col(V.Eval.fz.z0(V.PFill{D.SU32{0}}, C.CU32{n, d, C.Mask{m}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.fill(C.CU32{n, d, C.Mask{m}, a}, V.Eval.const_col(D.SU32{0}, D.TU32{}, n))), k) : D.Scalar}:
  (a1, a2, ea1, ea2, wf1, wf2) = wa
  (m1, m2, em1, em2) = wm
  pf4_k(n, d, m, a, k,
    (%ea1 : PI.MDW(~U32, n, d, _, m, 0, k); %em1 : PI.MDW(~U32, n, d, a1, _, 0, k); PI.mask_data_w(~U32, n, d, a1, m1, 0, k, wf1, fits, hk)),
    (%ea2 : PI.CHW(~U32, n, d, m, _, Array.new(U32, K.Kernel.depth_for(n), 0), k); %em2 : PI.CHW(~U32, n, d, _, a2, Array.new(U32, K.Kernel.depth_for(n), 0), k); PI.choose_w(~U32, n, d, m2, a2, Array.new(U32, K.Kernel.depth_for(n), 0), k, wf2, fits, hk)))

def Laws.peep_f4_cell(n, d, m, a, k, wf, fits, hk):
  pf4_c(n, d, m, a, k, fits, hk, wfa_clone(U32, d, a, wf), PC.clone_eq(U32, m))

# the borrowed fill's cell is the masked copy's slot (Eval.fz.dm.w takes Kernel.zipb's record apart)
def dmw_cell(+n: U32, +d: Nat, +k: U32, r: K.ZB<U32, U32, U32>) -> {Laws.ccell(Laws.z1_col(V.Eval.fz.dm.w(D.TU32{}, n, d, r)), k) == D.SU32{Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, r), k)} : D.Scalar}:
  match r:
    case K.ZB{o, x, m}:
      {==}

def pf4b_k(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +k: U32,
  e1: {Laws.ccell(Laws.z1_col(V.Eval.fz.dm.w(D.TU32{}, n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0))), k) == D.SU32{Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0)), k)} : D.Scalar},
  e2: {Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0)), k) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) : U32},
  w: PI.CHW(~U32, n, d, m, a, Array.new(U32, K.Kernel.depth_for(n), 0), k))
  -> {Laws.ccell(Laws.z1_col(V.Eval.fz.z0b(V.PFill{D.SU32{0}}, C.CU32{n, d, C.Mask{m}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.fill(C.CU32{n, d, C.Mask{m}, a}, V.Eval.const_col(D.SU32{0}, D.TU32{}, n))), k) : D.Scalar}:
  (mb2, o2, ech, emb2, wfo2, cell2) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.choose(~U32, n, m, a, Array.new(U32, K.Kernel.depth_for(n), 0)), (mb2, o2), ech) : {Laws.ccell(Laws.z1_col(V.Eval.fz.z0b(V.PFill{D.SU32{0}}, C.CU32{n, d, C.Mask{m}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.fill.w(D.TU32{}, n, d, V.Eval.fill.t2(~U32, n, d, C.AllValid{}, _))), k) : D.Scalar}
  %Equal.sym(D.Scalar, Laws.ccell(Laws.z1_col(V.Eval.fz.dm.w(D.TU32{}, n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0))), k), D.SU32{Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0)), k)}, e1) : {_ == Laws.ccell(C.CU32{n, d, C.AllValid{}, o2}, k) : D.Scalar}
  Equal.cong(U32, D.Scalar, q => D.SU32{q}, Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0)), k), Laws.rd_at(U32, o2, k),
    (%Equal.sym(U32, Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a, m, 0)), k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0), e2) : {_ == Laws.rd_at(U32, o2, k) : U32};
     %Equal.sym(U32, Laws.rd_at(U32, o2, k), Laws.rdN(U32, d, o2, k), Laws.rd_at_wf(U32, d, o2, k, wfo2)) : {Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) == _ : U32};
     %Equal.sym(U32, Laws.rdN(U32, d, o2, k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), Laws.rd_at(U32, Array.new(U32, K.Kernel.depth_for(n), 0), k)), cell2) : {Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) == _ : U32};
     %Equal.sym(U32, Laws.rd_at(U32, Array.new(U32, K.Kernel.depth_for(n), 0), k), 0, PF.rd_at_new(U32, K.Kernel.depth_for(n), 0, k)) : {Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), 0) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, a, k), _) : U32};
     {==}))

def pf4b_c(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool}, wf: Laws.WFArray(U32, d, a),
  wa: &a1: Array<U32> -> &a2: Array<U32> -> &a3: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>} & {a3 == a : Array<U32>},
  wm: &m1: Array<U32> -> &m2: Array<U32> -> &m3: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>} & {m3 == m : Array<U32>})
  -> {Laws.ccell(Laws.z1_col(V.Eval.fz.z0b(V.PFill{D.SU32{0}}, C.CU32{n, d, C.Mask{m}, a})), k) == Laws.ccell(Laws.res_col(V.Eval.fill(C.CU32{n, d, C.Mask{m}, a}, V.Eval.const_col(D.SU32{0}, D.TU32{}, n))), k) : D.Scalar}:
  (a1, a2, a3, +ea1, ea2, ea3) = wa
  (m1, m2, m3, em1, em2, em3) = wm
  pf4b_k(n, d, m, a, k,
    (%ea3 : {Laws.ccell(Laws.z1_col(V.Eval.fz.dm.w(D.TU32{}, n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, _, m, 0))), k) == D.SU32{Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, _, m, 0)), k)} : D.Scalar};
     %em3 : {Laws.ccell(Laws.z1_col(V.Eval.fz.dm.w(D.TU32{}, n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a3, _, 0))), k) == D.SU32{Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a3, _, 0)), k)} : D.Scalar};
     dmw_cell(n, d, k, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a3, m3, 0))),
    (%ea2 : {Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, _, m, 0)), k) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), Laws.rd_at(U32, _, k), 0) : U32};
     %em2 : {Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, a2, _, 0)), k) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, _, k), 0), Laws.rd_at(U32, a2, k), 0) : U32};
     PF.zb_cell(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), d, n, a2, m2, 0, k, fits, hk)),
    (%ea1 : PI.CHW(~U32, n, d, m, _, Array.new(U32, K.Kernel.depth_for(n), 0), k); %em1 : PI.CHW(~U32, n, d, _, a1, Array.new(U32, K.Kernel.depth_for(n), 0), k); PI.choose_w(~U32, n, d, m1, a1, Array.new(U32, K.Kernel.depth_for(n), 0), k, (%Equal.sym(Array<U32>, a1, a, ea1) : Laws.WFArray(U32, d, _); wf), fits, hk)))

def Laws.peep_f4_borrow_cell(n, d, m, a, k, wf, fits, hk):
  pf4b_c(n, d, m, a, k, fits, hk, wf, PF.clone3(U32, a), PF.clone3(U32, m))

# ---- post-review B1: the masked f32 neg (Eval.un, the producer whose null slot broke F4's premise) ------

def Laws.un_neg_f32(n, d, m, x):
  %Equal.sym(K.ZB<F32, U32, F32>, K.Kernel.zipb.go(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), U32.to_nat(n), 0, Array.new(F32, d, 0.0), Array.get(F32, x, 0), Array.get(U32, m, 0)), K.ZB{K.Kernel.zip.go(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), U32.to_nat(n), 0, Array.new(F32, d, 0.0), Array.get(F32, x, 0), Array.get(U32, m, 0)), x, m}, PF.zb_sim(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), U32.to_nat(n), 0, Array.new(F32, d, 0.0), x, m)) : {Done{V.Eval.un.mf(n, d, _)} == Done{C.CF32{n, d, C.Mask{m}, K.Kernel.zip(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x, m, 0.0)}} : E.ResT(C.Column)}
  {==}

# the f32 data of Eval.un.mf's column is the zipb record's output
def mfd(+n: U32, +d: Nat, r: K.ZB<F32, U32, F32>) -> {Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, r)})) == Laws.zb_o(F32, U32, F32, r) : Array<F32>}:
  match r:
    case K.ZB{o, x, m}:
      {==}

def unc_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<F32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wx: &x1: Array<F32> -> &x2: Array<F32> -> {x1 == x : Array<F32>} & {x2 == x : Array<F32>}, wm: &m1: Array<U32> -> &m2: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>})
  -> {Laws.rd_at(F32, Laws.fdata(Laws.res_col(V.Eval.un(X.Neg{}, C.CF32{n, d, C.Mask{m}, x}))), k) == Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.neg(Laws.rd_at(F32, x, k)), 0.0) : F32}:
  (x1, x2, ex1, ex2) = wx
  (m1, m2, em1, em2) = wm
  %Equal.sym(Array<F32>, Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x, m, 0.0))})), Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x, m, 0.0)),
    (%ex1 : {Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, _, m, 0.0))})) == Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, _, m, 0.0)) : Array<F32>};
     %em1 : {Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x1, _, 0.0))})) == Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x1, _, 0.0)) : Array<F32>};
     mfd(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x1, m1, 0.0)))) : {Laws.rd_at(F32, _, k) == Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.neg(Laws.rd_at(F32, x, k)), 0.0) : F32}
  %ex2 : {Laws.rd_at(F32, Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, _, m, 0.0)), k) == Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.neg(Laws.rd_at(F32, _, k)), 0.0) : F32}
  %em2 : {Laws.rd_at(F32, Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x2, _, 0.0)), k) == Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, _, k), 0), F32.neg(Laws.rd_at(F32, x2, k)), 0.0) : F32}
  PF.zb_cell(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), d, n, x2, m2, 0.0, k, fits, hk)

def Laws.un_neg_f32_cell(n, d, m, x, k, fits, hk):
  unc_k(n, d, m, x, k, fits, hk, PC.clone_eq(F32, x), PC.clone_eq(U32, m))

def Laws.un_neg_f32_null(n, d, m, x, k, fits, hk, hm):
  %Equal.sym(F32, Laws.rd_at(F32, Laws.fdata(Laws.res_col(V.Eval.un(X.Neg{}, C.CF32{n, d, C.Mask{m}, x}))), k), Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.neg(Laws.rd_at(F32, x, k)), 0.0), Laws.un_neg_f32_cell(n, d, m, x, k, fits, hk)) : {_ == 0.0 : F32}
  %Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(F32, U32.is_ne(_, 0), F32.neg(Laws.rd_at(F32, x, k)), 0.0) == 0.0 : F32}
  {==}

# the same cell for any masked f32 template g (abs, sqrt) and, through Eval.un.mi, any word template
def ucf_k(~g: F32 -> U32 -> F32, +n: U32, +d: Nat, -m: Array<U32>, -x: Array<F32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wx: &x1: Array<F32> -> &x2: Array<F32> -> {x1 == x : Array<F32>} & {x2 == x : Array<F32>}, wm: &m1: Array<U32> -> &m2: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>})
  -> {Laws.rd_at(F32, Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x, m, 0.0))})), k) == g(Laws.rd_at(F32, x, k), Laws.rd_at(U32, m, k)) : F32}:
  (x1, x2, ex1, ex2) = wx
  (m1, m2, em1, em2) = wm
  %Equal.sym(Array<F32>, Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x, m, 0.0))})), Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x, m, 0.0)),
    (%ex1 : {Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, _, m, 0.0))})) == Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, _, m, 0.0)) : Array<F32>};
     %em1 : {Laws.fdata(Laws.res_col(Done{V.Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x1, _, 0.0))})) == Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x1, _, 0.0)) : Array<F32>};
     mfd(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x1, m1, 0.0)))) : {Laws.rd_at(F32, _, k) == g(Laws.rd_at(F32, x, k), Laws.rd_at(U32, m, k)) : F32}
  %ex2 : {Laws.rd_at(F32, Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, _, m, 0.0)), k) == g(Laws.rd_at(F32, _, k), Laws.rd_at(U32, m, k)) : F32}
  %em2 : {Laws.rd_at(F32, Laws.zb_o(F32, U32, F32, K.Kernel.zipb(~F32, ~U32, ~F32, ~g, n, d, x2, _, 0.0)), k) == g(Laws.rd_at(F32, x2, k), Laws.rd_at(U32, _, k)) : F32}
  PF.zb_cell(~F32, ~U32, ~F32, ~g, d, n, x2, m2, 0.0, k, fits, hk)

def mid(+n: U32, +d: Nat, r: K.ZB<U32, U32, U32>) -> {Laws.wdata(Laws.res_col(Done{V.Eval.un.mi(n, d, r)})) == Laws.zb_o(U32, U32, U32, r) : Array<U32>}:
  match r:
    case K.ZB{o, x, m}:
      {==}

def uci_k(~g: U32 -> U32 -> U32, +n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wx: &x1: Array<U32> -> &x2: Array<U32> -> {x1 == x : Array<U32>} & {x2 == x : Array<U32>}, wm: &m1: Array<U32> -> &m2: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>})
  -> {Laws.rd_at(U32, Laws.wdata(Laws.res_col(Done{V.Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x, m, 0))})), k) == g(Laws.rd_at(U32, x, k), Laws.rd_at(U32, m, k)) : U32}:
  (x1, x2, ex1, ex2) = wx
  (m1, m2, em1, em2) = wm
  %Equal.sym(Array<U32>, Laws.wdata(Laws.res_col(Done{V.Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x, m, 0))})), Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x, m, 0)),
    (%ex1 : {Laws.wdata(Laws.res_col(Done{V.Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, _, m, 0))})) == Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, _, m, 0)) : Array<U32>};
     %em1 : {Laws.wdata(Laws.res_col(Done{V.Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x1, _, 0))})) == Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x1, _, 0)) : Array<U32>};
     mid(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x1, m1, 0)))) : {Laws.rd_at(U32, _, k) == g(Laws.rd_at(U32, x, k), Laws.rd_at(U32, m, k)) : U32}
  %ex2 : {Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, _, m, 0)), k) == g(Laws.rd_at(U32, _, k), Laws.rd_at(U32, m, k)) : U32}
  %em2 : {Laws.rd_at(U32, Laws.zb_o(U32, U32, U32, K.Kernel.zipb(~U32, ~U32, ~U32, ~g, n, d, x2, _, 0)), k) == g(Laws.rd_at(U32, x2, k), Laws.rd_at(U32, _, k)) : U32}
  PF.zb_cell(~U32, ~U32, ~U32, ~g, d, n, x2, m2, 0, k, fits, hk)

def Laws.un_abs_f32_null(n, d, m, x, k, fits, hk, hm):
  %Equal.sym(F32, Laws.rd_at(F32, Laws.fdata(Laws.res_col(V.Eval.un(X.Abs{}, C.CF32{n, d, C.Mask{m}, x}))), k), Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.abs(Laws.rd_at(F32, x, k)), 0.0), ucf_k(~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.abs(w), 0.0)), n, d, m, x, k, fits, hk, PC.clone_eq(F32, x), PC.clone_eq(U32, m))) : {_ == 0.0 : F32}
  %Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(F32, U32.is_ne(_, 0), F32.abs(Laws.rd_at(F32, x, k)), 0.0) == 0.0 : F32}
  {==}

def Laws.un_sqrt_f32_null(n, d, m, x, k, fits, hk, hm):
  %Equal.sym(F32, Laws.rd_at(F32, Laws.fdata(Laws.res_col(V.Eval.un(X.Sqrt{}, C.CF32{n, d, C.Mask{m}, x}))), k), Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.sqrt(Laws.rd_at(F32, x, k)), 0.0), ucf_k(~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.sqrt(w), 0.0)), n, d, m, x, k, fits, hk, PC.clone_eq(F32, x), PC.clone_eq(U32, m))) : {_ == 0.0 : F32}
  %Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(F32, U32.is_ne(_, 0), F32.sqrt(Laws.rd_at(F32, x, k)), 0.0) == 0.0 : F32}
  {==}

def Laws.un_neg_i32_null(n, d, m, x, k, fits, hk, hm):
  %Equal.sym(U32, Laws.rd_at(U32, Laws.wdata(Laws.res_col(V.Eval.un(X.Neg{}, C.CI32{n, d, C.Mask{m}, x}))), k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), U32.sub(0, Laws.rd_at(U32, x, k)), 0), uci_k(~(w => k => Bool.pick(U32, U32.is_ne(k, 0), U32.sub(0, w), 0)), n, d, m, x, k, fits, hk, PC.clone_eq(U32, x), PC.clone_eq(U32, m))) : {_ == 0 : U32}
  %Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(U32, U32.is_ne(_, 0), U32.sub(0, Laws.rd_at(U32, x, k)), 0) == 0 : U32}
  {==}

def Laws.un_abs_i32_null(n, d, m, x, k, fits, hk, hm):
  %Equal.sym(U32, Laws.rd_at(U32, Laws.wdata(Laws.res_col(V.Eval.un(X.Abs{}, C.CI32{n, d, C.Mask{m}, x}))), k), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, k), 0), D.I32.mag(D.I32{Laws.rd_at(U32, x, k)}), 0), uci_k(~(w => k => Bool.pick(U32, U32.is_ne(k, 0), D.I32.mag(D.I32{w}), 0)), n, d, m, x, k, fits, hk, PC.clone_eq(U32, x), PC.clone_eq(U32, m))) : {_ == 0 : U32}
  %Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(U32, U32.is_ne(_, 0), D.I32.mag(D.I32{Laws.rd_at(U32, x, k)}), 0) == 0 : U32}
  {==}

def Laws.un_neg_f32_valid(n, d, m, x, k, fits, hk, hm):
  %Equal.sym(F32, Laws.rd_at(F32, Laws.fdata(Laws.res_col(V.Eval.un(X.Neg{}, C.CF32{n, d, C.Mask{m}, x}))), k), Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, k), 0), F32.neg(Laws.rd_at(F32, x, k)), 0.0), Laws.un_neg_f32_cell(n, d, m, x, k, fits, hk)) : {_ == F32.neg(Laws.rd_at(F32, x, k)) : F32}
  %Equal.sym(Bool, U32.is_ne(Laws.rd_at(U32, m, k), 0), True{}, hm) : {Bool.pick(F32, _, F32.neg(Laws.rd_at(F32, x, k)), 0.0) == F32.neg(Laws.rd_at(F32, x, k)) : F32}
  {==}

# ---- F2 masked: the fused cell against Eval.bin's (vand + zip + fix) ------------------------------------
# The fused column (peep_f2_mask_back) holds zipv's value output O under mask_and; Eval.bin's is
# Eval.fix of the zip Z under the same mask_and, i.e. Kernel.mask_data's output (o2, mb2) over Z (well
# formed: zip_go) with mb2 == mask_and (mask_data_w); zipv_unfused is rd(O, k) == rd(fst(mask_data(Z,
# ..)), k). Each lemma runs on its own clones of the four arrays, transported back (`%e`).

def pf2m_back(+n: U32, +d: Nat, +d2: Nat, -a: Array<U32>, -ma: Array<U32>, -b: Array<U32>, -mb: Array<U32>, a1: Array<U32>, ea: {a1 == a : Array<U32>}, ma1: Array<U32>, ema: {ma1 == ma : Array<U32>}, b1: Array<U32>, eb: {b1 == b : Array<U32>}, mb1: Array<U32>, emb: {mb1 == mb : Array<U32>})
  -> {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}:
  %ea : {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, _}, C.CU32{n, d2, C.Mask{mb}, b}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, _, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, _}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}
  %ema : {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{_}, a1}, C.CU32{n, d2, C.Mask{mb}, b}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, _, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a1, _, b, mb, 0))}}, C.CU32{n, d, C.Mask{_}, a1}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}
  %eb : {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma1}, a1}, C.CU32{n, d2, C.Mask{mb}, _}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma1, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a1, ma1, _, mb, 0))}}, C.CU32{n, d, C.Mask{ma1}, a1}, C.CU32{n, d2, C.Mask{mb}, _}} : V.Z2R}
  %emb : {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma1}, a1}, C.CU32{n, d2, C.Mask{_}, b1}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma1, _)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a1, ma1, b1, _, 0))}}, C.CU32{n, d, C.Mask{ma1}, a1}, C.CU32{n, d2, C.Mask{_}, b1}} : V.Z2R}
  Laws.peep_f2_mask_back(n, d, d2, a1, ma1, b1, mb1)

def pf2m_unf(+n: U32, +d: Nat, -a: Array<U32>, -ma: Array<U32>, -b: Array<U32>, -mb: Array<U32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool}, a2: Array<U32>, ea: {a2 == a : Array<U32>}, ma2: Array<U32>, ema: {ma2 == ma : Array<U32>}, b2: Array<U32>, eb: {b2 == b : Array<U32>}, mb2: Array<U32>, emb: {mb2 == mb : Array<U32>})
  -> {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0), K.Kernel.mask_and(n, d, ma, mb), 0)), k) : U32}:
  %ea : {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, _, ma, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, _, b, 0), K.Kernel.mask_and(n, d, ma, mb), 0)), k) : U32}
  %ema : {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a2, _, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a2, b, 0), K.Kernel.mask_and(n, d, _, mb), 0)), k) : U32}
  %eb : {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a2, ma2, _, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a2, _, 0), K.Kernel.mask_and(n, d, ma2, mb), 0)), k) : U32}
  %emb : {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a2, ma2, b2, _, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a2, b2, 0), K.Kernel.mask_and(n, d, ma2, _), 0)), k) : U32}
  Laws.zipv_unfused(d, n, a2, ma2, b2, mb2, 0, k, fits, hk)

# the zip Z as a well-formed array o (zip_go's result), stated over the originals
def pf2m_zk(+n: U32, +d: Nat, -a: Array<U32>, -b: Array<U32>, -a3: Array<U32>, ea: {a3 == a : Array<U32>}, -b3: Array<U32>, eb: {b3 == b : Array<U32>},
  w: &o: Array<U32> -> {K.Kernel.zip.go(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a3, 0), Array.get(U32, b3, 0)) == o : Array<U32>} & PC.ZRes(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), d, a3, b3, o, Laws.addn(0, U32.to_nat(n))))
  -> &o: Array<U32> -> {K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0) == o : Array<U32>} & Laws.WFArray(U32, d, o):
  (o, e, wf, spec) = w
  (o, (%ea : {K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, _, b, 0) == o : Array<U32>}; %eb : {K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a3, _, 0) == o : Array<U32>}; e), wf)

def pf2m_zip(+n: U32, +d: Nat, -a: Array<U32>, -b: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, a3: Array<U32>, ea: {a3 == a : Array<U32>}, b3: Array<U32>, eb: {b3 == b : Array<U32>})
  -> &o: Array<U32> -> {K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0) == o : Array<U32>} & Laws.WFArray(U32, d, o):
  pf2m_zk(n, d, a, b, a3, ea, b3, eb, PC.zip_go(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), U32.to_nat(n), 0, d, a3, b3, Array.new(U32, d, 0), Laws.wf_new(U32, d, 0), B.room_from(d, n, fits))(PC.zhyp0(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), d, a3, b3, Array.new(U32, d, 0))))

# mask_data over o under mask_and as a pair (o2, mb2), mb2 the mask (mask_data_w), over the originals
def pf2m_mdk(+n: U32, +d: Nat, -ma: Array<U32>, -mb: Array<U32>, -o: Array<U32>, +k: U32, -ma3: Array<U32>, +ema: {ma3 == ma : Array<U32>}, -mb3: Array<U32>, +emb: {mb3 == mb : Array<U32>},
  w: PI.MDW(~U32, n, d, o, K.Kernel.mask_and(n, d, ma3, mb3), 0, k))
  -> &o2: Array<U32> -> &mb2: Array<U32> -> {K.Kernel.mask_data(~U32, n, o, K.Kernel.mask_and(n, d, ma, mb), 0) == (o2, mb2) : Array<U32> & Array<U32>} & {mb2 == K.Kernel.mask_and(n, d, ma, mb) : Array<U32>}:
  (o2, mb2, e1, e2, wf2, c) = w
  (o2, mb2,
   (%ema : {K.Kernel.mask_data(~U32, n, o, K.Kernel.mask_and(n, d, _, mb), 0) == (o2, mb2) : Array<U32> & Array<U32>}; %emb : {K.Kernel.mask_data(~U32, n, o, K.Kernel.mask_and(n, d, ma3, _), 0) == (o2, mb2) : Array<U32> & Array<U32>}; e1),
   (%ema : {mb2 == K.Kernel.mask_and(n, d, _, mb) : Array<U32>}; %emb : {mb2 == K.Kernel.mask_and(n, d, ma3, _) : Array<U32>}; e2))

def pf2m_j(+n: U32, +d: Nat, +d2: Nat, -a: Array<U32>, -ma: Array<U32>, -b: Array<U32>, -mb: Array<U32>, +k: U32, eback: {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}, eunf: {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0), K.Kernel.mask_and(n, d, ma, mb), 0)), k) : U32}, -o: Array<U32>, +eZ: {K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0) == o : Array<U32>},
  w: &o2: Array<U32> -> &mb2: Array<U32> -> {K.Kernel.mask_data(~U32, n, o, K.Kernel.mask_and(n, d, ma, mb), 0) == (o2, mb2) : Array<U32> & Array<U32>} & {mb2 == K.Kernel.mask_and(n, d, ma, mb) : Array<U32>})
  -> {Laws.ccell(Laws.z2_col(V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Add{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) : D.Scalar}:
  (o2, mb2, +emd, emb2) = w
  %Equal.sym(V.Z2R, V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}), V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}}, eback) : {Laws.ccell(Laws.z2_col(_), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Add{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) : D.Scalar}
  %Equal.sym(Array<U32>, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0), o, eZ) : {Laws.ccell(C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}, k) == Laws.ccell(V.Eval.fix.w2(D.TU32{}, n, d, K.Kernel.mask_data(~U32, n, _, K.Kernel.mask_and(n, d, ma, mb), 0)), k) : D.Scalar}
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, o, K.Kernel.mask_and(n, d, ma, mb), 0), (o2, mb2), emd) : {Laws.ccell(C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}, k) == Laws.ccell(V.Eval.fix.w2(D.TU32{}, n, d, _), k) : D.Scalar}
  %Equal.sym(Array<U32>, mb2, K.Kernel.mask_and(n, d, ma, mb), emb2) : {Laws.ccell(C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}, k) == Laws.ccell(C.CU32{n, d, C.Mask{_}, o2}, k) : D.Scalar}
  Equal.cong(U32, D.Scalar, x => Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, K.Kernel.mask_and(n, d, ma, mb), k), 0), D.SU32{x}, D.SNull{}), Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), k), Laws.rd_at(U32, o2, k),
    (%emd : {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, _), k) : U32};
     %eZ : {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, _, K.Kernel.mask_and(n, d, ma, mb), 0)), k) : U32};
     eunf))

def pf2m_i(+n: U32, +d: Nat, +d2: Nat, -a: Array<U32>, -ma: Array<U32>, -b: Array<U32>, -mb: Array<U32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool}, eback: {V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}) == V.Z2R{Some{C.CU32{n, d, C.Mask{K.Kernel.mask_and(n, d, ma, mb)}, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0))}}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b}} : V.Z2R}, eunf: {Laws.rd_at(U32, Laws.zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, ma, b, mb, 0)), k) == Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0), K.Kernel.mask_and(n, d, ma, mb), 0)), k) : U32}, ma3: Array<U32>, ema: {ma3 == ma : Array<U32>}, mb3: Array<U32>, emb: {mb3 == mb : Array<U32>},
  wz: &o: Array<U32> -> {K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0) == o : Array<U32>} & Laws.WFArray(U32, d, o))
  -> {Laws.ccell(Laws.z2_col(V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Add{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) : D.Scalar}:
  (o, +eZ, wfo) = wz
  pf2m_j(n, d, d2, a, ma, b, mb, k, eback, eunf, o, eZ, pf2m_mdk(n, d, ma, mb, o, k, ma3, ema, mb3, emb, PI.mask_data_w(~U32, n, d, o, K.Kernel.mask_and(n, d, ma3, mb3), 0, k, wfo, fits, hk)))

def pf2m(+n: U32, +d: Nat, +d2: Nat, -a: Array<U32>, -ma: Array<U32>, -b: Array<U32>, -mb: Array<U32>, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wa: &x1: Array<U32> -> &x2: Array<U32> -> &x3: Array<U32> -> {x1 == a : Array<U32>} & {x2 == a : Array<U32>} & {x3 == a : Array<U32>}, wma: &x1: Array<U32> -> &x2: Array<U32> -> &x3: Array<U32> -> {x1 == ma : Array<U32>} & {x2 == ma : Array<U32>} & {x3 == ma : Array<U32>}, wb: &x1: Array<U32> -> &x2: Array<U32> -> &x3: Array<U32> -> {x1 == b : Array<U32>} & {x2 == b : Array<U32>} & {x3 == b : Array<U32>}, wmb: &x1: Array<U32> -> &x2: Array<U32> -> &x3: Array<U32> -> {x1 == mb : Array<U32>} & {x2 == mb : Array<U32>} & {x3 == mb : Array<U32>})
  -> {Laws.ccell(Laws.z2_col(V.Eval.fz.z2(X.Add{}, V.PNone{}, V.PNone{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) == Laws.ccell(Laws.res_col(V.Eval.bin(X.Add{}, C.CU32{n, d, C.Mask{ma}, a}, C.CU32{n, d2, C.Mask{mb}, b})), k) : D.Scalar}:
  (a1, a2, a3, ea1, ea2, ea3) = wa
  (ma1, ma2, ma3, ema1, ema2, ema3) = wma
  (b1, b2, b3, eb1, eb2, eb3) = wb
  (mb1, mb2, mb3, emb1, emb2, emb3) = wmb
  pf2m_i(n, d, d2, a, ma, b, mb, k, fits, hk, pf2m_back(n, d, d2, a, ma, b, mb, a1, ea1, ma1, ema1, b1, eb1, mb1, emb1), pf2m_unf(n, d, a, ma, b, mb, k, fits, hk, a2, ea2, ma2, ema2, b2, eb2, mb2, emb2), ma3, ema3, mb3, emb3, pf2m_zip(n, d, a, b, fits, a3, ea3, b3, eb3))

def Laws.peep_f2_mask(n, d, d2, a, ma, b, mb, k, fits, hk):
  pf2m(n, d, d2, a, ma, b, mb, k, fits, hk, PF.clone3(U32, a), PF.clone3(U32, ma), PF.clone3(U32, b), PF.clone3(U32, mb))

# ---- F5's selector -----------------------------------------------------------------------------------------

def Laws.peep_f5_plan(lit):
  {==}

def Laws.peep_f5_or(lit):
  {==}

def Laws.peep_f5_dtype(lit):
  {==}
