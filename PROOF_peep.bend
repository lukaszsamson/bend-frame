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

def Laws.peep_f4_not_noop(n, d, m, a, k, hm, ha):
  ((%Equal.sym(U32, Laws.rd_at(U32, m, k), 0, hm) : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SU32{Laws.rd_at(U32, a, k)}, D.SNull{}) == D.SNull{} : D.Scalar}; {==}),
   (%Equal.sym(U32, Laws.rd_at(U32, a, k), 0, ha) : {D.SU32{_} == D.SU32{0} : D.Scalar}; {==}))

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
