# PROOF_sorthead.bend -- proofs of LAWS.bend section 17 (v0.2 T3.4): the Sort + Head bounded
# gather (src/sort.bend Sort.frame_head) and the physical runner step (src/exec.bend
# Exec.run_phys) show exactly what Sort.frame then Frame.head / Exec.run_pure show.
#
# Shape of the development:
#   * leaf lemmas: `vg_w` (Valid.gather) and `cg_w` (Column.gather) as witnesses: the gathered
#     column, the permutation back (equal to the input), and what `Laws.cobs` sees of the result
#     and of its head, from the section 11 gather loop proofs (PST.tgather_w at U32 / F32,
#     Laws.strs_gather_cells for Str). A forall over rows is affine, so the cell equation at the
#     one row k of the claim is taken once and then shared (it is an equation: duplicable).
#   * `gc`: Sort.gcols over the columns with two cuts (min(n, h) and h) in lockstep, the column
#     cloned (PV.clone_w) for the two gathers, the permutation cloned once (PC.clone_eq) at the
#     start; the accumulators are related by a Data equation over `lobs` / `lobsh`, and the
#     final List.reverse is commuted through the observation (`lr`, `lrh`).
#   * `core`: Sort.gather_head against Frame.head(Sort.gather): the height guard as a parameter.
#   * `ch`: the key chain of Sort.frame_head against Sort.frame (Frame.info, Sort.miss,
#     Sort.argsort, gather), for an arbitrary observation context (C1, C2) given how the context
#     treats a failure (hf) and a frame pair (hd); law sort_head_frame is the identity context,
#     sort_head_run the runner's final steps (push, IHead, fin) over x's code.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/sort.bend as O
import ./src/plan.bend as P
import ./src/exec.bend as Q
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B
import ./PROOF_contents.bend as PC
import ./PROOF_eval.bend as PV
import ./PROOF_strs.bend as PST
import ./PROOF_exec.bend as PE

# ---- comparisons ------------------------------------------------------------------------------

def lt_trans_u(a: U32, b: U32, c: U32, h1: {U32.is_lt(a, b) == True{} : Bool}, h2: {U32.is_lt(b, c) == True{} : Bool}) -> {U32.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      %Equal.sym(Cmp, Word.cmp(32n, x, z), LT{}, L.word_lt_trans(32n, x, y, z, B.is_lt_lt(Word.cmp(32n, x, y), h1), B.is_lt_lt(Word.cmp(32n, y, z), h2))) : {Cmp.is_lt(_) == True{} : Bool}
      {==}

def lt_min_k(+k: U32, +x: Word(32n), +y: Word(32n), c: Bool, e: {U32.is_lt(U32{x}, U32{y}) == c : Bool}, hk: {U32.is_lt(k, Bool.pick(U32, c, U32{x}, U32{y})) == True{} : Bool}) -> {U32.is_lt(k, U32{y}) == True{} : Bool}:
  match c:
    case True{}:
      lt_trans_u(k, U32{x}, U32{y}, hk, e)
    case False{}:
      hk

# k < min(j, n) gives k < n
def lt_min_r(+k: U32, j: U32, n: U32, hk: {U32.is_lt(k, U32.min(j, n)) == True{} : Bool}) -> {U32.is_lt(k, n) == True{} : Bool}:
  match j n:
    case U32{+x} U32{+y}:
      lt_min_k(k, x, y, U32.is_lt(U32{x}, U32{y}), {==}, hk)

# ---- the gathered validity ------------------------------------------------------------------------

# Valid.gather's result: the witness, perm back, the bit of row i the source bit of row perm[i]
def VGW(-v: C.Valid, -perm: Array<U32>, +n: U32, +d: Nat) -> Type:
  &v2: C.Valid -> &pm: Array<U32> -> {C.Valid.gather(v, perm, n, d) == (v2, pm) : C.Valid & Array<U32>} & {pm == perm : Array<U32>} & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(v, Laws.rd_at(U32, perm, i)) : Bool})

def vg_mask_k(-m: Array<U32>, -perm: Array<U32>, +n: U32, +d: Nat, -o: Array<U32>, pm: Array<U32>, eq: {K.Kernel.gather(~U32, n, d, m, perm, 0) == (o, pm) : Array<U32> & Array<U32>}, epm: {pm == perm : Array<U32>}, cells: @k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == Laws.rd_at(U32, m, Laws.rd_at(U32, perm, k)) : U32},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, d, b) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32})) -> VGW(C.Mask{m}, perm, n, d):
  (o2, +eo2, wf2, conv) = w
  (C.Mask{o2}, pm, (%Equal.sym(Array<U32>, o2, o, eo2) : {C.Valid.gather(C.Mask{m}, perm, n, d) == (C.Mask{_}, pm) : C.Valid & Array<U32>}; %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, n, d, m, perm, 0), (o, pm), eq) : {C.Valid.gather.k(_) == (C.Mask{o}, pm) : C.Valid & Array<U32>}; {==}), epm, +i => hi => (%Equal.sym(Array<U32>, o2, o, eo2) : {U32.is_ne(Laws.rd_at(U32, _, i), 0) == U32.is_ne(Laws.rd_at(U32, m, Laws.rd_at(U32, perm, i)), 0) : Bool}; Equal.cong(U32, Bool, x => U32.is_ne(x, 0), Laws.rd_at(U32, o, i), Laws.rd_at(U32, m, Laws.rd_at(U32, perm, i)), Equal.trans(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), Laws.rd_at(U32, m, Laws.rd_at(U32, perm, i)), conv(i), cells(i, hi)))))

def vg_mask(-m: Array<U32>, -perm: Array<U32>, +n: U32, +d: Nat, w: PST.TGW(~U32, d, n, m, perm, 0)) -> VGW(C.Mask{m}, perm, n, d):
  (o, pm, eq, res) = w
  (epm, wfo, cells) = res
  vg_mask_k(m, perm, n, d, o, pm, eq, epm, cells, PST.rd_all(U32, d, o, wfo))

def vg_w(v: C.Valid, perm: Array<U32>, +n: U32, +d: Nat, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}) -> VGW(v, perm, n, d):
  match v:
    case C.AllValid{}:
      (C.AllValid{}, perm, {==}, {==}, +i => hi => {==})
    case C.Mask{m}:
      vg_mask(m, perm, n, d, PST.tgather_w(~U32, d, n, m, perm, 0, fits))

# ---- the gathered column: what cobs sees of it, and of its head ------------------------------------

# Column.gather(col, perm, nn)'s result: the witness, perm back, and what cobs sees at row k of it
# and of its head j: col's dtype, the length (nn, min(j, nn)), and the cell of row perm[k] of col
# when k is a row
def CGW(-col: C.Column, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32) -> Type:
  &c2: C.Column -> &pm: Array<U32> -> {C.Column.gather(col, perm, nn) == (c2, pm) : C.Column & Array<U32>} & {pm == perm : Array<U32>} & {Laws.cobs(c2, k) == Laws.CObs{Laws.cdtype(col), nn, Bool.pick(D.Scalar, U32.is_lt(k, nn), Laws.ccell(col, Laws.rd_at(U32, perm, k)), D.SNull{})} : Laws.CObs} & {Laws.cobs(C.Column.head(c2, j), k) == Laws.CObs{Laws.cdtype(col), U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), Laws.ccell(col, Laws.rd_at(U32, perm, k)), D.SNull{})} : Laws.CObs}

# the two observations (itself; after a head j) of a column of nn rows whose cell at k is x, against
# one whose cell is y, when x == y holds as soon as k is a row
def PK2(+t: D.DType, +k: U32, +j: U32, +nn: U32, -x: D.Scalar, -y: D.Scalar) -> Type:
  {Laws.CObs{t, nn, Bool.pick(D.Scalar, U32.is_lt(k, nn), x, D.SNull{})} == Laws.CObs{t, nn, Bool.pick(D.Scalar, U32.is_lt(k, nn), y, D.SNull{})} : Laws.CObs} & {Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), x, D.SNull{})} == Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), y, D.SNull{})} : Laws.CObs}

def pk2_hf(+t: D.DType, +k: U32, +j: U32, +nn: U32, -x: D.Scalar, -y: D.Scalar, b2: Bool, eb2: {U32.is_lt(k, U32.min(j, nn)) == b2 : Bool}, +eb: {U32.is_lt(k, nn) == False{} : Bool})
  -> {Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), x, D.SNull{})} == Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), y, D.SNull{})} : Laws.CObs}:
  match b2:
    case True{}:
      Empty.absurd({Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), x, D.SNull{})} == Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), y, D.SNull{})} : Laws.CObs}, L.false_true(Equal.trans(Bool, False{}, U32.is_lt(k, nn), True{}, Equal.sym(Bool, U32.is_lt(k, nn), False{}, eb), lt_min_r(k, j, nn, eb2))))
    case False{}:
      %Equal.sym(Bool, U32.is_lt(k, U32.min(j, nn)), False{}, eb2) : {Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, _, x, D.SNull{})} == Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, _, y, D.SNull{})} : Laws.CObs}
      {==}

def pk2_t(+t: D.DType, +k: U32, +j: U32, +nn: U32, -x: D.Scalar, -y: D.Scalar, +e: {x == y : D.Scalar}) -> PK2(t, k, j, nn, x, y):
  (Equal.cong(D.Scalar, Laws.CObs, s => Laws.CObs{t, nn, Bool.pick(D.Scalar, U32.is_lt(k, nn), s, D.SNull{})}, x, y, e), Equal.cong(D.Scalar, Laws.CObs, s => Laws.CObs{t, U32.min(j, nn), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(j, nn)), s, D.SNull{})}, x, y, e))

def pk2(+t: D.DType, +k: U32, +j: U32, +nn: U32, -x: D.Scalar, -y: D.Scalar, b: Bool, +eb: {U32.is_lt(k, nn) == b : Bool}, hc: @_h: {U32.is_lt(k, nn) == True{} : Bool} -> {x == y : D.Scalar}) -> PK2(t, k, j, nn, x, y):
  match b:
    case True{}:
      pk2_t(t, k, j, nn, x, y, hc(eb))
    case False{}:
      (%Equal.sym(Bool, U32.is_lt(k, nn), False{}, eb) : {Laws.CObs{t, nn, Bool.pick(D.Scalar, _, x, D.SNull{})} == Laws.CObs{t, nn, Bool.pick(D.Scalar, _, y, D.SNull{})} : Laws.CObs}; {==}, pk2_hf(t, k, j, nn, x, y, U32.is_lt(k, U32.min(j, nn)), {==}, eb))

# CBool: the validity gathered (vg_w), the data gathered with the permutation that comes back
# (PST.tgather_w at U32), the output array handed back by rd_all (rd_at == rdN on it)
def cg_b.cell(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +k: U32, -v2: C.Valid, -o2: Array<U32>,
  vb: {Laws.vbit(v2, k) == Laws.vbit(valid, Laws.rd_at(U32, perm, k)) : Bool}, dv: {Laws.rd_at(U32, o2, k) == Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)) : U32})
  -> {Laws.ccell(C.CBool{nn, K.Kernel.depth_for(nn), v2, o2}, k) == Laws.ccell(C.CBool{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}:
  %Equal.sym(Bool, Laws.vbit(v2, k), Laws.vbit(valid, Laws.rd_at(U32, perm, k)), vb) : {Bool.pick(D.Scalar, _, D.SBool{U32.is_ne(Laws.rd_at(U32, o2, k), 0)}, D.SNull{}) == Laws.ccell(C.CBool{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), dv) : {Bool.pick(D.Scalar, Laws.vbit(valid, Laws.rd_at(U32, perm, k)), D.SBool{U32.is_ne(_, 0)}, D.SNull{}) == Laws.ccell(C.CBool{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  {==}

def cg_b.d(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, -o: Array<U32>, o2: Array<U32>, pm2: Array<U32>,
  +eo2: {o2 == o : Array<U32>}, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, etg: {K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0) == (o, pm2) : Array<U32> & Array<U32>}, epm1: {pm1 == perm : Array<U32>}, epm2: {pm2 == pm1 : Array<U32>},
  pk: PK2(D.TBool{}, k, j, nn, Laws.ccell(C.CBool{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CBool{len, depth, valid, data}, Laws.rd_at(U32, perm, k))))
  -> CGW(C.CBool{len, depth, valid, data}, perm, nn, j, k):
  (f1, f2) = pk
  (C.CBool{nn, K.Kernel.depth_for(nn), v2, o2}, pm2, (%Equal.sym(Array<U32>, o2, o, eo2) : {C.Column.gather(C.CBool{len, depth, valid, data}, perm, nn) == (C.CBool{nn, K.Kernel.depth_for(nn), v2, _}, pm2) : C.Column & Array<U32>}; %Equal.sym(C.Valid & Array<U32>, C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)), (v2, pm1), evg) : {C.Column.gather.c(C.CBool{len, depth, C.AllValid{}, data}, nn, K.Kernel.depth_for(nn), _) == (C.CBool{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0), (o, pm2), etg) : {C.Column.gather.d(v2, C.Column.out.w(D.TBool{}, nn, K.Kernel.depth_for(nn), _)) == (C.CBool{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; {==}), Equal.trans(Array<U32>, pm2, pm1, perm, epm2, epm1), f1, f2)

def cg_b.c(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  -o: Array<U32>, pm2: Array<U32>, etg: {K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0) == (o, pm2) : Array<U32> & Array<U32>}, epm2: {pm2 == pm1 : Array<U32>}, dcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.rdN(U32, K.Kernel.depth_for(nn), o, i) == Laws.rd_at(U32, data, Laws.rd_at(U32, pm1, i)) : U32},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, K.Kernel.depth_for(nn), b) & (@i: U32 -> {Laws.rd_at(U32, o, i) == Laws.rdN(U32, K.Kernel.depth_for(nn), o, i) : U32}))
  -> CGW(C.CBool{len, depth, valid, data}, perm, nn, j, k):
  (o2, +eo2, wf2, conv) = w
  cg_b.d(len, depth, valid, data, perm, nn, j, k, v2, pm1, o, o2, pm2, eo2, evg, etg, epm1, epm2, pk2(D.TBool{}, k, j, nn, Laws.ccell(C.CBool{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CBool{len, depth, valid, data}, Laws.rd_at(U32, perm, k)), U32.is_lt(k, nn), {==}, +hk => cg_b.cell(len, depth, valid, data, perm, nn, k, v2, o2, vcells(k, hk), Equal.trans(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, a, k), o2, o, eo2), Equal.trans(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), conv(k), Equal.trans(U32, Laws.rdN(U32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, pm1, k)), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), dcells(k, hk), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, data, Laws.rd_at(U32, a, k)), pm1, perm, epm1)))))))

def cg_b.b(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  w: PST.TGW(~U32, K.Kernel.depth_for(nn), nn, data, pm1, 0))
  -> CGW(C.CBool{len, depth, valid, data}, perm, nn, j, k):
  (o, pm2, etg, res) = w
  (epm2, wfo, dcells) = res
  cg_b.c(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, o, pm2, etg, epm2, dcells, PST.rd_all(U32, K.Kernel.depth_for(nn), o, wfo))

def cg_b.a(+len: U32, +depth: Nat, -valid: C.Valid, data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, +fits: {U32.is_le(nn, U32.shln(1, K.Kernel.depth_for(nn))) == True{} : Bool}, wv: VGW(valid, perm, nn, K.Kernel.depth_for(nn)))
  -> CGW(C.CBool{len, depth, valid, data}, perm, nn, j, k):
  (v2, pm1, evg, +epm1, vcells) = wv
  cg_b.b(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, PST.tgather_w(~U32, K.Kernel.depth_for(nn), nn, data, pm1, 0, fits))

# CU32: the validity gathered (vg_w), the data gathered with the permutation that comes back
# (PST.tgather_w at U32), the output array handed back by rd_all (rd_at == rdN on it)
def cg_u.cell(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +k: U32, -v2: C.Valid, -o2: Array<U32>,
  vb: {Laws.vbit(v2, k) == Laws.vbit(valid, Laws.rd_at(U32, perm, k)) : Bool}, dv: {Laws.rd_at(U32, o2, k) == Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)) : U32})
  -> {Laws.ccell(C.CU32{nn, K.Kernel.depth_for(nn), v2, o2}, k) == Laws.ccell(C.CU32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}:
  %Equal.sym(Bool, Laws.vbit(v2, k), Laws.vbit(valid, Laws.rd_at(U32, perm, k)), vb) : {Bool.pick(D.Scalar, _, D.SU32{Laws.rd_at(U32, o2, k)}, D.SNull{}) == Laws.ccell(C.CU32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), dv) : {Bool.pick(D.Scalar, Laws.vbit(valid, Laws.rd_at(U32, perm, k)), D.SU32{_}, D.SNull{}) == Laws.ccell(C.CU32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  {==}

def cg_u.d(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, -o: Array<U32>, o2: Array<U32>, pm2: Array<U32>,
  +eo2: {o2 == o : Array<U32>}, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, etg: {K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0) == (o, pm2) : Array<U32> & Array<U32>}, epm1: {pm1 == perm : Array<U32>}, epm2: {pm2 == pm1 : Array<U32>},
  pk: PK2(D.TU32{}, k, j, nn, Laws.ccell(C.CU32{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CU32{len, depth, valid, data}, Laws.rd_at(U32, perm, k))))
  -> CGW(C.CU32{len, depth, valid, data}, perm, nn, j, k):
  (f1, f2) = pk
  (C.CU32{nn, K.Kernel.depth_for(nn), v2, o2}, pm2, (%Equal.sym(Array<U32>, o2, o, eo2) : {C.Column.gather(C.CU32{len, depth, valid, data}, perm, nn) == (C.CU32{nn, K.Kernel.depth_for(nn), v2, _}, pm2) : C.Column & Array<U32>}; %Equal.sym(C.Valid & Array<U32>, C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)), (v2, pm1), evg) : {C.Column.gather.c(C.CU32{len, depth, C.AllValid{}, data}, nn, K.Kernel.depth_for(nn), _) == (C.CU32{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0), (o, pm2), etg) : {C.Column.gather.d(v2, C.Column.out.w(D.TU32{}, nn, K.Kernel.depth_for(nn), _)) == (C.CU32{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; {==}), Equal.trans(Array<U32>, pm2, pm1, perm, epm2, epm1), f1, f2)

def cg_u.c(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  -o: Array<U32>, pm2: Array<U32>, etg: {K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0) == (o, pm2) : Array<U32> & Array<U32>}, epm2: {pm2 == pm1 : Array<U32>}, dcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.rdN(U32, K.Kernel.depth_for(nn), o, i) == Laws.rd_at(U32, data, Laws.rd_at(U32, pm1, i)) : U32},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, K.Kernel.depth_for(nn), b) & (@i: U32 -> {Laws.rd_at(U32, o, i) == Laws.rdN(U32, K.Kernel.depth_for(nn), o, i) : U32}))
  -> CGW(C.CU32{len, depth, valid, data}, perm, nn, j, k):
  (o2, +eo2, wf2, conv) = w
  cg_u.d(len, depth, valid, data, perm, nn, j, k, v2, pm1, o, o2, pm2, eo2, evg, etg, epm1, epm2, pk2(D.TU32{}, k, j, nn, Laws.ccell(C.CU32{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CU32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)), U32.is_lt(k, nn), {==}, +hk => cg_u.cell(len, depth, valid, data, perm, nn, k, v2, o2, vcells(k, hk), Equal.trans(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, a, k), o2, o, eo2), Equal.trans(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), conv(k), Equal.trans(U32, Laws.rdN(U32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, pm1, k)), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), dcells(k, hk), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, data, Laws.rd_at(U32, a, k)), pm1, perm, epm1)))))))

def cg_u.b(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  w: PST.TGW(~U32, K.Kernel.depth_for(nn), nn, data, pm1, 0))
  -> CGW(C.CU32{len, depth, valid, data}, perm, nn, j, k):
  (o, pm2, etg, res) = w
  (epm2, wfo, dcells) = res
  cg_u.c(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, o, pm2, etg, epm2, dcells, PST.rd_all(U32, K.Kernel.depth_for(nn), o, wfo))

def cg_u.a(+len: U32, +depth: Nat, -valid: C.Valid, data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, +fits: {U32.is_le(nn, U32.shln(1, K.Kernel.depth_for(nn))) == True{} : Bool}, wv: VGW(valid, perm, nn, K.Kernel.depth_for(nn)))
  -> CGW(C.CU32{len, depth, valid, data}, perm, nn, j, k):
  (v2, pm1, evg, +epm1, vcells) = wv
  cg_u.b(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, PST.tgather_w(~U32, K.Kernel.depth_for(nn), nn, data, pm1, 0, fits))

# CI32: the validity gathered (vg_w), the data gathered with the permutation that comes back
# (PST.tgather_w at U32), the output array handed back by rd_all (rd_at == rdN on it)
def cg_i.cell(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +k: U32, -v2: C.Valid, -o2: Array<U32>,
  vb: {Laws.vbit(v2, k) == Laws.vbit(valid, Laws.rd_at(U32, perm, k)) : Bool}, dv: {Laws.rd_at(U32, o2, k) == Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)) : U32})
  -> {Laws.ccell(C.CI32{nn, K.Kernel.depth_for(nn), v2, o2}, k) == Laws.ccell(C.CI32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}:
  %Equal.sym(Bool, Laws.vbit(v2, k), Laws.vbit(valid, Laws.rd_at(U32, perm, k)), vb) : {Bool.pick(D.Scalar, _, D.SI32{D.I32{Laws.rd_at(U32, o2, k)}}, D.SNull{}) == Laws.ccell(C.CI32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), dv) : {Bool.pick(D.Scalar, Laws.vbit(valid, Laws.rd_at(U32, perm, k)), D.SI32{D.I32{_}}, D.SNull{}) == Laws.ccell(C.CI32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  {==}

def cg_i.d(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, -o: Array<U32>, o2: Array<U32>, pm2: Array<U32>,
  +eo2: {o2 == o : Array<U32>}, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, etg: {K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0) == (o, pm2) : Array<U32> & Array<U32>}, epm1: {pm1 == perm : Array<U32>}, epm2: {pm2 == pm1 : Array<U32>},
  pk: PK2(D.TI32{}, k, j, nn, Laws.ccell(C.CI32{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CI32{len, depth, valid, data}, Laws.rd_at(U32, perm, k))))
  -> CGW(C.CI32{len, depth, valid, data}, perm, nn, j, k):
  (f1, f2) = pk
  (C.CI32{nn, K.Kernel.depth_for(nn), v2, o2}, pm2, (%Equal.sym(Array<U32>, o2, o, eo2) : {C.Column.gather(C.CI32{len, depth, valid, data}, perm, nn) == (C.CI32{nn, K.Kernel.depth_for(nn), v2, _}, pm2) : C.Column & Array<U32>}; %Equal.sym(C.Valid & Array<U32>, C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)), (v2, pm1), evg) : {C.Column.gather.c(C.CI32{len, depth, C.AllValid{}, data}, nn, K.Kernel.depth_for(nn), _) == (C.CI32{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0), (o, pm2), etg) : {C.Column.gather.d(v2, C.Column.out.w(D.TI32{}, nn, K.Kernel.depth_for(nn), _)) == (C.CI32{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; {==}), Equal.trans(Array<U32>, pm2, pm1, perm, epm2, epm1), f1, f2)

def cg_i.c(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  -o: Array<U32>, pm2: Array<U32>, etg: {K.Kernel.gather(~U32, nn, K.Kernel.depth_for(nn), data, pm1, 0) == (o, pm2) : Array<U32> & Array<U32>}, epm2: {pm2 == pm1 : Array<U32>}, dcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.rdN(U32, K.Kernel.depth_for(nn), o, i) == Laws.rd_at(U32, data, Laws.rd_at(U32, pm1, i)) : U32},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, K.Kernel.depth_for(nn), b) & (@i: U32 -> {Laws.rd_at(U32, o, i) == Laws.rdN(U32, K.Kernel.depth_for(nn), o, i) : U32}))
  -> CGW(C.CI32{len, depth, valid, data}, perm, nn, j, k):
  (o2, +eo2, wf2, conv) = w
  cg_i.d(len, depth, valid, data, perm, nn, j, k, v2, pm1, o, o2, pm2, eo2, evg, etg, epm1, epm2, pk2(D.TI32{}, k, j, nn, Laws.ccell(C.CI32{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CI32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)), U32.is_lt(k, nn), {==}, +hk => cg_i.cell(len, depth, valid, data, perm, nn, k, v2, o2, vcells(k, hk), Equal.trans(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, a, k), o2, o, eo2), Equal.trans(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), conv(k), Equal.trans(U32, Laws.rdN(U32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(U32, data, Laws.rd_at(U32, pm1, k)), Laws.rd_at(U32, data, Laws.rd_at(U32, perm, k)), dcells(k, hk), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, data, Laws.rd_at(U32, a, k)), pm1, perm, epm1)))))))

def cg_i.b(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  w: PST.TGW(~U32, K.Kernel.depth_for(nn), nn, data, pm1, 0))
  -> CGW(C.CI32{len, depth, valid, data}, perm, nn, j, k):
  (o, pm2, etg, res) = w
  (epm2, wfo, dcells) = res
  cg_i.c(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, o, pm2, etg, epm2, dcells, PST.rd_all(U32, K.Kernel.depth_for(nn), o, wfo))

def cg_i.a(+len: U32, +depth: Nat, -valid: C.Valid, data: Array<U32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, +fits: {U32.is_le(nn, U32.shln(1, K.Kernel.depth_for(nn))) == True{} : Bool}, wv: VGW(valid, perm, nn, K.Kernel.depth_for(nn)))
  -> CGW(C.CI32{len, depth, valid, data}, perm, nn, j, k):
  (v2, pm1, evg, +epm1, vcells) = wv
  cg_i.b(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, PST.tgather_w(~U32, K.Kernel.depth_for(nn), nn, data, pm1, 0, fits))

# CF32: the validity gathered (vg_w), the data gathered with the permutation that comes back
# (PST.tgather_w at F32), the output array handed back by rd_all (rd_at == rdN on it)
def cg_f.cell(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<F32>, -perm: Array<U32>, +nn: U32, +k: U32, -v2: C.Valid, -o2: Array<F32>,
  vb: {Laws.vbit(v2, k) == Laws.vbit(valid, Laws.rd_at(U32, perm, k)) : Bool}, dv: {Laws.rd_at(F32, o2, k) == Laws.rd_at(F32, data, Laws.rd_at(U32, perm, k)) : F32})
  -> {Laws.ccell(C.CF32{nn, K.Kernel.depth_for(nn), v2, o2}, k) == Laws.ccell(C.CF32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}:
  %Equal.sym(Bool, Laws.vbit(v2, k), Laws.vbit(valid, Laws.rd_at(U32, perm, k)), vb) : {Bool.pick(D.Scalar, _, D.SF32{Laws.rd_at(F32, o2, k)}, D.SNull{}) == Laws.ccell(C.CF32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  %Equal.sym(F32, Laws.rd_at(F32, o2, k), Laws.rd_at(F32, data, Laws.rd_at(U32, perm, k)), dv) : {Bool.pick(D.Scalar, Laws.vbit(valid, Laws.rd_at(U32, perm, k)), D.SF32{_}, D.SNull{}) == Laws.ccell(C.CF32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  {==}

def cg_f.d(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<F32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, -o: Array<F32>, o2: Array<F32>, pm2: Array<U32>,
  +eo2: {o2 == o : Array<F32>}, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, etg: {K.Kernel.gather(~F32, nn, K.Kernel.depth_for(nn), data, pm1, 0.0) == (o, pm2) : Array<F32> & Array<U32>}, epm1: {pm1 == perm : Array<U32>}, epm2: {pm2 == pm1 : Array<U32>},
  pk: PK2(D.TF32{}, k, j, nn, Laws.ccell(C.CF32{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CF32{len, depth, valid, data}, Laws.rd_at(U32, perm, k))))
  -> CGW(C.CF32{len, depth, valid, data}, perm, nn, j, k):
  (f1, f2) = pk
  (C.CF32{nn, K.Kernel.depth_for(nn), v2, o2}, pm2, (%Equal.sym(Array<F32>, o2, o, eo2) : {C.Column.gather(C.CF32{len, depth, valid, data}, perm, nn) == (C.CF32{nn, K.Kernel.depth_for(nn), v2, _}, pm2) : C.Column & Array<U32>}; %Equal.sym(C.Valid & Array<U32>, C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)), (v2, pm1), evg) : {C.Column.gather.c(C.CF32{len, depth, C.AllValid{}, data}, nn, K.Kernel.depth_for(nn), _) == (C.CF32{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; %Equal.sym(Array<F32> & Array<U32>, K.Kernel.gather(~F32, nn, K.Kernel.depth_for(nn), data, pm1, 0.0), (o, pm2), etg) : {C.Column.gather.d(v2, C.Column.out.f(nn, K.Kernel.depth_for(nn), _)) == (C.CF32{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; {==}), Equal.trans(Array<U32>, pm2, pm1, perm, epm2, epm1), f1, f2)

def cg_f.c(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<F32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  -o: Array<F32>, pm2: Array<U32>, etg: {K.Kernel.gather(~F32, nn, K.Kernel.depth_for(nn), data, pm1, 0.0) == (o, pm2) : Array<F32> & Array<U32>}, epm2: {pm2 == pm1 : Array<U32>}, dcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.rdN(F32, K.Kernel.depth_for(nn), o, i) == Laws.rd_at(F32, data, Laws.rd_at(U32, pm1, i)) : F32},
  w: &b: Array<F32> -> {b == o : Array<F32>} & Laws.WFArray(F32, K.Kernel.depth_for(nn), b) & (@i: U32 -> {Laws.rd_at(F32, o, i) == Laws.rdN(F32, K.Kernel.depth_for(nn), o, i) : F32}))
  -> CGW(C.CF32{len, depth, valid, data}, perm, nn, j, k):
  (o2, +eo2, wf2, conv) = w
  cg_f.d(len, depth, valid, data, perm, nn, j, k, v2, pm1, o, o2, pm2, eo2, evg, etg, epm1, epm2, pk2(D.TF32{}, k, j, nn, Laws.ccell(C.CF32{nn, K.Kernel.depth_for(nn), v2, o2}, k), Laws.ccell(C.CF32{len, depth, valid, data}, Laws.rd_at(U32, perm, k)), U32.is_lt(k, nn), {==}, +hk => cg_f.cell(len, depth, valid, data, perm, nn, k, v2, o2, vcells(k, hk), Equal.trans(F32, Laws.rd_at(F32, o2, k), Laws.rd_at(F32, o, k), Laws.rd_at(F32, data, Laws.rd_at(U32, perm, k)), Equal.cong(Array<F32>, F32, a => Laws.rd_at(F32, a, k), o2, o, eo2), Equal.trans(F32, Laws.rd_at(F32, o, k), Laws.rdN(F32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(F32, data, Laws.rd_at(U32, perm, k)), conv(k), Equal.trans(F32, Laws.rdN(F32, K.Kernel.depth_for(nn), o, k), Laws.rd_at(F32, data, Laws.rd_at(U32, pm1, k)), Laws.rd_at(F32, data, Laws.rd_at(U32, perm, k)), dcells(k, hk), Equal.cong(Array<U32>, F32, a => Laws.rd_at(F32, data, Laws.rd_at(U32, a, k)), pm1, perm, epm1)))))))

def cg_f.b(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<F32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  w: PST.TGW(~F32, K.Kernel.depth_for(nn), nn, data, pm1, 0.0))
  -> CGW(C.CF32{len, depth, valid, data}, perm, nn, j, k):
  (o, pm2, etg, res) = w
  (epm2, wfo, dcells) = res
  cg_f.c(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, o, pm2, etg, epm2, dcells, PST.rd_all(F32, K.Kernel.depth_for(nn), o, wfo))

def cg_f.a(+len: U32, +depth: Nat, -valid: C.Valid, data: Array<F32>, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, +fits: {U32.is_le(nn, U32.shln(1, K.Kernel.depth_for(nn))) == True{} : Bool}, wv: VGW(valid, perm, nn, K.Kernel.depth_for(nn)))
  -> CGW(C.CF32{len, depth, valid, data}, perm, nn, j, k):
  (v2, pm1, evg, +epm1, vcells) = wv
  cg_f.b(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, PST.tgather_w(~F32, K.Kernel.depth_for(nn), nn, data, pm1, 0.0, fits))

# CStr: the validity gathered (vg_w), the strings through Laws.strs_gather_cells (both storages)
def cg_s.cell(+len: U32, +depth: Nat, -valid: C.Valid, -data: ST.Strs, -perm: Array<U32>, +nn: U32, +k: U32, -v2: C.Valid, -o: ST.Strs,
  vb: {Laws.vbit(v2, k) == Laws.vbit(valid, Laws.rd_at(U32, perm, k)) : Bool}, dv: {Laws.scell(o, k) == Laws.scell(data, Laws.rd_at(U32, perm, k)) : String})
  -> {Laws.ccell(C.CStr{nn, K.Kernel.depth_for(nn), v2, o}, k) == Laws.ccell(C.CStr{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}:
  %Equal.sym(Bool, Laws.vbit(v2, k), Laws.vbit(valid, Laws.rd_at(U32, perm, k)), vb) : {Bool.pick(D.Scalar, _, D.SStr{Laws.scell(o, k)}, D.SNull{}) == Laws.ccell(C.CStr{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  %Equal.sym(String, Laws.scell(o, k), Laws.scell(data, Laws.rd_at(U32, perm, k)), dv) : {Bool.pick(D.Scalar, Laws.vbit(valid, Laws.rd_at(U32, perm, k)), D.SStr{_}, D.SNull{}) == Laws.ccell(C.CStr{len, depth, valid, data}, Laws.rd_at(U32, perm, k)) : D.Scalar}
  {==}

def cg_s.d(+len: U32, +depth: Nat, -valid: C.Valid, -data: ST.Strs, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, o: ST.Strs, pm2: Array<U32>,
  evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, etg: {ST.Strs.gather(data, pm1, nn, K.Kernel.depth_for(nn)) == (o, pm2) : ST.Strs & Array<U32>}, epm1: {pm1 == perm : Array<U32>}, epm2: {pm2 == pm1 : Array<U32>},
  pk: PK2(D.TStr{}, k, j, nn, Laws.ccell(C.CStr{nn, K.Kernel.depth_for(nn), v2, o}, k), Laws.ccell(C.CStr{len, depth, valid, data}, Laws.rd_at(U32, perm, k))))
  -> CGW(C.CStr{len, depth, valid, data}, perm, nn, j, k):
  (f1, f2) = pk
  (C.CStr{nn, K.Kernel.depth_for(nn), v2, o}, pm2, (%Equal.sym(C.Valid & Array<U32>, C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)), (v2, pm1), evg) : {C.Column.gather.c(C.CStr{len, depth, C.AllValid{}, data}, nn, K.Kernel.depth_for(nn), _) == (C.CStr{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; %Equal.sym(ST.Strs & Array<U32>, ST.Strs.gather(data, pm1, nn, K.Kernel.depth_for(nn)), (o, pm2), etg) : {C.Column.gather.d(v2, C.Column.out.s(nn, K.Kernel.depth_for(nn), _)) == (C.CStr{nn, K.Kernel.depth_for(nn), v2, o}, pm2) : C.Column & Array<U32>}; {==}), Equal.trans(Array<U32>, pm2, pm1, perm, epm2, epm1), f1, f2)

def cg_s.c(+len: U32, +depth: Nat, -valid: C.Valid, -data: ST.Strs, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, v2: C.Valid, -pm1: Array<U32>, evg: {C.Valid.gather(valid, perm, nn, K.Kernel.depth_for(nn)) == (v2, pm1) : C.Valid & Array<U32>}, +epm1: {pm1 == perm : Array<U32>}, vcells: @i: U32 -> {U32.is_lt(i, nn) == True{} : Bool} -> {Laws.vbit(v2, i) == Laws.vbit(valid, Laws.rd_at(U32, perm, i)) : Bool},
  w: Laws.GatherW(data, pm1, nn, K.Kernel.depth_for(nn)))
  -> CGW(C.CStr{len, depth, valid, data}, perm, nn, j, k):
  (o, pm2, etg, epm2, scells) = w
  cg_s.d(len, depth, valid, data, perm, nn, j, k, v2, pm1, o, pm2, evg, etg, epm1, epm2, pk2(D.TStr{}, k, j, nn, Laws.ccell(C.CStr{nn, K.Kernel.depth_for(nn), v2, o}, k), Laws.ccell(C.CStr{len, depth, valid, data}, Laws.rd_at(U32, perm, k)), U32.is_lt(k, nn), {==}, +hk => cg_s.cell(len, depth, valid, data, perm, nn, k, v2, o, vcells(k, hk), Equal.trans(String, Laws.scell(o, k), Laws.scell(data, Laws.rd_at(U32, pm1, k)), Laws.scell(data, Laws.rd_at(U32, perm, k)), scells(k, hk), Equal.cong(Array<U32>, String, a => Laws.scell(data, Laws.rd_at(U32, a, k)), pm1, perm, epm1)))))

def cg_s.a(+len: U32, +depth: Nat, -valid: C.Valid, data: ST.Strs, -perm: Array<U32>, +nn: U32, +j: U32, +k: U32, +fits: {U32.is_le(nn, U32.shln(1, K.Kernel.depth_for(nn))) == True{} : Bool}, wv: VGW(valid, perm, nn, K.Kernel.depth_for(nn)))
  -> CGW(C.CStr{len, depth, valid, data}, perm, nn, j, k):
  (v2, pm1, evg, +epm1, vcells) = wv
  cg_s.c(len, depth, valid, data, perm, nn, j, k, v2, pm1, evg, epm1, vcells, Laws.strs_gather_cells(data, pm1, nn, K.Kernel.depth_for(nn), fits))

# Column.gather of any column: the CGW witness (nn <= 2^depth_for(nn): the rows fit the slots)
def cg_w(col: C.Column, perm: Array<U32>, +nn: U32, +j: U32, +k: U32, +fits: {U32.is_le(nn, U32.shln(1, K.Kernel.depth_for(nn))) == True{} : Bool}) -> CGW(col, perm, nn, j, k):
  match col:
    case C.CBool{+len, +depth, valid, data}:
      cg_b.a(len, depth, valid, data, perm, nn, j, k, fits, vg_w(valid, perm, nn, K.Kernel.depth_for(nn), fits))
    case C.CU32{+len, +depth, valid, data}:
      cg_u.a(len, depth, valid, data, perm, nn, j, k, fits, vg_w(valid, perm, nn, K.Kernel.depth_for(nn), fits))
    case C.CI32{+len, +depth, valid, data}:
      cg_i.a(len, depth, valid, data, perm, nn, j, k, fits, vg_w(valid, perm, nn, K.Kernel.depth_for(nn), fits))
    case C.CF32{+len, +depth, valid, data}:
      cg_f.a(len, depth, valid, data, perm, nn, j, k, fits, vg_w(valid, perm, nn, K.Kernel.depth_for(nn), fits))
    case C.CStr{+len, +depth, valid, data}:
      cg_s.a(len, depth, valid, data, perm, nn, j, k, fits, vg_w(valid, perm, nn, K.Kernel.depth_for(nn), fits))

# ---- the observation of the accumulators, and List.reverse --------------------------------------

# lobs of every column after a head n (what Frame.head's columns show)
def lobsh(cols: List<&1, C.Named>, +n: U32, +k: U32) -> List<&2, Laws.NObs>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{nm, c} <> rest:
      Laws.NObs{nm, Laws.cobs(C.Column.head(c, n), k)} <> lobsh(rest, n, k)

# lobs over Cols.head is lobsh
def lh(cols: List<&1, C.Named>, +n: U32, +k: U32) -> {Laws.lobs(C.Cols.head(cols, n), k) == lobsh(cols, n, k) : List<&2, Laws.NObs>}:
  match cols:
    case Nil{}:
      {==}
    case C.Named{nm, c} <> rest:
      Equal.cong(List<&2, Laws.NObs>, List<&2, Laws.NObs>, t => Laws.NObs{nm, Laws.cobs(C.Column.head(c, n), k)} <> t, Laws.lobs(C.Cols.head(rest, n), k), lobsh(rest, n, k), lh(rest, n, k))

# lobs commutes with List.reverse (its accumulator form)
def lr(xs: List<&1, C.Named>, acc: List<&1, C.Named>, +k: U32) -> {Laws.lobs(List.reverse.go(&1, C.Named, xs, acc), k) == List.reverse.go(&2, Laws.NObs, Laws.lobs(xs, k), Laws.lobs(acc, k)) : List<&2, Laws.NObs>}:
  match xs:
    case Nil{}:
      {==}
    case C.Named{nm, c} <> t:
      lr(t, C.Named{nm, c} <> acc, k)

# and so does lobs over Cols.head (lobsh)
def lrh(xs: List<&1, C.Named>, acc: List<&1, C.Named>, +n: U32, +k: U32) -> {Laws.lobs(C.Cols.head(List.reverse.go(&1, C.Named, xs, acc), n), k) == List.reverse.go(&2, Laws.NObs, lobsh(xs, n, k), lobsh(acc, n, k)) : List<&2, Laws.NObs>}:
  match xs:
    case Nil{}:
      lh(acc, n, k)
    case C.Named{nm, c} <> t:
      lrh(t, C.Named{nm, c} <> acc, n, k)

# ---- Sort.gcols at the two cuts, in lockstep ---------------------------------------------------------

# the end of the column list: both frames are the reversed accumulators
def gc_nil(-p1: Array<U32>, -p2: Array<U32>, a1: List<&1, C.Named>, a2: List<&1, C.Named>, +n: U32, +h: U32, +k: U32, +inv: {Laws.lobs(a1, k) == lobsh(a2, n, k) : List<&2, Laws.NObs>})
  -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(Nil{}, U32.min(n, h), (p1, a1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(Nil{}, h, (p2, a2))), n)}, k) : Laws.RObs}:
  %Equal.sym(List<&2, Laws.NObs>, Laws.lobs(List.reverse.go(&1, C.Named, a1, Nil{}), k), List.reverse.go(&2, Laws.NObs, Laws.lobs(a1, k), Nil{}), lr(a1, Nil{}, k)) : {Laws.RFrame{U32.min(n, h), _} == Laws.RFrame{U32.min(n, h), Laws.lobs(C.Cols.head(List.reverse.go(&1, C.Named, a2, Nil{}), n), k)} : Laws.RObs}
  %Equal.sym(List<&2, Laws.NObs>, Laws.lobs(C.Cols.head(List.reverse.go(&1, C.Named, a2, Nil{}), n), k), List.reverse.go(&2, Laws.NObs, lobsh(a2, n, k), Nil{}), lrh(a2, Nil{}, n, k)) : {Laws.RFrame{U32.min(n, h), List.reverse.go(&2, Laws.NObs, Laws.lobs(a1, k), Nil{})} == Laws.RFrame{U32.min(n, h), _} : Laws.RObs}
  Equal.cong(List<&2, Laws.NObs>, Laws.RObs, l => Laws.RFrame{U32.min(n, h), List.reverse.go(&2, Laws.NObs, l, Nil{})}, Laws.lobs(a1, k), lobsh(a2, n, k), inv)

# what the two cuts show of one column: min(n, h) rows of it, and h rows of it then head n
def gc_obs(-col: C.Column, -ca: C.Column, -cb: C.Column, -pp: Array<U32>, -p1: Array<U32>, -p2: Array<U32>, -c1: C.Column, -c2: C.Column, +n: U32, +h: U32, +k: U32,
  +eca: {ca == col : C.Column}, +ecb: {cb == col : C.Column}, +e1: {p1 == pp : Array<U32>}, +e2: {p2 == pp : Array<U32>},
  ob1: {Laws.cobs(c1, k) == Laws.CObs{Laws.cdtype(ca), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(ca, Laws.rd_at(U32, p1, k)), D.SNull{})} : Laws.CObs},
  obh2: {Laws.cobs(C.Column.head(c2, n), k) == Laws.CObs{Laws.cdtype(cb), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(cb, Laws.rd_at(U32, p2, k)), D.SNull{})} : Laws.CObs})
  -> {Laws.cobs(c1, k) == Laws.cobs(C.Column.head(c2, n), k) : Laws.CObs}:
  %Equal.sym(Laws.CObs, Laws.cobs(c1, k), Laws.CObs{Laws.cdtype(ca), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(ca, Laws.rd_at(U32, p1, k)), D.SNull{})}, ob1) : {_ == Laws.cobs(C.Column.head(c2, n), k) : Laws.CObs}
  %Equal.sym(Laws.CObs, Laws.cobs(C.Column.head(c2, n), k), Laws.CObs{Laws.cdtype(cb), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(cb, Laws.rd_at(U32, p2, k)), D.SNull{})}, obh2) : {Laws.CObs{Laws.cdtype(ca), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(ca, Laws.rd_at(U32, p1, k)), D.SNull{})} == _ : Laws.CObs}
  %Equal.sym(C.Column, ca, col, eca) : {Laws.CObs{Laws.cdtype(_), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(_, Laws.rd_at(U32, p1, k)), D.SNull{})} == Laws.CObs{Laws.cdtype(cb), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(cb, Laws.rd_at(U32, p2, k)), D.SNull{})} : Laws.CObs}
  %Equal.sym(C.Column, cb, col, ecb) : {Laws.CObs{Laws.cdtype(col), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(col, Laws.rd_at(U32, p1, k)), D.SNull{})} == Laws.CObs{Laws.cdtype(_), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(_, Laws.rd_at(U32, p2, k)), D.SNull{})} : Laws.CObs}
  %Equal.sym(Array<U32>, p1, pp, e1) : {Laws.CObs{Laws.cdtype(col), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(col, Laws.rd_at(U32, _, k)), D.SNull{})} == Laws.CObs{Laws.cdtype(col), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(col, Laws.rd_at(U32, p2, k)), D.SNull{})} : Laws.CObs}
  %Equal.sym(Array<U32>, p2, pp, e2) : {Laws.CObs{Laws.cdtype(col), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(col, Laws.rd_at(U32, pp, k)), D.SNull{})} == Laws.CObs{Laws.cdtype(col), U32.min(n, h), Bool.pick(D.Scalar, U32.is_lt(k, U32.min(n, h)), Laws.ccell(col, Laws.rd_at(U32, _, k)), D.SNull{})} : Laws.CObs}
  {==}

def gc_cons2(+nm: String, -rest: List<&1, C.Named>, -pp: Array<U32>, -p1: Array<U32>, -p2: Array<U32>, a1: List<&1, C.Named>, a2: List<&1, C.Named>, +n: U32, +h: U32, +k: U32,
  +e1: {p1 == pp : Array<U32>}, +e2: {p2 == pp : Array<U32>}, +inv: {Laws.lobs(a1, k) == lobsh(a2, n, k) : List<&2, Laws.NObs>},
  +fm: {U32.is_le(U32.min(n, h), U32.shln(1, K.Kernel.depth_for(U32.min(n, h)))) == True{} : Bool}, +fh: {U32.is_le(h, U32.shln(1, K.Kernel.depth_for(h))) == True{} : Bool},
  -col: C.Column, -ca: C.Column, -cb: C.Column, +eca: {ca == col : C.Column}, +ecb: {cb == col : C.Column},
  ih: @q1: Array<U32> -> @q2: Array<U32> -> @b1: List<&1, C.Named> -> @b2: List<&1, C.Named> -> @_e1: {q1 == pp : Array<U32>} -> @_e2: {q2 == pp : Array<U32>} -> @_i: {Laws.lobs(b1, k) == lobsh(b2, n, k) : List<&2, Laws.NObs>} -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(rest, U32.min(n, h), (q1, b1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(rest, h, (q2, b2))), n)}, k) : Laws.RObs},
  w1: CGW(ca, p1, U32.min(n, h), n, k), w2: CGW(cb, p2, h, n, k))
  -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(C.Named{nm, col} <> rest, U32.min(n, h), (p1, a1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(C.Named{nm, col} <> rest, h, (p2, a2))), n)}, k) : Laws.RObs}:
  (c1, q1, eq1, eqp1, ob1, obh1) = w1
  (c2, q2, eq2, eqp2, ob2, obh2) = w2
  %eca : {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(rest, U32.min(n, h), O.Sort.gcols.add(nm, a1, C.Column.gather(_, p1, U32.min(n, h)))))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(rest, h, O.Sort.gcols.add(nm, a2, C.Column.gather(col, p2, h)))), n)}, k) : Laws.RObs}
  %Equal.sym(C.Column & Array<U32>, C.Column.gather(ca, p1, U32.min(n, h)), (c1, q1), eq1) : {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(rest, U32.min(n, h), O.Sort.gcols.add(nm, a1, _)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(rest, h, O.Sort.gcols.add(nm, a2, C.Column.gather(col, p2, h)))), n)}, k) : Laws.RObs}
  %ecb : {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(rest, U32.min(n, h), (q1, C.Named{nm, c1} <> a1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(rest, h, O.Sort.gcols.add(nm, a2, C.Column.gather(_, p2, h)))), n)}, k) : Laws.RObs}
  %Equal.sym(C.Column & Array<U32>, C.Column.gather(cb, p2, h), (c2, q2), eq2) : {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(rest, U32.min(n, h), (q1, C.Named{nm, c1} <> a1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(rest, h, O.Sort.gcols.add(nm, a2, _))), n)}, k) : Laws.RObs}
  ih(q1, q2, C.Named{nm, c1} <> a1, C.Named{nm, c2} <> a2, Equal.trans(Array<U32>, q1, p1, pp, eqp1, e1), Equal.trans(Array<U32>, q2, p2, pp, eqp2, e2), Equal.trans(List<&2, Laws.NObs>, Laws.NObs{nm, Laws.cobs(c1, k)} <> Laws.lobs(a1, k), Laws.NObs{nm, Laws.cobs(C.Column.head(c2, n), k)} <> Laws.lobs(a1, k), Laws.NObs{nm, Laws.cobs(C.Column.head(c2, n), k)} <> lobsh(a2, n, k), Equal.cong(Laws.CObs, List<&2, Laws.NObs>, o => Laws.NObs{nm, o} <> Laws.lobs(a1, k), Laws.cobs(c1, k), Laws.cobs(C.Column.head(c2, n), k), gc_obs(col, ca, cb, pp, p1, p2, c1, c2, n, h, k, eca, ecb, e1, e2, ob1, obh2)), Equal.cong(List<&2, Laws.NObs>, List<&2, Laws.NObs>, l => Laws.NObs{nm, Laws.cobs(C.Column.head(c2, n), k)} <> l, Laws.lobs(a1, k), lobsh(a2, n, k), inv)))

def gc_cons(+nm: String, -rest: List<&1, C.Named>, -pp: Array<U32>, p1: Array<U32>, p2: Array<U32>, a1: List<&1, C.Named>, a2: List<&1, C.Named>, +n: U32, +h: U32, +k: U32,
  +e1: {p1 == pp : Array<U32>}, +e2: {p2 == pp : Array<U32>}, +inv: {Laws.lobs(a1, k) == lobsh(a2, n, k) : List<&2, Laws.NObs>},
  +fm: {U32.is_le(U32.min(n, h), U32.shln(1, K.Kernel.depth_for(U32.min(n, h)))) == True{} : Bool}, +fh: {U32.is_le(h, U32.shln(1, K.Kernel.depth_for(h))) == True{} : Bool},
  -col: C.Column, ih: @q1: Array<U32> -> @q2: Array<U32> -> @b1: List<&1, C.Named> -> @b2: List<&1, C.Named> -> @_e1: {q1 == pp : Array<U32>} -> @_e2: {q2 == pp : Array<U32>} -> @_i: {Laws.lobs(b1, k) == lobsh(b2, n, k) : List<&2, Laws.NObs>} -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(rest, U32.min(n, h), (q1, b1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(rest, h, (q2, b2))), n)}, k) : Laws.RObs}, w: PV.CloneW(col))
  -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(C.Named{nm, col} <> rest, U32.min(n, h), (p1, a1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(C.Named{nm, col} <> rest, h, (p2, a2))), n)}, k) : Laws.RObs}:
  (ca, cb, ecl, eca, ecb) = w
  gc_cons2(nm, rest, pp, p1, p2, a1, a2, n, h, k, e1, e2, inv, fm, fh, col, ca, cb, eca, ecb, ih, cg_w(ca, p1, U32.min(n, h), n, k, fm), cg_w(cb, p2, h, n, k, fh))

# Sort.gcols over the columns at the cut min(n, h) (accumulator a1, perm p1) and at h (a2, p2),
# with p1 and p2 equal to one permutation pp and the accumulators showing the same: the two frames
# (the second through Frame.head n) show the same at row k
def gc(cols: List<&1, C.Named>, -pp: Array<U32>, p1: Array<U32>, p2: Array<U32>, a1: List<&1, C.Named>, a2: List<&1, C.Named>, +n: U32, +h: U32, +k: U32,
  +e1: {p1 == pp : Array<U32>}, +e2: {p2 == pp : Array<U32>}, +inv: {Laws.lobs(a1, k) == lobsh(a2, n, k) : List<&2, Laws.NObs>},
  +fm: {U32.is_le(U32.min(n, h), U32.shln(1, K.Kernel.depth_for(U32.min(n, h)))) == True{} : Bool}, +fh: {U32.is_le(h, U32.shln(1, K.Kernel.depth_for(h))) == True{} : Bool})
  -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(cols, U32.min(n, h), (p1, a1)))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(cols, h, (p2, a2))), n)}, k) : Laws.RObs}:
  match cols:
    case Nil{}:
      gc_nil(p1, p2, a1, a2, n, h, k, inv)
    case C.Named{+nm, col} <> rest:
      gc_cons(nm, rest, pp, p1, p2, a1, a2, n, h, k, e1, e2, inv, fm, fh, col, q1 => q2 => b1 => b2 => +x1 => +x2 => +x3 => gc(rest, pp, q1, q2, b1, b2, n, h, k, x1, x2, x3, fm, fh), PV.clone_w(col))

# ---- core: Sort.gather_head against Frame.head(Sort.gather) ------------------------------------------

def core.q(+h: U32, cols: List<&1, C.Named>, -perm: Array<U32>, p1: Array<U32>, p2: Array<U32>, +n: U32, +k: U32, +hc: {U32.is_le(h, U32.shln(1, 31n)) == True{} : Bool}, +e1: {p1 == perm : Array<U32>}, +e2: {p2 == perm : Array<U32>})
  -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(cols, U32.min(n, h), (p1, Nil{})))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(cols, h, (perm, Nil{}))), n)}, k) : Laws.RObs}:
  %e2 : {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(cols, U32.min(n, h), (p1, Nil{})))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(cols, h, (_, Nil{}))), n)}, k) : Laws.RObs}
  gc(cols, perm, p1, p2, Nil{}, Nil{}, n, h, k, e1, e2, {==}, Laws.depth_for_fits(U32.min(n, h), Laws.u32_min_le(n, h, U32.shln(1, 31n), hc)), Laws.depth_for_fits(h, hc))

def core.p(+h: U32, cols: List<&1, C.Named>, -perm: Array<U32>, +n: U32, +k: U32, +hc: {U32.is_le(h, U32.shln(1, 31n)) == True{} : Bool},
  w: &a1: Array<U32> -> &a2: Array<U32> -> {a1 == perm : Array<U32>} & {a2 == perm : Array<U32>})
  -> {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(cols, U32.min(n, h), (perm, Nil{})))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(cols, h, (perm, Nil{}))), n)}, k) : Laws.RObs}:
  (p1, p2, +e1, e2) = w
  %e1 : {Laws.robs(Done{O.Sort.gather.k(U32.min(n, h), O.Sort.gcols(cols, U32.min(n, h), (_, Nil{})))}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(cols, h, (perm, Nil{}))), n)}, k) : Laws.RObs}
  core.q(h, cols, perm, p1, p2, n, k, hc, e1, e2)

def core.k(+h: U32, ok: Bool, +e: {U32.is_le(h, O.Sort.head_cap()) == ok : Bool}, cols: List<&1, C.Named>, perm: Array<U32>, +n: U32, +k: U32)
  -> {Laws.robs(Done{O.Sort.gh.k(ok, h, cols, perm, n)}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather.k(h, O.Sort.gcols(cols, h, (perm, Nil{}))), n)}, k) : Laws.RObs}:
  match ok:
    case True{}:
      core.p(h, cols, perm, n, k, e, PC.clone_eq(U32, perm))
    case False{}:
      {==}

# the bounded gather shows what the full gather then head shows (any frame, perm, n, row k)
def core(f: C.Frame, perm: Array<U32>, +n: U32, +k: U32) -> {Laws.robs(Done{O.Sort.gather_head(f, perm, n)}, k) == Laws.robs(Done{C.Frame.head(O.Sort.gather(f, perm), n)}, k) : Laws.RObs}:
  match f:
    case C.Frame{+h, cols}:
      core.k(h, U32.is_le(h, O.Sort.head_cap()), {==}, cols, perm, n, k)

# ---- the key chain, for an observation context (c1, c2) ----------------------------------------------
#
# hf: the context treats a failure alike on both sides; hd: it treats two frames alike when the
# first shows what the head n of the second shows. Each path of the chain uses one of them once.

def ch.a(+n: U32, +k: U32, -c1: E.ResT(C.Frame) -> Laws.RObs, -c2: E.ResT(C.Frame) -> Laws.RObs, hf: @e: E.Err -> {c1(Fail{e}) == c2(Fail{e}) : Laws.RObs},
  hd: @-g1: C.Frame -> @-g2: C.Frame -> @_h: {Laws.robs(Done{g1}, k) == Laws.robs(Done{C.Frame.head(g2, n)}, k) : Laws.RObs} -> {c1(Done{g1}) == c2(Done{g2}) : Laws.RObs},
  r: C.Frame & E.ResT(Array<U32>)) -> {c1(O.Sort.fh.a(n, r)) == c2(O.Sort.frame.a(r)) : Laws.RObs}:
  (f3, rp) = r
  match rp:
    case Fail{e}:
      hf(e)
    case Done{perm}:
      hd(O.Sort.gather_head(f3, perm, n), O.Sort.gather(f3, perm), core(f3, perm, n, k))

def ch.c(m: Maybe<&2, E.Err>, f: C.Frame, +keys: List<&2, O.SortKey>, +n: U32, +k: U32, -c1: E.ResT(C.Frame) -> Laws.RObs, -c2: E.ResT(C.Frame) -> Laws.RObs, hf: @e: E.Err -> {c1(Fail{e}) == c2(Fail{e}) : Laws.RObs},
  hd: @-g1: C.Frame -> @-g2: C.Frame -> @_h: {Laws.robs(Done{g1}, k) == Laws.robs(Done{C.Frame.head(g2, n)}, k) : Laws.RObs} -> {c1(Done{g1}) == c2(Done{g2}) : Laws.RObs})
  -> {c1(O.Sort.fh.c(m, f, keys, n)) == c2(O.Sort.frame.c(m, f, keys)) : Laws.RObs}:
  match m:
    case Some{e}:
      hf(e)
    case None{}:
      ch.a(n, k, c1, c2, hf, hd, O.Sort.argsort(f, keys))

def ch.b(+keys: List<&2, O.SortKey>, +n: U32, +k: U32, -c1: E.ResT(C.Frame) -> Laws.RObs, -c2: E.ResT(C.Frame) -> Laws.RObs, hf: @e: E.Err -> {c1(Fail{e}) == c2(Fail{e}) : Laws.RObs},
  hd: @-g1: C.Frame -> @-g2: C.Frame -> @_h: {Laws.robs(Done{g1}, k) == Laws.robs(Done{C.Frame.head(g2, n)}, k) : Laws.RObs} -> {c1(Done{g1}) == c2(Done{g2}) : Laws.RObs},
  r: C.Frame & C.FInfo) -> {c1(O.Sort.fh.b(keys, n, r)) == c2(O.Sort.frame.b(keys, r)) : Laws.RObs}:
  (f, i) = r
  match i:
    case C.FInfo{h, ns}:
      ch.c(O.Sort.miss(keys, ns), f, keys, n, k, c1, c2, hf, hd)

def ch(f: C.Frame, +ks: List<&2, O.SortKey>, +n: U32, +k: U32, -c1: E.ResT(C.Frame) -> Laws.RObs, -c2: E.ResT(C.Frame) -> Laws.RObs, hf: @e: E.Err -> {c1(Fail{e}) == c2(Fail{e}) : Laws.RObs},
  hd: @-g1: C.Frame -> @-g2: C.Frame -> @_h: {Laws.robs(Done{g1}, k) == Laws.robs(Done{C.Frame.head(g2, n)}, k) : Laws.RObs} -> {c1(Done{g1}) == c2(Done{g2}) : Laws.RObs})
  -> {c1(O.Sort.frame_head(f, ks, n)) == c2(O.Sort.frame(f, ks)) : Laws.RObs}:
  match ks:
    case Nil{}:
      hd(C.Frame.head(f, n), f, {==})
    case +kk <> t:
      ch.b(kk <> t, n, k, c1, c2, hf, hd, C.Frame.info(f))

def Laws.sort_head_frame(f, ks, n, k):
  ch(f, ks, n, k, r => Laws.robs(r, k), r => Laws.robs(Laws.hres(r, n), k), e => {==}, g1 => g2 => h => h)

# ---- the runner (src/exec.bend Exec.run_phys) ---------------------------------------------------------

# Exec.loop over an append: the suffix runs from the state the prefix leaves
def loop_app(w: List<&2, Q.Instr>, +b: List<&2, Q.Instr>, -st: Q.St) -> {Q.Exec.loop(List.append(&2, Q.Instr, w, b), st) == Q.Exec.loop(b, Q.Exec.loop(w, st)) : Q.St}:
  match w:
    case Nil{}:
      {==}
    case i <> t:
      loop_app(t, b, Q.Exec.step(i, st))

# Exec.mark of a code with nothing after it
def mark_nil(+a: List<&2, Q.Instr>) -> {Q.Exec.mark(a) == Laws.markw(a, Nil{}) : List<&2, Q.Instr>}:
  %PE.app_nil(a) : {Q.Exec.mark(_) == Laws.markw(a, Nil{}) : List<&2, Q.Instr>}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, a, Nil{})), List.append(&2, Q.Instr, Laws.markw(a, Nil{}), Q.Exec.mark(Nil{})), PE.mark_app(a, Nil{})) : {_ == Laws.markw(a, Nil{}) : List<&2, Q.Instr>}
  PE.app_nil(Laws.markw(a, Nil{}))

# the runner's last two steps as one: the context is the rest of the stack t (one frame left is the
# result; more is "not one result" on both sides) and the environment
def hd_b(-env: P.Env, t: List<&1, C.Frame>, +n: U32, +k: U32)
  -> @-g1: C.Frame -> @-g2: C.Frame -> @_h: {Laws.robs(Done{g1}, k) == Laws.robs(Done{C.Frame.head(g2, n)}, k) : Laws.RObs} -> {Laws.robs(Q.Exec.fin(Q.St{env, Q.Exec.push(Done{g1}, t)}), k) == Laws.robs(Q.Exec.fin(Q.Exec.step.r(Q.IHead{n}, env, Q.Exec.push(Done{g2}, t))), k) : Laws.RObs}:
  match t:
    case Nil{}:
      g1 => g2 => h => h
    case a <> b:
      g1 => g2 => h => {==}

def st_s(+ks: List<&2, O.SortKey>, +n: U32, +k: U32, -env: P.Env, stack: List<&1, C.Frame>)
  -> {Laws.robs(Q.Exec.fin(Q.St{env, Q.Exec.sorthead.s(ks, n, stack)}), k) == Laws.robs(Q.Exec.fin(Q.Exec.step(Q.IHead{n}, Q.St{env, Q.Exec.unary.pop(Q.ISort{ks}, stack)})), k) : Laws.RObs}:
  match stack:
    case Nil{}:
      {==}
    case f <> t:
      ch(f, ks, n, k, r => Laws.robs(Q.Exec.fin(Q.St{env, Q.Exec.push(r, t)}), k), r => Laws.robs(Q.Exec.fin(Q.Exec.step.r(Q.IHead{n}, env, Q.Exec.push(r, t))), k), e => {==}, hd_b(env, t, n, k))

def st_r(+ks: List<&2, O.SortKey>, +n: U32, +k: U32, -env: P.Env, r: E.ResT(List<&1, C.Frame>))
  -> {Laws.robs(Q.Exec.fin(Q.Exec.sorthead.r(ks, n, env, r)), k) == Laws.robs(Q.Exec.fin(Q.Exec.step(Q.IHead{n}, Q.Exec.step.r(Q.ISort{ks}, env, r))), k) : Laws.RObs}:
  match r:
    case Fail{e}:
      {==}
    case Done{stack}:
      st_s(ks, n, k, env, stack)

# Exec.sorthead against ISort then IHead, from any runner state
def st_k(+ks: List<&2, O.SortKey>, +n: U32, +k: U32, st: Q.St)
  -> {Laws.robs(Q.Exec.fin(Q.Exec.sorthead(ks, n, st)), k) == Laws.robs(Q.Exec.fin(Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.ISort{ks}, st))), k) : Laws.RObs}:
  match st:
    case Q.St{env, r}:
      st_r(ks, n, k, env, r)

def Laws.sort_head_run(x, ks, n, env, k):
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(Q.Exec.compile(x, Nil{})), Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), mark_nil(Q.Exec.compile(x, Nil{}))) : {Laws.robs(Q.Exec.fin(Q.Exec.sorthead(ks, n, Q.Exec.loop(_, Q.St{env, Done{Nil{}}}))), k) == Laws.robs(Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(Q.Exec.compile(x, Q.ISort{ks} <> Q.IHead{n} <> Nil{})), Q.St{env, Done{Nil{}}})), k) : Laws.RObs}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.ISort{ks} <> Q.IHead{n} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Q.IHead{n} <> Nil{}), PE.compile_app(x, Q.ISort{ks} <> Q.IHead{n} <> Nil{})) : {Laws.robs(Q.Exec.fin(Q.Exec.sorthead(ks, n, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))), k) == Laws.robs(Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(_), Q.St{env, Done{Nil{}}})), k) : Laws.RObs}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Q.IHead{n} <> Nil{})), List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Q.IHead{n} <> Nil{}), Q.Exec.mark(Q.ISort{ks} <> Q.IHead{n} <> Nil{})), PE.mark_app(Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Q.IHead{n} <> Nil{})) : {Laws.robs(Q.Exec.fin(Q.Exec.sorthead(ks, n, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))), k) == Laws.robs(Q.Exec.fin(Q.Exec.loop(_, Q.St{env, Done{Nil{}}})), k) : Laws.RObs}
  %PE.markw_ext(Q.Exec.compile(x, Nil{}), Nil{}, Q.ISort{ks} <> Q.IHead{n} <> Nil{}, {==}) : {Laws.robs(Q.Exec.fin(Q.Exec.sorthead(ks, n, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))), k) == Laws.robs(Q.Exec.fin(Q.Exec.loop(List.append(&2, Q.Instr, _, Q.Exec.mark(Q.ISort{ks} <> Q.IHead{n} <> Nil{})), Q.St{env, Done{Nil{}}})), k) : Laws.RObs}
  %Equal.sym(Q.St, Q.Exec.loop(List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.Exec.mark(Q.ISort{ks} <> Q.IHead{n} <> Nil{})), Q.St{env, Done{Nil{}}}), Q.Exec.loop(Q.Exec.mark(Q.ISort{ks} <> Q.IHead{n} <> Nil{}), Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}})), loop_app(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.Exec.mark(Q.ISort{ks} <> Q.IHead{n} <> Nil{}), Q.St{env, Done{Nil{}}})) : {Laws.robs(Q.Exec.fin(Q.Exec.sorthead(ks, n, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))), k) == Laws.robs(Q.Exec.fin(_), k) : Laws.RObs}
  st_k(ks, n, k, Q.Exec.loop(Laws.markw(Q.Exec.compile(x, Nil{}), Nil{}), Q.St{env, Done{Nil{}}}))

# a Head root: over a Sort, sort_head_run; over anything else run_phys IS run_pure
def run_head(+n: U32, +x: P.Plan, env: P.Env, +k: U32) -> {Laws.robs(Q.Exec.run_phys(P.Head{n, x}, env), k) == Laws.robs(Q.Exec.run_pure(P.Head{n, x}, env), k) : Laws.RObs}:
  match x:
    case P.Sort{+ks, +y}:
      Laws.sort_head_run(y, ks, n, env, k)
    case P.ScanCsv{path, o, s}:
      {==}
    case P.Source{nm, s}:
      {==}
    case P.Select{es, y}:
      {==}
    case P.WithColumns{es, y}:
      {==}
    case P.Filter{e, y}:
      {==}
    case P.GroupBy{gk, ags, mo, y}:
      {==}
    case P.Join{how, lo, ro, l, r}:
      {==}
    case P.Head{m, y}:
      {==}
    case P.Drop{ns, y}:
      {==}
    case P.Rename{ps, y}:
      {==}
    case P.Slice{o, l, y}:
      {==}
    case P.Tail{m, y}:
      {==}
    case P.Unique{ss, y}:
      {==}
    case P.Concat{i, l, r}:
      {==}

# every other root: run_phys IS run_pure
def Laws.run_phys_obs(p, env, k):
  match p:
    case P.Head{+n, x}:
      run_head(n, x, env, k)
    case P.ScanCsv{path, o, s}:
      {==}
    case P.Source{nm, s}:
      {==}
    case P.Select{es, x}:
      {==}
    case P.WithColumns{es, x}:
      {==}
    case P.Filter{e, x}:
      {==}
    case P.Sort{ks, x}:
      {==}
    case P.GroupBy{ks, ags, mo, x}:
      {==}
    case P.Join{how, lo, ro, l, r}:
      {==}
    case P.Drop{ns, x}:
      {==}
    case P.Rename{ps, x}:
      {==}
    case P.Slice{o, l, x}:
      {==}
    case P.Tail{n, x}:
      {==}
    case P.Unique{ss, x}:
      {==}
    case P.Concat{i, l, r}:
      {==}

# ---- two equal copies of an environment (proof-only: collect_obs spends env in two laws) ----------------

def col_dup(-c: C.Column, w: PV.CloneW(c)) -> &a: C.Column -> &b: C.Column -> {a == c : C.Column} & {b == c : C.Column}:
  (c1, c2, ecl, e1, e2) = w
  (c1, c2, e1, e2)

def cols_dup.k(+nm: String, -c: C.Column, -rest: List<&1, C.Named>, wc: &a: C.Column -> &b: C.Column -> {a == c : C.Column} & {b == c : C.Column}, wr: &a: List<&1, C.Named> -> &b: List<&1, C.Named> -> {a == rest : List<&1, C.Named>} & {b == rest : List<&1, C.Named>})
  -> &a: List<&1, C.Named> -> &b: List<&1, C.Named> -> {a == C.Named{nm, c} <> rest : List<&1, C.Named>} & {b == C.Named{nm, c} <> rest : List<&1, C.Named>}:
  (c1, c2, ec1, ec2) = wc
  (r1, r2, er1, er2) = wr
  (C.Named{nm, c1} <> r1, C.Named{nm, c2} <> r2, (%er1 : {C.Named{nm, c1} <> r1 == C.Named{nm, c} <> _ : List<&1, C.Named>}; %ec1 : {C.Named{nm, c1} <> r1 == C.Named{nm, _} <> r1 : List<&1, C.Named>}; {==}), (%er2 : {C.Named{nm, c2} <> r2 == C.Named{nm, c} <> _ : List<&1, C.Named>}; %ec2 : {C.Named{nm, c2} <> r2 == C.Named{nm, _} <> r2 : List<&1, C.Named>}; {==}))

def cols_dup(cols: List<&1, C.Named>) -> &a: List<&1, C.Named> -> &b: List<&1, C.Named> -> {a == cols : List<&1, C.Named>} & {b == cols : List<&1, C.Named>}:
  match cols:
    case Nil{}:
      (Nil{}, Nil{}, {==}, {==})
    case C.Named{+nm, c} <> rest:
      cols_dup.k(nm, c, rest, col_dup(c, PV.clone_w(c)), cols_dup(rest))

def frame_dup.k(+h: U32, -cols: List<&1, C.Named>, w: &a: List<&1, C.Named> -> &b: List<&1, C.Named> -> {a == cols : List<&1, C.Named>} & {b == cols : List<&1, C.Named>})
  -> &a: C.Frame -> &b: C.Frame -> {a == C.Frame{h, cols} : C.Frame} & {b == C.Frame{h, cols} : C.Frame}:
  (c1, c2, e1, e2) = w
  (C.Frame{h, c1}, C.Frame{h, c2}, (%e1 : {C.Frame{h, c1} == C.Frame{h, _} : C.Frame}; {==}), (%e2 : {C.Frame{h, c2} == C.Frame{h, _} : C.Frame}; {==}))

def frame_dup(f: C.Frame) -> &a: C.Frame -> &b: C.Frame -> {a == f : C.Frame} & {b == f : C.Frame}:
  match f:
    case C.Frame{+h, cols}:
      frame_dup.k(h, cols, cols_dup(cols))

def fl_dup.k(-f: C.Frame, -rest: List<&1, C.Frame>, wf: &a: C.Frame -> &b: C.Frame -> {a == f : C.Frame} & {b == f : C.Frame}, wr: &a: List<&1, C.Frame> -> &b: List<&1, C.Frame> -> {a == rest : List<&1, C.Frame>} & {b == rest : List<&1, C.Frame>})
  -> &a: List<&1, C.Frame> -> &b: List<&1, C.Frame> -> {a == f <> rest : List<&1, C.Frame>} & {b == f <> rest : List<&1, C.Frame>}:
  (f1, f2, ef1, ef2) = wf
  (r1, r2, er1, er2) = wr
  (f1 <> r1, f2 <> r2, (%er1 : {f1 <> r1 == f <> _ : List<&1, C.Frame>}; %ef1 : {f1 <> r1 == _ <> r1 : List<&1, C.Frame>}; {==}), (%er2 : {f2 <> r2 == f <> _ : List<&1, C.Frame>}; %ef2 : {f2 <> r2 == _ <> r2 : List<&1, C.Frame>}; {==}))

def fl_dup(fs: List<&1, C.Frame>) -> &a: List<&1, C.Frame> -> &b: List<&1, C.Frame> -> {a == fs : List<&1, C.Frame>} & {b == fs : List<&1, C.Frame>}:
  match fs:
    case Nil{}:
      (Nil{}, Nil{}, {==}, {==})
    case f <> rest:
      fl_dup.k(f, rest, frame_dup(f), fl_dup(rest))

def nf_dup.k(+nm: String, -f: C.Frame, -rest: List<&1, P.Named.Frame>, wf: &a: C.Frame -> &b: C.Frame -> {a == f : C.Frame} & {b == f : C.Frame}, wr: &a: List<&1, P.Named.Frame> -> &b: List<&1, P.Named.Frame> -> {a == rest : List<&1, P.Named.Frame>} & {b == rest : List<&1, P.Named.Frame>})
  -> &a: List<&1, P.Named.Frame> -> &b: List<&1, P.Named.Frame> -> {a == P.NF{nm, f} <> rest : List<&1, P.Named.Frame>} & {b == P.NF{nm, f} <> rest : List<&1, P.Named.Frame>}:
  (f1, f2, ef1, ef2) = wf
  (r1, r2, er1, er2) = wr
  (P.NF{nm, f1} <> r1, P.NF{nm, f2} <> r2, (%er1 : {P.NF{nm, f1} <> r1 == P.NF{nm, f} <> _ : List<&1, P.Named.Frame>}; %ef1 : {P.NF{nm, f1} <> r1 == P.NF{nm, _} <> r1 : List<&1, P.Named.Frame>}; {==}), (%er2 : {P.NF{nm, f2} <> r2 == P.NF{nm, f} <> _ : List<&1, P.Named.Frame>}; %ef2 : {P.NF{nm, f2} <> r2 == P.NF{nm, _} <> r2 : List<&1, P.Named.Frame>}; {==}))

def nf_dup(fs: List<&1, P.Named.Frame>) -> &a: List<&1, P.Named.Frame> -> &b: List<&1, P.Named.Frame> -> {a == fs : List<&1, P.Named.Frame>} & {b == fs : List<&1, P.Named.Frame>}:
  match fs:
    case Nil{}:
      (Nil{}, Nil{}, {==}, {==})
    case P.NF{+nm, f} <> rest:
      nf_dup.k(nm, f, rest, frame_dup(f), nf_dup(rest))

def env_dup.k(-fs: List<&1, P.Named.Frame>, -ss: List<&1, C.Frame>, wf: &a: List<&1, P.Named.Frame> -> &b: List<&1, P.Named.Frame> -> {a == fs : List<&1, P.Named.Frame>} & {b == fs : List<&1, P.Named.Frame>}, ws: &a: List<&1, C.Frame> -> &b: List<&1, C.Frame> -> {a == ss : List<&1, C.Frame>} & {b == ss : List<&1, C.Frame>})
  -> &a: P.Env -> &b: P.Env -> {a == P.Env{fs, ss} : P.Env} & {b == P.Env{fs, ss} : P.Env}:
  (f1, f2, ef1, ef2) = wf
  (s1, s2, es1, es2) = ws
  (P.Env{f1, s1}, P.Env{f2, s2}, (%es1 : {P.Env{f1, s1} == P.Env{fs, _} : P.Env}; %ef1 : {P.Env{f1, s1} == P.Env{_, s1} : P.Env}; {==}), (%es2 : {P.Env{f2, s2} == P.Env{fs, _} : P.Env}; %ef2 : {P.Env{f2, s2} == P.Env{_, s2} : P.Env}; {==}))

def env_dup(env: P.Env) -> &a: P.Env -> &b: P.Env -> {a == env : P.Env} & {b == env : P.Env}:
  match env:
    case P.Env{fs, ss}:
      env_dup.k(fs, ss, nf_dup(fs), fl_dup(ss))

def collect.k(+p: P.Plan, +k: U32, -env: P.Env, w: &a: P.Env -> &b: P.Env -> {a == env : P.Env} & {b == env : P.Env})
  -> {Laws.robs(Q.Exec.run_phys(P.Optimize.release(p), env), k) == Laws.robs(Q.Exec.run_pure(p, env), k) : Laws.RObs}:
  (e1, e2, +ee1, +ee2) = w
  %ee2 : {Laws.robs(Q.Exec.run_phys(P.Optimize.release(p), env), k) == Laws.robs(Q.Exec.run_pure(p, _), k) : Laws.RObs}
  %Laws.release_run(p, e2) : {Laws.robs(Q.Exec.run_phys(P.Optimize.release(p), env), k) == Laws.robs(_, k) : Laws.RObs}
  %Equal.sym(P.Env, e2, env, ee2) : {Laws.robs(Q.Exec.run_phys(P.Optimize.release(p), env), k) == Laws.robs(Q.Exec.run_pure(P.Optimize.release(p), _), k) : Laws.RObs}
  %ee1 : {Laws.robs(Q.Exec.run_phys(P.Optimize.release(p), _), k) == Laws.robs(Q.Exec.run_pure(P.Optimize.release(p), _), k) : Laws.RObs}
  Laws.run_phys_obs(P.Optimize.release(p), e1, k)

def Laws.collect_obs(p, env, k):
  collect.k(p, k, env, env_dup(env))
