# PROOF_strs.bend -- proofs of LAWS.bend section 14 (M5 part 3, P1): the Dictionary string
# storage (src/strs.bend) decodes to the same cells as the Raw storage, and the dictionary
# invariants (WFDictE: the entry list model, entry 0 = "", a sound index) are kept.
#
# Shape: the entries of a dictionary are modelled by a Data list `es` (duplicable), so the
# facts about every entry at once are Data equalities over `nthn` / `nthd`, not affine
# forall hypotheses over an array. The code-moving kernels (decode, gather, compact) are the
# section 11 theorems at the String / U32 instances: `tgather_*` is the gather loop proof of
# PROOF_contents as a template def (the law instances are String for Raw columns and the
# decode gather, U32 for the codes); `cspec_run` of PROOF_contents is already a template.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/eval.bend as V
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B
import ./PROOF_contents.bend as PC
import ./PROOF_eval.bend as PV

# ---- rd_at of a well-formed array as a forall (closed over the Data size equation) -------------------

# the array back (equal, well formed) and rd_at == rdN at EVERY index
def rd_all_k(-T: Data, +d: Nat, -a: Array<T>, w: &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & {Array.size(T, a) == (b, U32.shln(1, d)) : Array<T> & U32})
  -> &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & (@k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}):
  (b, +eb, wb, es) = w
  (b, eb, wb, +k => (%Equal.sym(Array<T> & U32, Array.size(T, a), (b, U32.shln(1, d)), es) : {Laws.rd_size(T, k, _) == Laws.rdN(T, d, a, k) : T}; %Equal.sym(Array<T>, b, a, eb) : {Laws.rd_size(T, k, (_, U32.shln(1, d))) == Laws.rdN(T, d, a, k) : T}; {==}))

def rd_all(-T: Data, +d: Nat, a: Array<T>, wf: Laws.WFArray(T, d, a)) -> &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & (@k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}):
  rd_all_k(T, d, a, PC.wf_size(T, d, a, wf))

# ---- the gather loop as a template (PROOF_contents' gather_* over a cell type T) --------------------

def TGHyp(~T: Data, +j: U32, +d: Nat, -src: Array<T>, -out: Array<T>, -perm: Array<U32>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(T, d, out, k) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}

def TGRes(~T: Data, +d: Nat, -src: Array<T>, -perm: Array<U32>, o: Array<T>, -pm: Array<U32>, +bound: U32) -> Type:
  {pm == perm : Array<U32>} & Laws.WFArray(T, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(T, d, o, k) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T})

def TGGoal(~T: Data, f: Nat, +j: U32, +d: Nat, -src: Array<T>, -out: Array<T>, -perm: Array<U32>, -r: Array<U32> & U32) -> Type:
  TGHyp(~T, j, d, src, out, perm) -> &o: Array<T> -> &pm: Array<U32> -> {K.Kernel.gather.go(~T, f, j, (src, out), r) == (o, pm) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o, pm, Laws.addn(j, f))

def TGMid(~T: Data, p: Nat, +j: U32, +d: Nat, -src: Array<T>, -out: Array<T>, -perm: Array<U32>, -rs: Array<T> & T) -> Type:
  TGHyp(~T, j, d, src, out, perm) -> &o: Array<T> -> &pm: Array<U32> -> {K.Kernel.gather.go(~T, p, U32.inc(j), K.Kernel.gather.put(~T, out, j, rs), Array.get(U32, perm, U32.inc(j))) == (o, pm) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o, pm, Laws.addn(j, 1n+p))

def TGSet(~T: Data, p: Nat, +j: U32, +d: Nat, -src: Array<T>, -out: Array<T>, -perm: Array<U32>, +y: T) -> Type:
  TGHyp(~T, j, d, src, out, perm) -> &o: Array<T> -> &pm: Array<U32> -> {K.Kernel.gather.go(~T, p, U32.inc(j), (src, Array.set(T, out, j, y)), Array.get(U32, perm, U32.inc(j))) == (o, pm) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o, pm, Laws.addn(j, 1n+p))

def TGC(~T: Data, p: Nat, +j: U32, +d: Nat, -src: Array<T>, -out: Array<T>, -c: Array<T>, -perm: Array<U32>, +bound: U32) -> Type:
  TGHyp(~T, j, d, src, out, perm) -> &o: Array<T> -> &pm: Array<U32> -> {K.Kernel.gather.go(~T, p, U32.inc(j), (src, c), Array.get(U32, perm, U32.inc(j))) == (o, pm) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o, pm, bound)

def tgnext_lt(~T: Data, +d: Nat, +j: U32, +k: U32, -src: Array<T>, -perm: Array<U32>, -out: Array<T>, -c: Array<T>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: T, g: TGHyp(~T, j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, j, k2), y, Laws.rdN(T, d, out, k2)) : T}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(T, d, c, k) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}:
  %Equal.sym(T, Laws.rdN(T, d, c, k), Bool.pick(T, Laws.same_at(d, j, k), y, Laws.rdN(T, d, out, k)), fj(k)) : {_ == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, PC.same_false_lt(d, j, k, hj, lt)) : {Bool.pick(T, _, y, Laws.rdN(T, d, out, k)) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}
  g(k, lt)

def tgnext_b(~T: Data, b: Bool, +d: Nat, +j: U32, +k: U32, -src: Array<T>, -perm: Array<U32>, -out: Array<T>, -c: Array<T>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: T, ey: {y == Laws.rd_at(T, src, Laws.rd_at(U32, perm, j)) : T}, g: TGHyp(~T, j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, j, k2), y, Laws.rdN(T, d, out, k2)) : T}, s: PC.IncLtU(b, k, j))
  -> {Laws.rdN(T, d, c, k) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}:
  match b:
    case True{}:
      tgnext_lt(~T, d, j, k, src, perm, out, c, hj, y, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(T, d, c, _) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, _)) : T}
      %Equal.sym(T, Laws.rdN(T, d, c, j), Bool.pick(T, Laws.same_at(d, j, j), y, Laws.rdN(T, d, out, j)), fj(j)) : {_ == Laws.rd_at(T, src, Laws.rd_at(U32, perm, j)) : T}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, PC.same_at_refl(d, j)) : {Bool.pick(T, _, y, Laws.rdN(T, d, out, j)) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, j)) : T}
      ey

def tgnext_k(~T: Data, +d: Nat, +j: U32, +k: U32, -src: Array<T>, -perm: Array<U32>, -out: Array<T>, -c: Array<T>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: T, ey: {y == Laws.rd_at(T, src, Laws.rd_at(U32, perm, j)) : T}, g: TGHyp(~T, j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, j, k2), y, Laws.rdN(T, d, out, k2)) : T}, w: &b: Bool -> PC.IncLtU(b, k, j))
  -> {Laws.rdN(T, d, c, k) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}:
  (b, s) = w
  tgnext_b(~T, b, d, j, k, src, perm, out, c, hj, y, ey, g, fj, s)

def tgnext(~T: Data, +d: Nat, +j: U32, -src: Array<T>, -perm: Array<U32>, -out: Array<T>, -c: Array<T>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: T, +ey: {y == Laws.rd_at(T, src, Laws.rd_at(U32, perm, j)) : T}, g: TGHyp(~T, j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, j, k2), y, Laws.rdN(T, d, out, k2)) : T})
  -> TGHyp(~T, U32.inc(j), d, src, c, perm):
  +k => hk => tgnext_k(~T, d, j, k, src, perm, out, c, hj, y, ey, g, fj, PC.inc_lt_u(k, j, hk))

def tgather_step3(~T: Data, p: Nat, +j: U32, +d: Nat, src: Array<T>, -out: Array<T>, perm: Array<U32>, +y: T, +ey: {y == Laws.rd_at(T, src, Laws.rd_at(U32, perm, j)) : T}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @src2: Array<T> -> @c: Array<T> -> @perm2: Array<U32> -> Laws.WFArray(T, d, c) -> Laws.Room(d, U32.inc(j), p) -> TGGoal(~T, p, U32.inc(j), d, src2, c, perm2, Array.get(U32, perm2, U32.inc(j))),
  w: &c: Array<T> -> {Array.set(T, out, j, y) == c : Array<T>} & Laws.WFArray(T, d, c) & (@k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, j, k2), y, Laws.rdN(T, d, out, k2)) : T}) & (@k2: U32 -> {Laws.rd_at(T, out, k2) == Laws.rdN(T, d, out, k2) : T}))
  -> TGSet(~T, p, j, d, src, out, perm, y):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<T>, Array.set(T, out, j, y), c, ec) : TGC(~T, p, j, d, src, out, _, perm, Laws.addn(j, 1n+p))
  %PC.addn_inc(j, p) : TGC(~T, p, j, d, src, out, c, perm, _)
  g => ih(src, c, perm, wc, room)(tgnext(~T, d, j, src, perm, out, c, hj, y, ey, g, fj))

def tgather_step2(~T: Data, p: Nat, +j: U32, +d: Nat, -src: Array<T>, out: Array<T>, perm: Array<U32>, wf: Laws.WFArray(T, d, out), +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @src2: Array<T> -> @c: Array<T> -> @perm2: Array<U32> -> Laws.WFArray(T, d, c) -> Laws.Room(d, U32.inc(j), p) -> TGGoal(~T, p, U32.inc(j), d, src2, c, perm2, Array.get(U32, perm2, U32.inc(j))),
  +x: U32, ex: {x == Laws.rd_at(U32, perm, j) : U32},
  w: &b: Array<T> -> &y: T -> {b == src : Array<T>} & {Array.get(T, src, x) == (src, y) : Array<T> & T} & {y == Laws.rd_at(T, src, x) : T})
  -> TGMid(~T, p, j, d, src, out, perm, Array.get(T, src, x)):
  (src2, +y, +es, e2, ey) = w
  %Equal.sym(Array<T> & T, Array.get(T, src, x), (src, y), e2) : TGMid(~T, p, j, d, src, out, perm, _)
  %es : TGSet(~T, p, j, d, _, out, perm, y)
  tgather_step3(~T, p, j, d, src2, out, perm, y, Equal.trans(T, y, Laws.rd_at(T, src2, x), Laws.rd_at(T, src2, Laws.rd_at(U32, perm, j)), Equal.trans(T, y, Laws.rd_at(T, src, x), Laws.rd_at(T, src2, x), ey, Equal.sym(T, Laws.rd_at(T, src2, x), Laws.rd_at(T, src, x), Equal.cong(Array<T>, T, a => Laws.rd_at(T, a, x), src2, src, es))), Equal.cong(U32, T, a => Laws.rd_at(T, src2, a), x, Laws.rd_at(U32, perm, j), ex)), hj, room, ih, PC.set_other_w(T, d, out, j, y, wf))

def tgather_step1(~T: Data, p: Nat, +j: U32, +d: Nat, src: Array<T>, out: Array<T>, -perm: Array<U32>, wf: Laws.WFArray(T, d, out), room: Laws.Room(d, j, 1n+p),
  ih: @src2: Array<T> -> @c: Array<T> -> @perm2: Array<U32> -> Laws.WFArray(T, d, c) -> Laws.Room(d, U32.inc(j), p) -> TGGoal(~T, p, U32.inc(j), d, src2, c, perm2, Array.get(U32, perm2, U32.inc(j))),
  w: &b: Array<U32> -> &x: U32 -> {b == perm : Array<U32>} & {Array.get(U32, perm, j) == (perm, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, perm, j) : U32})
  -> TGGoal(~T, 1n+p, j, d, src, out, perm, Array.get(U32, perm, j)):
  (hj, room2) = room
  (perm2, +x, +ep, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, perm, j), (perm, x), e1) : TGGoal(~T, 1n+p, j, d, src, out, perm, _)
  %ep : TGGoal(~T, 1n+p, j, d, src, out, _, (_, x))
  tgather_step2(~T, p, j, d, src, out, perm2, wf, hj, room2, ih, x, Equal.trans(U32, x, Laws.rd_at(U32, perm, j), Laws.rd_at(U32, perm2, j), ex, Equal.sym(U32, Laws.rd_at(U32, perm2, j), Laws.rd_at(U32, perm, j), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, a, j), perm2, perm, ep))), PC.get_w(T, src, x))

def tgather_zero(~T: Data, +j: U32, +d: Nat, src: Array<T>, out: Array<T>, -perm: Array<U32>, wf: Laws.WFArray(T, d, out),
  w: &b: Array<U32> -> &x: U32 -> {b == perm : Array<U32>} & {Array.get(U32, perm, j) == (perm, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, perm, j) : U32})
  -> TGGoal(~T, 0n, j, d, src, out, perm, Array.get(U32, perm, j)):
  (perm2, +x, ep, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, perm, j), (perm, x), e1) : TGGoal(~T, 0n, j, d, src, out, perm, _)
  %ep : TGGoal(~T, 0n, j, d, src, out, _, (_, x))
  g => (out, perm2, {==}, {==}, wf, g)

# Kernel.gather.go with f steps left at counter j, every k < j already right, the next f indices
# fitting the output: afterwards every k < addn(j, f) holds src[perm[k]]; perm comes back
def tgather_go(~T: Data, f: Nat, +j: U32, +d: Nat, src: Array<T>, out: Array<T>, perm: Array<U32>, wf: Laws.WFArray(T, d, out), room: Laws.Room(d, j, f)) -> TGGoal(~T, f, j, d, src, out, perm, Array.get(U32, perm, j)):
  match f:
    case 0n:
      tgather_zero(~T, j, d, src, out, perm, wf, PC.get_w(U32, perm, j))
    case 1n++p:
      tgather_step1(~T, p, j, d, src, out, perm, wf, room, src2 => c => perm2 => wc => room2 => tgather_go(~T, p, U32.inc(j), d, src2, c, perm2, wc, room2), PC.get_w(U32, perm, j))

def tghyp0(~T: Data, +d: Nat, -src: Array<T>, -out: Array<T>, -perm: Array<U32>) -> TGHyp(~T, 0, d, src, out, perm):
  +k => hk => Empty.absurd({Laws.rdN(T, d, out, k) == Laws.rd_at(T, src, Laws.rd_at(U32, perm, k)) : T}, PC.lt0(k, hk))

# the whole kernel as a witness: Kernel.gather(n, d, src, perm, z) == (o, pm) with pm == perm, o well
# formed, and o[k] == src[perm[k]] for every k < n
def TGW(~T: Data, +d: Nat, +n: U32, -src: Array<T>, -perm: Array<U32>, +z: T) -> Type:
  &o: Array<T> -> &pm: Array<U32> -> {K.Kernel.gather(~T, n, d, src, perm, z) == (o, pm) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o, pm, n)

def tgather_fin(~T: Data, +d: Nat, +n: U32, -src: Array<T>, -perm: Array<U32>, +z: T,
  w: &o: Array<T> -> &pm: Array<U32> -> {K.Kernel.gather.go(~T, U32.to_nat(n), 0, (src, Array.new(T, d, z)), Array.get(U32, perm, 0)) == (o, pm) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o, pm, Laws.addn(0, U32.to_nat(n))))
  -> TGW(~T, d, n, src, perm, z):
  (o, pm, eq, res) = w
  %B.addn_to_nat(n) : &o2: Array<T> -> &pm2: Array<U32> -> {K.Kernel.gather(~T, n, d, src, perm, z) == (o2, pm2) : Array<T> & Array<U32>} & TGRes(~T, d, src, perm, o2, pm2, _)
  (o, pm, eq, res)

def tgather_w(~T: Data, +d: Nat, +n: U32, src: Array<T>, perm: Array<U32>, +z: T, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}) -> TGW(~T, d, n, src, perm, z):
  tgather_fin(~T, d, n, src, perm, z, tgather_go(~T, U32.to_nat(n), 0, d, src, Array.new(T, d, z), perm, Laws.wf_new(T, d, z), B.room_from(d, n, fits))(tghyp0(~T, d, src, Array.new(T, d, z), perm)))

# ---- Laws.decode_cell ---------------------------------------------------------------------------------

# the gathered entries read as scell: o[i] == strs[codes[i]]
def decode_dict_k(+n: U32, +d: Nat, -codes: Array<U32>, +k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -slots: Array<ST.SSlot>, +tag: U32, +i: U32, hi: {U32.is_lt(i, n) == True{} : Bool}, w: TGW(~String, d, n, strs, codes, ""))
  -> {Laws.rd_at(String, ST.Dict.decode(n, d, codes, ST.Dict{k, dd, strs, b, slots, tag}), i) == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String}:
  (o, pm, eq, epm, wo, spec) = w
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.gather(~String, n, d, strs, codes, ""), (o, pm), eq) : {Laws.rd_at(String, ST.Strs.fst(~String, _), i) == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String}
  %Equal.sym(String, Laws.rd_at(String, o, i), Laws.rdN(String, d, o, i), Laws.rd_at_wf(String, d, o, i, wo)) : {_ == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String}
  spec(i, hi)

def decode_dict(+n: U32, +d: Nat, codes: Array<U32>, dict: ST.Dict, +i: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hi: {U32.is_lt(i, n) == True{} : Bool})
  -> {Laws.rd_at(String, ST.Dict.decode(n, d, codes, dict), i) == Laws.scell(ST.SDict{codes, dict}, i) : String}:
  match dict:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      decode_dict_k(n, d, codes, k, dd, strs, b, slots, tag, i, hi, tgather_w(~String, d, n, strs, codes, "", fits))

def Laws.decode_cell(n, d, s, i, fits, hi):
  match s:
    case ST.SRaw{a}:
      {==}
    case ST.SDict{codes, dict}:
      decode_dict(n, d, codes, dict, i, fits, hi)

# ---- Laws.strs_gather_cells ---------------------------------------------------------------------------

# the Raw case: the String gather; scell(SRaw{o}, k) is rd_at(o, k), rdN through rd_all (whose copy
# b of the output is the witness handed out)
def gather_raw_fin(+n: U32, +d: Nat, -a: Array<String>, -perm: Array<U32>, -o: Array<String>, pm: Array<U32>, +epm: {pm == perm : Array<U32>},
  spec: @k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.rdN(String, d, o, k) == Laws.rd_at(String, a, Laws.rd_at(U32, perm, k)) : String},
  w: &b: Array<String> -> {b == o : Array<String>} & Laws.WFArray(String, d, b) & (@k: U32 -> {Laws.rd_at(String, o, k) == Laws.rdN(String, d, o, k) : String}))
  -> &o2: ST.Strs -> &pm2: Array<U32> -> {ST.Strs.out.r((o, pm)) == (o2, pm2) : ST.Strs & Array<U32>} & {pm2 == perm : Array<U32>} & (@k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.scell(o2, k) == Laws.scell(ST.SRaw{a}, Laws.rd_at(U32, perm, k)) : String}):
  (b, +eb, wb, cv) = w
  (ST.SRaw{b}, pm, (%eb : {ST.Strs.out.r((_, pm)) == (ST.SRaw{b}, pm) : ST.Strs & Array<U32>}; {==}), epm, +k => hk => (%Equal.sym(Array<String>, b, o, eb) : {Laws.rd_at(String, _, k) == Laws.rd_at(String, a, Laws.rd_at(U32, perm, k)) : String}; %Equal.sym(String, Laws.rd_at(String, o, k), Laws.rdN(String, d, o, k), cv(k)) : {_ == Laws.rd_at(String, a, Laws.rd_at(U32, perm, k)) : String}; spec(k, hk)))

def gather_raw(+n: U32, +d: Nat, -a: Array<String>, -perm: Array<U32>, w: TGW(~String, d, n, a, perm, "")) -> Laws.GatherW(ST.SRaw{a}, perm, n, d):
  (o, pm, eq, +epm, wo, spec) = w
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.gather(~String, n, d, a, perm, ""), (o, pm), eq) : &o2: ST.Strs -> &pm2: Array<U32> -> {ST.Strs.out.r(_) == (o2, pm2) : ST.Strs & Array<U32>} & {pm2 == perm : Array<U32>} & (@k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.scell(o2, k) == Laws.scell(ST.SRaw{a}, Laws.rd_at(U32, perm, k)) : String})
  gather_raw_fin(n, d, a, perm, o, pm, epm, spec, rd_all(String, d, o, wo))

# the Dictionary case: the U32 gather of the codes; scell(SDict{o, dict}, k) is dentry(dict, rd_at(o, k))
def gather_dict_fin(+n: U32, +d: Nat, -codes: Array<U32>, dict: ST.Dict, -perm: Array<U32>, -o: Array<U32>, pm: Array<U32>, +epm: {pm == perm : Array<U32>},
  spec: @k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == Laws.rd_at(U32, codes, Laws.rd_at(U32, perm, k)) : U32},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, d, b) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32}))
  -> &o2: ST.Strs -> &pm2: Array<U32> -> {ST.Strs.out.d(dict, (o, pm)) == (o2, pm2) : ST.Strs & Array<U32>} & {pm2 == perm : Array<U32>} & (@k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.scell(o2, k) == Laws.scell(ST.SDict{codes, dict}, Laws.rd_at(U32, perm, k)) : String}):
  (b, +eb, wb, cv) = w
  (ST.SDict{b, dict}, pm, (%eb : {ST.Strs.out.d(dict, (_, pm)) == (ST.SDict{b, dict}, pm) : ST.Strs & Array<U32>}; {==}), epm, +k => hk => (%Equal.sym(Array<U32>, b, o, eb) : {Laws.dentry(dict, Laws.rd_at(U32, _, k)) == Laws.dentry(dict, Laws.rd_at(U32, codes, Laws.rd_at(U32, perm, k))) : String}; %Equal.sym(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, d, o, k), cv(k)) : {Laws.dentry(dict, _) == Laws.dentry(dict, Laws.rd_at(U32, codes, Laws.rd_at(U32, perm, k))) : String}; %Equal.sym(U32, Laws.rdN(U32, d, o, k), Laws.rd_at(U32, codes, Laws.rd_at(U32, perm, k)), spec(k, hk)) : {Laws.dentry(dict, _) == Laws.dentry(dict, Laws.rd_at(U32, codes, Laws.rd_at(U32, perm, k))) : String}; {==}))

def gather_dict(+n: U32, +d: Nat, -codes: Array<U32>, dict: ST.Dict, -perm: Array<U32>, w: TGW(~U32, d, n, codes, perm, 0)) -> Laws.GatherW(ST.SDict{codes, dict}, perm, n, d):
  (o, pm, eq, +epm, wo, spec) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, n, d, codes, perm, 0), (o, pm), eq) : &o2: ST.Strs -> &pm2: Array<U32> -> {ST.Strs.out.d(dict, _) == (o2, pm2) : ST.Strs & Array<U32>} & {pm2 == perm : Array<U32>} & (@k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.scell(o2, k) == Laws.scell(ST.SDict{codes, dict}, Laws.rd_at(U32, perm, k)) : String})
  gather_dict_fin(n, d, codes, dict, perm, o, pm, epm, spec, rd_all(U32, d, o, wo))

def Laws.strs_gather_cells(s, perm, n, d, fits):
  match s:
    case ST.SRaw{a}:
      gather_raw(n, d, a, perm, tgather_w(~String, d, n, a, perm, "", fits))
    case ST.SDict{codes, dict}:
      gather_dict(n, d, codes, dict, perm, tgather_w(~U32, d, n, codes, perm, 0, fits))

# ---- Laws.strs_clone_w / Laws.dict_clone_w (PROOF_eval's witnesses) ------------------------------------

def Laws.strs_clone_w(s):
  PV.sclone_w(s)

def Laws.dict_clone_w(d):
  PV.dclone_w(d)

# ---- Kernel.compact_keep as one witness: result pair, mask back, output well formed, CSpec --------------
# (PROOF_contents' cspec_run / cmask each consume the arrays and speak about Pair.fst / Pair.snd of
# the loop; the arrays are cloned, one copy per fact, and the facts restated to the originals)

# the output stays well formed: every step is one Array.set
def CWF(~T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, -a: Array<T>, -out: Array<T>, -r: Array<U32> & U32) -> Type:
  &o: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, f, i, k, (a, out), r)) == o : Array<T>} & Laws.WFArray(T, d, o)

def CWFmid(~T: Data, p: Nat, +i: U32, +k: U32, +x: U32, +d: Nat, -out: Array<T>, -mask: Array<U32>, -ra: Array<T> & T) -> Type:
  &o: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, x), K.Kernel.compact.put(~T, out, k, ra), Array.get(U32, mask, U32.inc(i)))) == o : Array<T>} & Laws.WFArray(T, d, o)

def cwf_s3(~T: Data, p: Nat, +i: U32, +k: U32, +x: U32, +d: Nat, a: Array<T>, -out: Array<T>, mask: Array<U32>, +y: T,
  ih: @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> Laws.WFArray(T, d, c) -> CWF(~T, p, U32.inc(i), U32.add(k, x), d, a2, c, Array.get(U32, m2, U32.inc(i))),
  w: &c: Array<T> -> {Array.set(T, out, k, y) == c : Array<T>} & Laws.WFArray(T, d, c) & (@k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, k, k2), y, Laws.rdN(T, d, out, k2)) : T}) & (@k2: U32 -> {Laws.rd_at(T, out, k2) == Laws.rdN(T, d, out, k2) : T}))
  -> CWF(~T, p, U32.inc(i), U32.add(k, x), d, a, Array.set(T, out, k, y), Array.get(U32, mask, U32.inc(i))):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<T>, Array.set(T, out, k, y), c, ec) : CWF(~T, p, U32.inc(i), U32.add(k, x), d, a, _, Array.get(U32, mask, U32.inc(i)))
  ih(a, c, mask, wc)

def cwf_s2(~T: Data, p: Nat, +i: U32, +k: U32, +x: U32, +d: Nat, -a: Array<T>, out: Array<T>, mask: Array<U32>, wf: Laws.WFArray(T, d, out),
  ih: @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> Laws.WFArray(T, d, c) -> CWF(~T, p, U32.inc(i), U32.add(k, x), d, a2, c, Array.get(U32, m2, U32.inc(i))),
  w: &a2: Array<T> -> &y: T -> {a2 == a : Array<T>} & {Array.get(T, a, i) == (a, y) : Array<T> & T} & {y == Laws.rd_at(T, a, i) : T})
  -> CWFmid(~T, p, i, k, x, d, out, mask, Array.get(T, a, i)):
  (a2, +y, ea, e2, ey) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, y), e2) : CWFmid(~T, p, i, k, x, d, out, mask, _)
  %ea : CWF(~T, p, U32.inc(i), U32.add(k, x), d, _, Array.set(T, out, k, y), Array.get(U32, mask, U32.inc(i)))
  cwf_s3(~T, p, i, k, x, d, a2, out, mask, y, ih, PC.set_other_w(T, d, out, k, y, wf))

def cwf_s1(~T: Data, p: Nat, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, -mask: Array<U32>, wf: Laws.WFArray(T, d, out),
  ih: @x: U32 -> @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> Laws.WFArray(T, d, c) -> CWF(~T, p, U32.inc(i), U32.add(k, x), d, a2, c, Array.get(U32, m2, U32.inc(i))),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> CWF(~T, 1n+p, i, k, d, a, out, Array.get(U32, mask, i)):
  (mask2, +x, em, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CWF(~T, 1n+p, i, k, d, a, out, _)
  %em : CWFmid(~T, p, i, k, x, d, out, _, Array.get(T, a, i))
  cwf_s2(~T, p, i, k, x, d, a, out, mask2, wf, ih(x), PC.get_w(T, a, i))

def cwf_zero(~T: Data, +i: U32, +k: U32, +d: Nat, -a: Array<T>, out: Array<T>, -mask: Array<U32>, wf: Laws.WFArray(T, d, out),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> CWF(~T, 0n, i, k, d, a, out, Array.get(U32, mask, i)):
  (mask2, +x, em, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CWF(~T, 0n, i, k, d, a, out, _)
  (out, {==}, wf)

def cwf(~T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, mask: Array<U32>, wf: Laws.WFArray(T, d, out)) -> CWF(~T, f, i, k, d, a, out, Array.get(U32, mask, i)):
  match f:
    case 0n:
      cwf_zero(~T, i, k, d, a, out, mask, wf, PC.get_w(U32, mask, i))
    case 1n++p:
      cwf_s1(~T, p, i, k, d, a, out, mask, wf, x => a2 => c => m2 => wc => cwf(~T, p, U32.inc(i), U32.add(k, x), d, a2, c, m2, wc), PC.get_w(U32, mask, i))

# the four facts over the production call on the live arrays a, mask
def CWfull(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -mask: Array<U32>, +z: T) -> Type:
  &o: Array<T> -> &m2: Array<U32> -> {K.Kernel.compact_keep(~T, len, d, a, mask, z) == (o, m2) : Array<T> & Array<U32>} & {m2 == mask : Array<U32>} & Laws.WFArray(T, d, o) & Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, o)

# a computed pair is some pair
def pair_eta(~T: Data, r: Array<T> & Array<U32>) -> &o: Array<T> -> &m2: Array<U32> -> {r == (o, m2) : Array<T> & Array<U32>}:
  (o, m2) = r
  (o, m2, {==})

# the facts on the copies, restated to the originals a / mask
def cf_eta(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -a1: Array<T>, -mask: Array<U32>, -m1: Array<U32>, +z: T, ea: {a1 == a : Array<T>}, em: {m1 == mask : Array<U32>},
  w: &o: Array<T> -> &m2: Array<U32> -> {K.Kernel.compact_keep(~T, len, d, a1, m1, z) == (o, m2) : Array<T> & Array<U32>})
  -> &o: Array<T> -> &m2: Array<U32> -> {K.Kernel.compact_keep(~T, len, d, a, mask, z) == (o, m2) : Array<T> & Array<U32>}:
  (o, m2, e) = w
  (o, m2, (%ea : {K.Kernel.compact_keep(~T, len, d, _, mask, z) == (o, m2) : Array<T> & Array<U32>}; %em : {K.Kernel.compact_keep(~T, len, d, a1, _, z) == (o, m2) : Array<T> & Array<U32>}; e))

def cf_mask(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -a3: Array<T>, -mask: Array<U32>, -m3: Array<U32>, +z: T, ea: {a3 == a : Array<T>}, em: {m3 == mask : Array<U32>},
  h: {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, U32.to_nat(len), 0, 0, (a3, Array.new(T, d, z)), Array.get(U32, m3, 0))) == m3 : Array<U32>})
  -> {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)) == mask : Array<U32>}:
  %ea : {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, _, mask, z)) == mask : Array<U32>}
  %em : {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a3, _, z)) == _ : Array<U32>}
  h

def cf_wf(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -a4: Array<T>, -mask: Array<U32>, -m4: Array<U32>, +z: T, ea: {a4 == a : Array<T>}, em: {m4 == mask : Array<U32>},
  h: CWF(~T, U32.to_nat(len), 0, 0, d, a4, Array.new(T, d, z), Array.get(U32, m4, 0)))
  -> &o3: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)) == o3 : Array<T>} & Laws.WFArray(T, d, o3):
  %ea : &o3: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, _, mask, z)) == o3 : Array<T>} & Laws.WFArray(T, d, o3)
  %em : &o3: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a4, _, z)) == o3 : Array<T>} & Laws.WFArray(T, d, o3)
  h

def cf_spec(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -a2: Array<T>, -mask: Array<U32>, -m2: Array<U32>, +z: T, ea: {a2 == a : Array<T>}, em: {m2 == mask : Array<U32>},
  h: PC.CS(~T, U32.to_nat(len), 0, 0, d, a2, Array.new(T, d, z), m2, Array.get(U32, m2, 0), a, mask))
  -> Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z))):
  %ea : Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, _, mask, z)))
  %em : Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a2, _, z)))
  h

def cf_fin2(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -mask: Array<U32>, +z: T, o: Array<T>, m2: Array<U32>,
  +e: {K.Kernel.compact_keep(~T, len, d, a, mask, z) == (o, m2) : Array<T> & Array<U32>},
  M: {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)) == mask : Array<U32>},
  W: &o3: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)) == o3 : Array<T>} & Laws.WFArray(T, d, o3),
  S: Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z))))
  -> CWfull(~T, len, d, a, mask, z):
  (o3, e3, w3) = W
  (o, m2, e, Equal.trans(Array<U32>, m2, Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)), mask, Equal.cong(Array<T> & Array<U32>, Array<U32>, r => Pair.snd(Array<T>, Array<U32>, r), (o, m2), K.Kernel.compact_keep(~T, len, d, a, mask, z), Equal.sym(Array<T> & Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z), (o, m2), e)), M), (%Equal.trans(Array<T>, o3, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)), o, Equal.sym(Array<T>, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)), o3, e3), Equal.cong(Array<T> & Array<U32>, Array<T>, r => Pair.fst(Array<T>, Array<U32>, r), K.Kernel.compact_keep(~T, len, d, a, mask, z), (o, m2), e)) : Laws.WFArray(T, d, _); w3), (%e : Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, Pair.fst(Array<T>, Array<U32>, _)); S))

def cf_fin(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -mask: Array<U32>, +z: T,
  E: &o: Array<T> -> &m2: Array<U32> -> {K.Kernel.compact_keep(~T, len, d, a, mask, z) == (o, m2) : Array<T> & Array<U32>},
  M: {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)) == mask : Array<U32>},
  W: &o3: Array<T> -> {Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z)) == o3 : Array<T>} & Laws.WFArray(T, d, o3),
  S: Laws.CSpec(T, U32.to_nat(len), 0, 0, d, a, mask, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep(~T, len, d, a, mask, z))))
  -> CWfull(~T, len, d, a, mask, z):
  (o, m2, e) = E
  cf_fin2(~T, len, d, a, mask, z, o, m2, e, M, W, S)

# the clones: a1 .. a4 copies of a (each with its equation), m1 .. m4 of mask
def cf_copies(~T: Data, +len: U32, +d: Nat, -a: Array<T>, -mask: Array<U32>, +z: T, room: Laws.CRoom(U32.to_nat(len), 0, 0, d, mask),
  wa: &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>},
  wm: &m1: Array<U32> -> &m2: Array<U32> -> &m3: Array<U32> -> &m4: Array<U32> -> {m1 == mask : Array<U32>} & {m2 == mask : Array<U32>} & {m3 == mask : Array<U32>} & {m4 == mask : Array<U32>})
  -> CWfull(~T, len, d, a, mask, z):
  (a1, a2, a3, a4, ea1, +ea2, ea3, ea4) = wa
  (m1, m2, m3, m4, em1, +em2, em3, em4) = wm
  cf_fin(~T, len, d, a, mask, z, cf_eta(~T, len, d, a, a1, mask, m1, z, ea1, em1, pair_eta(~T, K.Kernel.compact_keep(~T, len, d, a1, m1, z))), cf_mask(~T, len, d, a, a3, mask, m3, z, ea3, em3, PC.cmask(~T, U32.to_nat(len), 0, 0, a3, Array.new(T, d, z), m3)), cf_wf(~T, len, d, a, a4, mask, m4, z, ea4, em4, cwf(~T, U32.to_nat(len), 0, 0, d, a4, Array.new(T, d, z), m4, Laws.wf_new(T, d, z))), cf_spec(~T, len, d, a, a2, mask, m2, z, ea2, em2, PC.cspec_run(~T, U32.to_nat(len), 0, 0, d, a2, Array.new(T, d, z), m2, Laws.wf_new(T, d, z), a, mask, ea2, em2, room)))

# four copies of an array, each equal to it
def clone4_k3(-T: Data, -a: Array<T>, a1: Array<T>, a2: Array<T>, -c: Array<T>, e1: {a1 == a : Array<T>}, e2: {a2 == a : Array<T>}, +ec: {c == a : Array<T>}, w3: &a3: Array<T> -> &a4: Array<T> -> {a3 == c : Array<T>} & {a4 == c : Array<T>}) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  (a3, a4, e3, e4) = w3
  (a1, a2, a3, a4, e1, e2, Equal.trans(Array<T>, a3, c, a, e3, ec), Equal.trans(Array<T>, a4, c, a, e4, ec))

def clone4_k2(-T: Data, -a: Array<T>, a1: Array<T>, -b: Array<T>, e1: {a1 == a : Array<T>}, +eb: {b == a : Array<T>}, w2: &a2: Array<T> -> &c: Array<T> -> {a2 == b : Array<T>} & {c == b : Array<T>}) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  (a2, c, e2, ec) = w2
  clone4_k3(T, a, a1, a2, c, e1, Equal.trans(Array<T>, a2, b, a, e2, eb), Equal.trans(Array<T>, c, b, a, ec, eb), PC.clone_eq(T, c))

def clone4_k(-T: Data, -a: Array<T>, w1: &a1: Array<T> -> &b: Array<T> -> {a1 == a : Array<T>} & {b == a : Array<T>}) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  (a1, b, e1, eb) = w1
  clone4_k2(T, a, a1, b, e1, eb, PC.clone_eq(T, b))

def clone4(-T: Data, a: Array<T>) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  clone4_k(T, a, PC.clone_eq(T, a))

def compact_facts(~T: Data, +len: U32, +d: Nat, a: Array<T>, mask: Array<U32>, +z: T, room: Laws.CRoom(U32.to_nat(len), 0, 0, d, mask)) -> CWfull(~T, len, d, a, mask, z):
  cf_copies(~T, len, d, a, mask, z, room, clone4(T, a), clone4(U32, mask))

# ---- Laws.strs_compact_cells -------------------------------------------------------------------------

# CSpec over the codes (U32) read as scells of the Dictionary (rd_at(o, k) is rdN through the Data size
# equation of o's copy b, so every clause converts without an affine forall)
def cspec_to_d(f: Nat, +i: U32, +k: U32, +d: Nat, -codes: Array<U32>, -dict: ST.Dict, -mask: Array<U32>, -o: Array<U32>, -b: Array<U32>, +eb: {b == o : Array<U32>}, +es: {Array.size(U32, o) == (b, U32.shln(1, d)) : Array<U32> & U32}, spec: Laws.CSpec(U32, f, i, k, d, codes, mask, o))
  -> Laws.SCSpec(f, i, k, ST.SDict{codes, dict}, mask, ST.SDict{b, dict}):
  match f:
    case 0n:
      Unit{}
    case 1n++p:
      (+bb, e1, cl, rest) = spec
      (bb, e1, h => (%Equal.sym(Array<U32>, b, o, eb) : {Laws.dentry(dict, Laws.rd_at(U32, _, k)) == Laws.dentry(dict, Laws.rd_at(U32, codes, i)) : String}; %Equal.sym(Array<U32> & U32, Array.size(U32, o), (b, U32.shln(1, d)), es) : {Laws.dentry(dict, Laws.rd_size(U32, k, _)) == Laws.dentry(dict, Laws.rd_at(U32, codes, i)) : String}; %Equal.sym(Array<U32>, b, o, eb) : {Laws.dentry(dict, Laws.rd_size(U32, k, (_, U32.shln(1, d)))) == Laws.dentry(dict, Laws.rd_at(U32, codes, i)) : String}; %Equal.sym(U32, Laws.rdN(U32, d, o, k), Laws.rd_at(U32, codes, i), cl(h)) : {Laws.dentry(dict, _) == Laws.dentry(dict, Laws.rd_at(U32, codes, i)) : String}; {==}), cspec_to_d(p, U32.inc(i), U32.add(k, bb), d, codes, dict, mask, o, b, eb, es, rest))

# the same for a Raw column (String cells)
def cspec_to_r(f: Nat, +i: U32, +k: U32, +d: Nat, -a: Array<String>, -mask: Array<U32>, -o: Array<String>, -b: Array<String>, +eb: {b == o : Array<String>}, +es: {Array.size(String, o) == (b, U32.shln(1, d)) : Array<String> & U32}, spec: Laws.CSpec(String, f, i, k, d, a, mask, o))
  -> Laws.SCSpec(f, i, k, ST.SRaw{a}, mask, ST.SRaw{b}):
  match f:
    case 0n:
      Unit{}
    case 1n++p:
      (+bb, e1, cl, rest) = spec
      (bb, e1, h => (%Equal.sym(Array<String>, b, o, eb) : {Laws.rd_at(String, _, k) == Laws.rd_at(String, a, i) : String}; %Equal.sym(Array<String> & U32, Array.size(String, o), (b, U32.shln(1, d)), es) : {Laws.rd_size(String, k, _) == Laws.rd_at(String, a, i) : String}; %Equal.sym(Array<String>, b, o, eb) : {Laws.rd_size(String, k, (_, U32.shln(1, d))) == Laws.rd_at(String, a, i) : String}; cl(h)), cspec_to_r(p, U32.inc(i), U32.add(k, bb), d, a, mask, o, b, eb, es, rest))

def compact_dict_fin(+len: U32, +d: Nat, -codes: Array<U32>, dict: ST.Dict, -mask: Array<U32>, -o: Array<U32>, m2: Array<U32>, +em: {m2 == mask : Array<U32>}, spec: Laws.CSpec(U32, U32.to_nat(len), 0, 0, d, codes, mask, o),
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, d, b) & {Array.size(U32, o) == (b, U32.shln(1, d)) : Array<U32> & U32})
  -> &o2: ST.Strs -> &m22: Array<U32> -> {ST.Strs.out.d(dict, (o, m2)) == (o2, m22) : ST.Strs & Array<U32>} & {m22 == mask : Array<U32>} & Laws.SCSpec(U32.to_nat(len), 0, 0, ST.SDict{codes, dict}, mask, o2):
  (b, +eb, wb, es) = w
  (ST.SDict{b, dict}, m2, (%Equal.sym(Array<U32>, b, o, eb) : {ST.Strs.out.d(dict, (o, m2)) == (ST.SDict{_, dict}, m2) : ST.Strs & Array<U32>}; {==}), em, cspec_to_d(U32.to_nat(len), 0, 0, d, codes, dict, mask, o, b, eb, es, spec))

def compact_dict(+len: U32, +d: Nat, -codes: Array<U32>, dict: ST.Dict, -mask: Array<U32>, w: CWfull(~U32, len, d, codes, mask, 0)) -> Laws.CompactW(ST.SDict{codes, dict}, mask, len, d):
  (o, m2, e, +em, wo, spec) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.compact_keep(~U32, len, d, codes, mask, 0), (o, m2), e) : &o2: ST.Strs -> &m22: Array<U32> -> {ST.Strs.out.d(dict, _) == (o2, m22) : ST.Strs & Array<U32>} & {m22 == mask : Array<U32>} & Laws.SCSpec(U32.to_nat(len), 0, 0, ST.SDict{codes, dict}, mask, o2)
  compact_dict_fin(len, d, codes, dict, mask, o, m2, em, spec, PC.wf_size(U32, d, o, wo))

def compact_raw_fin(+len: U32, +d: Nat, -a: Array<String>, -mask: Array<U32>, -o: Array<String>, m2: Array<U32>, +em: {m2 == mask : Array<U32>}, spec: Laws.CSpec(String, U32.to_nat(len), 0, 0, d, a, mask, o),
  w: &b: Array<String> -> {b == o : Array<String>} & Laws.WFArray(String, d, b) & {Array.size(String, o) == (b, U32.shln(1, d)) : Array<String> & U32})
  -> &o2: ST.Strs -> &m22: Array<U32> -> {ST.Strs.out.r((o, m2)) == (o2, m22) : ST.Strs & Array<U32>} & {m22 == mask : Array<U32>} & Laws.SCSpec(U32.to_nat(len), 0, 0, ST.SRaw{a}, mask, o2):
  (b, +eb, wb, es) = w
  (ST.SRaw{b}, m2, (%Equal.sym(Array<String>, b, o, eb) : {ST.Strs.out.r((o, m2)) == (ST.SRaw{_}, m2) : ST.Strs & Array<U32>}; {==}), em, cspec_to_r(U32.to_nat(len), 0, 0, d, a, mask, o, b, eb, es, spec))

def compact_raw(+len: U32, +d: Nat, -a: Array<String>, -mask: Array<U32>, w: CWfull(~String, len, d, a, mask, "")) -> Laws.CompactW(ST.SRaw{a}, mask, len, d):
  (o, m2, e, +em, wo, spec) = w
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.compact_keep(~String, len, d, a, mask, ""), (o, m2), e) : &o2: ST.Strs -> &m22: Array<U32> -> {ST.Strs.out.r(_) == (o2, m22) : ST.Strs & Array<U32>} & {m22 == mask : Array<U32>} & Laws.SCSpec(U32.to_nat(len), 0, 0, ST.SRaw{a}, mask, o2)
  compact_raw_fin(len, d, a, mask, o, m2, em, spec, PC.wf_size(String, d, o, wo))

def Laws.strs_compact_cells(s, mask, len, d, room):
  match s:
    case ST.SRaw{a}:
      compact_raw(len, d, a, mask, compact_facts(~String, len, d, a, mask, "", room))
    case ST.SDict{codes, dict}:
      compact_dict(len, d, codes, dict, mask, compact_facts(~U32, len, d, codes, mask, 0, room))

# =====================================================================================
# The dictionary builders (LAWS.bend section 14, second part)
# =====================================================================================

# ---- Nat facts ---------------------------------------------------------------------------------------

def nat_cmp_refl(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_cmp_refl(p)

def nat_lt_succ(n: Nat) -> {Nat.cmp(n, 1n+n) == LT{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_lt_succ(p)

def nat_le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(n, n), EQ{}, nat_cmp_refl(n)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def nat_le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(n, 1n+n), LT{}, nat_lt_succ(n)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def zero_le(q: Nat) -> {Nat.is_le(0n, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

# a < b gives 1 + a <= b, and back
def succ_le_of_lt(a: Nat, b: Nat, h: {Cmp.is_lt(Nat.cmp(a, b)) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.false_true(h))
    case 0n 1n+q:
      zero_le(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      succ_le_of_lt(p, q, h)

def lt_of_succ_le(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Cmp.is_lt(Nat.cmp(a, b)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 0n)) == True{} : Bool}, L.false_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(1n+p, 0n)) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      lt_of_succ_le(p, q, h)

# a <= b gives a < 1 + b
def lt_succ_of_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Cmp.is_lt(Nat.cmp(a, 1n+b)) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(1n+p, 1n)) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      lt_succ_of_le(p, q, h)

def nat_le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      zero_le(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, L.false_true(h1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, L.false_true(h2))
    case 1n+p 1n+q 1n+r:
      nat_le_trans(p, q, r, h1, h2)

def nat_lt_le_trans(a: Nat, b: Nat, c: Nat, h1: {Cmp.is_lt(Nat.cmp(a, b)) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Cmp.is_lt(Nat.cmp(a, c)) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      Empty.absurd({Cmp.is_lt(Nat.cmp(a, c)) == True{} : Bool}, L.false_true(h1))
    case 0n 1n+q 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 0n)) == True{} : Bool}, L.false_true(h2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(1n+p, 0n)) == True{} : Bool}, L.false_true(h2))
    case 1n+p 1n+q 1n+r:
      nat_lt_le_trans(p, q, r, h1, h2)

def le_double(n: Nat) -> {Nat.is_le(n, Nat.double(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Cmp, Nat.cmp(p, 1n+Nat.double(p)), LT{}, B.is_lt_lt(Nat.cmp(p, 1n+Nat.double(p)), lt_succ_of_le(p, Nat.double(p), le_double(p)))) : {Cmp.is_le(_) == True{} : Bool}
      {==}

# 1 + n <= 2n for n >= 1
def succ_le_double(n: Nat, h: {Cmp.is_lt(Nat.cmp(0n, n)) == True{} : Bool}) -> {Nat.is_le(1n+n, Nat.double(n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.false_true(h))
    case 1n+p:
      le_double(p)

# ---- list facts (the entry list model) ------------------------------------------------------------------

def len_app1(es: List<&2, String>, +s: String) -> {List.length(&2, String, List.append(&2, String, es, s <> Nil{})) == 1n+List.length(&2, String, es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, t, s <> Nil{})), 1n+List.length(&2, String, t), len_app1(t, s)) : {1n+_ == 2n+List.length(&2, String, t) : Nat}
      {==}

def app_nil(es: List<&2, String>) -> {List.append(&2, String, es, Nil{}) == es : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<&2, String>, List.append(&2, String, t, Nil{}), t, app_nil(t)) : {h <> _ == h <> t : List<&2, String>}
      {==}

def app_assoc(xs: List<&2, String>, +ys: List<&2, String>, +zs: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, ys), zs) == List.append(&2, String, xs, List.append(&2, String, ys, zs)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, t, ys), zs), List.append(&2, String, t, List.append(&2, String, ys, zs)), app_assoc(t, ys, zs)) : {h <> _ == h <> List.append(&2, String, t, List.append(&2, String, ys, zs)) : List<&2, String>}
      {==}

# an index below the length reads the same entry after an append
def nth_app_lt(es: List<&2, String>, +more: List<&2, String>, j: Nat, h: {Cmp.is_lt(Nat.cmp(j, List.length(&2, String, es))) == True{} : Bool}) -> {Laws.nthn(List.append(&2, String, es, more), j) == Laws.nthn(es, j) : String}:
  match es j:
    case Nil{} 0n:
      Empty.absurd({Laws.nthn(more, 0n) == "" : String}, L.false_true(h))
    case Nil{} 1n+p:
      Empty.absurd({Laws.nthn(more, 1n+p) == "" : String}, L.false_true(h))
    case h2 <> t 0n:
      {==}
    case h2 <> t 1n+p:
      nth_app_lt(t, more, p, h)

# the appended entry sits at the old length
def nth_app_end(es: List<&2, String>, +s: String) -> {Laws.nthn(List.append(&2, String, es, s <> Nil{}), List.length(&2, String, es)) == s : String}:
  match es:
    case Nil{}:
      {==}
    case h <> t:
      nth_app_end(t, s)

# Ext is reflexive and transitive
def ext_refl(+es: List<&2, String>) -> Laws.Ext(es, es):
  (Nil{}, Equal.sym(List<&2, String>, List.append(&2, String, es, Nil{}), es, app_nil(es)))

def ext_trans_k(+es: List<&2, String>, +es2: List<&2, String>, +es3: List<&2, String>, +m1: List<&2, String>, +m2: List<&2, String>, e1: {es2 == List.append(&2, String, es, m1) : List<&2, String>}, e2: {es3 == List.append(&2, String, es2, m2) : List<&2, String>}) -> Laws.Ext(es, es3):
  (List.append(&2, String, m1, m2), (%app_assoc(es, m1, m2) : {es3 == _ : List<&2, String>}; %e1 : {es3 == List.append(&2, String, _, m2) : List<&2, String>}; e2))

def ext_trans(+es: List<&2, String>, +es2: List<&2, String>, +es3: List<&2, String>, x1: Laws.Ext(es, es2), x2: Laws.Ext(es2, es3)) -> Laws.Ext(es, es3):
  (m1, e1) = x1
  (m2, e2) = x2
  ext_trans_k(es, es2, es3, m1, m2, e1, e2)

# an extension keeps every entry below the old length, and is at least as long
def ext_nth(+es: List<&2, String>, +es2: List<&2, String>, x: Laws.Ext(es, es2), +j: Nat, h: {Cmp.is_lt(Nat.cmp(j, List.length(&2, String, es))) == True{} : Bool}) -> {Laws.nthn(es2, j) == Laws.nthn(es, j) : String}:
  (more, e) = x
  %Equal.sym(List<&2, String>, es2, List.append(&2, String, es, more), e) : {Laws.nthn(_, j) == Laws.nthn(es, j) : String}
  nth_app_lt(es, more, j, h)

def len_app_ge(es: List<&2, String>, +more: List<&2, String>) -> {Nat.is_le(List.length(&2, String, es), List.length(&2, String, List.append(&2, String, es, more))) == True{} : Bool}:
  match es:
    case Nil{}:
      zero_le(List.length(&2, String, more))
    case h <> t:
      len_app_ge(t, more)

def ext_len(+es: List<&2, String>, +es2: List<&2, String>, x: Laws.Ext(es, es2)) -> {Nat.is_le(List.length(&2, String, es), List.length(&2, String, es2)) == True{} : Bool}:
  (more, e) = x
  %Equal.sym(List<&2, String>, es2, List.append(&2, String, es, more), e) : {Nat.is_le(List.length(&2, String, es), List.length(&2, String, _)) == True{} : Bool}
  len_app_ge(es, more)

# ---- word facts: comparisons through to_nat, inc, dec, shl --------------------------------------------

def is_eq_eq(c: Cmp, h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.false_true(h))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.false_true(h))

# U32.is_eq is sound and complete
def u32_eq(x: U32, y: U32, h: {U32.is_eq(x, y) == True{} : Bool}) -> {x == y : U32}:
  match x y:
    case U32{+a} U32{+b}:
      Equal.cong(Word(32n), U32, w => U32{w}, a, b, L.word_cmp_eq(32n, a, b, is_eq_eq(Word.cmp(32n, a, b), h)))

def u32_eq_refl(x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{+a}:
      %Equal.sym(Cmp, Word.cmp(32n, a, a), EQ{}, L.word_cmp_refl(32n, a)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# the Nat value of a word below 2^30 after inc: one more (the word is not maximal)
def inc_small_k(b: Bool, +k: U32, s: B.IncSpecU(b, k), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.to_nat(U32.inc(k)) == 1n+U32.to_nat(k) : Nat}:
  match b:
    case True{}:
      s
    case False{}:
      Empty.absurd({U32.to_nat(U32.inc(k)) == 1n+U32.to_nat(k) : Nat}, s(U32.shln(1, 30n))(B.gt_of_lt_u(k, U32.shln(1, 30n), small)))

def inc_small_fin(+k: U32, w: &b: Bool -> B.IncSpecU(b, k), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.to_nat(U32.inc(k)) == 1n+U32.to_nat(k) : Nat}:
  (b, s) = w
  inc_small_k(b, k, s, small)

def inc_small(+k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.to_nat(U32.inc(k)) == 1n+U32.to_nat(k) : Nat}:
  inc_small_fin(k, B.inc_nat_u(k), small)

# U32 comparisons from Nat comparisons of the values
def lt_u_of_nat(+a: U32, +b: U32, h: {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == True{} : Bool}) -> {U32.is_lt(a, b) == True{} : Bool}:
  B.lt_of_nat_u(a, b, h)

def le_u_of_nat(+a: U32, +b: U32, h: {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}) -> {U32.is_le(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), B.cmp_nat_u(a, b)) : {Cmp.is_le(_) == True{} : Bool}
  h

def lt_nat_of_u(+a: U32, +b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == True{} : Bool}:
  %B.cmp_nat_u(a, b) : {Cmp.is_lt(_) == True{} : Bool}
  h

def eq_false_of_nat(+a: U32, +b: U32, h: {Nat.cmp(U32.to_nat(a), U32.to_nat(b)) == GT{} : Cmp}) -> {U32.is_eq(a, b) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), B.cmp_nat_u(a, b)) : {Cmp.is_eq(_) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(U32.to_nat(a), U32.to_nat(b)), GT{}, h) : {Cmp.is_eq(_) == False{} : Bool}
  {==}

# k < inc(k) for k below 2^30
def lt_inc(+k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.is_lt(k, U32.inc(k)) == True{} : Bool}:
  lt_u_of_nat(k, U32.inc(k), (%Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), inc_small(k, small)) : {Cmp.is_lt(Nat.cmp(U32.to_nat(k), _)) == True{} : Bool}; (%Equal.sym(Cmp, Nat.cmp(U32.to_nat(k), 1n+U32.to_nat(k)), LT{}, nat_lt_succ(U32.to_nat(k))) : {Cmp.is_lt(_) == True{} : Bool}; {==})))

# inc(k) != 0 for k below 2^30
def inc_ne_zero(+k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.is_eq(U32.inc(k), 0) == False{} : Bool}:
  eq_false_of_nat(U32.inc(k), 0, (%Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), inc_small(k, small)) : {Nat.cmp(_, U32.to_nat(0)) == GT{} : Cmp}; {==}))

# a <= b and a != b give a < b (the comparison as a parameter)
def le_ne_lt_k(c: Cmp, +a: U32, +b: U32, e: {U32.cmp(a, b) == c : Cmp}, hle: {Cmp.is_le(c) == True{} : Bool}, hne: {Cmp.is_eq(c) == False{} : Bool}) -> {U32.is_lt(a, b) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(a, b), LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      Empty.absurd({U32.is_lt(a, b) == True{} : Bool}, L.true_false(hne))
    case GT{}:
      Empty.absurd({U32.is_lt(a, b) == True{} : Bool}, L.false_true(hle))

def le_ne_lt(+a: U32, +b: U32, hle: {U32.is_le(a, b) == True{} : Bool}, hne: {U32.is_eq(a, b) == False{} : Bool}) -> {U32.is_lt(a, b) == True{} : Bool}:
  le_ne_lt_k(U32.cmp(a, b), a, b, {==}, hle, hne)

def lt_le_u(+a: U32, +b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> {U32.is_le(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), LT{}, B.is_lt_lt(U32.cmp(a, b), h)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

# a < b and b <= c give a < c
def lt_le_trans_u(+a: U32, +b: U32, +c: U32, h1: {U32.is_lt(a, b) == True{} : Bool}, h2: {U32.is_le(b, c) == True{} : Bool}) -> {U32.is_lt(a, c) == True{} : Bool}:
  lt_u_of_nat(a, c, nat_lt_le_trans(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c), lt_nat_of_u(a, b, h1), B.le_nat_u(b, c, h2)))

# to_nat(c) == 0 gives c == 0
def to_nat_zero(c: U32, h: {U32.to_nat(c) == 0n : Nat}) -> {c == 0 : U32}:
  match c:
    case U32{w}:
      %B.from_to(32n, w) : {U32{_} == 0 : U32}
      %Equal.sym(Nat, Word.to_nat(32n, w), 0n, h) : {U32{B.waddn(32n, Word.zero(32n), _)} == 0 : U32}
      {==}

# ---- dec of inc: U32.sub(U32.inc(k), 1) == k (Word.adc with the complement flag) ----------------------

# t - 0 == t (the complement of zero is all ones; with the carry in, the sum is t)
def sub_zero_w(n: Nat, t: Word(n)) -> {Word.adc(n, t, Word.zero(n), True{}, True{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, u}:
          %Equal.sym(Word(p), Word.adc(p, u, Word.zero(p), True{}, True{}), u, sub_zero_w(p, u)) : {WCon{False{}, _} == WCon{False{}, u} : Word(1n+p)}
          {==}
        case WCon{True{}, u}:
          %Equal.sym(Word(p), Word.adc(p, u, Word.zero(p), True{}, True{}), u, sub_zero_w(p, u)) : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}
          {==}

# inc(t) + ~0 (no carry in) == t
def dec_w(n: Nat, t: Word(n)) -> {Word.adc(n, Word.inc(n, t), Word.zero(n), True{}, False{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, u}:
          %Equal.sym(Word(p), Word.adc(p, u, Word.zero(p), True{}, True{}), u, sub_zero_w(p, u)) : {WCon{False{}, _} == WCon{False{}, u} : Word(1n+p)}
          {==}
        case WCon{True{}, u}:
          %Equal.sym(Word(p), Word.adc(p, Word.inc(p, u), Word.zero(p), True{}, False{}), u, dec_w(p, u)) : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}
          {==}

def dec_inc_w(n: Nat, w: Word(n)) -> {Word.sub(n, Word.inc(n, w), B.bitw(n, 0n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), True{}, True{}), t, sub_zero_w(p, t)) : {WCon{False{}, _} == WCon{False{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Word(p), Word.adc(p, Word.inc(p, t), Word.zero(p), True{}, False{}), t, dec_w(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}

def dec_inc(k: U32) -> {U32.sub(U32.inc(k), 1) == k : U32}:
  match k:
    case U32{w}:
      %Equal.sym(Word(32n), Word.sub(32n, Word.inc(32n, w), B.bitw(32n, 0n)), w, dec_inc_w(32n, w)) : {U32{_} == U32{w} : U32}
      {==}

# ---- shl through to_nat (the top bit clear): double -----------------------------------------------------

# Zabove is monotone in the position
def zabove_up(d: Nat, n: Nat, w: Word(n), hz: B.Zabove(d, n, w)) -> B.Zabove(1n+d, n, w):
  match d n:
    case 0n 0n:
      match w:
        case WNil{}:
          Unit{}
    case 0n 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Word(1n+p), WCon{b, t}, Word.zero(1n+p), hz) : B.Zabove(1n, 1n+p, _)
          {==}
    case 1n+r 0n:
      Unit{}
    case 1n+r 1n+p:
      match w:
        case WCon{b, t}:
          zabove_up(r, p, t, hz)

# shl.put inserts c below and drops a zero top bit: the value doubles plus c
def put_nat_zero(c: Bool, b: Bool, hz: {WCon{b, WNil{}} == Word.zero(1n) : Word(1n)}) -> {Word.to_nat(1n, Word.shl.put(1n, c, WCon{b, WNil{}})) == B.dbl(c, Word.to_nat(1n, WCon{b, WNil{}})) : Nat}:
  match c:
    case False{}:
      %Equal.sym(Word(1n), WCon{b, WNil{}}, Word.zero(1n), hz) : {Word.to_nat(1n, Word.shl.put(1n, False{}, _)) == B.dbl(False{}, Word.to_nat(1n, _)) : Nat}
      {==}
    case True{}:
      %Equal.sym(Word(1n), WCon{b, WNil{}}, Word.zero(1n), hz) : {Word.to_nat(1n, Word.shl.put(1n, True{}, _)) == B.dbl(True{}, Word.to_nat(1n, _)) : Nat}
      {==}

def put_nat_step(c: Bool, b: Bool, +r: Nat, -u: Word(1n+r), ih: {Word.to_nat(1n+r, Word.shl.put(1n+r, b, u)) == B.dbl(b, Word.to_nat(1n+r, u)) : Nat}) -> {Word.to_nat(2n+r, Word.shl.put(2n+r, c, WCon{b, u})) == B.dbl(c, Word.to_nat(2n+r, WCon{b, u})) : Nat}:
  match c b:
    case False{} False{}:
      %Equal.sym(Nat, Word.to_nat(1n+r, Word.shl.put(1n+r, False{}, u)), B.dbl(False{}, Word.to_nat(1n+r, u)), ih) : {Nat.double(_) == B.dbl(False{}, Word.to_nat(2n+r, WCon{False{}, u})) : Nat}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, Word.to_nat(1n+r, Word.shl.put(1n+r, True{}, u)), B.dbl(True{}, Word.to_nat(1n+r, u)), ih) : {Nat.double(_) == B.dbl(False{}, Word.to_nat(2n+r, WCon{True{}, u})) : Nat}
      {==}
    case True{} False{}:
      %Equal.sym(Nat, Word.to_nat(1n+r, Word.shl.put(1n+r, False{}, u)), B.dbl(False{}, Word.to_nat(1n+r, u)), ih) : {1n+Nat.double(_) == B.dbl(True{}, Word.to_nat(2n+r, WCon{False{}, u})) : Nat}
      {==}
    case True{} True{}:
      %Equal.sym(Nat, Word.to_nat(1n+r, Word.shl.put(1n+r, True{}, u)), B.dbl(True{}, Word.to_nat(1n+r, u)), ih) : {1n+Nat.double(_) == B.dbl(True{}, Word.to_nat(2n+r, WCon{True{}, u})) : Nat}
      {==}

def put_nat(q: Nat, +c: Bool, t: Word(1n+q), hz: B.Zabove(q, 1n+q, t)) -> {Word.to_nat(1n+q, Word.shl.put(1n+q, c, t)) == B.dbl(c, Word.to_nat(1n+q, t)) : Nat}:
  match q:
    case 0n:
      match t:
        case WCon{b, u}:
          match u:
            case WNil{}:
              put_nat_zero(c, b, hz)
    case 1n++r:
      match t:
        case WCon{+b, u}:
          put_nat_step(c, b, r, u, put_nat(r, b, u, hz))

def shl_nat_k(b: Bool, -t: Word(31n), h: {Word.to_nat(31n, Word.shl.put(31n, b, t)) == B.dbl(b, Word.to_nat(31n, t)) : Nat}) -> {Word.to_nat(32n, Word.shl(32n, WCon{b, t})) == Nat.double(Word.to_nat(32n, WCon{b, t})) : Nat}:
  match b:
    case False{}:
      %Equal.sym(Nat, Word.to_nat(31n, Word.shl.put(31n, False{}, t)), B.dbl(False{}, Word.to_nat(31n, t)), h) : {Nat.double(_) == Nat.double(Word.to_nat(32n, WCon{False{}, t})) : Nat}
      {==}
    case True{}:
      %Equal.sym(Nat, Word.to_nat(31n, Word.shl.put(31n, True{}, t)), B.dbl(True{}, Word.to_nat(31n, t)), h) : {Nat.double(_) == Nat.double(Word.to_nat(32n, WCon{True{}, t})) : Nat}
      {==}

def shl_nat_w(w: Word(32n), hz: B.Zabove(31n, 32n, w)) -> {Word.to_nat(32n, Word.shl(32n, w)) == Nat.double(Word.to_nat(32n, w)) : Nat}:
  match w:
    case WCon{+b, +t}:
      shl_nat_k(b, t, put_nat(30n, b, t, hz))

def U32.to_word(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# k below 2^30: to_nat(shl k) == 2 to_nat(k)
def shl_nat(k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.to_nat(U32.shl(k)) == Nat.double(U32.to_nat(k)) : Nat}:
  match k:
    case U32{+w}:
      shl_nat_w(w, zabove_up(30n, 32n, w, B.lt_bitw_zabove(32n, 30n, w, (%B.shln_bitw(30n) : {Word.cmp(32n, w, U32.to_word(_)) == LT{} : Cmp}; B.is_lt_lt(Word.cmp(32n, w, U32.to_word(U32.shln(1, 30n))), small)))))

# ---- Laws.str_same_sound / Laws.str_same_complete --------------------------------------------------------

# both conjuncts of a true Bool.and, from one hypothesis
def and_split(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, h)
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {b == True{} : Bool}, L.false_true(h))

def str_same_cons(+x: U32, +y: U32, +s: String, +t: String, w: {U32.is_eq(x, y) == True{} : Bool} & {ST.Str.same(s, t) == True{} : Bool}, ih: {ST.Str.same(s, t) == True{} : Bool} -> {s == t : String}) -> {SCon{Chr{x}, s} == SCon{Chr{y}, t} : String}:
  (hx, hs) = w
  %ih(hs) : {SCon{Chr{x}, s} == SCon{Chr{y}, _} : String}
  %u32_eq(x, y, hx) : {SCon{Chr{x}, s} == SCon{Chr{_}, s} : String}
  {==}

def Laws.str_same_sound(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, t}:
      Empty.absurd({SNil{} == SCon{y, t} : String}, L.false_true(h))
    case SCon{x, s} SNil{}:
      Empty.absurd({SCon{x, s} == SNil{} : String}, L.false_true(h))
    case SCon{Chr{+x}, +s} SCon{Chr{+y}, +t}:
      str_same_cons(x, y, s, t, and_split(U32.is_eq(x, y), ST.Str.same(s, t), h), h2 => Laws.str_same_sound(s, t, h2))

def Laws.str_same_complete(a):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +s}:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, u32_eq_refl(x)) : {Bool.and(_, ST.Str.same(s, s)) == True{} : Bool}
      Laws.str_same_complete(s)

# ---- Laws.dict_empty_wf (Dict.empty computes: "" hashes to slot 1 of the 4-slot index) ------------------

# nothing is below 0
def nat_lt0(p: Nat, h: {Cmp.is_lt(Nat.cmp(p, 0n)) == True{} : Bool}) -> Empty:
  match p:
    case 0n:
      L.false_true(h)
    case 1n+q:
      L.false_true(h)

def nat_lt1(n: Nat, h: {Cmp.is_lt(Nat.cmp(n, 1n)) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, nat_lt0(p, h))

# to_nat(c) < 1 gives to_nat(c) == 0
def lt1_zero(+c: U32, hc: {U32.is_lt(c, 1) == True{} : Bool}) -> {U32.to_nat(c) == 0n : Nat}:
  nat_lt1(U32.to_nat(c), lt_nat_of_u(c, 1, hc))

def empty_entries(+c: U32, hc: {U32.is_lt(c, 1) == True{} : Bool}) -> {Laws.rd_at(String, ALeaf{""}, c) == Laws.nthd("" <> Nil{}, c) : String}:
  %Equal.sym(U32, c, 0, to_nat_zero(c, lt1_zero(c, hc))) : {Laws.rd_at(String, ALeaf{""}, _) == Laws.nthd("" <> Nil{}, _) : String}
  {==}

def Laws.dict_empty_wf():
  ({==}, {==}, {==}, {==}, Unit{}, +c => hc => empty_entries(c, hc), ((Unit{}, ({==}, {==})), (Unit{}, Unit{})))

# ---- the index: SlotOk / WFIx structural lemmas (every lemma hands the inspected tree back) ---------------

# a SlotOk proof is Data: two copies
def dup2(-k: U32, -es: List<&2, String>, -key: String, -id: U32, +h1: {U32.is_lt(U32.sub(id, 1), k) == True{} : Bool}, +h2: {Laws.nthd(es, U32.sub(id, 1)) == key : String}) -> Laws.SlotOk.k(False{}, k, es, key, id) & Laws.SlotOk.k(False{}, k, es, key, id):
  ((h1, h2), (h1, h2))

def slotok_dup_k(e: Bool, +k: U32, +es: List<&2, String>, +key: String, +id: U32, p: Laws.SlotOk.k(e, k, es, key, id)) -> Laws.SlotOk.k(e, k, es, key, id) & Laws.SlotOk.k(e, k, es, key, id):
  match e:
    case True{}:
      (Unit{}, Unit{})
    case False{}:
      (h1, h2) = p
      dup2(k, es, key, id, h1, h2)

def slotok_dup(+k: U32, +es: List<&2, String>, x: ST.SSlot, p: Laws.SlotOk(k, es, x)) -> Laws.SlotOk(k, es, x) & Laws.SlotOk(k, es, x):
  match x:
    case ST.SSlot{+key, +id}:
      slotok_dup_k(U32.is_eq(id, 0), k, es, key, id, p)

# Array.size of a sound index: the tree back, 2^b slots
def wfix_size_node(+k: U32, +es: List<&2, String>, -xs: Array<ST.SSlot>, ys: Array<ST.SSlot>, +p: Nat, wr: Laws.WFIx(k, es, p, ys), w: &b: Array<ST.SSlot> -> {b == xs : Array<ST.SSlot>} & Laws.WFIx(k, es, p, b) & {Array.size(ST.SSlot, xs) == (b, U32.shln(1, p)) : Array<ST.SSlot> & U32})
  -> &b2: Array<ST.SSlot> -> {b2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+p, b2) & {Array.size(ST.SSlot, ANode{xs, ys}) == (b2, U32.shln(1, 1n+p)) : Array<ST.SSlot> & U32}:
  (b, eb, wb, es2) = w
  (ANode{b, ys}, (%eb : {ANode{b, ys} == ANode{_, ys} : Array<ST.SSlot>}; {==}), (wb, wr), (%Equal.sym(Array<ST.SSlot> & U32, Array.size(ST.SSlot, xs), (b, U32.shln(1, p)), es2) : {Array.size.node(ST.SSlot, ys, _) == (ANode{b, ys}, U32.shln(1, 1n+p)) : Array<ST.SSlot> & U32}; {==}))

def wfix_size(+k: U32, +es: List<&2, String>, b: Nat, t: Array<ST.SSlot>, wfx: Laws.WFIx(k, es, b, t)) -> &t2: Array<ST.SSlot> -> {t2 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t2) & {Array.size(ST.SSlot, t) == (t2, U32.shln(1, b)) : Array<ST.SSlot> & U32}:
  match b t:
    case 0n ALeaf{+x}:
      (ALeaf{x}, {==}, wfx, {==})
    case 1n++p ANode{xs, ys}:
      (wl, wr) = wfx
      wfix_size_node(k, es, xs, ys, p, wr, wfix_size(k, es, p, xs, wl))
    case 0n ANode{xs, ys}:
      Empty.absurd(&t2: Array<ST.SSlot> -> {t2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k, es, 0n, t2) & {Array.size(ST.SSlot, ANode{xs, ys}) == (t2, U32.shln(1, 0n)) : Array<ST.SSlot> & U32}, wfx)
    case 1n+p ALeaf{x}:
      Empty.absurd(&t2: Array<ST.SSlot> -> {t2 == ALeaf{x} : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+p, t2) & {Array.size(ST.SSlot, ALeaf{x}) == (t2, U32.shln(1, 1n+p)) : Array<ST.SSlot> & U32}, wfx)

# Array.swap.go with a sound slot keeps the index sound (the write goes down one path)
def wfix_swap_lo(+k: U32, +es: List<&2, String>, +p: Nat, -xs: Array<ST.SSlot>, ys: Array<ST.SSlot>, wr: Laws.WFIx(k, es, p, ys), +n: U32, +i: U32, +v: ST.SSlot,
  w: &c: Array<ST.SSlot> -> &o: ST.SSlot -> {Array.swap.go(ST.SSlot, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))) == (c, o) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, p, c))
  -> &c2: Array<ST.SSlot> -> &o2: ST.SSlot -> {Array.swap.lo(ST.SSlot, ys, Array.swap.go(ST.SSlot, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))) == (c2, o2) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, 1n+p, c2):
  (c, o, e, wc) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.swap.go(ST.SSlot, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), (c, o), e) : &c2: Array<ST.SSlot> -> &o2: ST.SSlot -> {Array.swap.lo(ST.SSlot, ys, _) == (c2, o2) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, 1n+p, c2)
  (ANode{c, ys}, o, {==}, (wc, wr))

def wfix_swap_hi(+k: U32, +es: List<&2, String>, +p: Nat, xs: Array<ST.SSlot>, -ys: Array<ST.SSlot>, wl: Laws.WFIx(k, es, p, xs), +n: U32, +i: U32, +v: ST.SSlot,
  w: &c: Array<ST.SSlot> -> &o: ST.SSlot -> {Array.swap.go(ST.SSlot, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) == (c, o) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, p, c))
  -> &c2: Array<ST.SSlot> -> &o2: ST.SSlot -> {Array.swap.hi(ST.SSlot, xs, Array.swap.go(ST.SSlot, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) == (c2, o2) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, 1n+p, c2):
  (c, o, e, wc) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.swap.go(ST.SSlot, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), (c, o), e) : &c2: Array<ST.SSlot> -> &o2: ST.SSlot -> {Array.swap.hi(ST.SSlot, xs, _) == (c2, o2) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, 1n+p, c2)
  (ANode{xs, c}, o, {==}, (wl, wc))

def wfix_swap(+k: U32, +es: List<&2, String>, b: Nat, t: Array<ST.SSlot>, +n: U32, +i: U32, +v: ST.SSlot, z: Bool, wfx: Laws.WFIx(k, es, b, t), ok: Laws.SlotOk(k, es, v)) -> &c: Array<ST.SSlot> -> &o: ST.SSlot -> {Array.swap.go(ST.SSlot, t, n, i, v, z) == (c, o) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, b, c):
  match b t z:
    case 0n ALeaf{x} _:
      (ALeaf{v}, x, {==}, ok)
    case 1n++p ANode{xs, ys} True{}:
      (wl, wr) = wfx
      wfix_swap_lo(k, es, p, xs, ys, wr, n, i, v, wfix_swap(k, es, p, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))), wl, ok))
    case 1n++p ANode{xs, ys} False{}:
      (wl, wr) = wfx
      wfix_swap_hi(k, es, p, xs, ys, wl, n, i, v, wfix_swap(k, es, p, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), wr, ok))
    case 0n ANode{xs, ys} zz:
      Empty.absurd(&c: Array<ST.SSlot> -> &o: ST.SSlot -> {Array.swap.go(ST.SSlot, ANode{xs, ys}, n, i, v, zz) == (c, o) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, 0n, c), wfx)
    case 1n+p ALeaf{x} zz:
      Empty.absurd(&c: Array<ST.SSlot> -> &o: ST.SSlot -> {Array.swap.go(ST.SSlot, ALeaf{x}, n, i, v, zz) == (c, o) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, 1n+p, c), wfx)

# Array.set of a sound slot keeps the index sound
def wfix_set_k2(+k: U32, +es: List<&2, String>, +b: Nat, -t2: Array<ST.SSlot>, +i: U32, +v: ST.SSlot,
  w: &c: Array<ST.SSlot> -> &o: ST.SSlot -> {Array.swap.go(ST.SSlot, t2, U32.shln(1, b), U32.and(i, U32.sub(U32.shln(1, b), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, b), 1)), U32.shr(U32.shln(1, b)))) == (c, o) : Array<ST.SSlot> & ST.SSlot} & Laws.WFIx(k, es, b, c))
  -> &c2: Array<ST.SSlot> -> {Array.set.fin(ST.SSlot, Array.swap.at(ST.SSlot, i, v, (t2, U32.shln(1, b)))) == c2 : Array<ST.SSlot>} & Laws.WFIx(k, es, b, c2):
  (c, o, e, wc) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.swap.go(ST.SSlot, t2, U32.shln(1, b), U32.and(i, U32.sub(U32.shln(1, b), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, b), 1)), U32.shr(U32.shln(1, b)))), (c, o), e) : &c2: Array<ST.SSlot> -> {Array.set.fin(ST.SSlot, _) == c2 : Array<ST.SSlot>} & Laws.WFIx(k, es, b, c2)
  (c, {==}, wc)

def wfix_set_k1(+k: U32, +es: List<&2, String>, +b: Nat, -t: Array<ST.SSlot>, +i: U32, +v: ST.SSlot, ok: Laws.SlotOk(k, es, v),
  w: &t2: Array<ST.SSlot> -> {t2 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t2) & {Array.size(ST.SSlot, t) == (t2, U32.shln(1, b)) : Array<ST.SSlot> & U32})
  -> &c: Array<ST.SSlot> -> {Array.set(ST.SSlot, t, i, v) == c : Array<ST.SSlot>} & Laws.WFIx(k, es, b, c):
  (t2, et, w2, es2) = w
  %Equal.sym(Array<ST.SSlot> & U32, Array.size(ST.SSlot, t), (t2, U32.shln(1, b)), es2) : &c: Array<ST.SSlot> -> {Array.set.fin(ST.SSlot, Array.swap.at(ST.SSlot, i, v, _)) == c : Array<ST.SSlot>} & Laws.WFIx(k, es, b, c)
  wfix_set_k2(k, es, b, t2, i, v, wfix_swap(k, es, b, t2, U32.shln(1, b), U32.and(i, U32.sub(U32.shln(1, b), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, b), 1)), U32.shr(U32.shln(1, b))), w2, ok))

def wfix_set(+k: U32, +es: List<&2, String>, +b: Nat, t: Array<ST.SSlot>, +i: U32, +v: ST.SSlot, wfx: Laws.WFIx(k, es, b, t), ok: Laws.SlotOk(k, es, v)) -> &c: Array<ST.SSlot> -> {Array.set(ST.SSlot, t, i, v) == c : Array<ST.SSlot>} & Laws.WFIx(k, es, b, c):
  wfix_set_k1(k, es, b, t, i, v, ok, wfix_size(k, es, b, t, wfx))

# the slot read at any index of a sound index is sound (the tree back, still sound)
def wfix_rd_leaf(+k: U32, +es: List<&2, String>, +x: ST.SSlot, -n: U32, -i: U32, -z: Bool, w: Laws.SlotOk(k, es, x) & Laws.SlotOk(k, es, x)) -> &t2: Array<ST.SSlot> -> {t2 == ALeaf{x} : Array<ST.SSlot>} & Laws.WFIx(k, es, 0n, t2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, ALeaf{x}, n, i, z)):
  (p1, p2) = w
  (ALeaf{x}, {==}, p1, p2)

def wfix_rd_lo(+k: U32, +es: List<&2, String>, +p: Nat, -xs: Array<ST.SSlot>, ys: Array<ST.SSlot>, wr: Laws.WFIx(k, es, p, ys), +n: U32, +i: U32,
  w: &xs2: Array<ST.SSlot> -> {xs2 == xs : Array<ST.SSlot>} & Laws.WFIx(k, es, p, xs2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))))
  -> &t2: Array<ST.SSlot> -> {t2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+p, t2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, ANode{xs, ys}, n, i, True{})):
  (xs2, e, w2, ok) = w
  (ANode{xs2, ys}, (%e : {ANode{xs2, ys} == ANode{_, ys} : Array<ST.SSlot>}; {==}), (w2, wr), ok)

def wfix_rd_hi(+k: U32, +es: List<&2, String>, +p: Nat, xs: Array<ST.SSlot>, -ys: Array<ST.SSlot>, wl: Laws.WFIx(k, es, p, xs), +n: U32, +i: U32,
  w: &ys2: Array<ST.SSlot> -> {ys2 == ys : Array<ST.SSlot>} & Laws.WFIx(k, es, p, ys2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))))
  -> &t2: Array<ST.SSlot> -> {t2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+p, t2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, ANode{xs, ys}, n, i, False{})):
  (ys2, e, w2, ok) = w
  (ANode{xs, ys2}, (%e : {ANode{xs, ys2} == ANode{xs, _} : Array<ST.SSlot>}; {==}), (wl, w2), ok)

def wfix_rd_go(+k: U32, +es: List<&2, String>, b: Nat, t: Array<ST.SSlot>, +n: U32, +i: U32, z: Bool, wfx: Laws.WFIx(k, es, b, t)) -> &t2: Array<ST.SSlot> -> {t2 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, t, n, i, z)):
  match b t z:
    case 0n ALeaf{+x} zz:
      wfix_rd_leaf(k, es, x, n, i, zz, slotok_dup(k, es, x, wfx))
    case 1n++p ANode{xs, ys} True{}:
      (wl, wr) = wfx
      wfix_rd_lo(k, es, p, xs, ys, wr, n, i, wfix_rd_go(k, es, p, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))), wl))
    case 1n++p ANode{xs, ys} False{}:
      (wl, wr) = wfx
      wfix_rd_hi(k, es, p, xs, ys, wl, n, i, wfix_rd_go(k, es, p, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), wr))
    case 0n ANode{xs, ys} zz:
      Empty.absurd(&t2: Array<ST.SSlot> -> {t2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k, es, 0n, t2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, ANode{xs, ys}, n, i, zz)), wfx)
    case 1n+p ALeaf{x} zz:
      Empty.absurd(&t2: Array<ST.SSlot> -> {t2 == ALeaf{x} : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+p, t2) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, ALeaf{x}, n, i, zz)), wfx)

def wfix_rd_fin(+k: U32, +es: List<&2, String>, +b: Nat, -t: Array<ST.SSlot>, -t2: Array<ST.SSlot>, et: {t2 == t : Array<ST.SSlot>}, +j: U32,
  w: &t3: Array<ST.SSlot> -> {t3 == t2 : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t3) & Laws.SlotOk(k, es, Laws.rd(ST.SSlot, t2, U32.shln(1, b), U32.and(j, U32.sub(U32.shln(1, b), 1)), U32.is_lt(U32.and(j, U32.sub(U32.shln(1, b), 1)), U32.shr(U32.shln(1, b))))))
  -> &t3: Array<ST.SSlot> -> {t3 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t3) & Laws.SlotOk(k, es, Laws.rd_size(ST.SSlot, j, (t2, U32.shln(1, b)))):
  (t3, e3, w3, ok) = w
  (t3, Equal.trans(Array<ST.SSlot>, t3, t2, t, e3, et), w3, ok)

def wfix_rd_k(+k: U32, +es: List<&2, String>, +b: Nat, -t: Array<ST.SSlot>, +j: U32, w: &t2: Array<ST.SSlot> -> {t2 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t2) & {Array.size(ST.SSlot, t) == (t2, U32.shln(1, b)) : Array<ST.SSlot> & U32})
  -> &t3: Array<ST.SSlot> -> {t3 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t3) & Laws.SlotOk(k, es, Laws.rd_at(ST.SSlot, t, j)):
  (t2, +et, w2, es2) = w
  %Equal.sym(Array<ST.SSlot> & U32, Array.size(ST.SSlot, t), (t2, U32.shln(1, b)), es2) : &t3: Array<ST.SSlot> -> {t3 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t3) & Laws.SlotOk(k, es, Laws.rd_size(ST.SSlot, j, _))
  wfix_rd_fin(k, es, b, t, t2, et, j, wfix_rd_go(k, es, b, t2, U32.shln(1, b), U32.and(j, U32.sub(U32.shln(1, b), 1)), U32.is_lt(U32.and(j, U32.sub(U32.shln(1, b), 1)), U32.shr(U32.shln(1, b))), w2))

def wfix_rd(+k: U32, +es: List<&2, String>, +b: Nat, t: Array<ST.SSlot>, +j: U32, wfx: Laws.WFIx(k, es, b, t)) -> &t3: Array<ST.SSlot> -> {t3 == t : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t3) & Laws.SlotOk(k, es, Laws.rd_at(ST.SSlot, t, j)):
  wfix_rd_k(k, es, b, t, j, wfix_size(k, es, b, t, wfx))

# a sound index stays sound for more entries (k2 >= k with es2 extending es)
def slotok_mono_k(e: Bool, +k: U32, +k2: U32, +es: List<&2, String>, +es2: List<&2, String>, +more: List<&2, String>, +e2: {es2 == List.append(&2, String, es, more) : List<&2, String>}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hk: {U32.is_le(k, k2) == True{} : Bool}, +key: String, +id: U32, p: Laws.SlotOk.k(e, k, es, key, id)) -> Laws.SlotOk.k(e, k2, es2, key, id):
  match e:
    case True{}:
      Unit{}
    case False{}:
      (+h1, h2) = p
      (lt_le_trans_u(U32.sub(id, 1), k, k2, h1, hk), (%Equal.sym(List<&2, String>, es2, List.append(&2, String, es, more), e2) : {Laws.nthn(_, U32.to_nat(U32.sub(id, 1))) == key : String}; %Equal.sym(String, Laws.nthn(List.append(&2, String, es, more), U32.to_nat(U32.sub(id, 1))), Laws.nthn(es, U32.to_nat(U32.sub(id, 1))), nth_app_lt(es, more, U32.to_nat(U32.sub(id, 1)), (%ek : {Cmp.is_lt(Nat.cmp(U32.to_nat(U32.sub(id, 1)), _)) == True{} : Bool}; lt_nat_of_u(U32.sub(id, 1), k, h1)))) : {_ == key : String}; h2))

def slotok_mono(+k: U32, +k2: U32, +es: List<&2, String>, +es2: List<&2, String>, +more: List<&2, String>, +e2: {es2 == List.append(&2, String, es, more) : List<&2, String>}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hk: {U32.is_le(k, k2) == True{} : Bool}, x: ST.SSlot, p: Laws.SlotOk(k, es, x)) -> Laws.SlotOk(k2, es2, x):
  match x:
    case ST.SSlot{+key, +id}:
      slotok_mono_k(U32.is_eq(id, 0), k, k2, es, es2, more, e2, ek, hk, key, id, p)

def wfix_mono_node(+k2: U32, +es2: List<&2, String>, -xs: Array<ST.SSlot>, -ys: Array<ST.SSlot>, +p: Nat, wx: &x2: Array<ST.SSlot> -> {x2 == xs : Array<ST.SSlot>} & Laws.WFIx(k2, es2, p, x2), wy: &y2: Array<ST.SSlot> -> {y2 == ys : Array<ST.SSlot>} & Laws.WFIx(k2, es2, p, y2)) -> &t2: Array<ST.SSlot> -> {t2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k2, es2, 1n+p, t2):
  (x2, ex, wx2) = wx
  (y2, ey, wy2) = wy
  (ANode{x2, y2}, (%ey : {ANode{x2, y2} == ANode{xs, _} : Array<ST.SSlot>}; %ex : {ANode{x2, y2} == ANode{_, y2} : Array<ST.SSlot>}; {==}), (wx2, wy2))

def wfix_mono(+k: U32, +k2: U32, +es: List<&2, String>, +es2: List<&2, String>, +more: List<&2, String>, +e2: {es2 == List.append(&2, String, es, more) : List<&2, String>}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hk: {U32.is_le(k, k2) == True{} : Bool}, b: Nat, t: Array<ST.SSlot>, wfx: Laws.WFIx(k, es, b, t)) -> &t2: Array<ST.SSlot> -> {t2 == t : Array<ST.SSlot>} & Laws.WFIx(k2, es2, b, t2):
  match b t:
    case 0n ALeaf{+x}:
      (ALeaf{x}, {==}, slotok_mono(k, k2, es, es2, more, e2, ek, hk, x, wfx))
    case 1n++p ANode{xs, ys}:
      (wl, wr) = wfx
      wfix_mono_node(k2, es2, xs, ys, p, wfix_mono(k, k2, es, es2, more, e2, ek, hk, p, xs, wl), wfix_mono(k, k2, es, es2, more, e2, ek, hk, p, ys, wr))
    case 0n ANode{xs, ys}:
      Empty.absurd(&t2: Array<ST.SSlot> -> {t2 == ANode{xs, ys} : Array<ST.SSlot>} & Laws.WFIx(k2, es2, 0n, t2), wfx)
    case 1n+p ALeaf{x}:
      Empty.absurd(&t2: Array<ST.SSlot> -> {t2 == ALeaf{x} : Array<ST.SSlot>} & Laws.WFIx(k2, es2, 1n+p, t2), wfx)

# ---- the probe Ix.seek is pure: the slots back, some index --------------------------------------------

def look_red(-t: Array<ST.SSlot>, +s: String, x: ST.SSlot) -> {ST.Ix.look(s, (t, x)) == (t, Laws.look_bit(s, x)) : Array<ST.SSlot> & Bool}:
  match x:
    case ST.SSlot{key, id}:
      {==}

def SeekW(-t: Array<ST.SSlot>, +n: Nat, +c: Bool, +s: String, +mask: U32, +i: U32) -> Type:
  &t2: Array<ST.SSlot> -> &i2: U32 -> {ST.Ix.seek.go(n, (t, c), s, mask, i) == (t2, i2) : Array<ST.SSlot> & U32} & {t2 == t : Array<ST.SSlot>}

def seek_step(p: Nat, -t: Array<ST.SSlot>, +s: String, +mask: U32, +i: U32,
  w: &t2: Array<ST.SSlot> -> &x: ST.SSlot -> {t2 == t : Array<ST.SSlot>} & {Array.get(ST.SSlot, t, U32.and(U32.inc(i), mask)) == (t, x) : Array<ST.SSlot> & ST.SSlot} & {x == Laws.rd_at(ST.SSlot, t, U32.and(U32.inc(i), mask)) : ST.SSlot},
  ih: @t3: Array<ST.SSlot> -> @c3: Bool -> SeekW(t3, p, c3, s, mask, U32.and(U32.inc(i), mask)))
  -> SeekW(t, 1n+p, True{}, s, mask, i):
  (t2, +x, et, e1, ex) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.get(ST.SSlot, t, U32.and(U32.inc(i), mask)), (t, x), e1) : &t4: Array<ST.SSlot> -> &i4: U32 -> {ST.Ix.seek.go(p, ST.Ix.look(s, _), s, mask, U32.and(U32.inc(i), mask)) == (t4, i4) : Array<ST.SSlot> & U32} & {t4 == t : Array<ST.SSlot>}
  %Equal.sym(Array<ST.SSlot> & Bool, ST.Ix.look(s, (t, x)), (t, Laws.look_bit(s, x)), look_red(t, s, x)) : &t4: Array<ST.SSlot> -> &i4: U32 -> {ST.Ix.seek.go(p, _, s, mask, U32.and(U32.inc(i), mask)) == (t4, i4) : Array<ST.SSlot> & U32} & {t4 == t : Array<ST.SSlot>}
  %et : SeekW(_, p, Laws.look_bit(s, x), s, mask, U32.and(U32.inc(i), mask))
  ih(t2, Laws.look_bit(s, x))

def seek_go_w(n: Nat, t: Array<ST.SSlot>, c: Bool, +s: String, +mask: U32, +i: U32) -> SeekW(t, n, c, s, mask, i):
  match n c:
    case 0n False{}:
      (t, i, {==}, {==})
    case 0n True{}:
      (t, i, {==}, {==})
    case 1n+p False{}:
      (t, i, {==}, {==})
    case 1n++p True{}:
      seek_step(p, t, s, mask, i, PC.get_w(ST.SSlot, t, U32.and(U32.inc(i), mask)), t3 => c3 => seek_go_w(p, t3, c3, s, mask, U32.and(U32.inc(i), mask)))

def seek_w_k(+b: Nat, -slots: Array<ST.SSlot>, +h: U32, +s: String,
  w: &t2: Array<ST.SSlot> -> &x: ST.SSlot -> {t2 == slots : Array<ST.SSlot>} & {Array.get(ST.SSlot, slots, ST.Ix.slot(h, b)) == (slots, x) : Array<ST.SSlot> & ST.SSlot} & {x == Laws.rd_at(ST.SSlot, slots, ST.Ix.slot(h, b)) : ST.SSlot})
  -> &t3: Array<ST.SSlot> -> &i3: U32 -> {ST.Ix.seek(b, slots, h, s) == (t3, i3) : Array<ST.SSlot> & U32} & {t3 == slots : Array<ST.SSlot>}:
  (t2, +x, et, e1, ex) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.get(ST.SSlot, slots, ST.Ix.slot(h, b)), (slots, x), e1) : &t3: Array<ST.SSlot> -> &i3: U32 -> {ST.Ix.seek.go(U32.to_nat(U32.shln(1, b)), ST.Ix.look(s, _), s, U32.sub(U32.shln(1, b), 1), ST.Ix.slot(h, b)) == (t3, i3) : Array<ST.SSlot> & U32} & {t3 == slots : Array<ST.SSlot>}
  %Equal.sym(Array<ST.SSlot> & Bool, ST.Ix.look(s, (slots, x)), (slots, Laws.look_bit(s, x)), look_red(slots, s, x)) : &t3: Array<ST.SSlot> -> &i3: U32 -> {ST.Ix.seek.go(U32.to_nat(U32.shln(1, b)), _, s, U32.sub(U32.shln(1, b), 1), ST.Ix.slot(h, b)) == (t3, i3) : Array<ST.SSlot> & U32} & {t3 == slots : Array<ST.SSlot>}
  %et : SeekW(_, U32.to_nat(U32.shln(1, b)), Laws.look_bit(s, x), s, U32.sub(U32.shln(1, b), 1), ST.Ix.slot(h, b))
  seek_go_w(U32.to_nat(U32.shln(1, b)), t2, Laws.look_bit(s, x), s, U32.sub(U32.shln(1, b), 1), ST.Ix.slot(h, b))

# Ix.seek(b, slots, h, s) == (t, i) with t == slots
def seek_w(+b: Nat, slots: Array<ST.SSlot>, +h: U32, +s: String) -> &t3: Array<ST.SSlot> -> &i3: U32 -> {ST.Ix.seek(b, slots, h, s) == (t3, i3) : Array<ST.SSlot> & U32} & {t3 == slots : Array<ST.SSlot>}:
  seek_w_k(b, slots, h, s, PC.get_w(ST.SSlot, slots, ST.Ix.slot(h, b)))

# the id of a slot (what Ix.id reads)
def sid(x: ST.SSlot) -> U32:
  match x:
    case ST.SSlot{k, id}:
      id

def idk_red(-t: Array<ST.SSlot>, x: ST.SSlot) -> {ST.Ix.id.k((t, x)) == (t, sid(x)) : Array<ST.SSlot> & U32}:
  match x:
    case ST.SSlot{k, id}:
      {==}

# casts along equations
def wfix_cast(+k: U32, +es: List<&2, String>, +b: Nat, -t: Array<ST.SSlot>, -t2: Array<ST.SSlot>, e: {t2 == t : Array<ST.SSlot>}, w: Laws.WFIx(k, es, b, t)) -> Laws.WFIx(k, es, b, t2):
  %Equal.sym(Array<ST.SSlot>, t2, t, e) : Laws.WFIx(k, es, b, _)
  w

def slotok_cast(+k: U32, +es: List<&2, String>, -x: ST.SSlot, -y: ST.SSlot, e: {x == y : ST.SSlot}, p: Laws.SlotOk(k, es, y)) -> Laws.SlotOk(k, es, x):
  %Equal.sym(ST.SSlot, x, y, e) : Laws.SlotOk(k, es, _)
  p

# the fresh index of Ix.grow is sound (every slot empty)
def wfix_new(+k: U32, +es: List<&2, String>, b: Nat) -> Laws.WFIx(k, es, b, Array.new(ST.SSlot, b, ST.SSlot{"", 0})):
  match b:
    case 0n:
      Unit{}
    case 1n++p:
      (wfix_new(k, es, p), wfix_new(k, es, p))

# ---- Ix.grow keeps the index sound at the doubled depth ---------------------------------------------------

# Ix.move: one old slot re-inserted into the new table (an empty old slot is skipped)
def MoveW(+k: U32, +es: List<&2, String>, +b2: Nat, -nt: Array<ST.SSlot>, +x: ST.SSlot) -> Type:
  &g: Array<ST.SSlot> -> {ST.Ix.move(b2, nt, x) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)

def MoveK(+k: U32, +es: List<&2, String>, +b2: Nat, -nt: Array<ST.SSlot>, +key: String, +id: U32, +e: Bool, -r: Array<ST.SSlot> & U32) -> Type:
  &g: Array<ST.SSlot> -> {ST.Ix.move.k(Bool.not(e), key, id, r) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)

def move_k2(+k: U32, +es: List<&2, String>, +b2: Nat, nt2: Array<ST.SSlot>, +key: String, +id: U32, e: Bool, +i: U32, ee: {U32.is_eq(id, 0) == e : Bool}, ok: Laws.SlotOk.k(e, k, es, key, id), wf: Laws.WFIx(k, es, b2, nt2)) -> MoveK(k, es, b2, nt2, key, id, e, (nt2, i)):
  match e:
    case True{}:
      (nt2, {==}, wf)
    case False{}:
      wfix_set(k, es, b2, nt2, i, ST.SSlot{key, id}, wf, (%Equal.sym(Bool, U32.is_eq(id, 0), False{}, ee) : Laws.SlotOk.k(_, k, es, key, id); ok))

def move_k(+k: U32, +es: List<&2, String>, +b2: Nat, -nt: Array<ST.SSlot>, +key: String, +id: U32, e: Bool, ee: {U32.is_eq(id, 0) == e : Bool}, ok: Laws.SlotOk.k(e, k, es, key, id), wf: Laws.WFIx(k, es, b2, nt),
  w: &nt2: Array<ST.SSlot> -> &i: U32 -> {ST.Ix.seek(b2, nt, ST.Str.hash(key), key) == (nt2, i) : Array<ST.SSlot> & U32} & {nt2 == nt : Array<ST.SSlot>})
  -> MoveK(k, es, b2, nt, key, id, e, ST.Ix.seek(b2, nt, ST.Str.hash(key), key)):
  (nt2, +i, eq, et) = w
  %Equal.sym(Array<ST.SSlot> & U32, ST.Ix.seek(b2, nt, ST.Str.hash(key), key), (nt2, i), eq) : MoveK(k, es, b2, nt, key, id, e, _)
  move_k2(k, es, b2, nt2, key, id, e, i, ee, ok, wfix_cast(k, es, b2, nt, nt2, et, wf))

def move_w(+k: U32, +es: List<&2, String>, +b2: Nat, nt: Array<ST.SSlot>, x: ST.SSlot, wf: Laws.WFIx(k, es, b2, nt), ok: Laws.SlotOk(k, es, x)) -> MoveW(k, es, b2, nt, x):
  match x:
    case ST.SSlot{+key, +id}:
      move_k(k, es, b2, nt, key, id, U32.is_eq(id, 0), {==}, ok, wf, seek_w(b2, nt, ST.Str.hash(key), key))

# the loop: f old slots from i re-inserted into nt
def GrowW(+k: U32, +es: List<&2, String>, +b2: Nat, -nt: Array<ST.SSlot>, +f: Nat, +i: U32, -old: Array<ST.SSlot>) -> Type:
  &g: Array<ST.SSlot> -> {ST.Ix.grow.go(f, i, b2, nt, Array.get(ST.SSlot, old, i)) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)

def GrowMid(+k: U32, +es: List<&2, String>, +b2: Nat, -nt: Array<ST.SSlot>, +p: Nat, +i: U32, -old: Array<ST.SSlot>, +x: ST.SSlot) -> Type:
  &g: Array<ST.SSlot> -> {ST.Ix.grow.go(p, U32.inc(i), b2, ST.Ix.move(b2, nt, x), Array.get(ST.SSlot, old, U32.inc(i))) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)

def grow_step3(+k: U32, +es: List<&2, String>, +b: Nat, +b2: Nat, +p: Nat, +i: U32, -nt: Array<ST.SSlot>, old3: Array<ST.SSlot>, +x: ST.SSlot, wf3: Laws.WFIx(k, es, b, old3),
  ih: @nt3: Array<ST.SSlot> -> @old4: Array<ST.SSlot> -> Laws.WFIx(k, es, b2, nt3) -> Laws.WFIx(k, es, b, old4) -> GrowW(k, es, b2, nt3, p, U32.inc(i), old4),
  w: MoveW(k, es, b2, nt, x))
  -> GrowMid(k, es, b2, nt, p, i, old3, x):
  (m, em, wm) = w
  %Equal.sym(Array<ST.SSlot>, ST.Ix.move(b2, nt, x), m, em) : &g: Array<ST.SSlot> -> {ST.Ix.grow.go(p, U32.inc(i), b2, _, Array.get(ST.SSlot, old3, U32.inc(i))) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)
  ih(m, old3, wm, wf3)

def grow_step2(+k: U32, +es: List<&2, String>, +b: Nat, +b2: Nat, +p: Nat, +i: U32, nt: Array<ST.SSlot>, -old: Array<ST.SSlot>, -old2: Array<ST.SSlot>, +eo: {old2 == old : Array<ST.SSlot>}, +x: ST.SSlot, ex: {x == Laws.rd_at(ST.SSlot, old, i) : ST.SSlot}, wf_nt: Laws.WFIx(k, es, b2, nt),
  ih: @nt3: Array<ST.SSlot> -> @old4: Array<ST.SSlot> -> Laws.WFIx(k, es, b2, nt3) -> Laws.WFIx(k, es, b, old4) -> GrowW(k, es, b2, nt3, p, U32.inc(i), old4),
  w: &old3: Array<ST.SSlot> -> {old3 == old2 : Array<ST.SSlot>} & Laws.WFIx(k, es, b, old3) & Laws.SlotOk(k, es, Laws.rd_at(ST.SSlot, old2, i)))
  -> GrowMid(k, es, b2, nt, p, i, old2, x):
  (old3, e3, wf3, ok) = w
  %e3 : GrowMid(k, es, b2, nt, p, i, _, x)
  grow_step3(k, es, b, b2, p, i, nt, old3, x, wf3, ih, move_w(k, es, b2, nt, x, wf_nt, slotok_cast(k, es, x, Laws.rd_at(ST.SSlot, old2, i), Equal.trans(ST.SSlot, x, Laws.rd_at(ST.SSlot, old, i), Laws.rd_at(ST.SSlot, old2, i), ex, Equal.cong(Array<ST.SSlot>, ST.SSlot, a => Laws.rd_at(ST.SSlot, a, i), old, old2, Equal.sym(Array<ST.SSlot>, old2, old, eo))), ok)))

def grow_step(+k: U32, +es: List<&2, String>, +b: Nat, +b2: Nat, +p: Nat, +i: U32, nt: Array<ST.SSlot>, -old: Array<ST.SSlot>, wf_nt: Laws.WFIx(k, es, b2, nt), wf_old: Laws.WFIx(k, es, b, old),
  ih: @nt3: Array<ST.SSlot> -> @old4: Array<ST.SSlot> -> Laws.WFIx(k, es, b2, nt3) -> Laws.WFIx(k, es, b, old4) -> GrowW(k, es, b2, nt3, p, U32.inc(i), old4),
  w: &old2: Array<ST.SSlot> -> &x: ST.SSlot -> {old2 == old : Array<ST.SSlot>} & {Array.get(ST.SSlot, old, i) == (old, x) : Array<ST.SSlot> & ST.SSlot} & {x == Laws.rd_at(ST.SSlot, old, i) : ST.SSlot})
  -> GrowW(k, es, b2, nt, 1n+p, i, old):
  (old2, +x, +eo, e1, ex) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.get(ST.SSlot, old, i), (old, x), e1) : &g: Array<ST.SSlot> -> {ST.Ix.grow.go(1n+p, i, b2, nt, _) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)
  %eo : GrowMid(k, es, b2, nt, p, i, _, x)
  grow_step2(k, es, b, b2, p, i, nt, old, old2, eo, x, ex, wf_nt, ih, wfix_rd(k, es, b, old2, i, wfix_cast(k, es, b, old, old2, eo, wf_old)))

def grow_zero(+k: U32, +es: List<&2, String>, +b2: Nat, +i: U32, nt: Array<ST.SSlot>, -old: Array<ST.SSlot>, wf_nt: Laws.WFIx(k, es, b2, nt),
  w: &old2: Array<ST.SSlot> -> &x: ST.SSlot -> {old2 == old : Array<ST.SSlot>} & {Array.get(ST.SSlot, old, i) == (old, x) : Array<ST.SSlot> & ST.SSlot} & {x == Laws.rd_at(ST.SSlot, old, i) : ST.SSlot})
  -> GrowW(k, es, b2, nt, 0n, i, old):
  (old2, +x, eo, e1, ex) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.get(ST.SSlot, old, i), (old, x), e1) : &g: Array<ST.SSlot> -> {ST.Ix.grow.go(0n, i, b2, nt, _) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, b2, g)
  (nt, {==}, wf_nt)

def grow_go(f: Nat, +k: U32, +es: List<&2, String>, +b: Nat, +b2: Nat, +i: U32, nt: Array<ST.SSlot>, old: Array<ST.SSlot>, wf_nt: Laws.WFIx(k, es, b2, nt), wf_old: Laws.WFIx(k, es, b, old)) -> GrowW(k, es, b2, nt, f, i, old):
  match f:
    case 0n:
      grow_zero(k, es, b2, i, nt, old, wf_nt, PC.get_w(ST.SSlot, old, i))
    case 1n++p:
      grow_step(k, es, b, b2, p, i, nt, old, wf_nt, wf_old, nt3 => old4 => w3 => wo4 => grow_go(p, k, es, b, b2, U32.inc(i), nt3, old4, w3, wo4), PC.get_w(ST.SSlot, old, i))

def add_one(b: Nat) -> {Nat.add(b, 1n) == 1n+b : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, add_one(p)) : {1n+_ == 2n+p : Nat}
      {==}

# Ix.grow(b, slots) == g with the index sound at depth b + 1 (production spells the depth Nat.add(b, 1n))
def grow_wf(+k: U32, +es: List<&2, String>, +b: Nat, slots: Array<ST.SSlot>, wfx: Laws.WFIx(k, es, b, slots)) -> &g: Array<ST.SSlot> -> {ST.Ix.grow(b, slots) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+b, g):
  %Equal.sym(Nat, Nat.add(b, 1n), 1n+b, add_one(b)) : &g: Array<ST.SSlot> -> {ST.Ix.grow.go(U32.to_nat(U32.shln(1, b)), 0, _, Array.new(ST.SSlot, _, ST.SSlot{"", 0}), Array.get(ST.SSlot, slots, 0)) == g : Array<ST.SSlot>} & Laws.WFIx(k, es, 1n+b, g)
  grow_go(U32.to_nat(U32.shln(1, b)), k, es, b, 1n+b, 0, Array.new(ST.SSlot, 1n+b, ST.SSlot{"", 0}), slots, wfix_new(k, es, 1n+b), wfx)

# ---- Dict.add's pieces: the new slot, the entry bounds, the doubled entry array -----------------------

# the slot of the new entry s (code k, id k + 1) is sound for the extended list
def new_slot_ok(+k: U32, +es: List<&2, String>, +s: String, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}) -> Laws.SlotOk(U32.inc(k), List.append(&2, String, es, s <> Nil{}), ST.SSlot{s, U32.inc(k)}):
  %Equal.sym(Bool, U32.is_eq(U32.inc(k), 0), False{}, inc_ne_zero(k, small)) : Laws.SlotOk.k(_, U32.inc(k), List.append(&2, String, es, s <> Nil{}), s, U32.inc(k))
  %Equal.sym(U32, U32.sub(U32.inc(k), 1), k, dec_inc(k)) : {U32.is_lt(_, U32.inc(k)) == True{} : Bool} & {Laws.nthd(List.append(&2, String, es, s <> Nil{}), _) == s : String}
  (lt_inc(k, small), (%Equal.sym(Nat, U32.to_nat(k), List.length(&2, String, es), ek) : {Laws.nthn(List.append(&2, String, es, s <> Nil{}), _) == s : String}; nth_app_end(es, s)))

# the new entry count: one more, in Nat
def ek_new(+k: U32, +es: List<&2, String>, +s: String, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}) -> {U32.to_nat(U32.inc(k)) == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), inc_small(k, small)) : {_ == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}
  %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, es, s <> Nil{})), 1n+List.length(&2, String, es), len_app1(es, s)) : {1n+U32.to_nat(k) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(k), List.length(&2, String, es), ek) : {1n+_ == 1n+List.length(&2, String, es) : Nat}
  {==}

# 0 < inc(k)
def pos_inc(+k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}) -> {U32.is_lt(0, U32.inc(k)) == True{} : Bool}:
  lt_u_of_nat(0, U32.inc(k), (%Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), inc_small(k, small)) : {Cmp.is_lt(Nat.cmp(U32.to_nat(0), _)) == True{} : Bool}; {==}))

# entry 0 of the extended list is still ""
def zero_new(+k: U32, +es: List<&2, String>, +s: String, hpos: {U32.is_lt(0, k) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, h0: {Laws.nthn(es, 0n) == "" : String}) -> {Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n) == "" : String}:
  %Equal.sym(String, Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n), Laws.nthn(es, 0n), nth_app_lt(es, s <> Nil{}, 0n, (%ek : {Cmp.is_lt(Nat.cmp(0n, _)) == True{} : Bool}; lt_nat_of_u(0, k, hpos)))) : {_ == "" : String}
  h0

# the new code k decodes to s in the extended list
def code_new(+k: U32, +es: List<&2, String>, +s: String, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}) -> {Laws.nthd(List.append(&2, String, es, s <> Nil{}), k) == s : String}:
  %Equal.sym(Nat, U32.to_nat(k), List.length(&2, String, es), ek) : {Laws.nthn(List.append(&2, String, es, s <> Nil{}), _) == s : String}
  nth_app_end(es, s)

# the extended list is one longer
def len_new(+es: List<&2, String>, +s: String) -> {Nat.is_le(List.length(&2, String, List.append(&2, String, es, s <> Nil{})), 1n+List.length(&2, String, es)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, es, s <> Nil{})), 1n+List.length(&2, String, es), len_app1(es, s)) : {Nat.is_le(_, 1n+List.length(&2, String, es)) == True{} : Bool}
  nat_le_refl(1n+List.length(&2, String, es))

# not full: k < 2^dd gives inc(k) <= 2^dd
def fit_nf(+k: U32, +dd: Nat, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hk: {U32.is_lt(k, U32.shln(1, dd)) == True{} : Bool}) -> {U32.is_le(U32.inc(k), U32.shln(1, dd)) == True{} : Bool}:
  le_u_of_nat(U32.inc(k), U32.shln(1, dd), (%Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), inc_small(k, small)) : {Nat.is_le(_, U32.to_nat(U32.shln(1, dd))) == True{} : Bool}; succ_le_of_lt(U32.to_nat(k), U32.to_nat(U32.shln(1, dd)), lt_nat_of_u(k, U32.shln(1, dd), hk))))

# full: k == 2^dd gives inc(k) <= 2^(dd + 1) (= shl k) and k < 2^(dd + 1)
def fit_full(+k: U32, +dd: Nat, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}, ekp: {k == U32.shln(1, dd) : U32}) -> {U32.is_le(U32.inc(k), U32.shln(1, 1n+dd)) == True{} : Bool}:
  %ekp : {U32.is_le(U32.inc(k), U32.shl(_)) == True{} : Bool}
  le_u_of_nat(U32.inc(k), U32.shl(k), (%Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), inc_small(k, small)) : {Nat.is_le(_, U32.to_nat(U32.shl(k))) == True{} : Bool}; (%Equal.sym(Nat, U32.to_nat(U32.shl(k)), Nat.double(U32.to_nat(k)), shl_nat(k, small)) : {Nat.is_le(1n+U32.to_nat(k), _) == True{} : Bool}; succ_le_double(U32.to_nat(k), lt_nat_of_u(0, k, hpos)))))

def lt_shl(+k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}) -> {U32.is_lt(k, U32.shl(k)) == True{} : Bool}:
  lt_u_of_nat(k, U32.shl(k), (%Equal.sym(Nat, U32.to_nat(U32.shl(k)), Nat.double(U32.to_nat(k)), shl_nat(k, small)) : {Cmp.is_lt(Nat.cmp(U32.to_nat(k), _)) == True{} : Bool}; lt_of_succ_le(U32.to_nat(k), Nat.double(U32.to_nat(k)), succ_le_double(U32.to_nat(k), lt_nat_of_u(0, k, hpos)))))

# 0 == double(n) is impossible for 0 < n
def nat_disc0(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def nat_double_zero(n: Nat, h: {Cmp.is_lt(Nat.cmp(0n, n)) == True{} : Bool}, e: {0n == Nat.double(n) : Nat}) -> Empty:
  match n:
    case 0n:
      L.false_true(h)
    case 1n+p:
      %e : nat_disc0(_)
      Unit{}

# shl(k) == 0 is impossible for 0 < k < 2^30
def shl_zero_absurd(+k: U32, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}, hz: {U32.shl(k) == 0 : U32}) -> Empty:
  nat_double_zero(U32.to_nat(k), lt_nat_of_u(0, k, hpos), Equal.trans(Nat, 0n, U32.to_nat(U32.shl(k)), Nat.double(U32.to_nat(k)), Equal.cong(U32, Nat, x => U32.to_nat(x), 0, U32.shl(k), Equal.sym(U32, U32.shl(k), 0, hz)), shl_nat(k, small)))

# 2^(dd + 1) is not 0 when 2^dd = k with 0 < k < 2^30: U32.shr of it is 2^dd
def shr_pow_k(bb: Bool, +k: U32, +dd: Nat, sp: B.ShrSpec(bb, dd), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}, ekp: {k == U32.shln(1, dd) : U32}) -> {U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}:
  match bb:
    case True{}:
      sp
    case False{}:
      Empty.absurd({U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}, shl_zero_absurd(k, small, hpos, (%Equal.sym(U32, k, U32.shln(1, dd), ekp) : {U32.shl(_) == 0 : U32}; sp)))

def shr_pow_fin(+k: U32, +dd: Nat, w: &bb: Bool -> B.ShrSpec(bb, dd), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}, ekp: {k == U32.shln(1, dd) : U32}) -> {U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}:
  (bb, sp) = w
  shr_pow_k(bb, k, dd, sp, small, hpos, ekp)

def shr_pow(+k: U32, +dd: Nat, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}, ekp: {k == U32.shln(1, dd) : U32}) -> {U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}:
  shr_pow_fin(k, dd, B.shr_shln(dd), small, hpos, ekp)

def not_false(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(h))

# ---- the doubled entry array (Dict.room when full) reads the old slots below 2^dd -------------------------

# a word below 2^dd
def zabove_of_lt(+dd: Nat, +cw: Word(32n), hc: {U32.is_lt(U32{cw}, U32.shln(1, dd)) == True{} : Bool}) -> B.Zabove(dd, 32n, cw):
  B.lt_bitw_zabove(32n, dd, cw, (%B.shln_bitw(dd) : {U32.cmp(U32{cw}, _) == LT{} : Cmp}; B.is_lt_lt(U32.cmp(U32{cw}, U32.shln(1, dd)), hc)))

def RoomRd(+dd: Nat, -strs: Array<String>, -b1: Array<String>) -> Type:
  @c: U32 -> {U32.is_lt(c, U32.shln(1, dd)) == True{} : Bool} -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, c) == Laws.rd_at(String, strs, c) : String}

def room_rd_c(+dd: Nat, -strs: Array<String>, -b0: Array<String>, -b1: Array<String>, +es0: {Array.size(String, strs) == (b0, U32.shln(1, dd)) : Array<String> & U32}, +eb1: {b1 == b0 : Array<String>}, +es1: {Array.size(String, b0) == (b1, U32.shln(1, dd)) : Array<String> & U32}, +hnz: {U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}, +cw: Word(32n), +hc: {U32.is_lt(U32{cw}, U32.shln(1, dd)) == True{} : Bool})
  -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, U32{cw}) == Laws.rd_at(String, strs, U32{cw}) : String}:
  %Equal.sym(Array<String>, b1, b0, eb1) : {Laws.rd_size(String, U32{cw}, Array.size(String, ANode{_, Array.new(String, dd, "")})) == Laws.rd_at(String, strs, U32{cw}) : String}
  %Equal.sym(Array<String> & U32, Array.size(String, b0), (b1, U32.shln(1, dd)), es1) : {Laws.rd_size(String, U32{cw}, Array.size.node(String, Array.new(String, dd, ""), _)) == Laws.rd_at(String, strs, U32{cw}) : String}
  %Equal.sym(Array<String> & U32, Array.size(String, strs), (b0, U32.shln(1, dd)), es0) : {Laws.rd_size(String, U32{cw}, (ANode{b1, Array.new(String, dd, "")}, U32.shln(1, 1n+dd))) == Laws.rd_size(String, U32{cw}, _) : String}
  %eb1 : {Laws.rd_size(String, U32{cw}, (ANode{b1, Array.new(String, dd, "")}, U32.shln(1, 1n+dd))) == Laws.rd_size(String, U32{cw}, (_, U32.shln(1, dd))) : String}
  %Equal.sym(U32, U32.and(U32{cw}, U32.sub(U32.shln(1, 1n+dd), 1)), U32{cw}, B.mask_id(1n+dd, cw, zabove_up(dd, 32n, cw, zabove_of_lt(dd, cw, hc)))) : {Laws.rd(String, ANode{b1, Array.new(String, dd, "")}, U32.shln(1, 1n+dd), _, U32.is_lt(_, U32.shr(U32.shln(1, 1n+dd)))) == Laws.rd_size(String, U32{cw}, (b1, U32.shln(1, dd))) : String}
  %Equal.sym(U32, U32.and(U32{cw}, U32.sub(U32.shln(1, dd), 1)), U32{cw}, B.mask_id(dd, cw, zabove_of_lt(dd, cw, hc))) : {Laws.rd(String, ANode{b1, Array.new(String, dd, "")}, U32.shln(1, 1n+dd), U32{cw}, U32.is_lt(U32{cw}, U32.shr(U32.shln(1, 1n+dd)))) == Laws.rd(String, b1, U32.shln(1, dd), _, U32.is_lt(_, U32.shr(U32.shln(1, dd)))) : String}
  %Equal.sym(U32, U32.shr(U32.shln(1, 1n+dd)), U32.shln(1, dd), hnz) : {Laws.rd(String, ANode{b1, Array.new(String, dd, "")}, U32.shln(1, 1n+dd), U32{cw}, U32.is_lt(U32{cw}, _)) == Laws.rd(String, b1, U32.shln(1, dd), U32{cw}, U32.is_lt(U32{cw}, U32.shr(U32.shln(1, dd)))) : String}
  %Equal.sym(Bool, U32.is_lt(U32{cw}, U32.shln(1, dd)), True{}, hc) : {Laws.rd(String, ANode{b1, Array.new(String, dd, "")}, U32.shln(1, 1n+dd), U32{cw}, _) == Laws.rd(String, b1, U32.shln(1, dd), U32{cw}, U32.is_lt(U32{cw}, U32.shr(U32.shln(1, dd)))) : String}
  %Equal.sym(U32, U32.shr(U32.shln(1, 1n+dd)), U32.shln(1, dd), hnz) : {Laws.rd(String, b1, _, U32{cw}, U32.is_lt(U32{cw}, U32.shr(_))) == Laws.rd(String, b1, U32.shln(1, dd), U32{cw}, U32.is_lt(U32{cw}, U32.shr(U32.shln(1, dd)))) : String}
  {==}

def room_rd_u(+dd: Nat, -strs: Array<String>, -b0: Array<String>, -b1: Array<String>, +es0: {Array.size(String, strs) == (b0, U32.shln(1, dd)) : Array<String> & U32}, +eb1: {b1 == b0 : Array<String>}, +es1: {Array.size(String, b0) == (b1, U32.shln(1, dd)) : Array<String> & U32}, +hnz: {U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}, c: U32, +hc: {U32.is_lt(c, U32.shln(1, dd)) == True{} : Bool})
  -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, c) == Laws.rd_at(String, strs, c) : String}:
  match c:
    case U32{+cw}:
      room_rd_c(dd, strs, b0, b1, es0, eb1, es1, hnz, cw, hc)

def room_rd(+dd: Nat, -strs: Array<String>, -b0: Array<String>, -b1: Array<String>, +es0: {Array.size(String, strs) == (b0, U32.shln(1, dd)) : Array<String> & U32}, +eb1: {b1 == b0 : Array<String>}, +es1: {Array.size(String, b0) == (b1, U32.shln(1, dd)) : Array<String> & U32}, +hnz: {U32.shr(U32.shln(1, 1n+dd)) == U32.shln(1, dd) : U32}) -> RoomRd(dd, strs, b1):
  +c => hc => room_rd_u(dd, strs, b0, b1, es0, eb1, es1, hnz, c, hc)

# ---- Laws.dict_code_spec ----------------------------------------------------------------------------------

# what Dict.code answers besides the result pair: the code in range, decoding to s, the entries extended
# by at most one, the dictionary well formed (es2 is the new entry list)
def CodeRest(d2: ST.Dict, +c: U32, +es: List<&2, String>, +es2: List<&2, String>, +s: String) -> Type:
  {U32.is_lt(c, Laws.dk(d2)) == True{} : Bool} & {Laws.nthd(es2, c) == s : String} & Laws.Ext(es, es2) & {Nat.is_le(List.length(&2, String, es2), 1n+List.length(&2, String, es)) == True{} : Bool} & Laws.WFDictE(d2, es2)

# the goal shapes along the production code (the pending term as a parameter)
def CodeBody(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, +tag: U32, +es: List<&2, String>, +s: String, -r: Array<ST.SSlot> & U32) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {ST.Dict.code.k(k, dd, strs, b, tag, ST.Str.hash(s), s, ST.Ix.id(r)) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeG(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, sl: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, -r: Array<ST.SSlot> & U32) -> Type:
  Laws.WFIx(k, es, b, sl) -> (&x: ST.SSlot -> {x == Laws.rd_at(ST.SSlot, sl, Pair.snd(Array<ST.SSlot>, U32, r)) : ST.SSlot} & {Laws.look_bit(s, x) == False{} : Bool}) -> CodeBody(k, dd, strs, b, tag, es, s, r)

def CodeB2(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, -rr: Array<ST.SSlot> & ST.SSlot) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {ST.Dict.code.k(k, dd, strs, b, tag, ST.Str.hash(s), s, ST.Ix.id.at(i, ST.Ix.id.k(rr))) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeB3(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, -q: Array<ST.SSlot> & U32) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {ST.Dict.code.k(k, dd, strs, b, tag, ST.Str.hash(s), s, ST.Ix.id.at(i, q)) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeP(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -t: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +x: ST.SSlot) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {ST.Dict.code.p(U32.is_eq(sid(x), 0), k, dd, strs, b, tag, ST.Str.hash(s), s, t, i, sid(x)) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodePB(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -t: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +id: U32, +isnew: Bool) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {ST.Dict.code.p(isnew, k, dd, strs, b, tag, ST.Str.hash(s), s, t, i, id) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeFull(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -t: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +full: Bool) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {(ST.Dict.fit(U32.inc(k), ST.Dict.dd(full, dd), Array.set(String, ST.Dict.room(full, dd, strs), k, s), b, Array.set(ST.SSlot, t, i, ST.SSlot{s, U32.inc(k)}), ST.Dict.mix(tag, ST.Str.hash(s))), k) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeRoom(+k: U32, +dd2: Nat, -room: Array<String>, +b: Nat, -t: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {(ST.Dict.fit(U32.inc(k), dd2, Array.set(String, room, k, s), b, Array.set(ST.SSlot, t, i, ST.SSlot{s, U32.inc(k)}), ST.Dict.mix(tag, ST.Str.hash(s))), k) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeSet(+k: U32, +dd2: Nat, -c1: Array<String>, +b: Nat, -t: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {(ST.Dict.fit(U32.inc(k), dd2, c1, b, Array.set(ST.SSlot, t, i, ST.SSlot{s, U32.inc(k)}), ST.Dict.mix(tag, ST.Str.hash(s))), k) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeFit(+k: U32, +dd2: Nat, -c1: Array<String>, +b: Nat, -c2: Array<ST.SSlot>, +tag2: U32, +es: List<&2, String>, +s: String) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {(ST.Dict.fit(U32.inc(k), dd2, c1, b, c2, tag2), k) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeBig(+k: U32, +dd2: Nat, -c1: Array<String>, +b: Nat, -c2: Array<ST.SSlot>, +tag2: U32, +es: List<&2, String>, +s: String, +big: Bool) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {(ST.Dict.fit.k(big, U32.inc(k), dd2, c1, b, c2, tag2), k) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

def CodeBigT(+k: U32, +dd2: Nat, -c1: Array<String>, +b2: Nat, -g: Array<ST.SSlot>, +tag2: U32, +es: List<&2, String>, +s: String) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {(ST.Dict{U32.inc(k), dd2, c1, b2, g, tag2}, k) == (d2, c) : ST.Dict & U32} & CodeRest(d2, c, es, es2, s)

# the rows' entry facts of the new entry array, in rdN form (the extended list es ++ [s])
def PreNew(+k: U32, +dd2: Nat, -c1: Array<String>, +es: List<&2, String>, +s: String) -> Type:
  @c: U32 -> {U32.is_lt(c, U32.inc(k)) == True{} : Bool} -> {Laws.rdN(String, dd2, c1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}

# ---- the fit: grow or not ----------------------------------------------------------------------------------

def code_grow(+k: U32, +dd2: Nat, b1: Array<String>, +b: Nat, -c2: Array<ST.SSlot>, +tag2: U32, +es: List<&2, String>, +s: String,
  ea: {U32.to_nat(U32.inc(k)) == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}, eb: {U32.is_le(U32.inc(k), U32.shln(1, dd2)) == True{} : Bool}, ec: {U32.is_lt(0, U32.inc(k)) == True{} : Bool}, ed: {Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n) == "" : String},
  wb1: Laws.WFArray(String, dd2, b1), entn: @c: U32 -> {U32.is_lt(c, U32.inc(k)) == True{} : Bool} -> {Laws.rd_at(String, b1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}, small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat},
  w: &g: Array<ST.SSlot> -> {ST.Ix.grow(b, c2) == g : Array<ST.SSlot>} & Laws.WFIx(U32.inc(k), List.append(&2, String, es, s <> Nil{}), 1n+b, g))
  -> CodeBigT(k, dd2, b1, Nat.add(b, 1n), ST.Ix.grow(b, c2), tag2, es, s):
  (g, eg, wg) = w
  %Equal.sym(Nat, Nat.add(b, 1n), 1n+b, add_one(b)) : CodeBigT(k, dd2, b1, _, ST.Ix.grow(b, c2), tag2, es, s)
  %Equal.sym(Array<ST.SSlot>, ST.Ix.grow(b, c2), g, eg) : CodeBigT(k, dd2, b1, 1n+b, _, tag2, es, s)
  (ST.Dict{U32.inc(k), dd2, b1, 1n+b, g, tag2}, k, List.append(&2, String, es, s <> Nil{}), {==}, lt_inc(k, small), code_new(k, es, s, ek), (s <> Nil{}, {==}), len_new(es, s), (ea, eb, ec, ed, wb1, entn, wg))

def code_big(big: Bool, +k: U32, +dd2: Nat, b1: Array<String>, +b: Nat, c2: Array<ST.SSlot>, +tag2: U32, +es: List<&2, String>, +s: String,
  ea: {U32.to_nat(U32.inc(k)) == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}, eb: {U32.is_le(U32.inc(k), U32.shln(1, dd2)) == True{} : Bool}, ec: {U32.is_lt(0, U32.inc(k)) == True{} : Bool}, ed: {Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n) == "" : String},
  wb1: Laws.WFArray(String, dd2, b1), entn: @c: U32 -> {U32.is_lt(c, U32.inc(k)) == True{} : Bool} -> {Laws.rd_at(String, b1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}, wc2: Laws.WFIx(U32.inc(k), List.append(&2, String, es, s <> Nil{}), b, c2), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat})
  -> CodeBig(k, dd2, b1, b, c2, tag2, es, s, big):
  match big:
    case False{}:
      (ST.Dict{U32.inc(k), dd2, b1, b, c2, tag2}, k, List.append(&2, String, es, s <> Nil{}), {==}, lt_inc(k, small), code_new(k, es, s, ek), (s <> Nil{}, {==}), len_new(es, s), (ea, eb, ec, ed, wb1, entn, wc2))
    case True{}:
      code_grow(k, dd2, b1, b, c2, tag2, es, s, ea, eb, ec, ed, wb1, entn, small, ek, grow_wf(U32.inc(k), List.append(&2, String, es, s <> Nil{}), b, c2, wc2))

# the entry array's copy b1 (rd_at through its Data size equation) and the new index, then the fit
def code_set3(+k: U32, +dd2: Nat, -c1: Array<String>, +b: Nat, c2: Array<ST.SSlot>, +tag2: U32, +es: List<&2, String>, +s: String, pre: PreNew(k, dd2, c1, es, s),
  ea: {U32.to_nat(U32.inc(k)) == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}, eb: {U32.is_le(U32.inc(k), U32.shln(1, dd2)) == True{} : Bool}, ec: {U32.is_lt(0, U32.inc(k)) == True{} : Bool}, ed: {Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n) == "" : String},
  wc2: Laws.WFIx(U32.inc(k), List.append(&2, String, es, s <> Nil{}), b, c2), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat},
  w: &b1: Array<String> -> {b1 == c1 : Array<String>} & Laws.WFArray(String, dd2, b1) & (@c: U32 -> {Laws.rd_at(String, c1, c) == Laws.rdN(String, dd2, c1, c) : String}))
  -> CodeFit(k, dd2, c1, b, c2, tag2, es, s):
  (b1, +eb1, wb1, cv) = w
  %eb1 : CodeFit(k, dd2, _, b, c2, tag2, es, s)
  code_big(U32.is_gt(U32.add(U32.inc(k), U32.inc(k)), U32.shln(1, b)), k, dd2, b1, b, c2, tag2, es, s, ea, eb, ec, ed, wb1, +c => hc => (%Equal.sym(Array<String>, b1, c1, eb1) : {Laws.rd_at(String, _, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}; (%Equal.sym(String, Laws.rd_at(String, c1, c), Laws.rdN(String, dd2, c1, c), cv(c)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}; pre(c, hc))), wc2, small, ek)

def code_set2(+k: U32, +dd2: Nat, c1: Array<String>, +b: Nat, -t5: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, wc1: Laws.WFArray(String, dd2, c1), pre: PreNew(k, dd2, c1, es, s),
  ea: {U32.to_nat(U32.inc(k)) == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}, eb: {U32.is_le(U32.inc(k), U32.shln(1, dd2)) == True{} : Bool}, ec: {U32.is_lt(0, U32.inc(k)) == True{} : Bool}, ed: {Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n) == "" : String},
  small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat},
  w: &c2: Array<ST.SSlot> -> {Array.set(ST.SSlot, t5, i, ST.SSlot{s, U32.inc(k)}) == c2 : Array<ST.SSlot>} & Laws.WFIx(U32.inc(k), List.append(&2, String, es, s <> Nil{}), b, c2))
  -> CodeSet(k, dd2, c1, b, t5, tag, es, s, i):
  (c2, ec2, wc2) = w
  %Equal.sym(Array<ST.SSlot>, Array.set(ST.SSlot, t5, i, ST.SSlot{s, U32.inc(k)}), c2, ec2) : CodeFit(k, dd2, c1, b, _, ST.Dict.mix(tag, ST.Str.hash(s)), es, s)
  code_set3(k, dd2, c1, b, c2, ST.Dict.mix(tag, ST.Str.hash(s)), es, s, pre, ea, eb, ec, ed, wc2, small, ek, rd_all(String, dd2, c1, wc1))

def code_set(+k: U32, +dd2: Nat, c1: Array<String>, +b: Nat, -t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, wc1: Laws.WFArray(String, dd2, c1), pre: PreNew(k, dd2, c1, es, s),
  ea: {U32.to_nat(U32.inc(k)) == List.length(&2, String, List.append(&2, String, es, s <> Nil{})) : Nat}, eb: {U32.is_le(U32.inc(k), U32.shln(1, dd2)) == True{} : Bool}, ec: {U32.is_lt(0, U32.inc(k)) == True{} : Bool}, ed: {Laws.nthn(List.append(&2, String, es, s <> Nil{}), 0n) == "" : String},
  +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat},
  w: &t5: Array<ST.SSlot> -> {t5 == t4 : Array<ST.SSlot>} & Laws.WFIx(U32.inc(k), List.append(&2, String, es, s <> Nil{}), b, t5))
  -> CodeSet(k, dd2, c1, b, t4, tag, es, s, i):
  (t5, et5, wfix5) = w
  %et5 : CodeSet(k, dd2, c1, b, _, tag, es, s, i)
  code_set2(k, dd2, c1, b, t5, tag, es, s, i, wc1, pre, ea, eb, ec, ed, small, ek, wfix_set(U32.inc(k), List.append(&2, String, es, s <> Nil{}), b, t5, i, ST.SSlot{s, U32.inc(k)}, wfix5, new_slot_ok(k, es, s, small, ek)))

# ---- the entry facts after the write at k: not full (room = strs) and full (room = the doubled array) -------

def pre_nf_b(bb: Bool, +k: U32, +dd: Nat, -strs: Array<String>, -c1: Array<String>, +es: List<&2, String>, +s: String, +hk: {U32.is_lt(k, U32.shln(1, dd)) == True{} : Bool}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +c: U32, hb: PC.IncLtU(bb, c, k),
  fj1: @j: U32 -> {Laws.rdN(String, dd, c1, j) == Bool.pick(String, Laws.same_at(dd, k, j), s, Laws.rdN(String, dd, strs, j)) : String}, cv1: @j: U32 -> {Laws.rd_at(String, strs, j) == Laws.rdN(String, dd, strs, j) : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String})
  -> {Laws.rdN(String, dd, c1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}:
  match bb:
    case True{}:
      %Equal.sym(String, Laws.rdN(String, dd, c1, c), Bool.pick(String, Laws.same_at(dd, k, c), s, Laws.rdN(String, dd, strs, c)), fj1(c)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %Equal.sym(Bool, Laws.same_at(dd, k, c), False{}, PC.same_false(dd, k, c, hk, PC.lt_trans_u(c, k, U32.shln(1, dd), hb, hk), e => PC.lt_ne(k, c)(e)(hb))) : {Bool.pick(String, _, s, Laws.rdN(String, dd, strs, c)) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %cv1(c) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %Equal.sym(String, Laws.rd_at(String, strs, c), Laws.nthd(es, c), ent(c, hb)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      Equal.sym(String, Laws.nthn(List.append(&2, String, es, s <> Nil{}), U32.to_nat(c)), Laws.nthn(es, U32.to_nat(c)), nth_app_lt(es, s <> Nil{}, U32.to_nat(c), (%ek : {Cmp.is_lt(Nat.cmp(U32.to_nat(c), _)) == True{} : Bool}; lt_nat_of_u(c, k, hb))))
    case False{}:
      %Equal.sym(U32, c, k, hb) : {Laws.rdN(String, dd, c1, _) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), _) : String}
      %Equal.sym(String, Laws.rdN(String, dd, c1, k), Bool.pick(String, Laws.same_at(dd, k, k), s, Laws.rdN(String, dd, strs, k)), fj1(k)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), k) : String}
      %Equal.sym(Bool, Laws.same_at(dd, k, k), True{}, PC.same_at_refl(dd, k)) : {Bool.pick(String, _, s, Laws.rdN(String, dd, strs, k)) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), k) : String}
      Equal.sym(String, Laws.nthd(List.append(&2, String, es, s <> Nil{}), k), s, code_new(k, es, s, ek))

def pre_nf_k(+k: U32, +dd: Nat, -strs: Array<String>, -c1: Array<String>, +es: List<&2, String>, +s: String, +hk: {U32.is_lt(k, U32.shln(1, dd)) == True{} : Bool}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +c: U32, w: &bb: Bool -> PC.IncLtU(bb, c, k),
  fj1: @j: U32 -> {Laws.rdN(String, dd, c1, j) == Bool.pick(String, Laws.same_at(dd, k, j), s, Laws.rdN(String, dd, strs, j)) : String}, cv1: @j: U32 -> {Laws.rd_at(String, strs, j) == Laws.rdN(String, dd, strs, j) : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String})
  -> {Laws.rdN(String, dd, c1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}:
  (bb, hb) = w
  pre_nf_b(bb, k, dd, strs, c1, es, s, hk, ek, c, hb, fj1, cv1, ent)

def pre_nf(+k: U32, +dd: Nat, -strs: Array<String>, -c1: Array<String>, +es: List<&2, String>, +s: String, +hk: {U32.is_lt(k, U32.shln(1, dd)) == True{} : Bool}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat},
  fj1: @j: U32 -> {Laws.rdN(String, dd, c1, j) == Bool.pick(String, Laws.same_at(dd, k, j), s, Laws.rdN(String, dd, strs, j)) : String}, cv1: @j: U32 -> {Laws.rd_at(String, strs, j) == Laws.rdN(String, dd, strs, j) : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String})
  -> PreNew(k, dd, c1, es, s):
  +c => hc => pre_nf_k(k, dd, strs, c1, es, s, hk, ek, c, PC.inc_lt_u(c, k, hc), fj1, cv1, ent)

# full: the room is ANode{b1, fresh}; its reads below 2^dd are the old entries (RoomRd)
def pre_f_b(bb: Bool, +k: U32, +dd: Nat, -strs: Array<String>, -b1: Array<String>, -c1: Array<String>, +es: List<&2, String>, +s: String, +hk2: {U32.is_lt(k, U32.shln(1, 1n+dd)) == True{} : Bool}, +ekp: {k == U32.shln(1, dd) : U32}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +c: U32, hb: PC.IncLtU(bb, c, k),
  fj1: @j: U32 -> {Laws.rdN(String, 1n+dd, c1, j) == Bool.pick(String, Laws.same_at(1n+dd, k, j), s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j)) : String}, cv1: @j: U32 -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, j) == Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j) : String}, rr: RoomRd(dd, strs, b1), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String})
  -> {Laws.rdN(String, 1n+dd, c1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}:
  match bb:
    case True{}:
      %Equal.sym(String, Laws.rdN(String, 1n+dd, c1, c), Bool.pick(String, Laws.same_at(1n+dd, k, c), s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, c)), fj1(c)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %Equal.sym(Bool, Laws.same_at(1n+dd, k, c), False{}, PC.same_false(1n+dd, k, c, hk2, PC.lt_trans_u(c, k, U32.shln(1, 1n+dd), hb, hk2), e => PC.lt_ne(k, c)(e)(hb))) : {Bool.pick(String, _, s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, c)) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %cv1(c) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %Equal.sym(String, Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, c), Laws.rd_at(String, strs, c), rr(c, (%ekp : {U32.is_lt(c, _) == True{} : Bool}; hb))) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      %Equal.sym(String, Laws.rd_at(String, strs, c), Laws.nthd(es, c), ent(c, hb)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}
      Equal.sym(String, Laws.nthn(List.append(&2, String, es, s <> Nil{}), U32.to_nat(c)), Laws.nthn(es, U32.to_nat(c)), nth_app_lt(es, s <> Nil{}, U32.to_nat(c), (%ek : {Cmp.is_lt(Nat.cmp(U32.to_nat(c), _)) == True{} : Bool}; lt_nat_of_u(c, k, hb))))
    case False{}:
      %Equal.sym(U32, c, k, hb) : {Laws.rdN(String, 1n+dd, c1, _) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), _) : String}
      %Equal.sym(String, Laws.rdN(String, 1n+dd, c1, k), Bool.pick(String, Laws.same_at(1n+dd, k, k), s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, k)), fj1(k)) : {_ == Laws.nthd(List.append(&2, String, es, s <> Nil{}), k) : String}
      %Equal.sym(Bool, Laws.same_at(1n+dd, k, k), True{}, PC.same_at_refl(1n+dd, k)) : {Bool.pick(String, _, s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, k)) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), k) : String}
      Equal.sym(String, Laws.nthd(List.append(&2, String, es, s <> Nil{}), k), s, code_new(k, es, s, ek))

def pre_f_k(+k: U32, +dd: Nat, -strs: Array<String>, -b1: Array<String>, -c1: Array<String>, +es: List<&2, String>, +s: String, +hk2: {U32.is_lt(k, U32.shln(1, 1n+dd)) == True{} : Bool}, +ekp: {k == U32.shln(1, dd) : U32}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +c: U32, w: &bb: Bool -> PC.IncLtU(bb, c, k),
  fj1: @j: U32 -> {Laws.rdN(String, 1n+dd, c1, j) == Bool.pick(String, Laws.same_at(1n+dd, k, j), s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j)) : String}, cv1: @j: U32 -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, j) == Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j) : String}, rr: RoomRd(dd, strs, b1), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String})
  -> {Laws.rdN(String, 1n+dd, c1, c) == Laws.nthd(List.append(&2, String, es, s <> Nil{}), c) : String}:
  (bb, hb) = w
  pre_f_b(bb, k, dd, strs, b1, c1, es, s, hk2, ekp, ek, c, hb, fj1, cv1, rr, ent)

def pre_f(+k: U32, +dd: Nat, -strs: Array<String>, -b1: Array<String>, -c1: Array<String>, +es: List<&2, String>, +s: String, +hk2: {U32.is_lt(k, U32.shln(1, 1n+dd)) == True{} : Bool}, +ekp: {k == U32.shln(1, dd) : U32}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat},
  fj1: @j: U32 -> {Laws.rdN(String, 1n+dd, c1, j) == Bool.pick(String, Laws.same_at(1n+dd, k, j), s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j)) : String}, cv1: @j: U32 -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, j) == Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j) : String}, rr: RoomRd(dd, strs, b1), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String})
  -> PreNew(k, 1n+dd, c1, es, s):
  +c => hc => pre_f_k(k, dd, strs, b1, c1, es, s, hk2, ekp, ek, c, PC.inc_lt_u(c, k, hc), fj1, cv1, rr, ent)

# ---- Dict.add: not full / full -------------------------------------------------------------------------------

def code_nf(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, dd)) == True{} : Bool},
  w: &c1: Array<String> -> {Array.set(String, strs, k, s) == c1 : Array<String>} & Laws.WFArray(String, dd, c1) & (@j: U32 -> {Laws.rdN(String, dd, c1, j) == Bool.pick(String, Laws.same_at(dd, k, j), s, Laws.rdN(String, dd, strs, j)) : String}) & (@j: U32 -> {Laws.rd_at(String, strs, j) == Laws.rdN(String, dd, strs, j) : String}))
  -> CodeFull(k, dd, strs, b, t4, tag, es, s, i, False{}):
  (c1, ec1, wc1, fj1, cv1) = w
  %Equal.sym(Array<String>, Array.set(String, strs, k, s), c1, ec1) : CodeSet(k, dd, _, b, t4, tag, es, s, i)
  code_set(k, dd, c1, b, t4, tag, es, s, i, wc1, pre_nf(k, dd, strs, c1, es, s, hk, ek, fj1, cv1, ent), ek_new(k, es, s, small, ek), fit_nf(k, dd, small, hk), pos_inc(k, small), zero_new(k, es, s, hpos, ek, h0), small, ek, wfix_mono(k, U32.inc(k), es, List.append(&2, String, es, s <> Nil{}), s <> Nil{}, {==}, ek, lt_le_u(k, U32.inc(k), lt_inc(k, small)), b, t4, wfix4))

def code_f3(+k: U32, +dd: Nat, -strs: Array<String>, -b0: Array<String>, -b1: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, +ekp: {k == U32.shln(1, dd) : U32},
  +es0: {Array.size(String, strs) == (b0, U32.shln(1, dd)) : Array<String> & U32}, +eb1: {b1 == b0 : Array<String>}, +es1: {Array.size(String, b0) == (b1, U32.shln(1, dd)) : Array<String> & U32},
  w: &c1: Array<String> -> {Array.set(String, ANode{b1, Array.new(String, dd, "")}, k, s) == c1 : Array<String>} & Laws.WFArray(String, 1n+dd, c1) & (@j: U32 -> {Laws.rdN(String, 1n+dd, c1, j) == Bool.pick(String, Laws.same_at(1n+dd, k, j), s, Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j)) : String}) & (@j: U32 -> {Laws.rd_at(String, ANode{b1, Array.new(String, dd, "")}, j) == Laws.rdN(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, j) : String}))
  -> CodeRoom(k, 1n+dd, ANode{b1, Array.new(String, dd, "")}, b, t4, tag, es, s, i):
  (c1, ec1, wc1, fj1, cv1) = w
  %Equal.sym(Array<String>, Array.set(String, ANode{b1, Array.new(String, dd, "")}, k, s), c1, ec1) : CodeSet(k, 1n+dd, _, b, t4, tag, es, s, i)
  code_set(k, 1n+dd, c1, b, t4, tag, es, s, i, wc1, pre_f(k, dd, strs, b1, c1, es, s, (%ekp : {U32.is_lt(k, U32.shl(_)) == True{} : Bool}; lt_shl(k, small, hpos)), ekp, ek, fj1, cv1, room_rd(dd, strs, b0, b1, es0, eb1, es1, shr_pow(k, dd, small, hpos, ekp)), ent), ek_new(k, es, s, small, ek), fit_full(k, dd, small, hpos, ekp), pos_inc(k, small), zero_new(k, es, s, hpos, ek, h0), small, ek, wfix_mono(k, U32.inc(k), es, List.append(&2, String, es, s <> Nil{}), s <> Nil{}, {==}, ek, lt_le_u(k, U32.inc(k), lt_inc(k, small)), b, t4, wfix4))

def code_f2(+k: U32, +dd: Nat, -strs: Array<String>, -b0: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, +ekp: {k == U32.shln(1, dd) : U32},
  +es0: {Array.size(String, strs) == (b0, U32.shln(1, dd)) : Array<String> & U32},
  w: &b1: Array<String> -> {b1 == b0 : Array<String>} & Laws.WFArray(String, dd, b1) & {Array.size(String, b0) == (b1, U32.shln(1, dd)) : Array<String> & U32})
  -> CodeRoom(k, 1n+dd, ANode{b0, Array.new(String, dd, "")}, b, t4, tag, es, s, i):
  (b1, +eb1, wb1, es1) = w
  %eb1 : CodeRoom(k, 1n+dd, ANode{_, Array.new(String, dd, "")}, b, t4, tag, es, s, i)
  code_f3(k, dd, strs, b0, b1, b, t4, tag, es, s, i, wfix4, ek, hpos, h0, ent, small, ekp, es0, eb1, es1, PC.set_other_w(String, 1n+dd, ANode{b1, Array.new(String, dd, "")}, k, s, (wb1, Laws.wf_new(String, dd, ""))))

def code_f(+k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, +ekp: {k == U32.shln(1, dd) : U32},
  w: &b0: Array<String> -> {b0 == strs : Array<String>} & Laws.WFArray(String, dd, b0) & {Array.size(String, strs) == (b0, U32.shln(1, dd)) : Array<String> & U32})
  -> CodeFull(k, dd, strs, b, t4, tag, es, s, i, True{}):
  (b0, eb0, wb0, es0) = w
  %Equal.sym(Nat, Nat.add(dd, 1n), 1n+dd, add_one(dd)) : CodeRoom(k, _, ANode{strs, Array.new(String, dd, "")}, b, t4, tag, es, s, i)
  %eb0 : CodeRoom(k, 1n+dd, ANode{_, Array.new(String, dd, "")}, b, t4, tag, es, s, i)
  code_f2(k, dd, strs, b0, b, t4, tag, es, s, i, wfix4, ek, hpos, h0, ent, small, ekp, es0, PC.wf_size(String, dd, b0, wb0))

def code_full(full: Bool, +k: U32, +dd: Nat, strs: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, efull: {U32.is_eq(k, U32.shln(1, dd)) == full : Bool}, wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool})
  -> CodeFull(k, dd, strs, b, t4, tag, es, s, i, full):
  match full:
    case False{}:
      code_nf(k, dd, strs, b, t4, tag, es, s, i, wfix4, ek, hpos, h0, ent, small, le_ne_lt(k, U32.shln(1, dd), hle, efull), PC.set_other_w(String, dd, strs, k, s, wfs))
    case True{}:
      code_f(k, dd, strs, b, t4, tag, es, s, i, wfix4, ek, hpos, h0, ent, small, u32_eq(k, U32.shln(1, dd), efull), PC.wf_size(String, dd, strs, wfs))

# ---- the slot found: Dict.code.p ------------------------------------------------------------------------------

def code_found(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +key: String, +id: U32, ok: Laws.SlotOk.k(False{}, k, es, key, id), wfix4: Laws.WFIx(k, es, b, t4), ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, eks: {key == s : String})
  -> CodePB(k, dd, strs, b, t4, tag, es, s, i, id, False{}):
  (h1, h2) = ok
  (ST.Dict{k, dd, strs, b, t4, tag}, U32.sub(id, 1), es, {==}, h1, Equal.trans(String, Laws.nthd(es, U32.sub(id, 1)), key, s, h2, eks), ext_refl(es), nat_le_succ(List.length(&2, String, es)), (ek, hle, hpos, h0, wfs, ent, wfix4))

def code_p(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +key: String, +id: U32, isnew: Bool, hit: {Bool.and(Bool.not(isnew), Bool.not(ST.Str.same(key, s))) == False{} : Bool}, ok: Laws.SlotOk.k(isnew, k, es, key, id), wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool})
  -> CodePB(k, dd, strs, b, t4, tag, es, s, i, id, isnew):
  match isnew:
    case False{}:
      code_found(k, dd, strs, b, t4, tag, es, s, i, key, id, ok, wfix4, ek, hle, hpos, h0, wfs, ent, Laws.str_same_sound(key, s, not_false(ST.Str.same(key, s), hit)))
    case True{}:
      code_full(U32.is_eq(k, U32.shln(1, dd)), k, dd, strs, b, t4, tag, es, s, i, {==}, wfix4, ek, hle, hpos, h0, wfs, ent, small)

def code_x(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, t4: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, x: ST.SSlot, hit: {Laws.look_bit(s, x) == False{} : Bool}, ok: Laws.SlotOk(k, es, x), wfix4: Laws.WFIx(k, es, b, t4), +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool})
  -> CodeP(k, dd, strs, b, t4, tag, es, s, i, x):
  match x:
    case ST.SSlot{+key, +id}:
      code_p(k, dd, strs, b, t4, tag, es, s, i, key, id, U32.is_eq(id, 0), hit, ok, wfix4, ek, hle, hpos, h0, wfs, ent, small)

def code_slot(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, -t3: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +x: ST.SSlot, hit: {Laws.look_bit(s, x) == False{} : Bool}, exx: {x == Laws.rd_at(ST.SSlot, t3, i) : ST.SSlot}, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool},
  w: &t4: Array<ST.SSlot> -> {t4 == t3 : Array<ST.SSlot>} & Laws.WFIx(k, es, b, t4) & Laws.SlotOk(k, es, Laws.rd_at(ST.SSlot, t3, i)))
  -> CodeP(k, dd, strs, b, t3, tag, es, s, i, x):
  (t4, e4, wfix4, ok) = w
  %e4 : CodeP(k, dd, strs, b, _, tag, es, s, i, x)
  code_x(k, dd, strs, b, t4, tag, es, s, i, x, hit, slotok_cast(k, es, x, Laws.rd_at(ST.SSlot, t3, i), exx, ok), wfix4, ek, hle, hpos, h0, wfs, ent, small)

# the probe's slot is the slot read
def hit_of(+s: String, -t2: Array<ST.SSlot>, +i: U32, +x: ST.SSlot, probe: &xp: ST.SSlot -> {xp == Laws.rd_at(ST.SSlot, t2, i) : ST.SSlot} & {Laws.look_bit(s, xp) == False{} : Bool}, ex: {x == Laws.rd_at(ST.SSlot, t2, i) : ST.SSlot}) -> {Laws.look_bit(s, x) == False{} : Bool}:
  (xp, exp, hb) = probe
  %Equal.sym(ST.SSlot, x, xp, Equal.trans(ST.SSlot, x, Laws.rd_at(ST.SSlot, t2, i), xp, ex, Equal.sym(ST.SSlot, xp, Laws.rd_at(ST.SSlot, t2, i), exp))) : {Laws.look_bit(s, _) == False{} : Bool}
  hb

def code_id(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, -t2: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +i: U32, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, wfix: Laws.WFIx(k, es, b, t2),
  probe: &xp: ST.SSlot -> {xp == Laws.rd_at(ST.SSlot, t2, i) : ST.SSlot} & {Laws.look_bit(s, xp) == False{} : Bool},
  w: &t3: Array<ST.SSlot> -> &x: ST.SSlot -> {t3 == t2 : Array<ST.SSlot>} & {Array.get(ST.SSlot, t2, i) == (t2, x) : Array<ST.SSlot> & ST.SSlot} & {x == Laws.rd_at(ST.SSlot, t2, i) : ST.SSlot})
  -> CodeBody(k, dd, strs, b, tag, es, s, (t2, i)):
  (t3, +x, +et3, e1, +ex) = w
  %Equal.sym(Array<ST.SSlot> & ST.SSlot, Array.get(ST.SSlot, t2, i), (t2, x), e1) : CodeB2(k, dd, strs, b, tag, es, s, i, _)
  %Equal.sym(Array<ST.SSlot> & U32, ST.Ix.id.k((t2, x)), (t2, sid(x)), idk_red(t2, x)) : CodeB3(k, dd, strs, b, tag, es, s, i, _)
  %et3 : CodeP(k, dd, strs, b, _, tag, es, s, i, x)
  code_slot(k, dd, strs, b, t3, tag, es, s, i, x, hit_of(s, t2, i, x, probe, ex), Equal.trans(ST.SSlot, x, Laws.rd_at(ST.SSlot, t2, i), Laws.rd_at(ST.SSlot, t3, i), ex, Equal.cong(Array<ST.SSlot>, ST.SSlot, a => Laws.rd_at(ST.SSlot, a, i), t2, t3, Equal.sym(Array<ST.SSlot>, t3, t2, et3))), ek, hle, hpos, h0, wfs, ent, small, wfix_rd(k, es, b, t3, i, wfix_cast(k, es, b, t2, t3, et3, wfix)))

def code_seek(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, -slots: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, +ek: {U32.to_nat(k) == List.length(&2, String, es) : Nat}, hle: {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool}, +hpos: {U32.is_lt(0, k) == True{} : Bool}, h0: {Laws.nthn(es, 0n) == "" : String}, wfs: Laws.WFArray(String, dd, strs), ent: @c2: U32 -> {U32.is_lt(c2, k) == True{} : Bool} -> {Laws.rd_at(String, strs, c2) == Laws.nthd(es, c2) : String}, +small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool},
  w: &t2: Array<ST.SSlot> -> &i: U32 -> {ST.Ix.seek(b, slots, ST.Str.hash(s), s) == (t2, i) : Array<ST.SSlot> & U32} & {t2 == slots : Array<ST.SSlot>})
  -> CodeG(k, dd, strs, b, slots, tag, es, s, ST.Ix.seek(b, slots, ST.Str.hash(s), s)):
  (t2, +i, eq, et) = w
  %Equal.sym(Array<ST.SSlot> & U32, ST.Ix.seek(b, slots, ST.Str.hash(s), s), (t2, i), eq) : CodeG(k, dd, strs, b, slots, tag, es, s, _)
  %et : CodeG(k, dd, strs, b, _, tag, es, s, (t2, i))
  wfix => probe => code_id(k, dd, strs, b, t2, tag, es, s, i, ek, hle, hpos, h0, wfs, ent, small, wfix, probe, PC.get_w(ST.SSlot, t2, i))

def code_wf(+k: U32, +dd: Nat, strs: Array<String>, +b: Nat, slots: Array<ST.SSlot>, +tag: U32, +es: List<&2, String>, +s: String, wf: Laws.WFDictE(ST.Dict{k, dd, strs, b, slots, tag}, es), small: {U32.is_lt(k, U32.shln(1, 30n)) == True{} : Bool}, probe: Laws.Probe(ST.Dict{k, dd, strs, b, slots, tag}, s)) -> Laws.CodeW(ST.Dict{k, dd, strs, b, slots, tag}, es, s):
  (ek, hle, hpos, h0, wfs, ent, wfix) = wf
  code_seek(k, dd, strs, b, slots, tag, es, s, ek, hle, hpos, h0, wfs, ent, small, seek_w(b, slots, ST.Str.hash(s), s))(wfix)(probe)

def Laws.dict_code_spec(d, es, s, wf, small, probe):
  match d:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      code_wf(k, dd, strs, b, slots, tag, es, s, wf, small, probe)
