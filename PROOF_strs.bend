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
