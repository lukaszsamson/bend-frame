# PROOF_where.bend -- proof of LAWS.bend section 23 (v0.3 W3): Kernel.where's contents. The proof is
# compact_contents' (PROOF_contents.bend) with the input array removed: where's step writes the row
# index i at the cursor k where compact_keep's writes a[i]. wkeep: later writes land at or above the
# cursor, so a cell below it keeps its value; wspec_run: the WSpec clause of each row from wkeep.
import Base
import ./src/kernels.bend as K
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_contents.bend as PC

# ---- keep one position: later writes of where land above it ------------------------------------------

# the cell at pos of the output of the remaining run (pending read r of mask[i])
def WK(f: Nat, +i: U32, +k: U32, +d: Nat, -out: Array<U32>, -mask: Array<U32>, -r: Array<U32> & U32, +pos: U32, +val: U32) -> Type:
  {Laws.rdN(U32, d, K.Kernel.where.go(f, i, k, out, r), pos) == val : U32}

def wkeep_s3(p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -out: Array<U32>, mask: Array<U32>, -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR), +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +pos: U32, +val: U32, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(U32, d, out, pos) == val : U32},
  ih: @c: Array<U32> -> @m2: Array<U32> -> Laws.WFArray(U32, d, c) -> {m2 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool} -> {Laws.rdN(U32, d, c, pos) == val : U32} -> WK(p, U32.inc(i), U32.add(k, b), d, c, m2, Array.get(U32, m2, U32.inc(i)), pos, val),
  w: &c: Array<U32> -> {Array.set(U32, out, k, i) == c : Array<U32>} & Laws.WFArray(U32, d, c) & (@k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, k, k2), i, Laws.rdN(U32, d, out, k2)) : U32}) & (@k2: U32 -> {Laws.rd_at(U32, out, k2) == Laws.rdN(U32, d, out, k2) : U32}))
  -> WK(p, U32.inc(i), U32.add(k, b), d, Array.set(U32, out, k, i), mask, Array.get(U32, mask, U32.inc(i)), pos, val):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, k, i), c, ec) : WK(p, U32.inc(i), U32.add(k, b), d, _, mask, Array.get(U32, mask, U32.inc(i)), pos, val)
  ih(c, mask, wc, em, room, PC.cursor_step(k, b, d, hb, hk, pos, hpos), (%Equal.sym(U32, Laws.rdN(U32, d, c, pos), Bool.pick(U32, Laws.same_at(d, k, pos), i, Laws.rdN(U32, d, out, pos)), fj(pos)) : {_ == val : U32}; %Equal.sym(Bool, Laws.same_at(d, k, pos), False{}, PC.same_false_lt(d, k, pos, hk, hpos)) : {Bool.pick(U32, _, i, Laws.rdN(U32, d, out, pos)) == val : U32}; hval))

def wkeep_s1(p: Nat, +i: U32, +k: U32, +d: Nat, out: Array<U32>, -mask: Array<U32>, wf: Laws.WFArray(U32, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(1n+p, i, k, d, maskR), +pos: U32, +val: U32, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(U32, d, out, pos) == val : U32},
  ih: @b: U32 -> @c: Array<U32> -> @m2: Array<U32> -> Laws.WFArray(U32, d, c) -> {m2 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool} -> {Laws.rdN(U32, d, c, pos) == val : U32} -> WK(p, U32.inc(i), U32.add(k, b), d, c, m2, Array.get(U32, m2, U32.inc(i)), pos, val),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> WK(1n+p, i, k, d, out, mask, Array.get(U32, mask, i), pos, val):
  (+b, eb, +hb, +hk, room2) = room
  (mask2, +x, +em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : WK(1n+p, i, k, d, out, mask, _, pos, val)
  %em2 : WK(1n+p, i, k, d, out, _, (_, x), pos, val)
  %Equal.sym(U32, x, b, Equal.trans(U32, x, Laws.rd_at(U32, mask, i), b, ex, Equal.trans(U32, Laws.rd_at(U32, mask, i), Laws.rd_at(U32, maskR, i), b, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mask, maskR, em), Equal.sym(U32, b, Laws.rd_at(U32, maskR, i), eb)))) : WK(1n+p, i, k, d, out, mask2, (mask2, _), pos, val)
  wkeep_s3(p, i, k, b, d, out, mask2, maskR, Equal.trans(Array<U32>, mask2, mask, maskR, em2, em), room2, hb, hk, pos, val, hpos, hval, ih(b), PC.set_other_w(U32, d, out, k, i, wf))

def wkeep_zero(+i: U32, +k: U32, +d: Nat, out: Array<U32>, -mask: Array<U32>, +pos: U32, +val: U32, hval: {Laws.rdN(U32, d, out, pos) == val : U32},
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> WK(0n, i, k, d, out, mask, Array.get(U32, mask, i), pos, val):
  (mask2, +x, em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : WK(0n, i, k, d, out, mask, _, pos, val)
  hval

# the remaining run never writes below the cursor: a cell at pos < k keeps its value
def wkeep(f: Nat, +i: U32, +k: U32, +d: Nat, out: Array<U32>, mask: Array<U32>, wf: Laws.WFArray(U32, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(f, i, k, d, maskR), +pos: U32, +val: U32, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(U32, d, out, pos) == val : U32})
  -> WK(f, i, k, d, out, mask, Array.get(U32, mask, i), pos, val):
  match f:
    case 0n:
      wkeep_zero(i, k, d, out, mask, pos, val, hval, PC.get_w(U32, mask, i))
    case 1n++p:
      wkeep_s1(p, i, k, d, out, mask, wf, maskR, em, room, pos, val, hpos, hval, b => c => m2 => wc => em3 => room2 => hp => hv => wkeep(p, U32.inc(i), U32.add(k, b), d, c, m2, wc, maskR, em3, room2, pos, val, hp, hv), PC.get_w(U32, mask, i))

# ---- the spec of the whole run -----------------------------------------------------------------------

def WS(f: Nat, +i: U32, +k: U32, +d: Nat, -out: Array<U32>, -mask: Array<U32>, -r: Array<U32> & U32, -maskR: Array<U32>) -> Type:
  Laws.WSpec(f, i, k, d, maskR, K.Kernel.where.go(f, i, k, out, r))

def WSfin(p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -out2: Array<U32>, -mask: Array<U32>, -maskR: Array<U32>) -> Type:
  Laws.WSpec(1n+p, i, k, d, maskR, K.Kernel.where.go(p, U32.inc(i), U32.add(k, b), out2, Array.get(U32, mask, U32.inc(i))))

# the clause of the row just written, restated from the wkeep copies to the spec's copies
def wrow(+p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -c1: Array<U32>, -c2: Array<U32>, -m3: Array<U32>, -m4: Array<U32>, ec: {c1 == c2 : Array<U32>}, em: {m3 == m4 : Array<U32>},
  fact: WK(p, U32.inc(i), U32.add(k, b), d, c1, m3, Array.get(U32, m3, U32.inc(i)), k, i))
  -> {Laws.rdN(U32, d, K.Kernel.where.go(p, U32.inc(i), U32.add(k, b), c2, Array.get(U32, m4, U32.inc(i))), k) == i : U32}:
  %ec : {Laws.rdN(U32, d, K.Kernel.where.go(p, U32.inc(i), U32.add(k, b), _, Array.get(U32, m4, U32.inc(i))), k) == i : U32}
  %em : {Laws.rdN(U32, d, K.Kernel.where.go(p, U32.inc(i), U32.add(k, b), c1, Array.get(U32, _, U32.inc(i))), k) == i : U32}
  fact

def wspec_s4(+p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -out: Array<U32>, -c: Array<U32>, -mask2: Array<U32>, -maskR: Array<U32>, +em2: {mask2 == maskR : Array<U32>}, +eb: {b == Laws.rd_at(U32, maskR, i) : U32}, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool},
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, k, k2), i, Laws.rdN(U32, d, out, k2)) : U32},
  rooms: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) & Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR),
  wc: &c1: Array<U32> -> &c2: Array<U32> -> {c1 == c : Array<U32>} & {c2 == c : Array<U32>} & Laws.WFArray(U32, d, c1) & Laws.WFArray(U32, d, c2),
  wm: &m3: Array<U32> -> &m4: Array<U32> -> {m3 == mask2 : Array<U32>} & {m4 == mask2 : Array<U32>},
  ih: @c2: Array<U32> -> @m4: Array<U32> -> Laws.WFArray(U32, d, c2) -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> WS(p, U32.inc(i), U32.add(k, b), d, c2, m4, Array.get(U32, m4, U32.inc(i)), maskR))
  -> WSfin(p, i, k, b, d, c, mask2, maskR):
  (r1, r2) = rooms
  (c1, c2, +ec1, +ec2, wc1, wc2) = wc
  (m3, m4, +em3, +em4) = wm
  %ec2 : WSfin(p, i, k, b, d, _, mask2, maskR)
  %em4 : WSfin(p, i, k, b, d, c2, _, maskR)
  (b, eb, nz => wrow(p, i, k, b, d, c1, c2, m3, m4, Equal.trans(Array<U32>, c1, c, c2, ec1, Equal.sym(Array<U32>, c2, c, ec2)), Equal.trans(Array<U32>, m3, mask2, m4, em3, Equal.sym(Array<U32>, m4, mask2, em4)), wkeep(p, U32.inc(i), U32.add(k, b), d, c1, m3, wc1, maskR, Equal.trans(Array<U32>, m3, mask2, maskR, em3, em2), r1, k, i, PC.cursor_set(k, b, d, hb, hk)(nz), PC.wrote_k(~U32, k, d, out, c, c1, i, ec1, fj(k)))), ih(c2, m4, wc2, Equal.trans(Array<U32>, m4, mask2, maskR, em4, em2), r2))

def wspec_s3(+p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -out: Array<U32>, mask2: Array<U32>, -maskR: Array<U32>, +em2: {mask2 == maskR : Array<U32>}, +eb: {b == Laws.rd_at(U32, maskR, i) : U32}, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, room: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR),
  ih: @c2: Array<U32> -> @m4: Array<U32> -> Laws.WFArray(U32, d, c2) -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> WS(p, U32.inc(i), U32.add(k, b), d, c2, m4, Array.get(U32, m4, U32.inc(i)), maskR),
  w: &c: Array<U32> -> {Array.set(U32, out, k, i) == c : Array<U32>} & Laws.WFArray(U32, d, c) & (@k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, k, k2), i, Laws.rdN(U32, d, out, k2)) : U32}) & (@k2: U32 -> {Laws.rd_at(U32, out, k2) == Laws.rdN(U32, d, out, k2) : U32}))
  -> WSfin(p, i, k, b, d, Array.set(U32, out, k, i), mask2, maskR):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, k, i), c, ec) : WSfin(p, i, k, b, d, _, mask2, maskR)
  wspec_s4(p, i, k, b, d, out, c, mask2, maskR, em2, eb, hb, hk, fj, PC.croom_dup(p, U32.inc(i), U32.add(k, b), d, maskR, room), PC.clone_wf(U32, d, c, wc), PC.clone_eq(U32, mask2), ih)

def wspec_s1(+p: Nat, +i: U32, +k: U32, +d: Nat, out: Array<U32>, -mask: Array<U32>, wf: Laws.WFArray(U32, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(1n+p, i, k, d, maskR),
  ih: @b: U32 -> @c2: Array<U32> -> @m4: Array<U32> -> Laws.WFArray(U32, d, c2) -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> WS(p, U32.inc(i), U32.add(k, b), d, c2, m4, Array.get(U32, m4, U32.inc(i)), maskR),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> WS(1n+p, i, k, d, out, mask, Array.get(U32, mask, i), maskR):
  (+b, +eb, +hb, +hk, room2) = room
  (mask2, +x, +em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : WS(1n+p, i, k, d, out, mask, _, maskR)
  %em2 : WS(1n+p, i, k, d, out, _, (_, x), maskR)
  %Equal.sym(U32, x, b, Equal.trans(U32, x, Laws.rd_at(U32, mask, i), b, ex, Equal.trans(U32, Laws.rd_at(U32, mask, i), Laws.rd_at(U32, maskR, i), b, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mask, maskR, em), Equal.sym(U32, b, Laws.rd_at(U32, maskR, i), eb)))) : WS(1n+p, i, k, d, out, mask2, (mask2, _), maskR)
  wspec_s3(p, i, k, b, d, out, mask2, maskR, Equal.trans(Array<U32>, mask2, mask, maskR, em2, em), eb, hb, hk, room2, ih(b), PC.set_other_w(U32, d, out, k, i, wf))

# where's contract for the remaining run
def wspec_run(f: Nat, +i: U32, +k: U32, +d: Nat, out: Array<U32>, mask: Array<U32>, wf: Laws.WFArray(U32, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(f, i, k, d, maskR))
  -> WS(f, i, k, d, out, mask, Array.get(U32, mask, i), maskR):
  match f:
    case 0n:
      Unit{}
    case 1n++p:
      wspec_s1(p, i, k, d, out, mask, wf, maskR, em, room, b => c2 => m4 => wc2 => em4 => room2 => wspec_run(p, U32.inc(i), U32.add(k, b), d, c2, m4, wc2, maskR, em4, room2), PC.get_w(U32, mask, i))

def Laws.where_contents(d, n, mask, room):
  wspec_run(U32.to_nat(n), 0, 0, d, Array.new(U32, d, 0), mask, Laws.wf_new(U32, d, 0), mask, {==}, room)
