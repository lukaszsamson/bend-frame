# T5 mutation (plan M_01 section 4, M5 part 3): a disposable copy of the production dictionary
# re-coding loop Dict.rc (Dict.merge: the entries of one dictionary coded into another, the map
# m[c] = the new code of entry c) whose put writes the map entry at the WRONG slot (c + 1: every
# code shifted by one entry), run through the merge theorem of LAWS.bend section 14
# (dict_merge_spec: m[c] names src's entry c in the extended dictionary). The real proof term
# (PROOF_strs.bend's merge_w over mgo) must be refused for the mutated loop: Bend answers SOME
# PROOFS FAIL with the mutated Dict.rc in `expected` and the production ST.Dict.merge in
# `observed`. The positive control dict_merge_spec_copy states the theorem over the real loop with
# the same term and checks, so only the mutation is reported.
import Base
import ./../../src/strs.bend as ST
import ./../../LAWS.bend as Laws
import ./../../PROOF_strs.bend as PST

# the production theorem, as in LAWS.bend section 14
law dict_merge_spec_copy:
  for src: ST.Dict
  for dst: ST.Dict
  for +esd: List<&2, String>
  for fits: {U32.is_le(Laws.dk(src), U32.shln(1, Laws.ddd(src))) == True{} : Bool}
  for wfd: Laws.WFDictE(dst, esd)
  for probes: Laws.MergeProbe(U32.to_nat(Laws.dk(src)), 0, Laws.dstrs(src), dst)
  Laws.MergeW(src, dst, esd)

def dict_merge_spec_copy(src, dst, esd, fits, wfd, probes):
  match src:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      PST.merge_w(k, dd, strs, b, slots, tag, dst, esd, fits, PST.wf_ek(dst, esd, wfd))(probes)

# MUTATED copy of Dict.rc.put: the map entry of src's code c is written at slot c + 1
def Mut.Dict.rc.put(+c: U32, out: Array<U32>, r: ST.Dict & U32) -> ST.Dict & Array<U32>:
  (dst, x) = r
  (dst, Array.set(U32, out, U32.inc(c), x))

def Mut.Dict.rc.step(+ins: Bool, +c: U32, s: String, st: ST.Dict & Array<U32>) -> ST.Dict & Array<U32>:
  (dst, out) = st
  Mut.Dict.rc.put(c, out, ST.Dict.rc.op(ins, dst, s))

def Mut.Dict.rc.go(n: Nat, +c: U32, +ins: Bool, st: ST.Dict & Array<U32>, r: Array<String> & String) -> Array<String> & (ST.Dict & Array<U32>):
  match n:
    case 0n:
      (strs, s) = r
      (strs, st)
    case 1n+p:
      (strs, s) = r
      +j = U32.inc(c)
      Mut.Dict.rc.go(p, j, ins, Mut.Dict.rc.step(ins, c, s, st), Array.get(String, strs, j))

def Mut.Dict.rc(+ins: Bool, src: ST.Dict, dst: ST.Dict) -> ST.Dict & ST.Dict & Array<U32>:
  match src:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      ST.Dict.rc.fin(k, dd, b, slots, tag, Mut.Dict.rc.go(U32.to_nat(k), 0, ins, (dst, Array.new(U32, dd, 0)), Array.get(String, strs, 0)))

def Mut.Dict.merge(src: ST.Dict, dst: ST.Dict) -> ST.Dict & ST.Dict & Array<U32>:
  Mut.Dict.rc(True{}, src, dst)

# the theorem's statement over the mutated loop
def MutMergeW(-src: ST.Dict, -dst: ST.Dict, +esd: List<&2, String>) -> Type:
  &src2: ST.Dict -> &dst2: ST.Dict -> &m: Array<U32> -> &es2: List<&2, String> -> {Mut.Dict.merge(src, dst) == (src2, dst2, m) : ST.Dict & ST.Dict & Array<U32>} & {src2 == src : ST.Dict} & Laws.Ext(esd, es2) & Laws.WFArray(U32, Laws.ddd(src), m) & Laws.WFDictE(dst2, es2) & (@c: U32 -> {U32.is_lt(c, Laws.dk(dst)) == True{} : Bool} -> {Laws.dentry(dst2, c) == Laws.dentry(dst, c) : String}) & Laws.EncRows(Laws.dk(src), Laws.ddd(src), Laws.dstrs(src), m, es2)

law dict_merge_spec_mutated:
  for src: ST.Dict
  for dst: ST.Dict
  for +esd: List<&2, String>
  for fits: {U32.is_le(Laws.dk(src), U32.shln(1, Laws.ddd(src))) == True{} : Bool}
  for wfd: Laws.WFDictE(dst, esd)
  for probes: Laws.MergeProbe(U32.to_nat(Laws.dk(src)), 0, Laws.dstrs(src), dst)
  MutMergeW(src, dst, esd)

def dict_merge_spec_mutated(src, dst, esd, fits, wfd, probes):
  match src:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      PST.merge_w(k, dd, strs, b, slots, tag, dst, esd, fits, PST.wf_ek(dst, esd, wfd))(probes)

#|SOME PROOFS FAIL
#|Error:
#|- expected : Sigma<&1, &1, ST.Dict, src2 => Sigma<&1, &1, ST.Dict, dst2 => Sigma<&1, &1, Array<U32>, m => Sigma<&1, &1, List<&2, String>, es2 => Sigma<&1, &1, {ST.Dict.rc.fin(k, dd, b, slots, tag, Mut.Dict.rc.go(U32.to_nat(k), 0, True{}, (dst, Array.new(U32, dd, 0)), Array.get.at(String, 0, Array.size(String, strs)))) == (src2, dst2, m) : Sigma<&1, &1, ST.Dict, _ => Sigma<&1, &1, ST.Dict, _ => Array<U32>>>}, _ => Sigma<&1, &1, {src2 == ST.Dict{k, dd, strs, b, slots, tag} : ST.Dict}, _ => Sigma<&1, &1, Sigma<&1, &1, List<&2, String>, more => {es2 == List.append(&2, String, esd, more) : List<&2, String>}>, _ => Sigma<&1, &1, Laws.WFArray(U32, dd, m), _ => Sigma<&1, &1, Laws.WFDictE(dst2, es2), _ => Sigma<&1, &1, @c:U32 -> @_:{Cmp.is_lt(U32.cmp(c, Laws.dk(dst))) == True{} : Bool} -> {Laws.dentry(dst2, c) == Laws.dentry(dst, c) : String}, _ => @j:U32 -> @_:{Cmp.is_lt(U32.cmp(j, k)) == True{} : Bool} -> @code:U32 -> @_:{code == Laws.rd(U32, m, U32.shln(1, dd), U32.and(j, U32.sub(U32.shln(1, dd), 1)), Cmp.is_lt(U32.cmp(U32.and(j, U32.sub(U32.shln(1, dd), 1)), U32.shr(U32.shln(1, dd))))) : U32} -> Sigma<&1, &1, {Cmp.is_lt(Nat.cmp(U32.to_nat(code), List.length(&2, String, es2))) == True{} : Bool}, _ => {Laws.nthn(es2, U32.to_nat(code)) == Laws.rd_size(String, j, Array.size(String, strs)) : String}>>>>>>>>>>>
#|- observed : Sigma<&1, &1, ST.Dict, src2 => Sigma<&1, &1, ST.Dict, dst2 => Sigma<&1, &1, Array<U32>, m => Sigma<&1, &1, List<&2, String>, es2 => Sigma<&1, &1, {ST.Dict.rc.fin(k, dd, b, slots, tag, ST.Dict.rc.go(U32.to_nat(k), 0, True{}, (dst, Array.new(U32, dd, 0)), Array.get.at(String, 0, Array.size(String, strs)))) == (src2, dst2, m) : Sigma<&1, &1, ST.Dict, _ => Sigma<&1, &1, ST.Dict, _ => Array<U32>>>}, _ => Sigma<&1, &1, {src2 == ST.Dict{k, dd, strs, b, slots, tag} : ST.Dict}, _ => Sigma<&1, &1, Sigma<&1, &1, List<&2, String>, more => {es2 == List.append(&2, String, esd, more) : List<&2, String>}>, _ => Sigma<&1, &1, Laws.WFArray(U32, dd, m), _ => Sigma<&1, &1, Laws.WFDictE(dst2, es2), _ => Sigma<&1, &1, @c:U32 -> @_:{Cmp.is_lt(U32.cmp(c, Laws.dk(dst))) == True{} : Bool} -> {Laws.dentry(dst2, c) == Laws.dentry(dst, c) : String}, _ => @j:U32 -> @_:{Cmp.is_lt(U32.cmp(j, k)) == True{} : Bool} -> @code:U32 -> @_:{code == Laws.rd(U32, m, U32.shln(1, dd), U32.and(j, U32.sub(U32.shln(1, dd), 1)), Cmp.is_lt(U32.cmp(U32.and(j, U32.sub(U32.shln(1, dd), 1)), U32.shr(U32.shln(1, dd))))) : U32} -> Sigma<&1, &1, {Cmp.is_lt(Nat.cmp(U32.to_nat(code), List.length(&2, String, es2))) == True{} : Bool}, _ => {Laws.nthn(es2, U32.to_nat(code)) == Laws.rd_size(String, j, Array.size(String, strs)) : String}>>>>>>>>>>>
#|Context:
#|- k      : U32
#|- dd     : Nat
#|- strs   : Array<String>
#|- b      : Nat
#|- slots  : Array<ST.SSlot>
#|- tag    : U32
#|- dst    : ST.Dict
#|- esd    : List<&2, String>
#|- fits   : {Cmp.is_le(U32.cmp(k, U32.shln(1, dd))) == True{} : Bool}
#|- wfd    : Laws.WFDictE(dst, esd)
#|- probes : Laws.MergeProbe(U32.to_nat(k), 0, strs, dst)
#|Location: dict_merge_spec_mutated
#|72 |     case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
#|73>|       PST.merge_w(k, dd, strs, b, slots, tag, dst, esd, fits, PST.wf_ek(dst, esd, wfd))(probes)
#|   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|74 | 
