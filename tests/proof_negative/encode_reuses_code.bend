# T5 mutation (plan M_01 section 4, M5 part 3): a disposable copy of the production string-encoding
# loop Enc.go whose step REUSES a code: every row is given code 0 (the empty string's) instead of the
# code Dict.code answered for its string, run through the encode theorem of LAWS.bend section 14
# (strs_encode_cells: every row's code names the row's string in the entry list). The real proof
# term (PROOF_strs.bend's enc_law over enc_go) must be refused for the mutated loop: Bend answers
# SOME PROOFS FAIL with the mutated encoder in `expected` and the production ST.Strs.encode in
# `observed`. The positive control strs_encode_cells_copy states the theorem over the real encoder
# with the same term and checks, so only the mutation is reported.
# Scope: this fixture checks the production proof term against a MUTATED, RENAMED disposable copy, so it shows that
# term is refused for that copy. The term is tied to the production function's NAME (the error compares the renamed copy
# with the production function), so an UNMUTATED renamed copy is refused too: on its own this fixture does NOT show that
# a wrong copy is rejected.
# That stronger claim, a wrong PRODUCTION function is rejected, is checked by scripts/mutation_check.sh
# (make mutation-check): it patches the production source in place and re-runs bend PROOF.bend.
import Base
import ./../../src/strs.bend as ST
import ./../../LAWS.bend as Laws
import ./../../PROOF_bits.bend as B
import ./../../PROOF_strs.bend as PST

# the production theorem, as in LAWS.bend section 14
law strs_encode_cells_copy:
  for +n: U32
  for +d: Nat
  for a: Array<String>
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for small: {U32.is_lt(n, U32.shln(1, 30n)) == True{} : Bool}
  for probes: Laws.EncProbe(U32.to_nat(n), 0, a, ST.Dict.empty())
  Laws.EncodeW(n, d, a)

def strs_encode_cells_copy(n, d, a, fits, small, probes):
  PST.enc_law(n, d, a, PST.enc_go(U32.to_nat(n), 0, d, a, ST.Dict.empty(), Array.new(U32, d, 0), "" <> Nil{}, Laws.wf_new(U32, d, 0), B.room_from(d, n, fits), PST.lim0(n, small), {==})(PST.ehyp0(d, a, Array.new(U32, d, 0), "" <> Nil{}))(Laws.dict_empty_wf())(probes))

# MUTATED copy of Enc.put: the code Dict.code answered is dropped, every row gets code 0 (a code that
# already names "" : wrong, every non-empty string would decode to "")
def Mut.Enc.put(+i: U32, out: Array<U32>, r: ST.Dict & U32) -> ST.Dict & Array<U32>:
  (dict, c) = r
  (dict, Array.set(U32, out, i, 0))

def Mut.Enc.step(+i: U32, s: String, st: ST.Dict & Array<U32>) -> ST.Dict & Array<U32>:
  (dict, out) = st
  Mut.Enc.put(i, out, ST.Dict.code(dict, s))

def Mut.Enc.go(n: Nat, +i: U32, st: ST.Dict & Array<U32>, r: Array<String> & String) -> ST.Dict & Array<U32>:
  match n:
    case 0n:
      (a, s) = r
      st
    case 1n+p:
      (a, s) = r
      +j = U32.inc(i)
      Mut.Enc.go(p, j, Mut.Enc.step(i, s, st), Array.get(String, a, j))

def Mut.Strs.encode(+n: U32, +d: Nat, a: Array<String>) -> ST.Strs:
  ST.Enc.fin(Mut.Enc.go(U32.to_nat(n), 0, (ST.Dict.empty(), Array.new(U32, d, 0)), Array.get(String, a, 0)))

# the theorem's statement over the mutated encoder
def MutEncodeW(+n: U32, +d: Nat, -a: Array<String>) -> Type:
  &codes: Array<U32> -> &dict: ST.Dict -> &es: List<&2, String> -> {Mut.Strs.encode(n, d, a) == ST.SDict{codes, dict} : ST.Strs} & Laws.WFArray(U32, d, codes) & Laws.WFDictE(dict, es) & Laws.EncRows(n, d, a, codes, es)

law strs_encode_cells_mutated:
  for +n: U32
  for +d: Nat
  for a: Array<String>
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for small: {U32.is_lt(n, U32.shln(1, 30n)) == True{} : Bool}
  for probes: Laws.EncProbe(U32.to_nat(n), 0, a, ST.Dict.empty())
  MutEncodeW(n, d, a)

def strs_encode_cells_mutated(n, d, a, fits, small, probes):
  PST.enc_law(n, d, a, PST.enc_go(U32.to_nat(n), 0, d, a, ST.Dict.empty(), Array.new(U32, d, 0), "" <> Nil{}, Laws.wf_new(U32, d, 0), B.room_from(d, n, fits), PST.lim0(n, small), {==})(PST.ehyp0(d, a, Array.new(U32, d, 0), "" <> Nil{}))(Laws.dict_empty_wf())(probes))

#|SOME PROOFS FAIL
#|Error:
#|- expected : Sigma<&1, &1, Array<U32>, codes => Sigma<&1, &1, ST.Dict, dict => Sigma<&1, &1, List<&2, String>, es => Sigma<&1, &1, {ST.Enc.fin(Mut.Enc.go(U32.to_nat(n), 0, (ST.Dict{1, 0n, [""], 2n, [ST.SSlot{"", 0}, ST.SSlot{"", 1}, ST.SSlot{"", 0}, ST.SSlot{"", 0}], 0}, Array.new(U32, d, 0)), Array.get.at(String, 0, Array.size(String, a)))) == ST.SDict{codes, dict} : ST.Strs}, _ => Sigma<&1, &1, Laws.WFArray(U32, d, codes), _ => Sigma<&1, &1, Laws.WFDictE(dict, es), _ => @j:U32 -> @_:{Cmp.is_lt(U32.cmp(j, n)) == True{} : Bool} -> @code:U32 -> @_:{code == Laws.rd(U32, codes, U32.shln(1, d), U32.and(j, U32.sub(U32.shln(1, d), 1)), Cmp.is_lt(U32.cmp(U32.and(j, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))) : U32} -> Sigma<&1, &1, {Cmp.is_lt(Nat.cmp(U32.to_nat(code), List.length(&2, String, es))) == True{} : Bool}, _ => {Laws.nthn(es, U32.to_nat(code)) == Laws.rd_size(String, j, Array.size(String, a)) : String}>>>>>>>
#|- observed : Sigma<&1, &1, Array<U32>, codes => Sigma<&1, &1, ST.Dict, dict => Sigma<&1, &1, List<&2, String>, es => Sigma<&1, &1, {ST.Enc.fin(ST.Enc.go(U32.to_nat(n), 0, (ST.Dict{1, 0n, [""], 2n, [ST.SSlot{"", 0}, ST.SSlot{"", 1}, ST.SSlot{"", 0}, ST.SSlot{"", 0}], 0}, Array.new(U32, d, 0)), Array.get.at(String, 0, Array.size(String, a)))) == ST.SDict{codes, dict} : ST.Strs}, _ => Sigma<&1, &1, Laws.WFArray(U32, d, codes), _ => Sigma<&1, &1, Laws.WFDictE(dict, es), _ => @j:U32 -> @_:{Cmp.is_lt(U32.cmp(j, n)) == True{} : Bool} -> @code:U32 -> @_:{code == Laws.rd(U32, codes, U32.shln(1, d), U32.and(j, U32.sub(U32.shln(1, d), 1)), Cmp.is_lt(U32.cmp(U32.and(j, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))) : U32} -> Sigma<&1, &1, {Cmp.is_lt(Nat.cmp(U32.to_nat(code), List.length(&2, String, es))) == True{} : Bool}, _ => {Laws.nthn(es, U32.to_nat(code)) == Laws.rd_size(String, j, Array.size(String, a)) : String}>>>>>>>
#|Context:
#|- n      : U32
#|- d      : Nat
#|- a      : Array<String>
#|- fits   : {Cmp.is_le(U32.cmp(n, U32.shln(1, d))) == True{} : Bool}
#|- small  : {Cmp.is_lt(U32.cmp(n, 1073741824)) == True{} : Bool}
#|- probes : Laws.EncProbe(U32.to_nat(n), 0, a, ST.Dict{1, 0n, [""], 2n, [ST.SSlot{"", 0}, ST.SSlot{"", 1}, ST.SSlot{"", 0}, ST.SSlot{"", 0}], 0})
#|Location: strs_encode_cells_mutated
#|70 | def strs_encode_cells_mutated(n, d, a, fits, small, probes):
#|71>|   PST.enc_law(n, d, a, PST.enc_go(U32.to_nat(n), 0, d, a, ST.Dict.empty(), Array.new(U32, d, 0), "" <> Nil{}, Laws.wf_new(U32, d, 0), B.room_from(d, n, fits), PST.lim0(n, small), {==})(PST.ehyp0(d, a, Array.new(U32, d, 0), "" <> Nil{}))(Laws.dict_empty_wf())(probes))
#|   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|72 | 
