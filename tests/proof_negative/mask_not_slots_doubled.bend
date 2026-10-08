# B05-h (Fable 6): the proof negative check (a slots law falsified to 2^(d+1)) was done by
# hand and not kept. Plan T5: a negative fixture must fail the checker. This file states
# LAWS.bend's mask_not_slots with the wrong right-hand side (2^(d+1) slots) and proves it
# with PROOF.bend's real proof term; Bend must answer SOME PROOFS FAIL with the observed
# 2^d term. The same term proves the correct statement (mask_not_slots_copy, a positive
# control: only the doubled law is reported). (The fuller T5 set, tests/proof_negative/ and mutation runs, is M2/M5 work.)
import Base
import ./../../src/kernels.bend as K
import ./../../LAWS.bend as Laws
import ./../../PROOF.bend as Pf

# the correct statement, proven by the same term
law mask_not_slots_copy:
  for n: U32
  for +d: Nat
  for a: Array<U32>
  {Laws.slots(U32, K.Kernel.mask_not(n, d, a)) == U32.shln(1, d) : U32}

def mask_not_slots_copy(n, d, a):
  Pf.map_go_slots(~U32, ~U32, ~(x => U32.xor(x, 1)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), U32.shln(1, d), Pf.new_slots(U32, d, 0))

# WRONG on purpose: Kernel.map writes 2^d slots, not 2^(d+1)
law mask_not_slots_doubled:
  for n: U32
  for +d: Nat
  for a: Array<U32>
  {Laws.slots(U32, K.Kernel.mask_not(n, d, a)) == U32.shln(2, d) : U32}

def mask_not_slots_doubled(n, d, a):
  Pf.map_go_slots(~U32, ~U32, ~(x => U32.xor(x, 1)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), U32.shln(1, d), Pf.new_slots(U32, d, 0))

#|SOME PROOFS FAIL
#|Error:
#|- expected : {Laws.slots(U32, K.Kernel.map.go(U32, U32, x => U32.xor(x, 1), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get.at(U32, 0, Array.size(U32, a)))) == U32.shln(2, d) : U32}
#|- observed : {Laws.slots(U32, K.Kernel.map.go(U32, U32, x => U32.xor(x, 1), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get.at(U32, 0, Array.size(U32, a)))) == U32.shln(1, d) : U32}
#|Context:
#|- n : U32
#|- d : Nat
#|- a : Array<U32>
#|Location: mask_not_slots_doubled
#|29 | def mask_not_slots_doubled(n, d, a):
#|30>|   Pf.map_go_slots(~U32, ~U32, ~(x => U32.xor(x, 1)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), U32.shln(1, d), Pf.new_slots(U32, d, 0))
#|   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|31 | 
