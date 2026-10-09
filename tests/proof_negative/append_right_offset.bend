# T5 mutation (plan M_01 section 4, M5 part 4): a disposable copy of the production concatenation
# kernel Kernel.append (concat_vertical's buffers: a's rows copied to 0 .. na, then b's to na .. na+nb
# by two Kernel.copy_into loops) whose second copy starts ONE SLOT TOO FAR RIGHT (offset na + 1: a gap
# at na and b's last row past the end), run through the content theorem of LAWS.bend section 15
# (append_cells: b's row k sits at na + k). The real proof term (PROOF_append.bend's append_w) must be
# refused for the mutated kernel: Bend answers SOME PROOFS FAIL with the mutated offset in `expected`
# and the production Kernel.append's offset na in `observed`. The positive control append_cells_copy
# states the theorem over the real kernel with the same term and checks, so only the mutation is
# reported.
import Base
import ./../../src/kernels.bend as K
import ./../../LAWS.bend as Laws
import ./../../PROOF_append.bend as PA

# the production theorem, as in LAWS.bend section 15
law append_cells_copy:
  for +na: U32
  for +nb: U32
  for +d: Nat
  for a: Array<U32>
  for b: Array<U32>
  for +z: U32
  for fits: Laws.CatFits(na, nb, d)
  Laws.AppendW(a, b, na, nb, d, z)

def append_cells_copy(na, nb, d, a, b, z, fits):
  PA.append_w(~U32, na, nb, d, a, b, z, fits)

# MUTATED copy of Kernel.append: b's rows are copied from offset na + 1 instead of na
def Mut.append(~T: Data, +na: U32, +nb: U32, +d: Nat, a: Array<T>, b: Array<T>, +z: T) -> Array<T>:
  K.Kernel.copy_into(~T, nb, U32.inc(na), K.Kernel.copy_into(~T, na, 0, Array.new(T, d, z), a), b)

# the theorem's statement over the mutated kernel (Laws.AppendW with Mut.append)
def MutAppendW(-a: Array<U32>, -b: Array<U32>, +na: U32, +nb: U32, +d: Nat, +z: U32) -> Type:
  &o: Array<U32> -> {Mut.append(~U32, na, nb, d, a, b, z) == o : Array<U32>} & Laws.WFArray(U32, d, o) & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == Laws.rd_at(U32, a, k) : U32}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.rdN(U32, d, o, U32.add(na, k)) == Laws.rd_at(U32, b, k) : U32})

law append_cells_mutated:
  for +na: U32
  for +nb: U32
  for +d: Nat
  for a: Array<U32>
  for b: Array<U32>
  for +z: U32
  for fits: Laws.CatFits(na, nb, d)
  MutAppendW(a, b, na, nb, d, z)

def append_cells_mutated(na, nb, d, a, b, z, fits):
  PA.append_w(~U32, na, nb, d, a, b, z, fits)

#|SOME PROOFS FAIL
#|Error:
#|- expected : Sigma<&1, &1, Array<U32>, o => Sigma<&1, &1, {K.Kernel.copy_into.go(U32, U32.to_nat(nb), 0, U32.inc(na), K.Kernel.copy_into.go(U32, U32.to_nat(na), 0, 0, Array.new(U32, d, z), Array.get.at(U32, 0, Array.size(U32, a))), Array.get.at(U32, 0, Array.size(U32, b))) == o : Array<U32>}, _ => Sigma<&1, &1, Laws.WFArray(U32, d, o), _ => Sigma<&1, &1, @k:U32 -> @_:{Cmp.is_lt(U32.cmp(k, na)) == True{} : Bool} -> {Laws.rd(U32, o, U32.shln(1, d), U32.and(k, U32.sub(U32.shln(1, d), 1)), Cmp.is_lt(U32.cmp(U32.and(k, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))) == Laws.rd_size(U32, k, Array.size(U32, a)) : U32}, _ => @k:U32 -> @_:{Cmp.is_lt(U32.cmp(k, nb)) == True{} : Bool} -> {Laws.rd(U32, o, U32.shln(1, d), U32.and(U32.add(na, k), U32.sub(U32.shln(1, d), 1)), Cmp.is_lt(U32.cmp(U32.and(U32.add(na, k), U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))) == Laws.rd_size(U32, k, Array.size(U32, b)) : U32}>>>>
#|- observed : Sigma<&1, &1, Array<U32>, o => Sigma<&1, &1, {K.Kernel.copy_into.go(U32, U32.to_nat(nb), 0, na, K.Kernel.copy_into.go(U32, U32.to_nat(na), 0, 0, Array.new(U32, d, z), Array.get.at(U32, 0, Array.size(U32, a))), Array.get.at(U32, 0, Array.size(U32, b))) == o : Array<U32>}, _ => Sigma<&1, &1, Laws.WFArray(U32, d, o), _ => Sigma<&1, &1, @k:U32 -> @_:{Cmp.is_lt(U32.cmp(k, na)) == True{} : Bool} -> {Laws.rd(U32, o, U32.shln(1, d), U32.and(k, U32.sub(U32.shln(1, d), 1)), Cmp.is_lt(U32.cmp(U32.and(k, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))) == Laws.rd_size(U32, k, Array.size(U32, a)) : U32}, _ => @k:U32 -> @_:{Cmp.is_lt(U32.cmp(k, nb)) == True{} : Bool} -> {Laws.rd(U32, o, U32.shln(1, d), U32.and(U32.add(na, k), U32.sub(U32.shln(1, d), 1)), Cmp.is_lt(U32.cmp(U32.and(U32.add(na, k), U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))) == Laws.rd_size(U32, k, Array.size(U32, b)) : U32}>>>>
#|Context:
#|- na   : U32
#|- nb   : U32
#|- d    : Nat
#|- a    : Array<U32>
#|- b    : Array<U32>
#|- z    : U32
#|- fits : {Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d)))) == True{} : Bool}
#|Location: append_cells_mutated
#|47 | def append_cells_mutated(na, nb, d, a, b, z, fits):
#|48>|   PA.append_w(~U32, na, nb, d, a, b, z, fits)
#|   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|49 | 
