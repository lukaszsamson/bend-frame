# T5 mutation (plan M_01 section 4, M5 part 4): a disposable copy of the production in-place
# selection loop Kernel.choose.go (fill_null / when: a[i] := m[i] ? a[i] : b[i]) with the mask
# INVERTED (a set word takes b's cell, a 0 word keeps a's), run through the content theorem of
# LAWS.bend section 15 (choose_cell: at every pos < n the output holds a's cell where the mask word
# is set and b's where it is 0). The real proof term (PROOF_inplace.bend's ch_cell_fin over
# choose_w) must be refused for the mutated loop: Bend answers SOME PROOFS FAIL with the mutated
# kernel in `expected` and the production Kernel.choose in `observed`. The positive control
# choose_cell_copy states the theorem over the real kernel with the same term and checks, so only
# the mutation is reported.
import Base
import ./../../src/kernels.bend as K
import ./../../LAWS.bend as Laws
import ./../../PROOF_inplace.bend as PI

# the production theorem, as in LAWS.bend section 15
law choose_cell_copy:
  for +n: U32
  for +d: Nat
  for m: Array<U32>
  for a: Array<U32>
  for b: Array<U32>
  for +pos: U32
  for wf: Laws.WFArray(U32, d, a)
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hpos: {U32.is_lt(pos, n) == True{} : Bool}
  {Laws.rd_at(U32, Pair.snd(Array<U32>, Array<U32>, K.Kernel.choose(~U32, n, m, a, b)), pos) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), Laws.rd_at(U32, b, pos)) : U32}

def choose_cell_copy(n, d, m, a, b, pos, wf, fits, hpos):
  PI.ch_cell_fin(n, d, m, a, b, pos, PI.choose_w(~U32, n, d, m, a, b, pos, wf, fits, hpos))

# MUTATED copy of Kernel.choose.go: the mask test is inverted (a set word picks b's cell)
def Mut.choose.go(~T: Data, n: Nat, +i: U32, ra: Array<T> & T, rb: Array<T> & T, rm: Array<U32> & U32) -> Array<U32> & Array<T>:
  match n:
    case 0n:
      (a, x) = ra
      (b, y) = rb
      (m, w) = rm
      (m, a)
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      (m, w) = rm
      +j = U32.inc(i)
      Mut.choose.go(~T, p, j, Array.get(T, Array.set(T, a, i, Bool.pick(T, U32.is_ne(w, 0), y, x)), j), Array.get(T, b, j), Array.get(U32, m, j))

def Mut.choose(~T: Data, +n: U32, m: Array<U32>, a: Array<T>, b: Array<T>) -> Array<U32> & Array<T>:
  Mut.choose.go(~T, U32.to_nat(n), 0, Array.get(T, a, 0), Array.get(T, b, 0), Array.get(U32, m, 0))

law choose_cell_mutated:
  for +n: U32
  for +d: Nat
  for m: Array<U32>
  for a: Array<U32>
  for b: Array<U32>
  for +pos: U32
  for wf: Laws.WFArray(U32, d, a)
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hpos: {U32.is_lt(pos, n) == True{} : Bool}
  {Laws.rd_at(U32, Pair.snd(Array<U32>, Array<U32>, Mut.choose(~U32, n, m, a, b)), pos) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), Laws.rd_at(U32, b, pos)) : U32}

def choose_cell_mutated(n, d, m, a, b, pos, wf, fits, hpos):
  PI.ch_cell_fin(n, d, m, a, b, pos, PI.choose_w(~U32, n, d, m, a, b, pos, wf, fits, hpos))

#|SOME PROOFS FAIL
#|Error:
#|- expected : {Laws.rd_size(U32, pos, Array.size(U32, Pair.snd(Array<U32>, Array<U32>, Mut.choose.go(U32, U32.to_nat(n), 0, Array.get.at(U32, 0, Array.size(U32, a)), Array.get.at(U32, 0, Array.size(U32, b)), Array.get.at(U32, 0, Array.size(U32, m)))))) == Bool.pick(U32, Bool.not(Cmp.is_eq(U32.cmp(Laws.rd_size(U32, pos, Array.size(U32, m)), 0))), Laws.rd_size(U32, pos, Array.size(U32, a)), Laws.rd_size(U32, pos, Array.size(U32, b))) : U32}
#|- observed : {Laws.rd_size(U32, pos, Array.size(U32, Pair.snd(Array<U32>, Array<U32>, K.Kernel.choose.go(U32, U32.to_nat(n), 0, Array.get.at(U32, 0, Array.size(U32, a)), Array.get.at(U32, 0, Array.size(U32, b)), Array.get.at(U32, 0, Array.size(U32, m)))))) == Bool.pick(U32, Bool.not(Cmp.is_eq(U32.cmp(Laws.rd_size(U32, pos, Array.size(U32, m)), 0))), Laws.rd_size(U32, pos, Array.size(U32, a)), Laws.rd_size(U32, pos, Array.size(U32, b))) : U32}
#|Context:
#|- n    : U32
#|- d    : Nat
#|- m    : Array<U32>
#|- a    : Array<U32>
#|- b    : Array<U32>
#|- pos  : U32
#|- wf   : Laws.WFArray(U32, d, a)
#|- fits : {Cmp.is_le(U32.cmp(n, U32.shln(1, d))) == True{} : Bool}
#|- hpos : {Cmp.is_lt(U32.cmp(pos, n)) == True{} : Bool}
#|Location: choose_cell_mutated
#|61 | def choose_cell_mutated(n, d, m, a, b, pos, wf, fits, hpos):
#|62>|   PI.ch_cell_fin(n, d, m, a, b, pos, PI.choose_w(~U32, n, d, m, a, b, pos, wf, fits, hpos))
#|   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|63 | 
