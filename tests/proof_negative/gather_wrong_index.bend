# T5 mutation (plan M_01 section 4, M5): a disposable copy of the production gather loop
# Kernel.gather.go that reads the source at the WRONG index (the pending index plus one), run
# through the content theorem of LAWS.bend section 11 (gather_contents: out[k] == src[perm[k]]
# for every k < n). The real proof term (PROOF_contents.bend's gather_fin over gather_go) must
# be refused for the mutated loop: Bend answers SOME PROOFS FAIL with the mutated kernel in
# `expected` and the production Kernel.gather.go in `observed`. The positive control
# gather_contents_copy states the theorem over the real kernel with the same term and checks,
# so only the mutation is reported.
# Scope: this fixture checks the production proof term against a MUTATED, RENAMED disposable copy, so it shows that
# term is refused for that copy. The term is tied to the production function's NAME (the error compares the renamed copy
# with the production function), so an UNMUTATED renamed copy is refused too: on its own this fixture does NOT show that
# a wrong copy is rejected.
# That stronger claim, a wrong PRODUCTION function is rejected, is checked by scripts/mutation_check.sh
# (make mutation-check): it patches the production source in place and re-runs bend PROOF.bend.
import Base
import ./../../src/kernels.bend as K
import ./../../LAWS.bend as Laws
import ./../../PROOF_bits.bend as B
import ./../../PROOF_contents.bend as PC

# the production theorem, as in LAWS.bend section 11
law gather_contents_copy:
  for +d: Nat
  for +n: U32
  for src: Array<U32>
  for perm: Array<U32>
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, d, src, perm, z)), k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}

def gather_contents_copy(d, n, src, perm, z, k, fits, hk):
  PC.gather_fin(d, n, src, perm, z, k, hk, PC.gather_go(U32.to_nat(n), 0, d, src, Array.new(U32, d, z), perm, Laws.wf_new(U32, d, z), B.room_from(d, n, fits))(PC.ghyp0(d, src, Array.new(U32, d, z), perm)))

# MUTATED copy of Kernel.gather.go: the cell read from src is at the pending index PLUS ONE
# (out[j] = src[perm[j] + 1]; wrong: a gather by the identity permutation would shift the rows)
def Mut.gather.go(~T: Data, n: Nat, +j: U32, so: Array<T> & Array<T>, r: Array<U32> & U32) -> Array<T> & Array<U32>:
  match n:
    case 0n:
      (src, out) = so
      (perm, i) = r
      (out, perm)
    case 1n+p:
      (src, out) = so
      (perm, i) = r
      +j2 = U32.inc(j)
      Mut.gather.go(~T, p, j2, K.Kernel.gather.put(~T, out, j, Array.get(T, src, U32.inc(i))), Array.get(U32, perm, j2))

def Mut.gather(~T: Data, +n: U32, +d: Nat, src: Array<T>, perm: Array<U32>, +z: T) -> Array<T> & Array<U32>:
  Mut.gather.go(~T, U32.to_nat(n), 0, (src, Array.new(T, d, z)), Array.get(U32, perm, 0))

law gather_contents_mutated:
  for +d: Nat
  for +n: U32
  for src: Array<U32>
  for perm: Array<U32>
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, Mut.gather(~U32, n, d, src, perm, z)), k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}

def gather_contents_mutated(d, n, src, perm, z, k, fits, hk):
  PC.gather_fin(d, n, src, perm, z, k, hk, PC.gather_go(U32.to_nat(n), 0, d, src, Array.new(U32, d, z), perm, Laws.wf_new(U32, d, z), B.room_from(d, n, fits))(PC.ghyp0(d, src, Array.new(U32, d, z), perm)))

#|SOME PROOFS FAIL
#|Error:
#|- expected : {Laws.rd_size(U32, k, Array.size(U32, Pair.fst(Array<U32>, Array<U32>, Mut.gather.go(U32, U32.to_nat(n), 0, (src, Array.new(U32, d, z)), Array.get.at(U32, 0, Array.size(U32, perm)))))) == Laws.rd_size(U32, Laws.rd_size(U32, k, Array.size(U32, perm)), Array.size(U32, src)) : U32}
#|- observed : {Laws.rd_size(U32, k, Array.size(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather.go(U32, U32.to_nat(n), 0, (src, Array.new(U32, d, z)), Array.get.at(U32, 0, Array.size(U32, perm)))))) == Laws.rd_size(U32, Laws.rd_size(U32, k, Array.size(U32, perm)), Array.size(U32, src)) : U32}
#|Context:
#|- d    : Nat
#|- n    : U32
#|- src  : Array<U32>
#|- perm : Array<U32>
#|- z    : U32
#|- k    : U32
#|- fits : {Cmp.is_le(U32.cmp(n, U32.shln(1, d))) == True{} : Bool}
#|- hk   : {Cmp.is_lt(U32.cmp(k, n)) == True{} : Bool}
#|Location: gather_contents_mutated
#|64 | def gather_contents_mutated(d, n, src, perm, z, k, fits, hk):
#|65>|   PC.gather_fin(d, n, src, perm, z, k, hk, PC.gather_go(U32.to_nat(n), 0, d, src, Array.new(U32, d, z), perm, Laws.wf_new(U32, d, z), B.room_from(d, n, fits))(PC.ghyp0(d, src, Array.new(U32, d, z), perm)))
#|   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|66 | 
