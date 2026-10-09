# T5 mutation (plan M_01 section 4, M5): a disposable copy of the production compaction loop
# Kernel.compact_keep.go with the mask FLIPPED (the cursor advances on a 0 word, so the dropped
# rows are kept and the kept rows overwritten), run through the content theorem of LAWS.bend
# section 11 (compact_contents: every row with a set mask word sits at its cursor position). The
# real proof term (PROOF_contents.bend's cspec_run) must be refused for the mutated loop: Bend
# answers SOME PROOFS FAIL with the mutated kernel in `expected` and the production
# Kernel.compact_keep.go in `observed`. The positive control compact_contents_copy states the
# theorem over the real kernel with the same term and checks, so only the mutation is reported.
import Base
import ./../../src/kernels.bend as K
import ./../../LAWS.bend as Laws
import ./../../PROOF_contents.bend as PC

# the production theorem, as in LAWS.bend section 11
law compact_contents_copy:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for mask: Array<U32>
  for +z: U32
  for room: Laws.CRoom(U32.to_nat(n), 0, 0, d, mask)
  Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a, mask, Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a, mask, z)))

def compact_contents_copy(d, n, a, mask, z, room):
  PC.cspec_run(~U32, U32.to_nat(n), 0, 0, d, a, Array.new(U32, d, z), mask, Laws.wf_new(U32, d, z), a, mask, {==}, {==}, room)

# MUTATED copy of Kernel.compact_keep.go: the cursor advances by 1 - bit (a flipped mask)
def Mut.compact_keep.go(~T: Data, n: Nat, +i: U32, +k: U32, ao: Array<T> & Array<T>, mi: Array<U32> & U32) -> Array<T> & Array<U32>:
  match n:
    case 0n:
      (a, out) = ao
      (mask, bit) = mi
      (out, mask)
    case 1n+p:
      (a, out) = ao
      (mask, bit) = mi
      +j = U32.inc(i)
      Mut.compact_keep.go(~T, p, j, U32.add(k, U32.sub(1, bit)), K.Kernel.compact.put(~T, out, k, Array.get(T, a, i)), Array.get(U32, mask, j))

def Mut.compact_keep(~T: Data, +n: U32, +d: Nat, a: Array<T>, mask: Array<U32>, +z: T) -> Array<T> & Array<U32>:
  Mut.compact_keep.go(~T, U32.to_nat(n), 0, 0, (a, Array.new(T, d, z)), Array.get(U32, mask, 0))

law compact_contents_mutated:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for mask: Array<U32>
  for +z: U32
  for room: Laws.CRoom(U32.to_nat(n), 0, 0, d, mask)
  Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a, mask, Pair.fst(Array<U32>, Array<U32>, Mut.compact_keep(~U32, n, d, a, mask, z)))

def compact_contents_mutated(d, n, a, mask, z, room):
  PC.cspec_run(~U32, U32.to_nat(n), 0, 0, d, a, Array.new(U32, d, z), mask, Laws.wf_new(U32, d, z), a, mask, {==}, {==}, room)

#|SOME PROOFS FAIL
#|Error:
#|- expected : Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a, mask, Pair.fst(Array<U32>, Array<U32>, Mut.compact_keep.go(U32, U32.to_nat(n), 0, 0, (a, Array.new(U32, d, z)), Array.get.at(U32, 0, Array.size(U32, mask)))))
#|- observed : Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a, mask, Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep.go(U32, U32.to_nat(n), 0, 0, (a, Array.new(U32, d, z)), Array.get.at(U32, 0, Array.size(U32, mask)))))
#|Context:
#|- d    : Nat
#|- n    : U32
#|- a    : Array<U32>
#|- mask : Array<U32>
#|- z    : U32
#|- room : Laws.CRoom(U32.to_nat(n), 0, 0, d, mask)
#|Location: compact_contents_mutated
#|52 | def compact_contents_mutated(d, n, a, mask, z, room):
#|53>|   PC.cspec_run(~U32, U32.to_nat(n), 0, 0, d, a, Array.new(U32, d, z), mask, Laws.wf_new(U32, d, z), a, mask, {==}, {==}, room)
#|   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|54 | 
