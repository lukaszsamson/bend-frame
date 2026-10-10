# T5 mutation (plan M_01 section 4, M5 part 2): a disposable copy of the stack machine's
# Eval.fit that does NOT broadcast a 1-row side to the other operand's length (every kind
# keeps its column), run through the shape lemma behind LAWS.bend section 13's run_typed
# (PROOF_evalrun.bend fit_w: the fitted column has fitlen rows, i.e. n for a literal or
# aggregation slot). The real proof text must be refused for the mutated fit: Bend answers
# SOME PROOFS FAIL with the un-broadcast column in `expected` and Eval.bcast in `observed`.
# The positive control fit_w_copy states the lemma over the real V.Eval.fit with the same
# text and checks, so only the mutation is reported.
# Scope: this fixture checks the production proof term against a MUTATED, RENAMED disposable copy, so it shows that
# term is refused for that copy; it is not a rejection of a mutated production function.
# That stronger claim, a wrong PRODUCTION function is rejected, is checked by scripts/mutation_check.sh
# (make mutation-check): it patches the production source in place and re-runs bend PROOF.bend.
import Base
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/eval.bend as V
import ./../../LAWS.bend as Laws
import ./../../PROOF_evalrun.bend as PR

# the production lemma, as PROOF_evalrun.bend proves it
law fit_w_copy:
  for k: V.SKind
  for c: C.Column
  for +n: U32
  for +t: D.DType
  for +m: U32
  for hc: Laws.ColTy(t, m, c)
  Laws.ColW(t, PR.fitlen(k, m, n), V.Eval.fit(k, c, n))

def fit_w_copy(k, c, n, t, m, hc):
  match k:
    case V.KFull{}:
      (c, {==}, hc)
    case V.KLit{}:
      (ed, el) = hc
      PR.fit_lit(n, t, c, ed, Laws.bcast_typed(c, n))
    case V.KAgg{}:
      (ed, el) = hc
      PR.fit_lit(n, t, c, ed, Laws.bcast_typed(c, n))

# MUTATED copy of Eval.fit: a 1-row side is NOT broadcast
def Mut.fit(k: V.SKind, c: C.Column, +n: U32) -> C.Column:
  match k:
    case V.KFull{}:
      c
    case _:
      c

# the same lemma over the mutated fit, with the same text: refused
law fit_w_mutated:
  for k: V.SKind
  for c: C.Column
  for +n: U32
  for +t: D.DType
  for +m: U32
  for hc: Laws.ColTy(t, m, c)
  Laws.ColW(t, PR.fitlen(k, m, n), Mut.fit(k, c, n))

def fit_w_mutated(k, c, n, t, m, hc):
  match k:
    case V.KFull{}:
      (c, {==}, hc)
    case V.KLit{}:
      (ed, el) = hc
      PR.fit_lit(n, t, c, ed, Laws.bcast_typed(c, n))
    case V.KAgg{}:
      (ed, el) = hc
      PR.fit_lit(n, t, c, ed, Laws.bcast_typed(c, n))

#|SOME PROOFS FAIL
#|Error:
#|- expected : Sigma<&1, &1, C.Column, c2 => Sigma<&1, &1, {c == c2 : C.Column}, _ => Sigma<&1, &1, {Laws.cdtype(c2) == t : D.DType}, _ => {Laws.clen(c2) == n : U32}>>>
#|- observed : Sigma<&1, &1, C.Column, c2 => Sigma<&1, &1, {V.Eval.bcast.a(n, C.Column.dtype(c)) == c2 : C.Column}, _ => Sigma<&1, &1, {Laws.cdtype(c2) == t : D.DType}, _ => {Laws.clen(c2) == n : U32}>>>
#|Context:
#|- c  : C.Column
#|- n  : U32
#|- t  : D.DType
#|- m  : U32
#|- ed : {Laws.cdtype(c) == t : D.DType}
#|- el : {Laws.clen(c) == m : U32}
#|Location: fit_w_mutated
#|65 |       (ed, el) = hc
#|66>|       PR.fit_lit(n, t, c, ed, Laws.bcast_typed(c, n))
#|   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|67 |     case V.KAgg{}:
