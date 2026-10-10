# T5 mutation (plan M_01 section 4): a disposable copy of the production head rule
# Opt.hmin with the WRONG merge (the outer Head's limit wins instead of the min), run
# through the R1 theorem of LAWS.bend section 8 against the production runner
# Exec.run_pure. The real proof term (PROOF_exec.bend's run_suffix / two_heads) must
# be refused for the mutated rule: Bend answers SOME PROOFS FAIL with the mutated
# limit in `expected` and the real `U32.min(m, n)` in `observed`. The positive control
# head_merge_run_copy states the theorem over the real P.Opt.hmin with the same term
# and checks, so only the mutation is reported.
# Scope: this fixture checks the production proof term against a MUTATED, RENAMED disposable copy, so it shows that
# term is refused for that copy; it is not a rejection of a mutated production function.
# That stronger claim, a wrong PRODUCTION function is rejected, is checked by scripts/mutation_check.sh
# (make mutation-check): it patches the production source in place and re-runs bend PROOF.bend.
import Base
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/exec.bend as Q
import ./../../LAWS.bend as Laws
import ./../../PROOF_exec.bend as PE

# the production rule, as in src/plan.bend
law head_merge_run_copy:
  for +x: P.Plan
  for +n: U32
  for +m: U32
  for env: P.Env
  {Q.Exec.run_pure(P.Head{n, P.Head{m, x}}, env) == Q.Exec.run_pure(P.Head{P.Opt.hmin(m, Some{n}), x}, env) : E.ResT(C.Frame)}

def head_merge_run_copy(x, n, m, env):
  PE.run_suffix(x, Q.IHead{m} <> Q.IHead{n} <> Nil{}, Q.IHead{P.Opt.hmin(m, Some{n})} <> Nil{}, env, {==}, s => PE.two_heads(n, m, s))

# MUTATED copy of Opt.hmin: the outer limit replaces the inner one (wrong: Head{1, Head{0, x}} would keep a row)
def Mut.hmin(+m: U32, n: Maybe<&2, U32>) -> U32:
  match n:
    case None{}:
      m
    case Some{k}:
      k

law head_merge_run_mutated:
  for +x: P.Plan
  for +n: U32
  for +m: U32
  for env: P.Env
  {Q.Exec.run_pure(P.Head{n, P.Head{m, x}}, env) == Q.Exec.run_pure(P.Head{Mut.hmin(m, Some{n}), x}, env) : E.ResT(C.Frame)}

def head_merge_run_mutated(x, n, m, env):
  PE.run_suffix(x, Q.IHead{m} <> Q.IHead{n} <> Nil{}, Q.IHead{Mut.hmin(m, Some{n})} <> Nil{}, env, {==}, s => PE.two_heads(n, m, s))

#|SOME PROOFS FAIL
#|Error:
#|- expected : {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, s)) == Q.Exec.step(Q.IHead{n}, s) : Q.St}
#|- observed : {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, s)) == Q.Exec.step(Q.IHead{U32.min(m, n)}, s) : Q.St}
#|Context:
#|- x   : P.Plan
#|- n   : U32
#|- m   : U32
#|- env : P.Env
#|- s   : Q.St
#|Location: head_merge_run_mutated
#|47 | def head_merge_run_mutated(x, n, m, env):
#|48>|   PE.run_suffix(x, Q.IHead{m} <> Q.IHead{n} <> Nil{}, Q.IHead{Mut.hmin(m, Some{n})} <> Nil{}, env, {==}, s => PE.two_heads(n, m, s))
#|   |                                                                                                               ^^^^^^^^^^^^^^^^^^^^^
#|49 | 
