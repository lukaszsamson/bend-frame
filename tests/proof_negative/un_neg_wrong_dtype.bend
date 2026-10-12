# T5 mutation (plan M_01 section 4, M5 part 2): a disposable copy of the production unary
# evaluator Eval.un (Eval.un.v / Eval.un.i / Eval.un.ineg) in which Neg over an I32 column answers a U32
# column (the WRONG dtype: the words are the same two's-complement bits, so only the typing
# claim sees it), run through the typing law of LAWS.bend section 13 (eval_un_typed: the
# operation answers the dtype its rule gives). The real proof term of PROOF_evalops.bend's
# (Neg, CI32) case must be refused for the mutated evaluator: Bend answers SOME PROOFS FAIL
# with a CU32 column in `expected` and the CI32 the witness builds in `observed` (the witness body is
# PROOF_evalops.bend's ineg_w, copied over the mutation). The positive control un_neg_i32_copy states
# the claim over the real V.Eval.un with the same term and checks, so only the mutation is
# reported.
# Scope: this fixture checks the production proof term against a MUTATED, RENAMED disposable copy, so it shows that
# term is refused for that copy; it is not a rejection of a mutated production function.
# That stronger claim, a wrong PRODUCTION function is rejected, is checked by scripts/mutation_check.sh
# (make mutation-check): it patches the production source in place and re-runs bend PROOF.bend.
import Base
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/eval.bend as V
import ./../../LAWS.bend as Laws
import ./../../PROOF_lib.bend as L
import ./../../PROOF_eval.bend as PV
import ./../../PROOF_evalops.bend as PO

# the production claim at (Neg, CI32), as PROOF_evalops.bend proves it (post-review B1: Eval.un.i
# answers Eval.un.ineg, which splits on the validity: AllValid, Kernel.map; Mask, the masked
# Kernel.zipb loop; the witness PO.ineg_w splits the same way)
law un_neg_i32_copy:
  for +n: U32
  for +d: Nat
  for v: C.Valid
  for x: Array<U32>
  for +t: D.DType
  for hok: {X.Expr.type.un.ok(X.Neg{}, D.TI32{}) == Done{t} : E.Res(D.DType)}
  Laws.ResW(True{}, t, n, V.Eval.un(X.Neg{}, C.CI32{n, d, v, x}))

def un_neg_i32_copy(n, d, v, x, t, hok):
  PV.resw_dtype(True{}, t, D.TI32{}, n, Done{V.Eval.un.ineg(n, d, v, x)}, L.done_inj(D.DType, D.TI32{}, t, hok), PV.done_w(D.TI32{}, n, V.Eval.un.ineg(n, d, v, x), PO.ineg_w(n, d, v, x)))

# MUTATED copy of Eval.un.ineg: over an AllValid column, Neg builds a CU32 column (same words, wrong
# dtype); the masked branch is the production one
def Mut.un.ineg(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CU32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}
    case C.Mask{m}:
      V.Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), U32.sub(0, w), 0)), n, d, x, m, 0))

def Mut.un.i(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.Neg{}:
      Done{Mut.un.ineg(n, d, v, x)}
    case X.Abs{}:
      Done{V.Eval.un.iabs(n, d, v, x)}
    case _:
      Fail{V.Eval.bug("unary op on i32")}

def Mut.un.v(op: X.UnOp, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CBool{n, d, v, x}:
      V.Eval.un.b(op, n, d, v, x)
    case C.CI32{n, d, v, x}:
      Mut.un.i(op, n, d, v, x)
    case C.CF32{n, d, v, x}:
      V.Eval.un.f(op, n, d, v, x)
    case C.CStr{n, d, v, x}:
      V.Eval.un.s(op, n, d, v, x)
    case _:
      Fail{V.Eval.bug("unary op")}

def Mut.un(op: X.UnOp, c: C.Column) -> E.ResT(C.Column):
  match op:
    case X.IsNull{}:
      Done{V.Eval.un.nulls(True{}, c)}
    case X.IsNotNull{}:
      Done{V.Eval.un.nulls(False{}, c)}
    case other:
      Mut.un.v(other, c)

# PROOF_evalops.bend's witness PO.ineg_w, its body verbatim, stated over the mutated copy
def ineg_w_mut(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> Laws.ColW(D.TI32{}, n, Mut.un.ineg(n, d, v, x)):
  match v:
    case C.AllValid{}:
      (C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}, {==}, ({==}, {==}))
    case C.Mask{m}:
      PO.mi_w(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), U32.sub(0, w), 0)), n, d, x, m, 0))

# the same claim over the mutated evaluator, with the same proof term: refused
law un_neg_i32_mutated:
  for +n: U32
  for +d: Nat
  for v: C.Valid
  for x: Array<U32>
  for +t: D.DType
  for hok: {X.Expr.type.un.ok(X.Neg{}, D.TI32{}) == Done{t} : E.Res(D.DType)}
  Laws.ResW(True{}, t, n, Mut.un(X.Neg{}, C.CI32{n, d, v, x}))

def un_neg_i32_mutated(n, d, v, x, t, hok):
  PV.resw_dtype(True{}, t, D.TI32{}, n, Done{Mut.un.ineg(n, d, v, x)}, L.done_inj(D.DType, D.TI32{}, t, hok), PV.done_w(D.TI32{}, n, Mut.un.ineg(n, d, v, x), ineg_w_mut(n, d, v, x)))

#|SOME PROOFS FAIL
#|Error:
#|- expected : C.CU32{n, d, C.AllValid{}, K.Kernel.map.go(U32, U32, w => U32.sub(0, w), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get.at(U32, 0, Array.size(U32, x)))}
#|- observed : C.CI32{n, d, C.AllValid{}, K.Kernel.map.go(U32, U32, w => U32.sub(0, w), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get.at(U32, 0, Array.size(U32, x)))}
#|Context:
#|- n : U32
#|- d : Nat
#|- x : Array<U32>
#|Location: ineg_w_mut
#|85 |     case C.AllValid{}:
#|86>|       (C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}, {==}, ({==}, {==}))
#|   |                                                                                                 ^^^^
#|87 |     case C.Mask{m}:
