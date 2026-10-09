# T5 mutation (plan M_01 section 4, M5 part 2): a disposable copy of the production unary
# evaluator Eval.un (Eval.un.v / Eval.un.i) in which Neg over an I32 column answers a U32
# column (the WRONG dtype: the words are the same two's-complement bits, so only the typing
# claim sees it), run through the typing law of LAWS.bend section 13 (eval_un_typed: the
# operation answers the dtype its rule gives). The real proof term of PROOF_evalops.bend's
# (Neg, CI32) case must be refused for the mutated evaluator: Bend answers SOME PROOFS FAIL
# with u32 in `expected` and i32 in `observed`. The positive control un_neg_i32_copy states
# the claim over the real V.Eval.un with the same term and checks, so only the mutation is
# reported.
import Base
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/eval.bend as V
import ./../../LAWS.bend as Laws
import ./../../PROOF_lib.bend as L

# the production claim at (Neg, CI32), as PROOF_evalops.bend proves it
law un_neg_i32_copy:
  for +n: U32
  for +d: Nat
  for v: C.Valid
  for x: Array<U32>
  for +t: D.DType
  for hok: {X.Expr.type.un.ok(X.Neg{}, D.TI32{}) == Done{t} : E.Res(D.DType)}
  Laws.ResW(True{}, t, n, V.Eval.un(X.Neg{}, C.CI32{n, d, v, x}))

def un_neg_i32_copy(n, d, v, x, t, hok):
  (V.Eval.un(X.Neg{}, C.CI32{n, d, v, x}), {==}, (L.done_inj(D.DType, D.TI32{}, t, hok), {==}))

# MUTATED copy of Eval.un.i: Neg builds a CU32 column (same words, wrong dtype)
def Mut.un.i(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.Neg{}:
      Done{C.CU32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}}
    case X.Abs{}:
      Done{C.CI32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => D.I32.mag(D.I32{w})), n, d, x, 0)}}
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
  (Mut.un(X.Neg{}, C.CI32{n, d, v, x}), {==}, (L.done_inj(D.DType, D.TI32{}, t, hok), {==}))

#|SOME PROOFS FAIL
#|Error:
#|- expected : {D.TU32{} == t : D.DType}
#|- observed : {D.TI32{} == t : D.DType}
#|Context:
#|- n   : U32
#|- d   : Nat
#|- v   : C.Valid
#|- x   : Array<U32>
#|- t   : D.DType
#|- hok : {Done{D.TI32{}} == Done{t} : Result<&2, &2, E.Err, D.DType>}
#|Location: un_neg_i32_mutated
#|75 | def un_neg_i32_mutated(n, d, v, x, t, hok):
#|76>|   (Mut.un(X.Neg{}, C.CI32{n, d, v, x}), {==}, (L.done_inj(D.DType, D.TI32{}, t, hok), {==}))
#|   |                                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|77 | 
