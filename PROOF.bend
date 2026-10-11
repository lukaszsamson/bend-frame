# PROOF.bend -- the proofs of LAWS.bend. Each `law x` there is proven by a
# `def Laws.x` in one of the files below; `bend PROOF.bend` (make proofs) and
# `bend PROOF.bend --verdict` (make verdict) check them all. The toolkit and
# its conventions are in PROOF_lib.bend; DESIGN.md section 8 lists what is
# proven, over which production function, and what is not.
#
#   PROOF_lib.bend      toolkit; Word/U32 comparison lemmas; String.eq; I32
#   PROOF_schema.bend   section 1  schema operations
#   PROOF_expr.bend     section 2  expression typing
#   PROOF_plan.bend     sections 3, 4  Plan.schema and the optimizer passes (schema level)
#   PROOF_kernels.bend  sections 5, 5b, 7  columns, kernels (array shape and contents), P0 well-formedness
#   PROOF_exec.bend     section 8  the production runner: R1 head merge against Exec.run_pure
#   PROOF_bits.bend     word-level toolkit (single bits, below-2^d, sub/mask/inc) for section 11
#   PROOF_contents.bend section 11  buffer contents: distinct paths, Array.set separation, kernel contents
#   PROOF_eval.bend     section 13  evaluator typing: purity, shapes, the WF bridge, get_cloned
#   PROOF_evalops.bend  section 13  the operations: eval_un/bin/cast/..agg_typed
#   PROOF_evalrun.bend  section 13  the stack machine (run_typed) and Eval.full / Eval.expr
#   PROOF_strs.bend     section 14  Dictionary strings: decode, Dict.code / encode, merge, same, find, recode
#   PROOF_append.bend   section 15  Kernel.append / copy_into and Strs.append (concat)
#   PROOF_inplace.bend  section 15  Kernel.mask_data / Kernel.choose (in place), Eval.fix / fill / when on Str
#   PROOF_sorthead.bend section 16  Sort + Head: Sort.frame_head and Exec.run_phys against Sort.frame / Frame.head / Exec.run_pure
import Base
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_schema.bend as PS
import ./PROOF_expr.bend as PX
import ./PROOF_plan.bend as PP
import ./PROOF_kernels.bend as PK
import ./PROOF_exec.bend as PE
import ./PROOF_bits.bend as PB
import ./PROOF_contents.bend as PC
import ./PROOF_eval.bend as PV
import ./PROOF_evalops.bend as PO
import ./PROOF_evalrun.bend as PR
import ./PROOF_strs.bend as PST
import ./PROOF_append.bend as PA
import ./PROOF_inplace.bend as PI
import ./PROOF_sorthead.bend as PSH
