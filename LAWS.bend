# LAWS.bend -- the laws of bend-frame: precise claims about the library's
# pure layer (schemas, expression typing, plan schema inference, optimizer
# passes, column shapes, I32 arithmetic). The human states them here;
# PROOF.bend imports this file and proves every one (`law x` is proven by
# `def Laws.x`). `bend PROOF.bend` prints ALL PROOFS CHECK once every law
# holds. DESIGN.md section 8 lists what is proven and what is still future.
#
# Conventions: a law parameter is `+x` when the proof spends it more than
# once; hypotheses are equalities (`{a == b : T}`) over the library's own
# functions; `E.Res(A)` is `Result<&2, &2, E.Err, A>` (schema.bend answers
# Done{schema} or Fail{error}).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/plan.bend as P
import ./src/exec.bend as Q
import ./src/eval.bend as V
import ./src/dump.bend as DP
import ./src/chunks.bend as CH
import ./src/ckernels.bend as KC

# ---- helpers used only to state laws ----------------------------------------------

# the plain column expressions of the given names (Polars `pl.col(name)`)
def cols(names: List<&2, String>) -> List<&2, X.Expr>:
  match names:
    case Nil{}:
      Nil{}
    case n <> rest:
      X.Col{n} <> cols(rest)

# every sort key names a column of the schema
def keys_exist(ks: List<&2, O.SortKey>, +s: List<&2, S.Field>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case O.SortKey{n, d, nl} <> t:
      Bool.and(S.Schema.has(s, n), keys_exist(t, s))

# the comparison operators (== != < <= > >=)
def is_cmp(op: X.BinOp) -> Bool:
  match op:
    case X.Eq{}:
      True{}
    case X.Ne{}:
      True{}
    case X.Lt{}:
      True{}
    case X.Le{}:
      True{}
    case X.Gt{}:
      True{}
    case X.Ge{}:
      True{}
    case _:
      False{}

# the arithmetic operators that keep any numeric operand type (+ - *; `/` is f32-only and
# `//` integer-only since DESIGN.md 15.5.1)
def is_arith(op: X.BinOp) -> Bool:
  match op:
    case X.Add{}:
      True{}
    case X.Sub{}:
      True{}
    case X.Mul{}:
      True{}
    case _:
      False{}

# the boolean connectives (& |)
def is_logic(op: X.BinOp) -> Bool:
  match op:
    case X.And{}:
      True{}
    case X.Or{}:
      True{}
    case _:
      False{}

# the aggregations that answer a count (count, len, n_unique)
def is_counting(op: X.AggOp) -> Bool:
  match op:
    case X.Count{}:
      True{}
    case X.Len{}:
      True{}
    case X.NUnique{}:
      True{}
    case _:
      False{}

# the aggregations that keep the input dtype (min, max, first, last)
def keeps_dtype(op: X.AggOp) -> Bool:
  match op:
    case X.Min{}:
      True{}
    case X.Max{}:
      True{}
    case X.First{}:
      True{}
    case X.Last{}:
      True{}
    case _:
      False{}

# is the plan a Filter node?
def is_filter(p: P.Plan) -> Bool:
  match p:
    case P.Filter{e, x}:
      True{}
    case _:
      False{}

# no Filter has a Filter as its direct input (what the merge pass removes)
def no_adjacent_filters(p: P.Plan) -> Bool:
  match p:
    case P.ScanCsv{path, o, s}:
      True{}
    case P.Source{n, s}:
      True{}
    case P.Select{es, x}:
      no_adjacent_filters(x)
    case P.WithColumns{es, x}:
      no_adjacent_filters(x)
    case P.Filter{e, +x}:
      Bool.and(Bool.not(is_filter(x)), no_adjacent_filters(x))
    case P.Sort{ks, x}:
      no_adjacent_filters(x)
    case P.Drop{ks, x}:
      no_adjacent_filters(x)
    case P.Rename{ks, x}:
      no_adjacent_filters(x)
    case P.Slice{ks, kl, x}:
      no_adjacent_filters(x)
    case P.Tail{ks, x}:
      no_adjacent_filters(x)
    case P.Unique{ks, x}:
      no_adjacent_filters(x)
    case P.GroupBy{ks, ags, mo, x}:
      no_adjacent_filters(x)
    case P.Join{how, lo, ro, l, r}:
      Bool.and(no_adjacent_filters(l), no_adjacent_filters(r))
    case P.Concat{ci, l, r}:
      Bool.and(no_adjacent_filters(l), no_adjacent_filters(r))
    case P.Head{n, x}:
      no_adjacent_filters(x)

# is the plan a Head node?
def is_head(p: P.Plan) -> Bool:
  match p:
    case P.Head{n, x}:
      True{}
    case _:
      False{}

# no Head has a Head as its direct input (what the head pass removes)
def no_adjacent_heads(p: P.Plan) -> Bool:
  match p:
    case P.ScanCsv{path, o, s}:
      True{}
    case P.Source{n, s}:
      True{}
    case P.Select{es, x}:
      no_adjacent_heads(x)
    case P.WithColumns{es, x}:
      no_adjacent_heads(x)
    case P.Filter{e, x}:
      no_adjacent_heads(x)
    case P.Sort{ks, x}:
      no_adjacent_heads(x)
    case P.Drop{ks, x}:
      no_adjacent_heads(x)
    case P.Rename{ks, x}:
      no_adjacent_heads(x)
    case P.Slice{ks, kl, x}:
      no_adjacent_heads(x)
    case P.Tail{ks, x}:
      no_adjacent_heads(x)
    case P.Unique{ks, x}:
      no_adjacent_heads(x)
    case P.GroupBy{ks, ags, mo, x}:
      no_adjacent_heads(x)
    case P.Join{how, lo, ro, l, r}:
      Bool.and(no_adjacent_heads(l), no_adjacent_heads(r))
    case P.Concat{ci, l, r}:
      Bool.and(no_adjacent_heads(l), no_adjacent_heads(r))
    case P.Head{n, +x}:
      Bool.and(Bool.not(is_head(x)), no_adjacent_heads(x))

# the slots of an array: the count Array.size answers, as a pure function
# of the tree (a leaf is one slot, a node doubles its left half)
def slots(-T: Type, a: Array<T>) -> U32:
  match a:
    case ALeaf{x}:
      1
    case ANode{xs, ys}:
      U32.shl(slots(T, xs))

# =====================================================================================
# 1. Schema operations (src/schema.bend)
# =====================================================================================

# LAW: selecting no column of any schema succeeds with the empty schema
law project_nil:
  for +s: List<&2, S.Field>
  {S.Schema.project(Nil{}, s) == Done{Nil{}} : E.Res(List<&2, S.Field>)}

# LAW: a successful projection has exactly one field per requested name
law project_length:
  for +names: List<&2, String>
  for +s: List<&2, S.Field>
  for out: List<&2, S.Field>
  for ok: {S.Schema.project(names, s) == Done{out} : E.Res(List<&2, S.Field>)}
  {List.length(&2, S.Field, out) == List.length(&2, String, names) : Nat}

# LAW: a successful projection has exactly the requested names, in order
law project_names:
  for +names: List<&2, String>
  for +s: List<&2, S.Field>
  for out: List<&2, S.Field>
  for ok: {S.Schema.project(names, s) == Done{out} : E.Res(List<&2, S.Field>)}
  {S.Schema.names(out) == names : List<&2, String>}

# LAW: with_columns of a name the schema already has replaces the field in
# place: the width does not change
law with_existing_keeps_width:
  for +s: List<&2, S.Field>
  for +n: String
  for t: D.DType
  for has: {S.Schema.has(s, n) == True{} : Bool}
  {List.length(&2, S.Field, S.Schema.with(s, S.Field{n, t})) == List.length(&2, S.Field, s) : Nat}

# LAW: with_columns of a new name appends the field at the end
law with_new_appends:
  for s: List<&2, S.Field>
  for +n: String
  for t: D.DType
  for has: {S.Schema.has(s, n) == False{} : Bool}
  {S.Schema.with(s, S.Field{n, t}) == List.append(&2, S.Field, s, S.Field{n, t} <> Nil{}) : List<&2, S.Field>}

# =====================================================================================
# 2. Expression typing (src/expr.bend): Expr.type is strict and total
# =====================================================================================

# LAW: dtype equality is reflexive
law dtype_eq_refl:
  for t: D.DType
  {D.DType.eq(t, t) == True{} : Bool}

# LAW: an alias names its expression
law alias_name:
  for e: X.Expr
  for n: String
  {X.Expr.name(X.Alias{e, n}) == n : String}

# LAW: a column expression is named after its column
law col_name:
  for n: String
  {X.Expr.name(X.Col{n}) == n : String}

# LAW: an alias has the type of the expression it names
law alias_type:
  for e: X.Expr
  for +s: List<&2, S.Field>
  for n: String
  {X.Expr.type(X.Alias{e, n}, s) == X.Expr.type(e, s) : E.Res(D.DType)}

# LAW: an alias aggregates exactly when its expression does
law alias_is_agg:
  for e: X.Expr
  for n: String
  {X.Expr.is_agg(X.Alias{e, n}) == X.Expr.is_agg(e) : Bool}

# LAW: an aggregation is an aggregation
law agg_is_agg:
  for op: X.AggOp
  for e: X.Expr
  {X.Expr.is_agg(X.Agg{op, e}) == True{} : Bool}

# LAW: a column reads itself and nothing else
law col_refs:
  for n: String
  {X.Expr.refs(X.Col{n}) == n <> Nil{} : List<&2, String>}

# LAW: a typed literal has the type of its scalar, under any schema
law lit_type:
  for v: D.Scalar
  for s: List<&2, S.Field>
  for t: D.DType
  for d: {D.Scalar.dtype(v) == Some{t} : Maybe<&2, D.DType>}
  {X.Expr.type(X.Lit{v}, s) == Done{t} : E.Res(D.DType)}

# LAW: a column expression has the dtype the schema gives its name
law col_type:
  for +n: String
  for +s: List<&2, S.Field>
  for t: D.DType
  for f: {S.Schema.find(s, n) == Some{t} : Maybe<&2, D.DType>}
  {X.Expr.type(X.Col{n}, s) == Done{t} : E.Res(D.DType)}

# LAW: comparing two expressions of one dtype gives bool
law cmp_type_bool:
  for op: X.BinOp
  for a: X.Expr
  for b: X.Expr
  for +s: List<&2, S.Field>
  for +t: D.DType
  for cmp: {is_cmp(op) == True{} : Bool}
  for ta: {X.Expr.type(a, s) == Done{t} : E.Res(D.DType)}
  for tb: {X.Expr.type(b, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Bin{op, a, b}, s) == Done{D.TBool{}} : E.Res(D.DType)}

# LAW: arithmetic over two expressions of one numeric dtype keeps that dtype
law arith_type:
  for op: X.BinOp
  for a: X.Expr
  for b: X.Expr
  for +s: List<&2, S.Field>
  for +t: D.DType
  for ar: {is_arith(op) == True{} : Bool}
  for num: {X.DType.is_num(t) == True{} : Bool}
  for ta: {X.Expr.type(a, s) == Done{t} : E.Res(D.DType)}
  for tb: {X.Expr.type(b, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Bin{op, a, b}, s) == Done{t} : E.Res(D.DType)}

# LAW: modulo over two expressions of one integer dtype keeps that dtype
law mod_type:
  for a: X.Expr
  for b: X.Expr
  for +s: List<&2, S.Field>
  for +t: D.DType
  for int: {X.DType.is_int(t) == True{} : Bool}
  for ta: {X.Expr.type(a, s) == Done{t} : E.Res(D.DType)}
  for tb: {X.Expr.type(b, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Bin{X.Mod{}, a, b}, s) == Done{t} : E.Res(D.DType)}

# LAW: a boolean connective over two bool expressions gives bool
law logic_type:
  for op: X.BinOp
  for a: X.Expr
  for b: X.Expr
  for +s: List<&2, S.Field>
  for lg: {is_logic(op) == True{} : Bool}
  for ta: {X.Expr.type(a, s) == Done{D.TBool{}} : E.Res(D.DType)}
  for tb: {X.Expr.type(b, s) == Done{D.TBool{}} : E.Res(D.DType)}
  {X.Expr.type(X.Bin{op, a, b}, s) == Done{D.TBool{}} : E.Res(D.DType)}

# LAW: an allowed cast has the target dtype
law cast_type:
  for e: X.Expr
  for +s: List<&2, S.Field>
  for +t: D.DType
  for +to: D.DType
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  for ok: {X.Cast.ok(t, to) == True{} : Bool}
  {X.Expr.type(X.Cast{e, to}, s) == Done{to} : E.Res(D.DType)}

# LAW: is_null of any well-typed expression is bool
law is_null_type:
  for e: X.Expr
  for +s: List<&2, S.Field>
  for t: D.DType
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Un{X.IsNull{}, e}, s) == Done{D.TBool{}} : E.Res(D.DType)}

# LAW: is_not_null of any well-typed expression is bool
law is_not_null_type:
  for e: X.Expr
  for +s: List<&2, S.Field>
  for t: D.DType
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Un{X.IsNotNull{}, e}, s) == Done{D.TBool{}} : E.Res(D.DType)}

# LAW: count, len and n_unique of any well-typed expression are u32
law counting_type:
  for op: X.AggOp
  for e: X.Expr
  for +s: List<&2, S.Field>
  for t: D.DType
  for cnt: {is_counting(op) == True{} : Bool}
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Agg{op, e}, s) == Done{D.TU32{}} : E.Res(D.DType)}

# LAW: min, max, first and last keep the dtype of their expression
law keeping_agg_type:
  for op: X.AggOp
  for e: X.Expr
  for +s: List<&2, S.Field>
  for t: D.DType
  for kp: {keeps_dtype(op) == True{} : Bool}
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Agg{op, e}, s) == Done{t} : E.Res(D.DType)}

# LAW: the sum of a numeric expression keeps its dtype
law sum_type:
  for e: X.Expr
  for +s: List<&2, S.Field>
  for +t: D.DType
  for num: {X.DType.is_num(t) == True{} : Bool}
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Agg{X.Sum{}, e}, s) == Done{t} : E.Res(D.DType)}

# LAW: the mean of a numeric expression is f32
law mean_type:
  for e: X.Expr
  for +s: List<&2, S.Field>
  for +t: D.DType
  for num: {X.DType.is_num(t) == True{} : Bool}
  for ta: {X.Expr.type(e, s) == Done{t} : E.Res(D.DType)}
  {X.Expr.type(X.Agg{X.Mean{}, e}, s) == Done{D.TF32{}} : E.Res(D.DType)}

# =====================================================================================
# 3. Plan schema inference (src/plan.bend): Plan.schema is Polars' collect_schema
# =====================================================================================

# LAW: a Source answers its declared schema
law source_schema:
  for n: String
  for s: List<&2, S.Field>
  {P.Plan.schema(P.Source{n, s}) == Done{s} : E.Res(List<&2, S.Field>)}

# LAW: head never changes the schema (nor whether it resolves)
law head_keeps_schema:
  for p: P.Plan
  for n: U32
  {P.Plan.schema(P.Head{n, p}) == P.Plan.schema(p) : E.Res(List<&2, S.Field>)}

# LAW: a filter by a bool predicate keeps the schema (the predicate's dtype is
# the shared analysis' (A.Ana.type); reductions are allowed, DESIGN.md 15.4)
law filter_keeps_schema:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for e: X.Expr
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for t: {A.Ana.type(e, s) == Done{D.TBool{}} : E.Res(D.DType)}
  {P.Plan.schema(P.Filter{e, p}) == Done{s} : E.Res(List<&2, S.Field>)}

# LAW: whenever a filter's schema resolves, it is the input's schema (no
# side condition: an ill-typed predicate is an error, never a different schema)
law filter_schema_is_input:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for e: X.Expr
  for out: List<&2, S.Field>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for h: {P.Plan.schema(P.Filter{e, p}) == Done{out} : E.Res(List<&2, S.Field>)}
  {out == s : List<&2, S.Field>}

# LAW: sorting by keys the schema has keeps the schema
law sort_keeps_schema:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for +ks: List<&2, O.SortKey>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for keys: {keys_exist(ks, s) == True{} : Bool}
  {P.Plan.schema(P.Sort{ks, p}) == Done{s} : E.Res(List<&2, S.Field>)}

# LAW: whenever a sort's schema resolves, it is the input's schema
law sort_schema_is_input:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for +ks: List<&2, O.SortKey>
  for out: List<&2, S.Field>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for h: {P.Plan.schema(P.Sort{ks, p}) == Done{out} : E.Res(List<&2, S.Field>)}
  {out == s : List<&2, S.Field>}

# LAW: selecting plain columns is projecting the schema: the same fields in
# the same order, the same ColumnNotFound / DuplicateColumn errors
law select_cols_is_project:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for +names: List<&2, String>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  {P.Plan.schema(P.Select{cols(names), p}) == S.Schema.project(names, s) : E.Res(List<&2, S.Field>)}

# LAW: a select of plain columns that resolves has exactly those names, in order
law select_cols_names:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for +names: List<&2, String>
  for out: List<&2, S.Field>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for h: {P.Plan.schema(P.Select{cols(names), p}) == Done{out} : E.Res(List<&2, S.Field>)}
  {S.Schema.names(out) == names : List<&2, String>}

# LAW: with_columns of one expression whose output name the input already
# has keeps the width (the column is replaced, not added)
law with_column_keeps_width:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for +e: X.Expr
  for out: List<&2, S.Field>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for has: {S.Schema.has(s, X.Expr.name(e)) == True{} : Bool}
  for h: {P.Plan.schema(P.WithColumns{e <> Nil{}, p}) == Done{out} : E.Res(List<&2, S.Field>)}
  {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}

# =====================================================================================
# 4. Optimizer soundness at the schema level (src/plan.bend, Plan.optimize passes)
# =====================================================================================

# LAW: the head pass (Head merging, and sinking below the Select/WithColumns
# the analysis certifies) never changes the schema of any plan, for any
# pending row limit
law head_pass_keeps_schema:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  {P.Plan.schema(P.Opt.head(p, n)) == P.Plan.schema(p) : E.Res(List<&2, S.Field>)}

# LAW: the filter-merge pass keeps the schema of every well-typed plan
law merge_pass_keeps_schema:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  {P.Plan.schema(P.Opt.merge(p)) == Done{s} : E.Res(List<&2, S.Field>)}

# LAW: merging filters and then sinking heads keeps the schema of every
# well-typed plan
law merge_head_keeps_schema:
  for +p: P.Plan
  for +s: List<&2, S.Field>
  for n: Maybe<&2, U32>
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  {P.Plan.schema(P.Opt.head(P.Opt.merge(p), n)) == Done{s} : E.Res(List<&2, S.Field>)}

# LAW: after the merge pass no Filter sits directly on another Filter
law merge_pass_merges:
  for p: P.Plan
  {no_adjacent_filters(P.Opt.merge(p)) == True{} : Bool}

# LAW: a plan with no adjacent filters is a fixed point of the merge pass
law merge_fixed_point:
  for p: P.Plan
  for +h: {no_adjacent_filters(p) == True{} : Bool}
  {P.Opt.merge(p) == p : P.Plan}

# LAW: the merge pass is idempotent
law merge_idempotent:
  for +p: P.Plan
  {P.Opt.merge(P.Opt.merge(p)) == P.Opt.merge(p) : P.Plan}

# LAW: after the head pass no Head sits directly on another Head
law head_pass_merges:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  {no_adjacent_heads(P.Opt.head(p, n)) == True{} : Bool}

# LAW: the release optimizer's head pass (Opt.hmerge: Head merging only, every other node
# a barrier) keeps the schema of every plan, for any pending row limit
law hmerge_keeps_schema:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  {P.Plan.schema(P.Opt.hmerge(p, n)) == P.Plan.schema(p) : E.Res(List<&2, S.Field>)}

# LAW: after it no Head sits directly on another Head
law hmerge_merges:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  {no_adjacent_heads(P.Opt.hmerge(p, n)) == True{} : Bool}

# =====================================================================================
# 5. Columns (src/column.bend)
# =====================================================================================

# LAW: head(c, n) has min(n, len(c)) rows
law head_len:
  for c: C.Column
  for +n: U32
  {Pair.snd(C.Column, U32, C.Column.len(C.Column.head(c, n))) == U32.min(n, Pair.snd(C.Column, U32, C.Column.len(c))) : U32}

# LAW: head keeps the dtype
law head_dtype:
  for c: C.Column
  for n: U32
  {Pair.snd(C.Column, D.DType, C.Column.dtype(C.Column.head(c, n))) == Pair.snd(C.Column, D.DType, C.Column.dtype(c)) : D.DType}

# =====================================================================================
# 5b. Kernels (src/kernels.bend): a kernel's output has the 2^d slots it is asked for
# =====================================================================================

# LAW: Kernel.map (here as mask_not) writes into an array of exactly 2^d slots
law mask_not_slots:
  for n: U32
  for +d: Nat
  for a: Array<U32>
  {slots(U32, K.Kernel.mask_not(n, d, a)) == U32.shln(1, d) : U32}

# LAW: Kernel.zip (here as mask_and) writes into an array of exactly 2^d slots
law mask_and_slots:
  for n: U32
  for +d: Nat
  for a: Array<U32>
  for b: Array<U32>
  {slots(U32, K.Kernel.mask_and(n, d, a, b)) == U32.shln(1, d) : U32}

# LAW: Kernel.iota_from writes into an array of exactly 2^d slots
law iota_slots:
  for n: U32
  for +d: Nat
  for off: U32
  {slots(U32, K.Kernel.iota_from(n, d, off)) == U32.shln(1, d) : U32}

# =====================================================================================
# 6. I32 (src/dtype.bend): two's complement over U32
# =====================================================================================

# LAW: i32 addition is commutative
law i32_add_comm:
  for a: D.I32
  for b: D.I32
  {D.I32.add(a, b) == D.I32.add(b, a) : D.I32}

# LAW: the bit pattern round-trips through I32
law i32_bits_roundtrip:
  for a: D.I32
  {D.I32.from_u32(D.I32.to_u32(a)) == a : D.I32}

# =====================================================================================
# 7. Names and numbers (Base: U32 is Word(32n); String.eq is String.order through Char.cmp)
# =====================================================================================

# LAW: U32.min is commutative
law u32_min_comm:
  for a: U32
  for b: U32
  {U32.min(a, b) == U32.min(b, a) : U32}

# LAW: U32.min is associative (what two Heads in a row compute)
law u32_min_assoc:
  for a: U32
  for b: U32
  for c: U32
  {U32.min(a, U32.min(b, c)) == U32.min(U32.min(a, b), c) : U32}

# LAW: the runtime name equality is reflexive (the name-equality spike of plan
# M_01 section 6 P0: String.eq itself is provable, no local Str.eq is needed)
law str_eq_refl:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

# LAW: the runtime name equality is sound: equal names are the same string
law str_eq_sound:
  for a: String
  for b: String
  for h: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

# LAW: a name is found in a list that starts with it
law names_has_head:
  for ns: List<&2, String>
  for +n: String
  {C.Names.has(n <> ns, n) == True{} : Bool}

# =====================================================================================
# 8. The production runner (src/exec.bend): rewrite rules against Exec.run_pure
# =====================================================================================
#
# Exec.run_pure(p, env) = Exec.run_code(Exec.mark(Exec.compile(p, Nil{})), env) is
# the physical runner collect calls after validation and scan materialisation.
# The theorems below are stated as equalities of its results (E.ResT(C.Frame),
# frames included), so every observer (DF.dump: dtypes, names, height, validity,
# cells, F32 bits; the error) agrees; `release_merge_only_obs` spells that out.

# the code a pending Head limit adds after a sub-plan's code (what Opt.hwrap compiles to)
def hcode(n: Maybe<&2, U32>) -> List<&2, Q.Instr>:
  match n:
    case None{}:
      Nil{}
    case Some{k}:
      Q.IHead{k} <> Nil{}

# Exec.mark of `code` when the code is followed by `suffix` (the last-use flags
# look into the suffix too); Exec.mark(a ++ b) == markw(a, b) ++ Exec.mark(b)
def markw(code: List<&2, Q.Instr>, +suffix: List<&2, Q.Instr>) -> List<&2, Q.Instr>:
  match code:
    case Nil{}:
      Nil{}
    case i <> +t:
      Q.Exec.mark.i(i, List.append(&2, Q.Instr, t, suffix)) <> markw(t, suffix)

# the R1 fragment of optimize_full's head pass (Opt.head): a plan in which every
# Select / WithColumns is a Head barrier (the analysis does not certify it: Opt.sinks
# is False), so Opt.head only ever merges adjacent Heads. Head sinking through
# certified nodes is R3 (plan M_01 section 6 P3), not claimed anywhere: since M5 part
# 2 the release optimizer runs Opt.hmerge, which never sinks (hmerge_run,
# release_run below need no such hypothesis).
def merge_only(p: P.Plan) -> Bool:
  match p:
    case P.ScanCsv{path, o, s}:
      True{}
    case P.Source{n, s}:
      True{}
    case P.Select{+es, +x}:
      Bool.and(Bool.not(P.Opt.sinks(es, P.Plan.schema(x))), merge_only(x))
    case P.WithColumns{+es, +x}:
      Bool.and(Bool.not(P.Opt.sinks(es, P.Plan.schema(x))), merge_only(x))
    case P.Filter{e, x}:
      merge_only(x)
    case P.Sort{ks, x}:
      merge_only(x)
    case P.Drop{ks, x}:
      merge_only(x)
    case P.Rename{ks, x}:
      merge_only(x)
    case P.Slice{ks, kl, x}:
      merge_only(x)
    case P.Tail{ks, x}:
      merge_only(x)
    case P.Unique{ks, x}:
      merge_only(x)
    case P.GroupBy{ks, ags, mo, x}:
      merge_only(x)
    case P.Join{how, lo, ro, l, r}:
      Bool.and(merge_only(l), merge_only(r))
    case P.Concat{ci, l, r}:
      Bool.and(merge_only(l), merge_only(r))
    case P.Head{n, x}:
      merge_only(x)

# LAW: two heads in a row are one head with the min, on a frame (production Frame.head)
law frame_head_head:
  for f: C.Frame
  for +n: U32
  for +m: U32
  {C.Frame.head(C.Frame.head(f, m), n) == C.Frame.head(f, U32.min(n, m)) : C.Frame}

# LAW: the same for the runner's state: IHead m then IHead n is IHead min(n, m),
# whatever the stack holds (an error, an empty stack, a frame)
law head_step:
  for +n: U32
  for +m: U32
  for st: Q.St
  {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, st)) == Q.Exec.step(Q.IHead{U32.min(n, m)}, st) : Q.St}

# LAW R1 (the rule): Head{n, Head{m, x}} and the merged Head{Opt.hmin(m, Some n), x}
# run to the same result in the production runner, for every plan x (certified
# or not, scans included) and every environment, n and m included 0
law head_merge_run:
  for +x: P.Plan
  for +n: U32
  for +m: U32
  for env: P.Env
  {Q.Exec.run_pure(P.Head{n, P.Head{m, x}}, env) == Q.Exec.run_pure(P.Head{P.Opt.hmin(m, Some{n}), x}, env) : E.ResT(C.Frame)}

# the Source names an instruction list reads, in order (what Exec.later / Exec.mark look at)
def srcs(code: List<&2, Q.Instr>) -> List<&2, String>:
  match code:
    case Nil{}:
      Nil{}
    case Q.ISource{n, s, l} <> t:
      n <> srcs(t)
    case i <> t:
      srcs(t)

# Exec.later as a lookup over srcs (same String.eq argument order as Exec.later)
def has_src(ns: List<&2, String>, +nm: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(String.eq(h, nm), has_src(t, nm))

# LAW: Opt.head never changes which Sources the code reads, in which order (so the
# last-use marks of Exec.mark are the same before and after the pass)
law head_pass_keeps_sources:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +acc: List<&2, Q.Instr>
  {srcs(Q.Exec.compile(P.Opt.head(p, n), acc)) == srcs(Q.Exec.compile(P.Opt.hwrap(n, p), acc)) : List<&2, String>}

# LAW R1 (the pass): on the merge-only fragment, Opt.head with a pending limit n
# followed by the code s1 runs exactly like the plan followed by s2, whenever
# "hcode(n) then s1" and s2 read the same Sources (rs) and run alike from every
# state (rf). With n = None and s1 = s2 = Nil this is Optimize.release's body.
law head_pass_run:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +s1: List<&2, Q.Instr>
  for +s2: List<&2, Q.Instr>
  for st: Q.St
  for +mo: {merge_only(p) == True{} : Bool}
  for +rs: {srcs(List.append(&2, Q.Instr, hcode(n), s1)) == srcs(s2) : List<&2, String>}
  for rf: @s: Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, hcode(n), s1)), s) == Q.Exec.loop(Q.Exec.mark(s2), s) : Q.St}
  {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(p, n), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(p, Nil{}), s2)), st) : Q.St}

# LAW: Opt.hmerge never changes which Sources the code reads, in which order
law hmerge_keeps_sources:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +acc: List<&2, Q.Instr>
  {srcs(Q.Exec.compile(P.Opt.hmerge(p, n), acc)) == srcs(Q.Exec.compile(P.Opt.hwrap(n, p), acc)) : List<&2, String>}

# LAW R1 (the release pass): Opt.hmerge with a pending limit n followed by the code s1
# runs exactly like the plan followed by s2, for EVERY plan, whenever "hcode(n) then s1"
# and s2 read the same Sources (rs) and run alike from every state (rf). With n = None
# and s1 = s2 = Nil this is Optimize.release's body on a well-typed plan.
law hmerge_run:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +s1: List<&2, Q.Instr>
  for +s2: List<&2, Q.Instr>
  for st: Q.St
  for +rs: {srcs(List.append(&2, Q.Instr, hcode(n), s1)) == srcs(s2) : List<&2, String>}
  for rf: @s: Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, hcode(n), s1)), s) == Q.Exec.loop(Q.Exec.mark(s2), s) : Q.St}
  {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(p, n), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(p, Nil{}), s2)), st) : Q.St}

# the ScanCsv instructions a code holds, in order: what Exec.mat reads (one file per
# IScan, postfix order) and what the runner's IScans take from env's scan namespace
def scans(code: List<&2, Q.Instr>) -> List<&2, Q.Instr>:
  match code:
    case Nil{}:
      Nil{}
    case Q.IScan{path, o, s} <> t:
      Q.IScan{path, o, s} <> scans(t)
    case i <> t:
      scans(t)

# LAW: Opt.hmerge never changes which scans the code holds, in which order
law hmerge_keeps_scans:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +acc: List<&2, Q.Instr>
  {scans(Q.Exec.compile(P.Opt.hmerge(p, n), acc)) == scans(Q.Exec.compile(P.Opt.hwrap(n, p), acc)) : List<&2, Q.Instr>}

# LAW: the release optimizer keeps the scans (files, options, frozen schemas, order), so
# collect (Optimize.release, then Exec.run) materialises exactly the frames collect_raw
# does, in the same order, before release_run compares the two runs
law release_keeps_scans:
  for +p: P.Plan
  {scans(Q.Exec.compile(P.Optimize.release(p), Nil{})) == scans(Q.Exec.compile(p, Nil{})) : List<&2, Q.Instr>}

# LAW G6: the release optimizer preserves the production runner's result for EVERY
# plan (well typed or not: an ill-typed plan comes back unchanged) and every env
law release_run:
  for +p: P.Plan
  for env: P.Env
  {Q.Exec.run_pure(P.Optimize.release(p), env) == Q.Exec.run_pure(p, env) : E.ResT(C.Frame)}

# LAW: the same, observed through the typed oracle (dtypes, ordered names,
# height, validity, cells as DF.dump prints them, or the error)
law release_run_obs:
  for +p: P.Plan
  for env: P.Env
  {DP.Dump.result(Q.Exec.run_pure(P.Optimize.release(p), env)) == DP.Dump.result(Q.Exec.run_pure(p, env)) : String}

# =====================================================================================
# 9. P0 well-formedness (plan M_01 section 6 P0): the invariants every kernel assumes
# =====================================================================================
#
# Type-valued predicates over the production representations (src/column.bend): a
# proof of WFColumn(c) is evidence that c obeys them. Bend has no module privacy, so
# the constructors CBool{..} .. CStr{..}, Frame{..} and the Array constructors can be
# written by anyone; building a column or frame directly is UNSUPPORTED (DESIGN.md
# section 14, M2). The supported constructors (Column.from_scalars, Csv.read,
# Frame.from_columns, the verbs) are the ones whose outputs these predicates are
# meant to describe; the smart-constructor lemmas below cover the buffer allocators
# and the head verb; every other verb is M5 work (P1).

# a perfect tree of depth d: exactly 2^d slots, the shape Array.get / Array.set index
def WFArray(-T: Type, d: Nat, a: Array<T>) -> Type:
  match d a:
    case 0n ALeaf{x}:
      Unit
    case 1n+p ANode{xs, ys}:
      WFArray(T, p, xs) & WFArray(T, p, ys)
    case _ _:
      Empty

# a word is 0 or 1 when the buffer holds bools (or a validity mask)
def Bits01(bits: Bool, +x: U32) -> Type:
  match bits:
    case True{}:
      {U32.is_le(x, 1) == True{} : Bool}
    case False{}:
      Unit

# a word buffer of depth d; with bits, every word is 0 or 1
def WFWords(+bits: Bool, d: Nat, a: Array<U32>) -> Type:
  match d a:
    case 0n ALeaf{x}:
      Bits01(bits, x)
    case 1n+p ANode{xs, ys}:
      WFWords(bits, p, xs) & WFWords(bits, p, ys)
    case _ _:
      Empty

# a null slot (mask word 0) holds the dtype default
def NullDef(-T: Data, +z: T, +w: U32, x: T) -> Type:
  {Bool.pick(T, U32.is_zero(w), x, z) == z : T}

# mask and word data of depth d: mask words 0/1, data words 0/1 when bits, nulls hold 0
def WFMaskedW(+bits: Bool, d: Nat, m: Array<U32>, a: Array<U32>) -> Type:
  match d m a:
    case 0n ALeaf{+w} ALeaf{+x}:
      {U32.is_le(w, 1) == True{} : Bool} & Bits01(bits, x) & NullDef(U32, 0, w, x)
    case 1n+p ANode{ms, mt} ANode{xs, ys}:
      WFMaskedW(bits, p, ms, xs) & WFMaskedW(bits, p, mt, ys)
    case _ _ _:
      Empty

# mask and data of depth d for a Data cell type with default z
def WFMaskedT(-T: Data, +z: T, d: Nat, m: Array<U32>, a: Array<T>) -> Type:
  match d m a:
    case 0n ALeaf{+w} ALeaf{x}:
      {U32.is_le(w, 1) == True{} : Bool} & NullDef(T, z, w, x)
    case 1n+p ANode{ms, mt} ANode{xs, ys}:
      WFMaskedT(T, z, p, ms, xs) & WFMaskedT(T, z, p, mt, ys)
    case _ _ _:
      Empty

# validity against a word buffer: AllValid needs only the buffer's shape
def WFValidW(+bits: Bool, d: Nat, v: C.Valid, a: Array<U32>) -> Type:
  match v:
    case C.AllValid{}:
      WFWords(bits, d, a)
    case C.Mask{m}:
      WFMaskedW(bits, d, m, a)

def WFValidT(-T: Data, +z: T, d: Nat, v: C.Valid, a: Array<T>) -> Type:
  match v:
    case C.AllValid{}:
      WFArray(T, d, a)
    case C.Mask{m}:
      WFMaskedT(T, z, d, m, a)

# M4 (src/strs.bend): a Dictionary-encoded Str column's codes. Every code is below k (in
# range); with a mask, a null row holds code 0, which is the entry "" (the dictionary's slot
# 0), so a null row decodes to the default as a Raw null slot does.
def WFBelow(+k: U32, d: Nat, a: Array<U32>) -> Type:
  match d a:
    case 0n ALeaf{+x}:
      {U32.is_lt(x, k) == True{} : Bool}
    case 1n+p ANode{xs, ys}:
      WFBelow(k, p, xs) & WFBelow(k, p, ys)
    case _ _:
      Empty

def WFMaskedBelow(+k: U32, d: Nat, m: Array<U32>, a: Array<U32>) -> Type:
  match d m a:
    case 0n ALeaf{+w} ALeaf{+x}:
      {U32.is_le(w, 1) == True{} : Bool} & NullDef(U32, 0, w, x) & {U32.is_lt(x, k) == True{} : Bool}
    case 1n+p ANode{ms, mt} ANode{xs, ys}:
      WFMaskedBelow(k, p, ms, xs) & WFMaskedBelow(k, p, mt, ys)
    case _ _ _:
      Empty

def WFCodesV(+k: U32, d: Nat, v: C.Valid, codes: Array<U32>) -> Type:
  match v:
    case C.AllValid{}:
      WFBelow(k, d, codes)
    case C.Mask{m}:
      WFMaskedBelow(k, d, m, codes)

# the entry buffer: depth dd, slot 0 the empty string
def WFEntries(d: Nat, a: Array<String>) -> Type:
  match d a:
    case 0n ALeaf{x}:
      {x == "" : String}
    case 1n+p ANode{xs, ys}:
      WFEntries(p, xs) & WFArray(String, p, ys)
    case _ _:
      Empty

# k <= 2^dd entries (the index and the pairwise distinctness of the entries are not stated
# here: they are what src/strs.bend's builders maintain, tests/strs_decode.bend checks them
# through decode equivalence)
def WFDictCodes(+d: Nat, v: C.Valid, codes: Array<U32>, dict: ST.Dict) -> Type:
  match dict:
    case ST.Dict{+k, +dd, strs, b, slots, tag}:
      {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool} & WFEntries(dd, strs) & WFCodesV(k, d, v, codes)

# a Str column's storage: Raw as before; a Dictionary: codes in range, entries well formed
def WFStrs(d: Nat, v: C.Valid, s: ST.Strs) -> Type:
  match s:
    case ST.SRaw{a}:
      WFValidT(String, "", d, v, a)
    case ST.SDict{codes, dict}:
      WFDictCodes(d, v, codes, dict)

# a well-formed column: len <= 2^depth, buffers of that depth, mask words 0/1,
# bool words 0/1, null slots holding the default (0, 0.0, ""); the dtype is the
# constructor, so dtype/storage agreement is by construction
def WFColumn(c: C.Column) -> Type:
  match c:
    case C.CBool{len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & WFValidW(True{}, depth, valid, data)
    case C.CU32{len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & WFValidW(False{}, depth, valid, data)
    case C.CI32{len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & WFValidW(False{}, depth, valid, data)
    case C.CF32{len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & WFValidT(F32, 0.0, depth, valid, data)
    case C.CStr{len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & WFStrs(depth, valid, data)

# a well-formed column of exactly h rows
def WFColumnH(+h: U32, c: C.Column) -> Type:
  match c:
    case C.CBool{+len, depth, valid, data}:
      {len == h : U32} & WFColumn(C.CBool{len, depth, valid, data})
    case C.CU32{+len, depth, valid, data}:
      {len == h : U32} & WFColumn(C.CU32{len, depth, valid, data})
    case C.CI32{+len, depth, valid, data}:
      {len == h : U32} & WFColumn(C.CI32{len, depth, valid, data})
    case C.CF32{+len, depth, valid, data}:
      {len == h : U32} & WFColumn(C.CF32{len, depth, valid, data})
    case C.CStr{+len, depth, valid, data}:
      {len == h : U32} & WFColumn(C.CStr{len, depth, valid, data})

# columns of height h with names not among `seen` and pairwise distinct
def WFCols(+h: U32, cols: List<&1, C.Named>, +seen: List<&2, String>) -> Type:
  match cols:
    case Nil{}:
      Unit
    case C.Named{+n, c} <> rest:
      {C.Names.has(seen, n) == False{} : Bool} & WFColumnH(h, c) & WFCols(h, rest, n <> seen)

# a well-formed frame: every column has the frame's height and a unique name; a
# frame with no columns has any height (the zero-column convention)
def WFFrame(f: C.Frame) -> Type:
  match f:
    case C.Frame{h, cols}:
      WFCols(h, cols, Nil{})

# LAW: a head of a bounded length stays bounded (what Column.head needs)
law u32_min_le:
  for +n: U32
  for +a: U32
  for +b: U32
  for h: {U32.is_le(a, b) == True{} : Bool}
  {U32.is_le(U32.min(n, a), b) == True{} : Bool}

# LAW (smart constructor): Array.new / Kernel.const allocate a well-formed buffer of depth d
law wf_new:
  for -T: Data
  for d: Nat
  for +z: T
  WFArray(T, d, Array.new(T, d, z))

# LAW (smart constructor): a word buffer filled with a 0/1 word is well formed for any
# bits flag (Kernel.const(0) data, Valid.materialize's all-ones mask, Kernel.map's zero fill)
law wf_new_words:
  for +bits: Bool
  for d: Nat
  for +w: U32
  for +hw: {U32.is_le(w, 1) == True{} : Bool}
  WFWords(bits, d, Array.new(U32, d, w))

# LAW (smart constructor): the empty frame is well formed
law wf_frame_empty:
  WFFrame(C.Frame.empty())

# LAW (preservation): Column.head keeps a column well formed
law wf_column_head:
  for c: C.Column
  for +n: U32
  for wf: WFColumn(c)
  WFColumn(C.Column.head(c, n))

# LAW (preservation): Frame.head keeps a frame well formed
law wf_frame_head:
  for f: C.Frame
  for +n: U32
  for wf: WFFrame(f)
  WFFrame(C.Frame.head(f, n))

# =====================================================================================
# 10. Buffer contents (plan M_01 section 6 P1, the M2 part): what Array.get reads,
#     what Array.set writes, and what one step of gather / compact does with them
# =====================================================================================
#
# `rd` is the pure read model: the cell Array.get.go answers, making exactly the
# production getter's halving decisions (n the slot count, i the masked index, z the
# "left half" test); array_get_pure ties it to the real Array.get (which also hands the
# array back unchanged). array_set_get is read-after-write at the same index through
# the real Array.set. gather_step / compact_step are one iteration of the production
# kernels: the cell read at perm[j] (resp. a[i]) is the cell written at out[j] (resp.
# out[k]). These are ONE-step lemmas: that later writes leave earlier slots alone (two
# indices below 2^d take different paths; the bit-vector fact over Word.and / shr / sub /
# is_lt) is not used here. It is proven in section 11 (paths_distinct, array_set_other),
# which turns these steps into the full "out[i] == in[index[i]]" / subsequence theorems
# (gather_contents, compact_contents).

def rd(-T: Data, a: Array<T>, +n: U32, +i: U32, z: Bool) -> T:
  match a z:
    case ALeaf{x} _:
      x
    case ANode{xs, ys} True{}:
      rd(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))
    case ANode{xs, ys} False{}:
      rd(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))

# the cell at logical index i (masked to the slot count, as Array.get.at does)
def rd_size(-T: Data, +i: U32, an: Array<T> & U32) -> T:
  (a, +n) = an
  +j = U32.and(i, U32.sub(n, 1))
  rd(T, a, n, j, U32.is_lt(j, U32.shr(n)))

def rd_at(-T: Data, a: Array<T>, +i: U32) -> T:
  rd_size(T, i, Array.size(T, a))

# LAW: Array.get is pure: it hands the array back and answers the modelled cell
law array_get_pure:
  for -T: Data
  for a: Array<T>
  for +i: U32
  {Array.get(T, a, i) == (a, rd_at(T, a, i)) : Array<T> & T}

# LAW: read-after-write at the same index through the production Array.set
law array_set_get:
  for -T: Data
  for a: Array<T>
  for +i: U32
  for +v: T
  {rd_at(T, Array.set(T, a, i, v), i) == v : T}

# LAW: one step of Kernel.gather.go (the production gather, at the U32 instance: the
# word buffers of Bool/U32/I32 columns and every validity mask) writes the cell read at
# perm's slot into out's slot j: out'[j] == src[i] where i is the pending read of perm[j].
# (Stated at U32 because BendTT's --verdict kernel does not yet accept a template applied
# to a quantified cell type; the proof is the same text for F32 and String.)
law gather_step:
  for src: Array<U32>
  for out: Array<U32>
  for perm: Array<U32>
  for +j: U32
  for +i: U32
  {rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather.go(~U32, 1n, j, (src, out), (perm, i))), j) == rd_at(U32, src, i) : U32}

# LAW: one step of Kernel.compact.go (the production compaction) advances the write
# index by the mask bit ...
law compact_step:
  for a: Array<U32>
  for out: Array<U32>
  for mask: Array<U32>
  for +i: U32
  for +k: U32
  for +bit: U32
  {Pair.snd(Array<U32>, U32, K.Kernel.compact.go(~U32, 1n, i, k, (a, out), (mask, bit))) == U32.add(k, bit) : U32}

# LAW: ... and writes a[i] into out's slot k
law compact_step_cell:
  for a: Array<U32>
  for out: Array<U32>
  for mask: Array<U32>
  for +i: U32
  for +k: U32
  for +bit: U32
  {rd_at(U32, Pair.fst(Array<U32>, U32, K.Kernel.compact.go(~U32, 1n, i, k, (a, out), (mask, bit))), k) == rd_at(U32, a, i) : U32}

# =====================================================================================
# 11. Buffer contents, the full theorems (plan M_01 section 6 P1, M5): writes at distinct
#     indices below 2^d take distinct paths, so the production kernels' outputs are what
#     the per-step lemmas of section 10 say, slot by slot
# =====================================================================================
#
# The read model is `rd` (section 10). `rdN(d, a, k)` is the cell at logical index k of a
# well-formed array of depth d: rd_at with Array.size's answer 2^d in place (rd_at_wf ties
# them). `same_d` is the sequence of halving decisions two masked indices make through a
# perfect tree of depth d (True when they reach the same leaf); `same_at` applies the
# masking of Array.get.at / Array.swap.at first. `paths_distinct` is the bit-vector lemma:
# indices below 2^d that reach the same leaf are equal. `addn(j, f)` is the loop counter
# after f increments; `Room(d, j, f)` says the next f write indices from j are below 2^d.

# the cell at logical index k of a well-formed array of depth d (Array.size answers 2^d)
def rdN(-T: Data, +d: Nat, a: Array<T>, +k: U32) -> T:
  rd_size(T, k, (a, U32.shln(1, d)))

# do two masked indices i (left-half test zi) and j (zj) reach the same leaf of a perfect
# tree of depth d whose slot count is n? (rd's descent, decision by decision)
def same_d(d: Nat, +n: U32, +i: U32, zi: Bool, +j: U32, zj: Bool) -> Bool:
  match d zi zj:
    case 0n _ _:
      True{}
    case 1n+p True{} True{}:
      same_d(p, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))), j, U32.is_lt(j, U32.shr(U32.shr(n))))
    case 1n+p False{} False{}:
      same_d(p, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), U32.sub(j, U32.shr(n)), U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))
    case 1n+p _ _:
      False{}

# the same for two logical indices, masked to 2^d slots as Array.get / Array.set do
def same_at(+d: Nat, +i: U32, +j: U32) -> Bool:
  +nn = U32.shln(1, d)
  +mi = U32.and(i, U32.sub(nn, 1))
  +mj = U32.and(j, U32.sub(nn, 1))
  same_d(d, nn, mi, U32.is_lt(mi, U32.shr(nn)), mj, U32.is_lt(mj, U32.shr(nn)))

# the loop counter after f increments (the kernels count with U32.inc)
def addn(j: U32, f: Nat) -> U32:
  match f:
    case 0n:
      j
    case 1n+p:
      U32.inc(addn(j, p))

# the next f write indices from j are below 2^d (what a kernel needs of its output array)
def Room(+d: Nat, j: U32, f: Nat) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool} & Room(d, U32.inc(j), p)

# LAW: rd_at of a well-formed array of depth d reads with the slot count 2^d
law rd_at_wf:
  for -T: Data
  for +d: Nat
  for a: Array<T>
  for +k: U32
  for wf: WFArray(T, d, a)
  {rd_at(T, a, k) == rdN(T, d, a, k) : T}

# LAW (the distinct-paths lemma): two indices below 2^d that reach the same leaf are equal
law paths_distinct:
  for +d: Nat
  for +i: U32
  for +j: U32
  for +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}
  for +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}
  for h: {same_at(d, i, j) == True{} : Bool}
  {i == j : U32}

# LAW: a write at i below 2^d leaves every other slot j below 2^d alone (the production
# Array.set on a well-formed array; array_set_get of section 10 is the slot i itself)
law array_set_other:
  for -T: Data
  for +d: Nat
  for a: Array<T>
  for +i: U32
  for +j: U32
  for +v: T
  for wf: WFArray(T, d, a)
  for hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}
  for hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}
  for ne: {i != j : U32}
  {rd_at(T, Array.set(T, a, i, v), j) == rd_at(T, a, j) : T}

# LAW: Array.set keeps an array well formed
law wf_array_set:
  for -T: Data
  for +d: Nat
  for a: Array<T>
  for +i: U32
  for +v: T
  for wf: WFArray(T, d, a)
  WFArray(T, d, Array.set(T, a, i, v))

# LAW: the production gather (U32 instance) writes out[k] == src[perm[k]] for every k < n,
# whenever the output's 2^d slots hold the n rows (indexes read through perm wrap as
# Array.get wraps them; the index array comes back unchanged)
law gather_contents:
  for +d: Nat
  for +n: U32
  for src: Array<U32>
  for perm: Array<U32>
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, d, src, perm, z)), k) == rd_at(U32, src, rd_at(U32, perm, k)) : U32}

law gather_keeps_perm:
  for +d: Nat
  for +n: U32
  for src: Array<U32>
  for perm: Array<U32>
  for +z: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  {Pair.snd(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, d, src, perm, z)) == perm : Array<U32>}

# LAW: Kernel.map (as mask_not) writes f(a[k]) at every k < n when n <= 2^d
law mask_not_cell:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, K.Kernel.mask_not(n, d, a), k) == U32.xor(rd_at(U32, a, k), 1) : U32}

# LAW: Kernel.zip (as mask_and / mask_or) writes f(a[k], b[k]) at every k < n when n <= 2^d:
# the validity combinators' truth tables, slot by slot
law mask_and_cell:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for b: Array<U32>
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, K.Kernel.mask_and(n, d, a, b), k) == U32.and(rd_at(U32, a, k), rd_at(U32, b, k)) : U32}

law mask_or_cell:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for b: Array<U32>
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, K.Kernel.mask_or(n, d, a, b), k) == U32.or(rd_at(U32, a, k), rd_at(U32, b, k)) : U32}

# LAW: Kernel.range (Column.slice's range copy, W1f) at the U32 instance: out[k] == a[off + k]
# at every k < n when n <= 2^d (the read index is any word: rd_at answers what Array.get reads)
law range_cell:
  for +d: Nat
  for +n: U32
  for +off: U32
  for a: Array<U32>
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, K.Kernel.range(~U32, n, d, off, a, z), k) == rd_at(U32, a, U32.add(off, k)) : U32}

# LAW: Kernel.iota_from writes off + k at every k < n when n <= 2^d (Kernel.iota's index arrays)
law iota_cell:
  for +d: Nat
  for +n: U32
  for +off: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, K.Kernel.iota_from(n, d, off), k) == U32.add(off, k) : U32}

# the modulo-2^32 running sum of the first f cells from index i, started at acc: res is it
# (the Type-level spec of Kernel.fold with U32.add; each cell is named so the mask is read
# once per step)
def FSum(f: Nat, +i: U32, +acc: U32, -a: Array<U32>, +res: U32) -> Type:
  match f:
    case 0n:
      {res == acc : U32}
    case 1n+p:
      &x: U32 -> {x == rd_at(U32, a, i) : U32} & FSum(p, U32.inc(i), U32.add(acc, x), a, res)

# LAW: the production U32 fold with U32.add is the modulo-2^32 sum of the first n cells
# (what sum() over a U32 column computes, after its nulls are compacted away)
law u32_fold_sum:
  for +n: U32
  for a: Array<U32>
  for +z: U32
  FSum(U32.to_nat(n), 0, z, a, Pair.snd(Array<U32>, U32, K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, z)))

# LAW: the fold hands the array back unchanged
law u32_fold_keeps:
  for +n: U32
  for a: Array<U32>
  for +z: U32
  {Pair.fst(Array<U32>, U32, K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, z)) == a : Array<U32>}

# LAW: Kernel.popcount (the kept-row count of filter, the valid count of null_count / sum / mean)
# is the modulo-2^32 sum of the first n mask words
law popcount_sum:
  for +n: U32
  for mask: Array<U32>
  FSum(U32.to_nat(n), 0, 0, mask, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, mask)))

# the compaction's write cursor over the next f rows from (i, k): each mask word b is 0/1 and
# the cursor stays below 2^d at every step (Column.compact allocates depth_for(kept + 1) slots:
# the cursor never exceeds the number of kept rows; that arithmetic is not proven here)
def CRoom(f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      &b: U32 -> {b == rd_at(U32, mask, i) : U32} & {U32.is_le(b, 1) == True{} : Bool} & {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool} & CRoom(p, U32.inc(i), U32.add(k, b), d, mask)

# the compaction's contract over the next f rows from (i, k): every row whose mask word is set
# sits in o at the cursor value of its step, i.e. o[0 ..) is the order-preserving subsequence of
# the rows with a set mask word (the kept rows), slot by slot
def CSpec(-T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, -a: Array<T>, -mask: Array<U32>, -o: Array<T>) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      &b: U32 -> {b == rd_at(U32, mask, i) : U32} & ({U32.is_ne(b, 0) == True{} : Bool} -> {rdN(T, d, o, k) == rd_at(T, a, i) : T}) & CSpec(T, p, U32.inc(i), U32.add(k, b), d, a, mask, o)

# LAW: the production compaction (Kernel.compact_keep, the loop behind Column.compact and so
# behind filter and drop-nulls; U32 instance) writes the kept rows in order at the cursor
# positions, whenever the mask is 0/1 and the cursor stays below 2^d (CRoom)
law compact_contents:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for mask: Array<U32>
  for +z: U32
  for room: CRoom(U32.to_nat(n), 0, 0, d, mask)
  CSpec(U32, U32.to_nat(n), 0, 0, d, a, mask, Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a, mask, z)))

# LAW: the compaction hands the mask back unchanged (so one mask filters every buffer of a column
# and every column of a frame: data and validity stay aligned)
law compact_keeps_mask:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for mask: Array<U32>
  for +z: U32
  {Pair.snd(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a, mask, z)) == mask : Array<U32>}


# =====================================================================================
# 12. Column cells (plan M_01 section 6 P1, M5): Column.cell is pure and reads the model
#     ccell; head keeps every cell; slice of a U32 column is the exact subrange
# =====================================================================================

# the validity bit at row i as Column.cell reads it (AllValid: every row)
def vbit(v: C.Valid, +i: U32) -> Bool:
  match v:
    case C.AllValid{}:
      True{}
    case C.Mask{m}:
      U32.is_ne(rd_at(U32, m, i), 0)

# the entry of code c of a dictionary
def dentry(d: ST.Dict, +c: U32) -> String:
  match d:
    case ST.Dict{k, dd, strs, b, slots, tag}:
      rd_at(String, strs, c)

# the string of row i of a Str column's storage (M4): Raw, the slot; Dictionary, the entry of the
# row's code
def scell(s: ST.Strs, +i: U32) -> String:
  match s:
    case ST.SRaw{a}:
      rd_at(String, a, i)
    case ST.SDict{codes, d}:
      dentry(d, rd_at(U32, codes, i))

# the scalar at row i (SNull when the row is invalid), as a pure function of the buffers: the
# model of Column.cell (Column.cell.word's dtype dispatch written out per constructor)
def ccell(c: C.Column, +i: U32) -> D.Scalar:
  match c:
    case C.CBool{len, depth, valid, data}:
      Bool.pick(D.Scalar, vbit(valid, i), D.SBool{U32.is_ne(rd_at(U32, data, i), 0)}, D.SNull{})
    case C.CU32{len, depth, valid, data}:
      Bool.pick(D.Scalar, vbit(valid, i), D.SU32{rd_at(U32, data, i)}, D.SNull{})
    case C.CI32{len, depth, valid, data}:
      Bool.pick(D.Scalar, vbit(valid, i), D.SI32{D.I32{rd_at(U32, data, i)}}, D.SNull{})
    case C.CF32{len, depth, valid, data}:
      Bool.pick(D.Scalar, vbit(valid, i), D.SF32{rd_at(F32, data, i)}, D.SNull{})
    case C.CStr{len, depth, valid, data}:
      Bool.pick(D.Scalar, vbit(valid, i), D.SStr{scell(data, i)}, D.SNull{})

# the row count Column.slice(c, off, n) answers: min(n, len - off), 0 past the end
def slice_len(+off: U32, +n: U32, +len: U32) -> U32:
  U32.min(n, Bool.pick(U32, U32.is_lt(off, len), U32.sub(len, off), 0))

# LAW: Column.cell is pure: it hands the column back and answers the modelled cell
law cell_pure:
  for c: C.Column
  for +i: U32
  {C.Column.cell(c, i) == (c, ccell(c, i)) : C.Column & D.Scalar}

# LAW: head keeps every cell (with head_len / head_dtype: the exact prefix)
law head_cell:
  for c: C.Column
  for +n: U32
  for +k: U32
  {ccell(C.Column.head(c, n), k) == ccell(c, k) : D.Scalar}

# LAW: Kernel.depth_for(n) gives at least n slots (for n <= 2^31; the row cap keeps n <= 2^23)
law depth_for_fits:
  for +n: U32
  for h: {U32.is_le(n, U32.shln(1, 31n)) == True{} : Bool}
  {U32.is_le(n, U32.shln(1, K.Kernel.depth_for(n))) == True{} : Bool}

# LAW: slice of a U32 column is the exact subrange: row k of slice(c, off, n) is row off + k of c,
# for every k below the slice's length (data through range_cell, validity through the same
# range copy of the mask; W1f: one range copy per buffer, no index array). The U32 instance
# stands for the word columns (Bool, I32: same buffers); F32 / String need the kernel theorem at
# those instances (the template proof is generic: PROOF_contents' range_tcell)
law slice_cell_u32:
  for +len: U32
  for +depth: Nat
  for valid: C.Valid
  for data: Array<U32>
  for +off: U32
  for +n: U32
  for +k: U32
  for h31: {U32.is_le(n, U32.shln(1, 31n)) == True{} : Bool}
  for hk: {U32.is_lt(k, slice_len(off, n, len)) == True{} : Bool}
  {ccell(C.Column.slice(C.CU32{len, depth, valid, data}, off, n), k) == ccell(C.CU32{len, depth, valid, data}, U32.add(off, k)) : D.Scalar}

# =====================================================================================
# 13. Evaluator typing (plan M_01 section 6 P2, M5 part 2): the production evaluator
#     (src/eval.bend) answers columns of the dtype the shared analysis (src/analysis.bend)
#     predicts, of the frame's height, and fails only where the analysis says it may
# =====================================================================================
#
# Models (pure functions of a column's fields, the column erased): cdtype / clen are what
# Column.dtype / Column.len answer (len_w, dtype_w); a typed slot of the stack machine
# holds a column of the analysis' dtype whose length is the frame's height for a KFull
# slot and 1 for a literal / reduction slot (klen). ColTy / ResTy / StkTy / RunTy state
# that over the production values; every law below is over src/eval.bend's functions.

def cdtype(c: C.Column) -> D.DType:
  match c:
    case C.CBool{len, depth, valid, data}:
      D.TBool{}
    case C.CU32{len, depth, valid, data}:
      D.TU32{}
    case C.CI32{len, depth, valid, data}:
      D.TI32{}
    case C.CF32{len, depth, valid, data}:
      D.TF32{}
    case C.CStr{len, depth, valid, data}:
      D.TStr{}

def clen(c: C.Column) -> U32:
  match c:
    case C.CBool{len, depth, valid, data}:
      len
    case C.CU32{len, depth, valid, data}:
      len
    case C.CI32{len, depth, valid, data}:
      len
    case C.CF32{len, depth, valid, data}:
      len
    case C.CStr{len, depth, valid, data}:
      len

# the dtype Column.mk_w(t, ..) builds (U32 for every non-word dtype; Eval only asks for word dtypes)
def mkd(t: D.DType) -> D.DType:
  match t:
    case D.TBool{}:
      D.TBool{}
    case D.TI32{}:
      D.TI32{}
    case _:
      D.TU32{}

# the dtype of a scalar, t for the null scalar (what Eval.const_col / Eval.unit build)
def lit_dtype(s: D.Scalar, t: D.DType) -> D.DType:
  match s:
    case D.SNull{}:
      t
    case D.SBool{b}:
      D.TBool{}
    case D.SU32{v}:
      D.TU32{}
    case D.SI32{v}:
      D.TI32{}
    case D.SF32{v}:
      D.TF32{}
    case D.SStr{v}:
      D.TStr{}

# the length of a slot's column: the height for a full column, one row otherwise
def klen(k: V.SKind, +h: U32) -> U32:
  match k:
    case V.KFull{}:
      h
    case _:
      1

# the stack machine's kind of an analysis kind (KRow <-> KFull, KScalar <-> KLit, KRed <-> KAgg)
def skind(k: A.AKind) -> V.SKind:
  match k:
    case A.KRow{}:
      V.KFull{}
    case A.KScalar{}:
      V.KLit{}
    case A.KRed{}:
      V.KAgg{}

# Eval.expr's height for a kind: a reduction stays one row, a literal broadcasts
def elen(k: A.AKind, +h: U32) -> U32:
  match k:
    case A.KRed{}:
      1
    case _:
      h

# a column has dtype t and n rows (the column erased: the claim is about any column term)
def ColTy(+t: D.DType, +n: U32, -c: C.Column) -> Type:
  {cdtype(c) == t : D.DType} & {clen(c) == n : U32}

# a column result: Done holds a typed column; Fail is allowed only when tot is False
def ResTy(+tot: Bool, +t: D.DType, +n: U32, r: E.ResT(C.Column)) -> Type:
  match r:
    case Fail{e}:
      {tot == False{} : Bool}
    case Done{c}:
      ColTy(t, n, c)

# the production result r0 as a witness r (the live value) that ResTy describes
def ResW(+tot: Bool, +t: D.DType, +n: U32, -r0: E.ResT(C.Column)) -> Type:
  &r: E.ResT(C.Column) -> {r0 == r : E.ResT(C.Column)} & ResTy(tot, t, n, r)

# the shape of a stack slot: its dtype and kind
type Sh is Data:
  Sh{t: D.DType, k: V.SKind}

# every slot of the stack has its shape: the kind, and a column of the dtype with klen rows
def StkTy(+h: U32, sh: List<&2, Sh>, stk: List<&1, V.Slot>) -> Type:
  match sh stk:
    case Nil{} Nil{}:
      Unit
    case Sh{t, +k} <> sh2 V.Slot{+k2, c} <> rest:
      {k2 == k : V.SKind} & ColTy(t, klen(k, h), c) & StkTy(h, sh2, rest)
    case _ _:
      Empty

# the machine's state after a run: the frame is f again and a slot of shape Sh{t, k} sits on
# a stack of shape sh; or the run failed, which the analysis allowed (tot False)
def ResSt(+h: U32, +t: D.DType, +k: V.SKind, +tot: Bool, -f: C.Frame, sh: List<&2, Sh>, f2: C.Frame, r: E.ResT(List<&1, V.Slot>)) -> Type:
  match r:
    case Fail{e}:
      {tot == False{} : Bool}
    case Done{stk2}:
      {f2 == f : C.Frame} & StkTy(h, Sh{t, k} <> sh, stk2)

def RunTy(+h: U32, +t: D.DType, +k: V.SKind, +tot: Bool, -f: C.Frame, sh: List<&2, Sh>, st: V.EvSt) -> Type:
  match st:
    case V.EvSt{f2, r}:
      ResSt(h, t, k, tot, f, sh, f2, r)

# running `code` from frame f and stack stk, then acc, is running acc from a state st that
# RunTy describes (the witness st is the live state after code)
def RunW(+h: U32, +t: D.DType, +k: V.SKind, +tot: Bool, -f: C.Frame, sh: List<&2, Sh>, -stk: List<&1, V.Slot>, -acc: List<&2, V.Instr>, -code: List<&2, V.Instr>) -> Type:
  &st: V.EvSt -> {V.Eval.run(code, h, V.EvSt{f, Done{stk}}) == V.Eval.run(acc, h, st) : V.EvSt} & RunTy(h, t, k, tot, f, sh, st)

# the frame's height and schema as pure functions (what Frame.height / Frame.schema answer)
def fheight(f: C.Frame) -> U32:
  match f:
    case C.Frame{h, cols}:
      h

def cschema(cols: List<&1, C.Named>) -> List<&2, S.Field>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> rest:
      S.Field{n, cdtype(c)} <> cschema(rest)

def fschema(f: C.Frame) -> List<&2, S.Field>:
  match f:
    case C.Frame{h, cols}:
      cschema(cols)

# every column has h rows and a name not among the earlier ones (the Bool form of WFCols'
# shape facts, so it can be a reusable hypothesis)
def cols_ok(+h: U32, cols: List<&1, C.Named>, +seen: List<&2, String>) -> Bool:
  match cols:
    case Nil{}:
      True{}
    case C.Named{+n, c} <> rest:
      Bool.and(Bool.not(C.Names.has(seen, n)), Bool.and(U32.is_eq(clen(c), h), cols_ok(h, rest, n <> seen)))

def frame_ok(+h: U32, f: C.Frame) -> Bool:
  match f:
    case C.Frame{h2, cols}:
      Bool.and(U32.is_eq(h2, h), cols_ok(h, cols, Nil{}))

# Eval.full / Eval.expr's answer: on success the frame back unchanged and a column of dtype t
# with n rows; on failure only that the analysis allowed one (tot == False): nothing is stated
# about the frame or the error then
def EvalTyR(+t: D.DType, +tot: Bool, +n: U32, -f: C.Frame, f2: C.Frame, rc: E.ResT(C.Column)) -> Type:
  match rc:
    case Fail{e}:
      {tot == False{} : Bool}
    case Done{c}:
      {f2 == f : C.Frame} & ColTy(t, n, c)

def EvalTy(+t: D.DType, +tot: Bool, +n: U32, -f: C.Frame, r: C.Frame & E.ResT(C.Column)) -> Type:
  (f2, rc) = r
  EvalTyR(t, tot, n, f, f2, rc)

# LAW: Column.len is pure: the column back (as a live witness equal to it) and clen
def LenW(-c: C.Column) -> Type:
  &c2: C.Column -> {C.Column.len(c) == (c2, clen(c)) : C.Column & U32} & {c2 == c : C.Column}

law len_w:
  for c: C.Column
  LenW(c)

# LAW: Column.dtype is pure the same way
def DtypeW(-c: C.Column) -> Type:
  &c2: C.Column -> {C.Column.dtype(c) == (c2, cdtype(c)) : C.Column & D.DType} & {c2 == c : C.Column}

law dtype_w:
  for c: C.Column
  DtypeW(c)

# LAW: Column.cell answers a scalar of the column's dtype, or the null scalar
def CellW(-c: C.Column, +i: U32) -> Type:
  &s: D.Scalar -> {C.Column.cell(c, i) == (c, s) : C.Column & D.Scalar} & {lit_dtype(s, cdtype(c)) == cdtype(c) : D.DType}

law cell_w:
  for c: C.Column
  for +i: U32
  CellW(c, i)

# LAW: Frame.height / Frame.schema are pure (the frame back, equal to the input)
def HeightW(-f: C.Frame) -> Type:
  &f2: C.Frame -> {C.Frame.height(f) == (f2, fheight(f)) : C.Frame & U32} & {f2 == f : C.Frame}

def SchemaW(-f: C.Frame) -> Type:
  &f2: C.Frame -> {S.Frame.schema(f) == (f2, fschema(f)) : C.Frame & List<&2, S.Field>} & {f2 == f : C.Frame}

law frame_height_w:
  for f: C.Frame
  HeightW(f)

law frame_schema_w:
  for f: C.Frame
  SchemaW(f)

# LAW: a well-formed frame (P0) satisfies the shape facts the typing theorems assume
law wf_frame_ok:
  for f: C.Frame
  for wf: WFFrame(f)
  {frame_ok(fheight(f), f) == True{} : Bool}

# the frame back (equal to f) and a copy of the column named n: dtype t, h rows
def GetW(-f: C.Frame, +n: String, +h: U32, +t: D.DType) -> Type:
  &f2: C.Frame -> &c: C.Column -> {C.Frame.get_cloned(f, n) == (f2, Done{c}) : C.Frame & E.ResT(C.Column)} & {f2 == f : C.Frame} & ColTy(t, h, c)

# LAW: Frame.get_cloned on a frame of h rows with unique names answers the frame unchanged and
# a copy of the column the schema names, of the schema's dtype and h rows
law get_cloned_typed:
  for f: C.Frame
  for +n: String
  for +h: U32
  for +t: D.DType
  for +hf: {frame_ok(h, f) == True{} : Bool}
  for hfind: {S.Schema.find(fschema(f), n) == Some{t} : Maybe<&2, D.DType>}
  GetW(f, n, h, t)

# LAW: broadcasting keeps the dtype and gives n rows
def ColW(+t: D.DType, +n: U32, -c0: C.Column) -> Type:
  &c2: C.Column -> {c0 == c2 : C.Column} & ColTy(t, n, c2)

law bcast_typed:
  for c: C.Column
  for +n: U32
  ColW(cdtype(c), n, V.Eval.bcast(c, n))

# LAW: a one-row constant column has the scalar's dtype (t for a null) and one row
law unit_typed:
  for +v: D.Scalar
  for +t: D.DType
  ColTy(lit_dtype(v, t), 1, V.Eval.unit(v, t))

# ---- the operations (src/eval.bend): each answers a column of the dtype its typing rule
#      (src/expr.bend) gives, as long as the operand, and fails only where the analysis allows --

# LAW: Eval.un on an operand the un rule accepts: that dtype, the same length, never a failure
law eval_un_typed:
  for op: X.UnOp
  for c: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.un.ok(op, cdtype(c)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(c), V.Eval.un(op, c))

# LAW: Eval.bin on operands the bin rule accepts: that dtype, the left operand's length
law eval_bin_typed:
  for +op: X.BinOp
  for a: C.Column
  for b: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.bin.ok(op, cdtype(a), cdtype(b)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(a), V.Eval.bin(op, a, b))

# LAW: a well-typed cast answers `to` with the operand's length; it may fail only when the
# pair is fallible (X.Cast.total False), which is exactly the analysis' totality flag
law eval_cast_typed:
  for +to: D.DType
  for c: C.Column
  for hok: {X.Cast.ok(cdtype(c), to) == True{} : Bool}
  ResW(X.Cast.total(cdtype(c), to), to, clen(c), V.Eval.cast(to, c))

# LAW: try_cast never fails on a castable pair
law eval_try_cast_typed:
  for +to: D.DType
  for c: C.Column
  for hok: {X.Cast.ok(cdtype(c), to) == True{} : Bool}
  ResW(True{}, to, clen(c), V.Eval.try_cast(to, c))

# LAW: fill_null keeps the (shared) dtype and the first operand's length
law eval_fill_typed:
  for a: C.Column
  for b: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.fill(Done{cdtype(a)}, Done{cdtype(b)}) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(a), V.Eval.fill(a, b))

# LAW: when / then / otherwise answers the branches' dtype with the then-branch's length
law eval_when_typed:
  for c: C.Column
  for a: C.Column
  for b: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.when.ok(cdtype(c), cdtype(a), cdtype(b)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(a), V.Eval.when(c, a, b))

# LAW: is_in answers bool, same length
law eval_isin_typed:
  for +vs: List<&2, D.Scalar>
  for c: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.isin.ok(vs, cdtype(c)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(c), V.Eval.isin(vs, c))

# LAW: clip keeps the numeric dtype, same length
law eval_clip_typed:
  for +lo: D.Scalar
  for +hi: D.Scalar
  for c: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.clip.ok(lo, hi, cdtype(c)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(c), V.Eval.clip(lo, hi, c))

# LAW: the string predicates answer bool, same length
law eval_strpred_typed:
  for op: X.StrPredOp
  for +pat: String
  for c: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.strpred.ok(op, cdtype(c)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, clen(c), V.Eval.strpred(op, pat, c))

# LAW: an aggregation answers one row of the agg rule's dtype, never a failure
law eval_agg_typed:
  for op: X.AggOp
  for c: C.Column
  for +t: D.DType
  for hok: {X.Expr.type.agg.ok(op, cdtype(c)) == Done{t} : E.Res(D.DType)}
  ResW(True{}, t, 1, V.Eval.agg(op, c))

# ---- the stack machine (Eval.compile + Eval.run) and the entry points Eval.full / Eval.expr ------
#
# The main theorem: the postfix code of an expression the analysis accepts, run from a
# frame of h rows (frame_ok: every column h rows, names unique) whose schema s the
# analysis saw, on a stack whose slots have shape sh, leaves the frame unchanged and
# pushes one slot of the analysis' dtype and kind (klen rows), or fails where the
# analysis allowed (tot False). By induction over the expression with the stack
# invariant StkTy; every operation's typing law (above) supplies the step.

# LAW: the stack machine's typing invariant (P2)
law run_typed:
  for +e: X.Expr
  for +s: List<&2, S.Field>
  for +h: U32
  for +acc: List<&2, V.Instr>
  for f: C.Frame
  for stk: List<&1, V.Slot>
  for +sh: List<&2, Sh>
  for +hs: {fschema(f) == s : List<&2, S.Field>}
  for +hf: {frame_ok(h, f) == True{} : Bool}
  for ev: StkTy(h, sh, stk)
  for +t: D.DType
  for +rs: List<&2, String>
  for +k: A.AKind
  for +tot: Bool
  for +loc: Bool
  for ha: {A.Expr.analyse(e, s) == Done{A.Ana{t, rs, k, tot, loc}} : E.Res(A.Ana)}
  RunW(h, t, skind(k), tot, f, sh, stk, acc, V.Eval.compile(e, acc))

# LAW (P2, the theorem the release claim names): over a well-formed frame, an expression
# the shared analysis types as (dtype t, total tot) evaluates with Eval.full to the frame
# unchanged and a column of dtype t with the frame's height; it fails only when tot is
# False (a fallible strict cast). The law states nothing about the frame on a failure
# (EvalTyR's Fail case gives only tot == False)
law eval_full_typed:
  for f: C.Frame
  for +e: X.Expr
  for wf: WFFrame(f)
  for +t: D.DType
  for +rs: List<&2, String>
  for +k: A.AKind
  for +tot: Bool
  for +loc: Bool
  for ha: {A.Expr.analyse(e, fschema(f)) == Done{A.Ana{t, rs, k, tot, loc}} : E.Res(A.Ana)}
  EvalTy(t, tot, fheight(f), f, V.Eval.full(f, e))

# LAW: Eval.expr (select's per-expression evaluation): the same, with the analysis' kind
# deciding the height: a reduction (KRed) answers one row, a row-wise or literal expression
# the frame's height (elen)
law eval_expr_typed:
  for f: C.Frame
  for +e: X.Expr
  for wf: WFFrame(f)
  for +t: D.DType
  for +rs: List<&2, String>
  for +k: A.AKind
  for +tot: Bool
  for +loc: Bool
  for ha: {A.Expr.analyse(e, fschema(f)) == Done{A.Ana{t, rs, k, tot, loc}} : E.Res(A.Ana)}
  EvalTy(t, tot, elen(k, fheight(f)), f, V.Eval.expr(f, e))

# =====================================================================================
# 14. Dictionary strings (M4, src/strs.bend; plan M_01 section 5 last paragraph and
#     section 6 P1): the Dictionary storage decodes to the same cells as the Raw storage
# =====================================================================================
#
# The cell model is `scell` (section 12): a Raw row is its slot, a Dictionary row is the
# entry of its code. Every law here says that a Dictionary operation answers the same
# `scell`s as the Raw operation (both equal the one model expression), and that the
# dictionary invariants below are kept. A dictionary's entries in code order are modelled
# by a Data LIST `es` (duplicable, so the proofs can speak about every entry at once):
# `WFDictE(d, es)` ties the production `ST.Dict` to it.

# the string at Nat index j of the entry list, "" past the end
def nthn(es: List<&2, String>, j: Nat) -> String:
  match es j:
    case Nil{} _:
      ""
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nthn(t, p)

# the entry of code c in the list model
def nthd(+es: List<&2, String>, +c: U32) -> String:
  nthn(es, U32.to_nat(c))

# the entry count of a dictionary
def dk(d: ST.Dict) -> U32:
  match d:
    case ST.Dict{k, dd, strs, b, slots, tag}:
      k

# an index slot is empty (id 0) or names entry id - 1: a code in range whose entry is the
# slot's key (soundness of the index; the hash probe only ever answers such a slot)
def SlotOk.k(e: Bool, +k: U32, +es: List<&2, String>, +key: String, +id: U32) -> Type:
  match e:
    case True{}:
      Unit
    case False{}:
      {U32.is_lt(U32.sub(id, 1), k) == True{} : Bool} & {nthd(es, U32.sub(id, 1)) == key : String}

def SlotOk(+k: U32, +es: List<&2, String>, x: ST.SSlot) -> Type:
  match x:
    case ST.SSlot{+key, +id}:
      SlotOk.k(U32.is_eq(id, 0), k, es, key, id)

# the index: a perfect tree of depth b whose every slot is sound
def WFIx(+k: U32, +es: List<&2, String>, +b: Nat, t: Array<ST.SSlot>) -> Type:
  match b t:
    case 0n ALeaf{x}:
      SlotOk(k, es, x)
    case 1n+p ANode{xs, ys}:
      WFIx(k, es, p, xs) & WFIx(k, es, p, ys)
    case _ _:
      Empty

# a well-formed dictionary with the entry list es: k = |es| entries fitting the 2^dd slots
# of strs, entry 0 the empty string (so a null row's code 0 decodes to the Raw default),
# every entry slot below k holding its list entry, and a sound index
def WFDictE(d: ST.Dict, +es: List<&2, String>) -> Type:
  match d:
    case ST.Dict{+k, +dd, strs, +b, slots, tag}:
      {U32.to_nat(k) == List.length(&2, String, es) : Nat} & {U32.is_le(k, U32.shln(1, dd)) == True{} : Bool} & {U32.is_lt(0, k) == True{} : Bool} & {nthn(es, 0n) == "" : String} & WFArray(String, dd, strs) & (@c: U32 -> {U32.is_lt(c, k) == True{} : Bool} -> {rd_at(String, strs, c) == nthd(es, c) : String}) & WFIx(k, es, b, slots)

def WFDict(d: ST.Dict) -> Type:
  &es: List<&2, String> -> WFDictE(d, es)

# es2 extends es: the old entries keep their codes (a Data relation: duplicable)
def Ext(+es: List<&2, String>, +es2: List<&2, String>) -> Type:
  &more: List<&2, String> -> {es2 == List.append(&2, String, es, more) : List<&2, String>}

# ---- the decode model and the code-moving kernels ---------------------------------------------

# LAW: Strs.decode reads row i as scell(s, i) for every i < n <= 2^d (a Raw column is its array;
# a Dictionary is the gather of the entries by the codes: decode(Dictionary) is the Raw column)
law decode_cell:
  for +n: U32
  for +d: Nat
  for s: ST.Strs
  for +i: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hi: {U32.is_lt(i, n) == True{} : Bool}
  {rd_at(String, ST.Strs.decode(n, d, s), i) == scell(s, i) : String}

# Strs.gather's result: perm back, row k of the output is row perm[k] of the input for k < n
def GatherW(-s: ST.Strs, -perm: Array<U32>, +n: U32, +d: Nat) -> Type:
  &o: ST.Strs -> &pm: Array<U32> -> {ST.Strs.gather(s, perm, n, d) == (o, pm) : ST.Strs & Array<U32>} & {pm == perm : Array<U32>} & (@k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {scell(o, k) == scell(s, rd_at(U32, perm, k)) : String})

# LAW: Strs.gather (rows perm[0..n) into 2^d slots) in both storages: a Dictionary gathers
# codes only (the dictionary moves along), a Raw column gathers the strings; both read row k as
# scell(s, perm[k]) (Column.gather.data, hence Column.gather / Column.slice on Str columns)
law strs_gather_cells:
  for s: ST.Strs
  for perm: Array<U32>
  for +n: U32
  for +d: Nat
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  GatherW(s, perm, n, d)

# the compaction's contract on Str cells: every row with a set mask word sits at its cursor
# position with the same scell (the Str form of CSpec, section 11)
def SCSpec(f: Nat, +i: U32, +k: U32, -s: ST.Strs, -mask: Array<U32>, -o: ST.Strs) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      &b: U32 -> {b == rd_at(U32, mask, i) : U32} & ({U32.is_ne(b, 0) == True{} : Bool} -> {scell(o, k) == scell(s, i) : String}) & SCSpec(p, U32.inc(i), U32.add(k, b), s, mask, o)

# Strs.compact's result: the mask back, the kept rows' cells in order
def CompactW(-s: ST.Strs, -mask: Array<U32>, +len: U32, +d: Nat) -> Type:
  &o: ST.Strs -> &m2: Array<U32> -> {ST.Strs.compact(s, mask, len, d) == (o, m2) : ST.Strs & Array<U32>} & {m2 == mask : Array<U32>} & SCSpec(U32.to_nat(len), 0, 0, s, mask, o)

# LAW: Strs.compact (the first len rows where mask = 1, into 2^d slots) in both storages: the
# kept rows keep their cells in order (Column.compact.data, hence filter / drop_nulls on Str
# columns), under the compaction precondition CRoom of section 11; the mask comes back
law strs_compact_cells:
  for s: ST.Strs
  for mask: Array<U32>
  for +len: U32
  for +d: Nat
  for room: CRoom(U32.to_nat(len), 0, 0, d, mask)
  CompactW(s, mask, len, d)

# LAW: Strs.clone / Dict.clone answer two copies equal to the input (Column.clone.s): every cell
# and the dictionary itself are kept
def SCloneW(-s: ST.Strs) -> Type:
  &s1: ST.Strs -> &s2: ST.Strs -> {ST.Strs.clone(s) == (s1, s2) : ST.Strs & ST.Strs} & {s1 == s : ST.Strs} & {s2 == s : ST.Strs}

def DCloneW(-d: ST.Dict) -> Type:
  &d1: ST.Dict -> &d2: ST.Dict -> {ST.Dict.clone(d) == (d1, d2) : ST.Dict & ST.Dict} & {d1 == d : ST.Dict} & {d2 == d : ST.Dict}

law strs_clone_w:
  for s: ST.Strs
  SCloneW(s)

law dict_clone_w:
  for d: ST.Dict
  DCloneW(d)

# ---- the dictionary builders: Str.same, Dict.empty, Dict.code, Strs.encode ------------------------

# LAW: Str.same (the index's key comparison) is sound and complete: equal strings exactly
law str_same_sound:
  for a: String
  for b: String
  for h: {ST.Str.same(a, b) == True{} : Bool}
  {a == b : String}

law str_same_complete:
  for +a: String
  {ST.Str.same(a, a) == True{} : Bool}

# LAW: Dict.empty is the well-formed dictionary with the one entry "" (code 0)
law dict_empty_wf:
  WFDictE(ST.Dict.empty(), "" <> Nil{})

# the look bit of the probe at a slot (Ix.look): 1 while the slot holds ANOTHER key
def look_bit(+s: String, x: ST.SSlot) -> Bool:
  match x:
    case ST.SSlot{key, +id}:
      Bool.and(U32.is_ne(id, 0), Bool.not(ST.Str.same(key, s)))

def dslots(d: ST.Dict) -> Array<ST.SSlot>:
  match d:
    case ST.Dict{k, dd, strs, b, slots, tag}:
      slots

def dbits(d: ST.Dict) -> Nat:
  match d:
    case ST.Dict{k, dd, strs, b, slots, tag}:
      b

# HYPOTHESIS of the builder laws (not proven here, see DESIGN.md section 8): the probe for s in d's
# index (Ix.seek: FNV-1a + Fibonacci slot, linear probing) stops at a slot that is empty or holds s.
# Production guarantees it by the load factor <= 1/2 (an empty slot is always within the probe's
# fuel) and the pairwise distinct entries; that termination argument is the part not proven.
def Probe(-d: ST.Dict, +s: String) -> Type:
  &x: ST.SSlot -> {x == rd_at(ST.SSlot, dslots(d), Pair.snd(Array<ST.SSlot>, U32, ST.Ix.seek(dbits(d), dslots(d), ST.Str.hash(s), s))) : ST.SSlot} & {look_bit(s, x) == False{} : Bool}

# Dict.code's answer: the dictionary d2 with entries es2 (es plus at most one new entry) and the
# code c of s in it: in range (below the entry count, as a word and in the list model), decoding
# to s; d2 well formed; every old code keeps its entry
def CodeW(-d: ST.Dict, +es: List<&2, String>, +s: String) -> Type:
  &d2: ST.Dict -> &c: U32 -> &es2: List<&2, String> -> {ST.Dict.code(d, s) == (d2, c) : ST.Dict & U32} & {U32.is_lt(c, dk(d2)) == True{} : Bool} & {Cmp.is_lt(Nat.cmp(U32.to_nat(c), List.length(&2, String, es2))) == True{} : Bool} & {nthd(es2, c) == s : String} & Ext(es, es2) & {Nat.is_le(List.length(&2, String, es2), 1n+List.length(&2, String, es)) == True{} : Bool} & WFDictE(d2, es2) & (@c2: U32 -> {U32.is_lt(c2, dk(d)) == True{} : Bool} -> {dentry(d2, c2) == dentry(d, c2) : String})

# LAW: Dict.code (the code of s, inserted when absent: Dict.code.h/k/p, Dict.add, Dict.fit, Dict.room,
# the index Ix.seek/look/slot, Ix.grow/move) keeps the dictionary well formed, extends the entries by
# at most s, and answers a code in range that decodes to s. Below 2^30 entries (the row cap keeps
# every dictionary far below); under the probe hypothesis
law dict_code_spec:
  for d: ST.Dict
  for +es: List<&2, String>
  for +s: String
  for wf: WFDictE(d, es)
  for small: {U32.is_lt(dk(d), U32.shln(1, 30n)) == True{} : Bool}
  for probe: Probe(d, s)
  CodeW(d, es, s)

# the probe hypotheses along Strs.encode's loop (Enc.go): row i against the dictionary built so far
def EncProbe(f: Nat, +i: U32, -a: Array<String>, -d: ST.Dict) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      Probe(d, rd_at(String, a, i)) & EncProbe(p, U32.inc(i), a, Pair.fst(ST.Dict, U32, ST.Dict.code(d, rd_at(String, a, i))))

# the rows below i of a code array against the entry list es: row j's code (any word equal to the
# slot, so the fact is Data) is below the entry count and names row j of the Raw array in the list
def EncRows(+i: U32, +d: Nat, -a: Array<String>, -codes: Array<U32>, +es: List<&2, String>) -> Type:
  @j: U32 -> {U32.is_lt(j, i) == True{} : Bool} -> @code: U32 -> {code == rdN(U32, d, codes, j) : U32} -> {Cmp.is_lt(Nat.cmp(U32.to_nat(code), List.length(&2, String, es))) == True{} : Bool} & {nthd(es, code) == rd_at(String, a, j) : String}

# Strs.encode's answer on a Raw array: a Dictionary with a well-formed code array and a well-formed
# dictionary over the entry list es, every row i < n coded below the entry count to the entry that
# is the Raw row (the per-row dentry form is strs_encode_cell)
def EncodeW(+n: U32, +d: Nat, -a: Array<String>) -> Type:
  &codes: Array<U32> -> &dict: ST.Dict -> &es: List<&2, String> -> {ST.Strs.encode(n, d, ST.SRaw{a}) == ST.SDict{codes, dict} : ST.Strs} & WFArray(U32, d, codes) & WFDictE(dict, es) & EncRows(n, d, a, codes, es)

# LAW: Strs.encode of a Raw column (Strs.encode.raw: Enc.go / Enc.step / Enc.put / Enc.fin over
# Dict.code from Dict.empty) is a well-formed Dictionary whose every row i < n decodes to the Raw
# row; n <= 2^d (the slots), n < 2^30 (the entry bound), under the probe hypotheses
law strs_encode_cells:
  for +n: U32
  for +d: Nat
  for a: Array<String>
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for small: {U32.is_lt(n, U32.shln(1, 30n)) == True{} : Bool}
  for probes: EncProbe(U32.to_nat(n), 0, a, ST.Dict.empty())
  EncodeW(n, d, a)

# the probe hypotheses of Strs.encode on a storage (none for an already encoded Dictionary)
def EncProbeS(+n: U32, s: ST.Strs) -> Type:
  match s:
    case ST.SRaw{a}:
      EncProbe(U32.to_nat(n), 0, a, ST.Dict.empty())
    case ST.SDict{codes, dict}:
      Unit

# LAW: Strs.encode keeps every cell: scell(encode(s), i) == scell(s, i) for i < n (a Dictionary is
# kept as it is; a Raw column is encoded)
law strs_encode_cell:
  for +n: U32
  for +d: Nat
  for s: ST.Strs
  for +i: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for small: {U32.is_lt(n, U32.shln(1, 30n)) == True{} : Bool}
  for hi: {U32.is_lt(i, n) == True{} : Bool}
  for probes: EncProbeS(n, s)
  {scell(ST.Strs.encode(n, d, s), i) == scell(s, i) : String}

# ---- decode back and the column / frame wrappers (Strs.raw, Column.encode / decode / recode,
#      Frame.encode = DF.encode_strings) --------------------------------------------------------

# LAW: Strs.raw (the Raw form of a storage: one decode) keeps every cell
law strs_raw_cell:
  for +n: U32
  for +d: Nat
  for s: ST.Strs
  for +i: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hi: {U32.is_lt(i, n) == True{} : Bool}
  {scell(ST.Strs.raw(n, d, s), i) == scell(s, i) : String}

# the hypotheses of Column.recode(dict, c) at row i: a Str column fits its slots and i is a row;
# when encoding (dict) also the row cap and the probe hypotheses of Strs.encode; nothing for the
# other dtypes (they pass through)
def RecodeHyp.enc(+dict: Bool, +n: U32, x: ST.Strs) -> Type:
  match dict:
    case True{}:
      {U32.is_lt(n, U32.shln(1, 30n)) == True{} : Bool} & EncProbeS(n, x)
    case False{}:
      Unit

def RecodeHyp(+dict: Bool, c: C.Column, +i: U32) -> Type:
  match c:
    case C.CStr{+len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & {U32.is_lt(i, len) == True{} : Bool} & RecodeHyp.enc(dict, len, data)
    case other:
      Unit

# LAW: Column.encode / Column.decode / Column.recode keep every cell (the Str storage is encoded
# by Strs.encode or decoded by Strs.raw; validity and the other dtypes are untouched)
law column_encode_cell:
  for c: C.Column
  for +i: U32
  for hyp: RecodeHyp(True{}, c, i)
  {ccell(C.Column.encode(c), i) == ccell(c, i) : D.Scalar}

law column_decode_cell:
  for c: C.Column
  for +i: U32
  for hyp: RecodeHyp(False{}, c, i)
  {ccell(C.Column.decode(c), i) == ccell(c, i) : D.Scalar}

law column_recode_cell:
  for +dict: Bool
  for c: C.Column
  for +i: U32
  for hyp: RecodeHyp(dict, c, i)
  {ccell(C.Column.recode(dict, c), i) == ccell(c, i) : D.Scalar}

# the columns of a frame recoded one by one: the same names, every cell kept (under the row
# hypotheses of the column)
def ColsCells(+dict: Bool, cols: List<&1, C.Named>, cols2: List<&1, C.Named>) -> Type:
  match cols cols2:
    case Nil{} Nil{}:
      Unit
    case C.Named{n, c} <> rest C.Named{n2, c2} <> rest2:
      {n2 == n : String} & (@i: U32 -> RecodeHyp(dict, c, i) -> {ccell(c2, i) == ccell(c, i) : D.Scalar}) & ColsCells(dict, rest, rest2)
    case _ _:
      Empty

# LAW: Cols.encode recodes every column in place
law cols_encode_cells:
  for cols: List<&1, C.Named>
  for +dict: Bool
  ColsCells(dict, cols, C.Cols.encode(cols, dict))

def FrameCells(+dict: Bool, f: C.Frame, f2: C.Frame) -> Type:
  match f f2:
    case C.Frame{h, cols} C.Frame{h2, cols2}:
      {h2 == h : U32} & ColsCells(dict, cols, cols2)

# LAW: Frame.encode (DF.encode_strings) keeps the height, the column names and every cell
law frame_encode_cells:
  for f: C.Frame
  for +dict: Bool
  FrameCells(dict, f, C.Frame.encode(f, dict))

# ---- remap: Dict.merge (one dictionary's entries into another), Dict.miss -----------------------

def ddd(d: ST.Dict) -> Nat:
  match d:
    case ST.Dict{k, dd, strs, b, slots, tag}:
      dd

def dstrs(d: ST.Dict) -> Array<String>:
  match d:
    case ST.Dict{k, dd, strs, b, slots, tag}:
      strs

# LAW: Dict.miss() (the "absent" answer of Dict.find / Dict.recode) is never a code of a dictionary
# below 2^30 entries
law dict_miss_not_code:
  for d: ST.Dict
  for small: {U32.is_lt(dk(d), U32.shln(1, 30n)) == True{} : Bool}
  {U32.is_lt(ST.Dict.miss(), dk(d)) == False{} : Bool}

# the probe hypotheses and the entry bound along Dict.merge (Dict.rc.go with ins): entry c of src
# against the dictionary built so far, which holds fewer than 2^30 entries (the row cap keeps every
# dictionary far below)
def MergeProbe(f: Nat, +c: U32, -strs: Array<String>, -d: ST.Dict) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      Probe(d, rd_at(String, strs, c)) & {U32.is_lt(dk(d), U32.shln(1, 30n)) == True{} : Bool} & MergeProbe(p, U32.inc(c), strs, Pair.fst(ST.Dict, U32, ST.Dict.code(d, rd_at(String, strs, c))))

# Dict.merge's answer: src back unchanged; dst extended (es2 extends esd) and well formed, every old
# code of dst keeping its entry; the map m (2^ddd(src) slots, well formed) re-codes every entry c of
# src: m[c] (any word equal to the slot) is below the extended entry count and names src's entry c
# there (EncRows over src's entry array: nthd(es2, m[c]) == dentry(src, c))
def MergeW(-src: ST.Dict, -dst: ST.Dict, +esd: List<&2, String>) -> Type:
  &src2: ST.Dict -> &dst2: ST.Dict -> &m: Array<U32> -> &es2: List<&2, String> -> {ST.Dict.merge(src, dst) == (src2, dst2, m) : ST.Dict & ST.Dict & Array<U32>} & {src2 == src : ST.Dict} & Ext(esd, es2) & WFArray(U32, ddd(src), m) & WFDictE(dst2, es2) & (@c: U32 -> {U32.is_lt(c, dk(dst)) == True{} : Bool} -> {dentry(dst2, c) == dentry(dst, c) : String}) & EncRows(dk(src), ddd(src), dstrs(src), m, es2)

# LAW: Dict.merge(src, dst) (Dict.rc with ins over Dict.code: Dict.rc.go / .step / .op / .put / .fin /
# .fin2) extends dst by the entries of src it lacks and maps src's codes into the result; src fits its
# slots (k <= 2^dd, part of WFDictE(src, _)), under the probe hypotheses and the entry bound at every step
law dict_merge_spec:
  for src: ST.Dict
  for dst: ST.Dict
  for +esd: List<&2, String>
  for fits: {U32.is_le(dk(src), U32.shln(1, ddd(src))) == True{} : Bool}
  for wfd: WFDictE(dst, esd)
  for probes: MergeProbe(U32.to_nat(dk(src)), 0, dstrs(src), dst)
  MergeW(src, dst, esd)

# ---- Dict.same: the equality test that lets two columns compare codes directly ---------------------

# the entries in code order agree below k
def SameRows(+k: U32, -x: ST.Dict, -y: ST.Dict) -> Type:
  @c: U32 -> {U32.is_lt(c, k) == True{} : Bool} -> {dentry(x, c) == dentry(y, c) : String}

# Dict.same's answer: both dictionaries back unchanged; a True answer means equal entry counts and
# equal entries code by code (the tag is only a fingerprint: it is verified entry by entry)
def SameW(-x: ST.Dict, -y: ST.Dict) -> Type:
  &x2: ST.Dict -> &y2: ST.Dict -> &ok: Bool -> {ST.Dict.same(x, y) == (x2, y2, ok) : ST.Dict & ST.Dict & Bool} & {x2 == x : ST.Dict} & {y2 == y : ST.Dict} & ({ok == True{} : Bool} -> {dk(x) == dk(y) : U32} & SameRows(dk(x), x, y))

# LAW: Dict.same (Dict.same.k / .u / .t / .v / .w / .go / .fin over Dict.size, Dict.tag, Str.same) is
# sound: True only for dictionaries with the same entries in the same order (so equal codes mean
# equal strings across the two columns, Eval.zd.eq.*)
law dict_same_sound:
  for x: ST.Dict
  for y: ST.Dict
  SameW(x, y)

# ---- Dict.find and Dict.recode: codes of one dictionary in another, Dict.miss() when absent --------

# a lookup's answer: the miss word, or a code below k naming s (soundness of the index; completeness,
# "every entry is found", is what the builders maintain and tests check, not stated here)
def FoundK(e: Bool, +c: U32, +k: U32, +es: List<&2, String>, +s: String) -> Type:
  match e:
    case True{}:
      {c == ST.Dict.miss() : U32}
    case False{}:
      {U32.is_lt(c, k) == True{} : Bool} & {nthd(es, c) == s : String}

# Dict.find's answer: the dictionary back unchanged (still well formed) and a code that is a miss or
# names s
def FindW(-d: ST.Dict, +es: List<&2, String>, +s: String) -> Type:
  &d2: ST.Dict -> &c: U32 -> {ST.Dict.find(d, s) == (d2, c) : ST.Dict & U32} & {d2 == d : ST.Dict} & WFDictE(d2, es) & (&e: Bool -> FoundK(e, c, dk(d), es, s))

# LAW: Dict.find (Dict.find.k over the probe Ix.seek / Ix.id) never invents a code: its answer is
# Dict.miss() or a code in range whose entry is s; the dictionary comes back unchanged
law dict_find_spec:
  for d: ST.Dict
  for +es: List<&2, String>
  for +s: String
  for wf: WFDictE(d, es)
  for probe: Probe(d, s)
  FindW(d, es, s)

# the probe hypotheses along Dict.recode (Dict.rc.go without ins): entry c of src against dst, which
# every Dict.find hands back unchanged (the chain threads the production's dictionary all the same)
def FindProbe(f: Nat, +c: U32, -strs: Array<String>, -d: ST.Dict) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+p:
      Probe(d, rd_at(String, strs, c)) & FindProbe(p, U32.inc(c), strs, Pair.fst(ST.Dict, U32, ST.Dict.find(d, rd_at(String, strs, c))))

# the rows below c of the map m: entry j of src re-coded to Dict.miss() or to a code of dst naming it
def RecRows(+c: U32, +dd: Nat, -strs: Array<String>, -m: Array<U32>, +kd: U32, +esd: List<&2, String>) -> Type:
  @j: U32 -> {U32.is_lt(j, c) == True{} : Bool} -> @code: U32 -> {code == rdN(U32, dd, m, j) : U32} -> &e: Bool -> FoundK(e, code, kd, esd, rd_at(String, strs, j))

# Dict.recode's answer: both dictionaries back unchanged (dst well formed); the map m (2^ddd(src) slots,
# well formed) re-codes every entry of src into dst or answers Dict.miss() (never a code there:
# dict_miss_not_code)
def RecodeW(-src: ST.Dict, -dst: ST.Dict, +esd: List<&2, String>) -> Type:
  &src2: ST.Dict -> &dst2: ST.Dict -> &m: Array<U32> -> {ST.Dict.recode(src, dst) == (src2, dst2, m) : ST.Dict & ST.Dict & Array<U32>} & {src2 == src : ST.Dict} & {dst2 == dst : ST.Dict} & WFArray(U32, ddd(src), m) & WFDictE(dst2, esd) & RecRows(dk(src), ddd(src), dstrs(src), m, dk(dst), esd)

# LAW: Dict.recode(src, dst) (Dict.rc without ins over Dict.find) maps src's codes into dst's, a miss
# where dst lacks the entry; src fits its slots; under the probe hypotheses
law dict_recode_spec:
  for src: ST.Dict
  for dst: ST.Dict
  for +esd: List<&2, String>
  for fits: {U32.is_le(dk(src), U32.shln(1, ddd(src))) == True{} : Bool}
  for wfd: WFDictE(dst, esd)
  for probes: FindProbe(U32.to_nat(dk(src)), 0, dstrs(src), dst)
  RecodeW(src, dst, esd)

# =====================================================================================
# 15. Concatenation and the in-place kernels (plan M_01 section 6 P1, M5 part 4):
#     Kernel.append (concat_vertical's buffers), Kernel.mask_data (Eval.fix, the null
#     slots back to the default) and Kernel.choose (fill_null / when), each with its
#     content theorem, and the Str storage of both kinds through them
# =====================================================================================
#
# Kernel.append writes a's rows at 0 .. na and b's at na + k through two Kernel.copy_into
# loops whose write index is U32.add(off, i); the in-place kernels overwrite their input
# array slot by slot. Every claim is slot by slot over the model rdN / scell / ccell.

# the slot condition of a concatenation: na + nb <= 2^d as natural numbers (Cat.join
# allocates depth_for of the saturating sum, so the sum never wraps in production)
def CatFits(+na: U32, +nb: U32, +d: Nat) -> Type:
  {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool}

# Kernel.append's answer (U32 instance): the output, well formed, holds a's rows below na and
# b's row k at na + k
def AppendW(-a: Array<U32>, -b: Array<U32>, +na: U32, +nb: U32, +d: Nat, +z: U32) -> Type:
  &o: Array<U32> -> {K.Kernel.append(~U32, na, nb, d, a, b, z) == o : Array<U32>} & WFArray(U32, d, o) & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {rdN(U32, d, o, k) == rd_at(U32, a, k) : U32}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {rdN(U32, d, o, U32.add(na, k)) == rd_at(U32, b, k) : U32})

# LAW: the production Kernel.append (two Kernel.copy_into loops, U32 instance: the word buffers of
# Bool/U32/I32 columns, every validity mask of Cat.valid, and the codes of a Dictionary) places
# a's rows first and b's rows after them, whenever na + nb rows fit the 2^d slots
law append_cells:
  for +na: U32
  for +nb: U32
  for +d: Nat
  for a: Array<U32>
  for b: Array<U32>
  for +z: U32
  for fits: CatFits(na, nb, d)
  AppendW(a, b, na, nb, d, z)

# every row below n of a code array names an entry below k (in range)
def CodesBelow(+n: U32, -codes: Array<U32>, +k: U32) -> Type:
  @i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {U32.is_lt(rd_at(U32, codes, i), k) == True{} : Bool}

# Strs.append's hypotheses beyond the slot counts: for two Dictionaries, a's dictionary well
# formed, b's entries fitting its slots, both code arrays in range, and the probe hypotheses of
# the merge of b's entries into a's; nothing for the other storage pairs (they decode to Raw)
def AppendHyp(xa: ST.Strs, xb: ST.Strs, +na: U32, +nb: U32) -> Type:
  match xa xb:
    case ST.SDict{ca, dca} ST.SDict{cb, dcb}:
      WFDict(dca) & {U32.is_le(dk(dcb), U32.shln(1, ddd(dcb))) == True{} : Bool} & CodesBelow(na, ca, dk(dca)) & CodesBelow(nb, cb, dk(dcb)) & MergeProbe(U32.to_nat(dk(dcb)), 0, dstrs(dcb), dca)
    case _ _:
      Unit

# Strs.append's answer: a's cells below na, b's cell k at na + k
def AppendStrsW(-xa: ST.Strs, -xb: ST.Strs, +na: U32, +nb: U32, +da: Nat, +db: Nat, +d: Nat) -> Type:
  &o: ST.Strs -> {ST.Strs.append(na, nb, da, db, d, xa, xb) == o : ST.Strs} & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {scell(o, k) == scell(xa, k) : String}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {scell(o, U32.add(na, k)) == scell(xb, k) : String})

# LAW: Strs.append (the Str storage of Cat.col, concat_vertical) keeps every cell in both storages:
# two Dictionaries merge b's entries into a's (Dict.merge, a's codes kept) and append a's codes to
# b's re-coded ones; any other pair decodes both sides and appends the strings
law strs_append_cells:
  for xa: ST.Strs
  for xb: ST.Strs
  for +na: U32
  for +nb: U32
  for +da: Nat
  for +db: Nat
  for +d: Nat
  for fa: {U32.is_le(na, U32.shln(1, da)) == True{} : Bool}
  for fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}
  for fits: CatFits(na, nb, d)
  for hyp: AppendHyp(xa, xb, na, nb)
  AppendStrsW(xa, xb, na, nb, da, db, d)

# ---- the in-place kernels: Kernel.mask_data (Eval.fix) and Kernel.choose (fill_null / when) -----------

# LAW: Kernel.mask_data(n, a, m, z) (in place: the slots of a whose mask word is 0 reset to z; the
# U32 instance) leaves at every pos < n the old cell where the mask word is set and z where it is 0,
# when the n rows fit a's 2^d slots and a is well formed
law mask_data_cell:
  for +n: U32
  for +d: Nat
  for a: Array<U32>
  for m: Array<U32>
  for +z: U32
  for +pos: U32
  for wf: WFArray(U32, d, a)
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hpos: {U32.is_lt(pos, n) == True{} : Bool}
  {rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, a, m, z)), pos) == Bool.pick(U32, U32.is_ne(rd_at(U32, m, pos), 0), rd_at(U32, a, pos), z) : U32}

# LAW: Kernel.mask_data hands the mask back unchanged
law mask_data_keeps_mask:
  for +n: U32
  for a: Array<U32>
  for m: Array<U32>
  for +z: U32
  {Pair.snd(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, a, m, z)) == m : Array<U32>}

# LAW: Kernel.choose(n, m, a, b) (in place into a: a[i] := m[i] ? a[i] : b[i]; the U32 instance) leaves
# at every pos < n a's old cell where the mask word is set and b's cell where it is 0, when the n rows
# fit a's 2^d slots and a is well formed
law choose_cell:
  for +n: U32
  for +d: Nat
  for m: Array<U32>
  for a: Array<U32>
  for b: Array<U32>
  for +pos: U32
  for wf: WFArray(U32, d, a)
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hpos: {U32.is_lt(pos, n) == True{} : Bool}
  {rd_at(U32, Pair.snd(Array<U32>, Array<U32>, K.Kernel.choose(~U32, n, m, a, b)), pos) == Bool.pick(U32, U32.is_ne(rd_at(U32, m, pos), 0), rd_at(U32, a, pos), rd_at(U32, b, pos)) : U32}

# LAW: Kernel.choose hands the mask back unchanged
law choose_keeps_mask:
  for +n: U32
  for m: Array<U32>
  for a: Array<U32>
  for b: Array<U32>
  {Pair.fst(Array<U32>, Array<U32>, K.Kernel.choose(~U32, n, m, a, b)) == m : Array<U32>}

# ---- the column verbs over the in-place kernels: Eval.fix (every column), Eval.fill on Str columns ----

# the data buffer of a Str storage is a well-formed array of depth d
def WFStrData(+d: Nat, s: ST.Strs) -> Type:
  match s:
    case ST.SRaw{a}:
      WFArray(String, d, a)
    case ST.SDict{codes, dict}:
      WFArray(U32, d, codes)

# the hypotheses of Eval.fix at row i: the rows fit the slots, i is a row, the data buffer is well
# formed (the P0 shape facts; the mask is only read)
def FixHyp(c: C.Column, +i: U32) -> Type:
  match c:
    case C.CBool{+len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & {U32.is_lt(i, len) == True{} : Bool} & WFArray(U32, depth, data)
    case C.CU32{+len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & {U32.is_lt(i, len) == True{} : Bool} & WFArray(U32, depth, data)
    case C.CI32{+len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & {U32.is_lt(i, len) == True{} : Bool} & WFArray(U32, depth, data)
    case C.CF32{+len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & {U32.is_lt(i, len) == True{} : Bool} & WFArray(F32, depth, data)
    case C.CStr{+len, +depth, valid, data}:
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & {U32.is_lt(i, len) == True{} : Bool} & WFStrData(depth, data)

# LAW: Eval.fix (the null slots back to the dtype default through Kernel.mask_data / Strs.fix, in
# place; the result of every arithmetic / cast / clip / string-conversion operation goes through it)
# keeps every cell of every column kind, both Str storages included (a null row stays null, a valid
# row keeps its value: the reset never touches a valid slot)
law fix_cell:
  for c: C.Column
  for +i: U32
  for hyp: FixHyp(c, i)
  {ccell(V.Eval.fix(c), i) == ccell(c, i) : D.Scalar}

# a mask word at row i is 0 or 1 (the P0 invariant WFMaskedW at one row; AllValid needs nothing)
def Mask01(v: C.Valid, +i: U32) -> Type:
  match v:
    case C.AllValid{}:
      Unit
    case C.Mask{m}:
      {U32.is_le(rd_at(U32, m, i), 1) == True{} : Bool}

# the dictionary hypotheses of fill_null on two Str storages at row i: for two Dictionaries, a's
# dictionary well formed, b's entries fitting its slots, both rows' codes in range, the probe
# hypotheses of the merge of b's entries into a's; nothing for the other pairs (they decode to Raw)
def FillDictHyp(xa: ST.Strs, xb: ST.Strs, +i: U32) -> Type:
  match xa xb:
    case ST.SDict{ca, dca} ST.SDict{cb, dcb}:
      WFDict(dca) & {U32.is_le(dk(dcb), U32.shln(1, ddd(dcb))) == True{} : Bool} & {U32.is_lt(rd_at(U32, ca, i), dk(dca)) == True{} : Bool} & {U32.is_lt(rd_at(U32, cb, i), dk(dcb)) == True{} : Bool} & MergeProbe(U32.to_nat(dk(dcb)), 0, dstrs(dcb), dca)
    case _ _:
      Unit

# the hypotheses of fill_null at row i: a's rows fit its slots, i is a row, a's data buffer is well
# formed (the kernel writes into it), both mask words at i are 0/1, the dictionary hypotheses
def FillHyp(+n: U32, +d: Nat, va: C.Valid, xa: ST.Strs, vb: C.Valid, xb: ST.Strs, +i: U32) -> Type:
  {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & WFStrData(d, xa) & Mask01(va, i) & Mask01(vb, i) & FillDictHyp(xa, xb, i)

# Eval.fill's answer on two Str columns: a column whose row i is a's cell where a is valid and b's
# cell where a is null (Polars fill_null)
def FillW(+n: U32, +d: Nat, -va: C.Valid, -xa: ST.Strs, +n2: U32, +d2: Nat, -vb: C.Valid, -xb: ST.Strs, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill(C.CStr{n, d, va, xa}, C.CStr{n2, d2, vb, xb}) == Done{c} : E.ResT(C.Column)} & {ccell(c, i) == Bool.pick(D.Scalar, vbit(va, i), ccell(C.CStr{n, d, va, xa}, i), ccell(C.CStr{n2, d2, vb, xb}, i)) : D.Scalar}

# LAW: Eval.fill (fill_null) on two Str columns, in both storages: two Dictionaries merge b's entries
# into a's and choose the codes (Kernel.choose through Eval.zd.map), the validity is the OR of the
# masks; any other pair decodes both sides and chooses the strings. Row i of the result is a's cell
# where a is valid, b's cell otherwise
law fill_str_cell:
  for +n: U32
  for +d: Nat
  for va: C.Valid
  for xa: ST.Strs
  for +n2: U32
  for +d2: Nat
  for vb: C.Valid
  for xb: ST.Strs
  for +i: U32
  for hyp: FillHyp(n, d, va, xa, vb, xb, i)
  FillW(n, d, va, xa, n2, d2, vb, xb, i)

# ---- when over Str columns: the storage half ---------------------------------------------------------

# the string stored at row i of a Str column (the data half of ccell, validity ignored; "" for the
# other dtypes): what Eval.when.str chooses, before Eval.when.valid decides the row's validity
def sdata(c: C.Column, +i: U32) -> String:
  match c:
    case C.CStr{len, depth, valid, data}:
      scell(data, i)
    case other:
      ""

# the hypotheses of when's storage at row i: a's rows fit its slots, i is a row, a's data buffer is
# well formed, the dictionary hypotheses of two Dictionaries (FillDictHyp)
def WhenHyp(+n: U32, +d: Nat, xa: ST.Strs, xb: ST.Strs, +i: U32) -> Type:
  {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & WFStrData(d, xa) & FillDictHyp(xa, xb, i)

# Eval.when.str's answer: a Str column whose stored string at row i is a's where the condition mask
# word is set and b's where it is 0
def WhenDataW(+n: U32, +d: Nat, -m: Array<U32>, -va: C.Valid, -vb: C.Valid, -xa: ST.Strs, -xb: ST.Strs, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.when.str(n, d, m, va, vb, xa, xb) == Done{c} : E.ResT(C.Column)} & {sdata(c, i) == Bool.pick(String, U32.is_ne(rd_at(U32, m, i), 0), scell(xa, i), scell(xb, i)) : String}

# LAW: Eval.when.str (the Str case of when(c).then(a).otherwise(b), m the condition's "true and valid"
# mask) stores at row i a's string where m is set and b's where it is 0, in both storages (two
# Dictionaries: b's entries merged into a's, the codes chosen through Eval.zd.map and Kernel.choose;
# otherwise the decoded strings chosen). The row's validity (Eval.when.valid: the chosen mask, or
# AllValid when its popcount is n) is not stated here: see DESIGN.md section 8
law when_str_data:
  for +n: U32
  for +d: Nat
  for m: Array<U32>
  for va: C.Valid
  for vb: C.Valid
  for xa: ST.Strs
  for xb: ST.Strs
  for +i: U32
  for hyp: WhenHyp(n, d, xa, xb, i)
  WhenDataW(n, d, m, va, vb, xa, xb, i)

# =====================================================================================
# 16. Moves (v0.2 T3.1, DESIGN.md 16.2 rule 1): Frame.lend observes as Frame.get_cloned
# =====================================================================================
#
# The liveness pass (Eval.mark) turns a column reference that copies (ICol: Frame.get_cloned)
# into one that takes the column out of its frame (IMove: Frame.lend) when no later reference
# of the operator reads it and the operator's output does not keep it; a borrow (unique's key
# columns) lends a column and puts it back with Frame.replace after a kernel hands it back.
# The law: over a frame whose names are unique (frame_ok) and whose column named n is c (the
# model fcol: the last column of that name, the one Cols.cg.go and Cols.lend.go pick), Frame.lend
# answers that very column c (no copy) and leaves the frame with a hollow stand-in in its place
# (holedf); Frame.get_cloned answers the same column c with the frame unchanged; and
# Frame.replace of c into the lent frame gives back the input frame. A moved column is therefore
# equal, as a value, to the copy the reference read before (every observer agrees: dtype,
# length, validity, cells, F32 bits), and a borrow leaves the frame as it found it.

# the last column named n in cols, sl when there is none
def lastm.k(b: Bool, c: C.Column, sl: Maybe<&1, C.Column>) -> Maybe<&1, C.Column>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      sl

def lastm(cols: List<&1, C.Named>, +n: String, sl: Maybe<&1, C.Column>) -> Maybe<&1, C.Column>:
  match cols:
    case Nil{}:
      sl
    case C.Named{+nj, c} <> rest:
      lastm(rest, n, lastm.k(String.eq(n, nj), c, sl))

# the frame's column named n
def fcol(f: C.Frame, +n: String) -> Maybe<&1, C.Column>:
  match f:
    case C.Frame{h, cols}:
      lastm(cols, n, None{})

# the hollow stand-in Column.hollow leaves: the constructor (dtype) and length, one empty slot
def hollowm(c: C.Column) -> C.Column:
  match c:
    case C.CBool{len, depth, valid, data}:
      C.CBool{len, 0n, C.AllValid{}, Array.new(U32, 0n, 0)}
    case C.CU32{len, depth, valid, data}:
      C.CU32{len, 0n, C.AllValid{}, Array.new(U32, 0n, 0)}
    case C.CI32{len, depth, valid, data}:
      C.CI32{len, 0n, C.AllValid{}, Array.new(U32, 0n, 0)}
    case C.CF32{len, depth, valid, data}:
      C.CF32{len, 0n, C.AllValid{}, Array.new(F32, 0n, 0.0)}
    case C.CStr{len, depth, valid, data}:
      C.CStr{len, 0n, C.AllValid{}, ST.SRaw{Array.new(String, 0n, "")}}

def holed.k(b: Bool, nj: String, c: C.Column) -> C.Named:
  match b:
    case True{}:
      C.Named{nj, hollowm(c)}
    case False{}:
      C.Named{nj, c}

# the columns with every column named n replaced by its hollow stand-in
def holed(cols: List<&1, C.Named>, +n: String) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{+nj, c} <> rest:
      holed.k(String.eq(n, nj), nj, c) <> holed(rest, n)

def holedf(f: C.Frame, +n: String) -> C.Frame:
  match f:
    case C.Frame{h, cols}:
      C.Frame{h, holed(cols, n)}

def LendObs(-f: C.Frame, +n: String, -c: C.Column) -> Type:
  {C.Frame.lend(f, n) == (holedf(f, n), Done{c}) : C.Frame & E.ResT(C.Column)} & {C.Frame.get_cloned(f, n) == (f, Done{c}) : C.Frame & E.ResT(C.Column)} & {C.Frame.replace(holedf(f, n), n, c) == Done{f} : E.ResT(C.Frame)}

# LAW (the move / borrow observation law; plan M_02 section 4 "projection/moves"): over a frame of
# h rows with unique names whose column named n is c, Frame.lend answers c itself and the frame
# with c's hollow stand-in; Frame.get_cloned answers the same c and the frame unchanged; and
# Frame.replace(lent frame, n, c) is the input frame again
law lend_observes:
  for f: C.Frame
  for +n: String
  for +h: U32
  for c: C.Column
  for +hf: {frame_ok(h, f) == True{} : Bool}
  for +hc: {fcol(f, n) == Some{c} : Maybe<&1, C.Column>}
  LendObs(f, n, c)

# ---- the liveness pass (Eval.mark): a move is the last read of its column ----------------------------
#
# Eval.mark runs over the postfix code of one expression with the operator's facts: `all` (the
# operator keeps none of its input columns: select, group_by) or `dead` (the input columns its
# output does not keep: with_columns' overwritten names), and `later` (the references of the
# expressions the operator evaluates after this one, Eval.refs). The laws: marking changes no read
# (the names read, in order: mark_reads); every IMove{n} it makes is allowed (n in dead, or all) and
# is the last read of n (no later instruction of the code reads n, and n is not in later:
# mark_moves_ok, for code with no move yet, which is what Eval.compile emits: compile_nomove); and
# the reads of compiled code are the expression's X.Expr.refs (compile_reads), the list the
# operators pass as `later`. With lend_observes: a moved column is the copy the reference would have
# read, and nothing reads its stand-in afterwards.

# no instruction of the code is a move
def nomove(code: List<&2, V.Instr>) -> Bool:
  match code:
    case Nil{}:
      True{}
    case V.IMove{n} <> t:
      False{}
    case i <> t:
      nomove(t)

# every IMove{n} of the code is allowed and is the last read of n
def moves_ok(code: List<&2, V.Instr>, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>) -> Bool:
  match code:
    case Nil{}:
      True{}
    case V.IMove{+n} <> +t:
      Bool.and(Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(V.Eval.reads(t), n)))), moves_ok(t, all, dead, later))
    case i <> t:
      moves_ok(t, all, dead, later)

# LAW: marking changes no read: the same names, in the same order
law mark_reads:
  for +code: List<&2, V.Instr>
  for +all: Bool
  for +dead: List<&2, String>
  for +later: List<&2, String>
  {V.Eval.reads(V.Eval.mark(code, all, dead, later)) == V.Eval.reads(code) : List<&2, String>}

# LAW: every move Eval.mark makes in move-free code is allowed and is the last read of its column
law mark_moves_ok:
  for +code: List<&2, V.Instr>
  for +all: Bool
  for +dead: List<&2, String>
  for +later: List<&2, String>
  for h: {nomove(code) == True{} : Bool}
  {moves_ok(V.Eval.mark(code, all, dead, later), all, dead, later) == True{} : Bool}

# LAW: Eval.compile emits no move
law compile_nomove:
  for +e: X.Expr
  for +acc: List<&2, V.Instr>
  for +h: {nomove(acc) == True{} : Bool}
  {nomove(V.Eval.compile(e, acc)) == True{} : Bool}

# LAW: the code of an expression reads exactly the expression's column references (X.Expr.refs), in
# order, then the reads of what follows
law compile_reads:
  for +e: X.Expr
  for +acc: List<&2, V.Instr>
  {V.Eval.reads(V.Eval.compile(e, acc)) == X.Expr.refs.go(e, V.Eval.reads(acc)) : List<&2, String>}
# 17. Sort + Head (v0.2 T3.4): the bounded gather (src/sort.bend Sort.frame_head) and the
#     physical runner step (src/exec.bend Exec.run_phys) against Sort.frame then Frame.head
#     and against Exec.run_pure
# =====================================================================================
#
# Sort.frame_head(f, ks, n) computes the exact full argsort of Sort.frame (same key checks,
# same errors in the same order, n = 0 included) and gathers only min(n, height) rows; Frame.head
# keeps the full buffers and lowers the length. The two results are different terms (their
# arrays have different sizes), so the claim is OBSERVATIONAL: robs(r, k) is everything a reader
# of r can see at row k: the error, or the height and, per column in order, its name, dtype,
# length and the cell at row k (Column.cell's model ccell, section 12) when k is a row (SNull
# past the length). Equal robs for EVERY k is equal results for every observer of rows, values
# (F32 bits included), validity, order, names, dtypes, heights and errors (DF.dump reads exactly
# these through Column.cell / len / dtype).

# what a reader sees of one column at row k
type CObs is Data:
  CObs{t: D.DType, len: U32, cell: D.Scalar}

type NObs is Data:
  NObs{name: String, c: CObs}

# what a reader sees of a result at row k
type RObs is Data:
  RErr{e: E.Err}
  RFrame{h: U32, cols: List<&2, NObs>}

def cobs(c: C.Column, +k: U32) -> CObs:
  match c:
    case C.CBool{+len, depth, valid, data}:
      CObs{D.TBool{}, len, Bool.pick(D.Scalar, U32.is_lt(k, len), ccell(C.CBool{len, depth, valid, data}, k), D.SNull{})}
    case C.CU32{+len, depth, valid, data}:
      CObs{D.TU32{}, len, Bool.pick(D.Scalar, U32.is_lt(k, len), ccell(C.CU32{len, depth, valid, data}, k), D.SNull{})}
    case C.CI32{+len, depth, valid, data}:
      CObs{D.TI32{}, len, Bool.pick(D.Scalar, U32.is_lt(k, len), ccell(C.CI32{len, depth, valid, data}, k), D.SNull{})}
    case C.CF32{+len, depth, valid, data}:
      CObs{D.TF32{}, len, Bool.pick(D.Scalar, U32.is_lt(k, len), ccell(C.CF32{len, depth, valid, data}, k), D.SNull{})}
    case C.CStr{+len, depth, valid, data}:
      CObs{D.TStr{}, len, Bool.pick(D.Scalar, U32.is_lt(k, len), ccell(C.CStr{len, depth, valid, data}, k), D.SNull{})}

def lobs(cols: List<&1, C.Named>, +k: U32) -> List<&2, NObs>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> rest:
      NObs{n, cobs(c, k)} <> lobs(rest, k)

def robs.f(f: C.Frame, +k: U32) -> RObs:
  match f:
    case C.Frame{h, cols}:
      RFrame{h, lobs(cols, k)}

def robs(r: E.ResT(C.Frame), +k: U32) -> RObs:
  match r:
    case Fail{e}:
      RErr{e}
    case Done{f}:
      robs.f(f, k)

# Sort then Head, as a function of the sort's result
def hres(r: E.ResT(C.Frame), +n: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{C.Frame.head(f, n)}

# LAW: the bounded gather shows exactly what Sort.frame then Frame.head shows, at every row k,
# for every frame, key list (none, missing keys, any dtypes, desc / nulls_last) and n (0 and past
# the height included): the same error (ColumnNotFound for the first missing key, list order),
# or the same height, names, dtypes, lengths and cells in the same stable order
law sort_head_frame:
  for f: C.Frame
  for +ks: List<&2, O.SortKey>
  for +n: U32
  for +k: U32
  {robs(O.Sort.frame_head(f, ks, n), k) == robs(hres(O.Sort.frame(f, ks), n), k) : RObs}

# LAW (production equivalence): the runner collect executes (Exec.run_phys: run_pure with the
# Sort + Head step at the root) on Head{n, Sort{ks, x}} shows exactly what the proofs' runner
# Exec.run_pure (x's code, then ISort{ks}, then IHead{n}) shows, for every plan x, environment,
# key list, n and row k: the same error from x, from the keys or from a malformed stack, or the
# same frame contents
law sort_head_run:
  for +x: P.Plan
  for +ks: List<&2, O.SortKey>
  for +n: U32
  for env: P.Env
  for +k: U32
  {robs(Q.Exec.run_phys(P.Head{n, P.Sort{ks, x}}, env), k) == robs(Q.Exec.run_pure(P.Head{n, P.Sort{ks, x}}, env), k) : RObs}

# LAW: the same for every plan (any other root runs run_pure itself)
law run_phys_obs:
  for +p: P.Plan
  for env: P.Env
  for +k: U32
  {robs(Q.Exec.run_phys(p, env), k) == robs(Q.Exec.run_pure(p, env), k) : RObs}

# LAW G6 with the physical step: what collect runs (Optimize.release, then run_phys) shows what
# the plan as written shows under run_pure (release_run composed with run_phys_obs)
law collect_obs:
  for +p: P.Plan
  for env: P.Env
  for +k: U32
  {robs(Q.Exec.run_phys(P.Optimize.release(p), env), k) == robs(Q.Exec.run_pure(p, env), k) : RObs}

# =====================================================================================
# 17. Fused kernels (v0.2 T4.1, DESIGN.md 16.3 F1-F6): each borrowing loop of src/kernels.bend
#     (W4 section) equals the unfused passes it replaces, slot by slot, and hands its inputs back
# =====================================================================================
#
# Every claim is over the production kernels (Kernel.map_pb, zipb, zipv, pred_count, compact3,
# compact4) and the production passes Eval runs today (Kernel.map_p, zip, map, mask_and,
# mask_data, popcount, compact_keep). Laws over templates are stated at instances (section 10's
# note: BendTT does not take a template over a quantified cell type); the proofs in
# PROOF_fused.bend are template proofs, so any other instance is a one-line law. The instances:
# F1 `x > lit` (u32) and `lit - x` (f32, q2's 1.0 - discount); F2 `a + b` (u32) and `a * b` (f32);
# F3 `f32(a) * b` (u32 x f32, q2's cast product); F5 q1's `ok & (qty > lit)`; F6 q1's u32/u32/f32
# buffers (the record laws) and U32 (the per-column CSpec, compact_contents' instance).
# The borrowing loops write fresh outputs (D2 rule 2) and read their inputs only: the hand-back
# laws say each returned input buffer IS the input (an equality of terms), so a column lent with
# Frame.lend and put back with Frame.replace leaves the frame as it was (lend_observes).

# ---- the kernels' records, projected --------------------------------------------------------------

def zb_o(-T: Data, -U: Data, -V: Data, r: K.ZB<T, U, V>) -> Array<V>:
  match r:
    case K.ZB{o, a, b}:
      o

def zv_o(-T: Data, -U: Data, -V: Data, r: K.ZV<T, U, V>) -> Array<V>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      o

def zv_vo(-T: Data, -U: Data, -V: Data, r: K.ZV<T, U, V>) -> Array<U32>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      vo

def pc_m(-T: Data, -U: Data, r: K.PC<T, U>) -> Array<U32>:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      m

def pc_k(-T: Data, -U: Data, r: K.PC<T, U>) -> U32:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      k

# ---- F1: a literal operand as a scalar parameter (Kernel.map_p / Kernel.map_pb) --------------------

# LAW: Kernel.map_p (the existing consuming map with a Data parameter: is_in, clip, and now F1) writes
# f(p, a[k]) at every k < n when n <= 2^d (u32 `x > lit`)
law map_p_cell:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for +lit: U32
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, K.Kernel.map_p(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, a, lit, z), k) == Bool.to_u32(U32.is_gt(rd_at(U32, a, k), lit)) : U32}

# LAW: the borrowing map IS the consuming map paired with its input: Kernel.map_pb answers
# Kernel.map_p's output and a itself (u32 `x > lit`; no hypothesis: the same loop, a only read)
law map_pb_unfused:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for +lit: U32
  for +z: U32
  {K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, a, lit, z) == (K.Kernel.map_p(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, a, lit, z), a) : Array<U32> & Array<U32>}

# LAW (F1 against v0.1's broadcast): Kernel.map_pb's `x > lit` equals, slot by slot below n, the zip of
# Eval.zip.u's Gt template against the broadcast literal column (Eval.const_col's Array.new(d, lit))
law map_pb_bcast:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for +lit: U32
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, a, lit, z)), k) == rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, d, lit), z), k) : U32}

# LAW: the same at f32 with the literal on the left (q2's `1.0 - discount`: Eval.zip.fa's Sub template
# over the broadcast column and the operand)
law map_pb_bcast_f32:
  for +d: Nat
  for +n: U32
  for a: Array<F32>
  for +lit: F32
  for +z: F32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(F32, Pair.fst(Array<F32>, Array<F32>, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, a, lit, z)), k) == rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, lit), a, z), k) : F32}

# ---- F3 (and F1 over two columns): the borrowing zip, a total cast composed into the template -------

# LAW: Kernel.zipb IS Kernel.zip with both operands handed back (F3's `f32(a) * b`)
law zipb_unfused:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for b: Array<F32>
  for +z: F32
  {K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, z) == K.ZB{K.Kernel.zip(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, z), a, b} : K.ZB<U32, F32, F32>}

# LAW (F3: the cast's own rounding, then the product's; no reassociation, no FMA): the fused
# `f32(a) * b` equals, slot by slot below n, the two passes Eval runs today (the cast map of
# Eval.cast, then Eval.zip.fa's Mul zip)
law zipb_cast_cell:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for b: Array<F32>
  for +z: F32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(F32, zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, z)), k) == rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a, 0.0), b, z), k) : F32}

# ---- F2: the null-propagating zip with validity in one loop (Kernel.zipv) -----------------------------

# LAW: Kernel.zipv's value cell (u32 `a + b`): (va[k] & vb[k]) != 0 ? a[k] + b[k] : z at every k < n
law zipv_cell:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for va: Array<U32>
  for b: Array<U32>
  for vb: Array<U32>
  for +z: U32
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, va, b, vb, z)), k) == Bool.pick(U32, U32.is_ne(U32.and(rd_at(U32, va, k), rd_at(U32, vb, k)), 0), U32.add(rd_at(U32, a, k), rd_at(U32, b, k)), z) : U32}

# LAW: Kernel.zipv's validity output IS Kernel.mask_and of the operands' validity (Eval.vand's pass,
# the AND of two masks; an AllValid side is the 1-slot ones array, and(1, w) = w on 0/1 words) and
# the four operands come back unchanged (u32 `a + b`; no hypothesis: zipv only reads its inputs)
law zipv_valid:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for va: Array<U32>
  for b: Array<U32>
  for vb: Array<U32>
  for +z: U32
  {K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, va, b, vb, z) == K.ZV{zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, va, b, vb, z)), K.Kernel.mask_and(n, d, va, vb), a, va, b, vb} : K.ZV<U32, U32, U32>}

# LAW (F2 against v0.1's three passes): Kernel.zipv's value output equals, slot by slot below n, Eval's
# vand + zip + fix: the zip of the operands with the null slots reset by Kernel.mask_data over
# Kernel.mask_and of the validity (u32 `a + b`)
law zipv_unfused:
  for +d: Nat
  for +n: U32
  for a: Array<U32>
  for va: Array<U32>
  for b: Array<U32>
  for vb: Array<U32>
  for +z: U32
  for +k: U32
  for +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for +hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, va, b, vb, z)), k) == rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k) : U32}

# LAW: the same at f32 (q2's nullable product, Eval.zip.fa's Mul template; F32 bits as written: the
# fused cell is the same Bool.pick over the same F32.mul, no reassociation)
law zipv_unfused_f32:
  for +d: Nat
  for +n: U32
  for a: Array<F32>
  for va: Array<U32>
  for b: Array<F32>
  for vb: Array<U32>
  for +z: F32
  for +k: U32
  for +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for +hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(F32, zv_o(F32, F32, F32, K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, a, va, b, vb, z)), k) == rd_at(F32, Pair.fst(Array<F32>, Array<U32>, K.Kernel.mask_data(~F32, n, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k) : F32}

# ---- F5: the filter predicate's mask and its kept count in one loop (Kernel.pred_count) ----------------
#
# Instance: q1's `ok & (qty > lit)` over the borrowed ok (a) and qty (b) with their validity words (an
# AllValid side is the 1-slot ones array): the predicate is f(p, x, y) = x AND (y > p).

# LAW: the mask cell: the predicate where both operands are valid, 0 (row dropped) where either is null
# (the cell Kernel.mask_data(zip(..), mask_and(va, vb), 0) answers: zipv_unfused's shape; Eval.pred's
# AND with the validity drops the same rows)
law pred_count_cell:
  for +d: Nat
  for +n: U32
  for +lit: U32
  for a: Array<U32>
  for va: Array<U32>
  for b: Array<U32>
  for vb: Array<U32>
  for +k: U32
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for hk: {U32.is_lt(k, n) == True{} : Bool}
  {rd_at(U32, pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb)), k) == Bool.pick(U32, U32.is_ne(U32.and(rd_at(U32, va, k), rd_at(U32, vb, k)), 0), U32.and(rd_at(U32, a, k), Bool.to_u32(U32.is_gt(rd_at(U32, b, k), lit))), 0) : U32}

# LAW: the kept count IS Kernel.popcount of the mask (the cardinality filter computes today, from the
# same mask, in the same loop)
law pred_count_count:
  for +d: Nat
  for +n: U32
  for +lit: U32
  for a: Array<U32>
  for va: Array<U32>
  for b: Array<U32>
  for vb: Array<U32>
  for +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  {pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb)) == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb)))) : U32}

# LAW: the four operands come back unchanged (the record is its mask, its count and the inputs)
law pred_count_keeps:
  for +d: Nat
  for +n: U32
  for +lit: U32
  for a: Array<U32>
  for va: Array<U32>
  for b: Array<U32>
  for vb: Array<U32>
  {K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb) == K.PC{pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb)), pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb)), a, va, b, vb} : K.PC<U32, U32>}

# ---- F6: aligned buffers compacted by one mask with one cursor (Kernel.compact3 / compact4) ----------------

def c3_o1(-A: Data, -B: Data, -C: Data, r: K.C3<A, B, C>) -> Array<A>:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, k}:
      o1

def c3_o2(-A: Data, -B: Data, -C: Data, r: K.C3<A, B, C>) -> Array<B>:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, k}:
      o2

def c3_o3(-A: Data, -B: Data, -C: Data, r: K.C3<A, B, C>) -> Array<C>:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, k}:
      o3

# LAW: Kernel.compact3 IS one Kernel.compact_keep per buffer with the same mask (what Column.compact
# runs per buffer today), the mask and the three inputs handed back, and the cursor IS Kernel.popcount
# of the mask (the kept count). q1's instance: id and region codes (u32), price (f32). No hypothesis:
# the same writes in the same order, whatever the room
law compact3_unfused:
  for +d: Nat
  for +n: U32
  for m: Array<U32>
  for a1: Array<U32>
  for a2: Array<U32>
  for a3: Array<F32>
  for +z1: U32
  for +z2: U32
  for +z3: F32
  {K.Kernel.compact3(~U32, ~U32, ~F32, n, d, m, a1, a2, a3, z1, z2, z3) == K.C3{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a1, m, z1)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a2, m, z2)), Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, d, a3, m, z3)), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))} : K.C3<U32, U32, F32>}

# LAW (compact_contents per column, one mask, one cursor): each output of Kernel.compact3 holds its
# column's kept rows in order at the cursor positions, under compact_contents' own hypothesis (CRoom:
# 0/1 mask words, the cursor below 2^d; Column.compact's depth_for(kept + 1) gives it, the leaf
# capacity of W5 too: croom_of_cap, T5.1). U32 instance (the word buffers and every validity mask)
law compact3_contents:
  for +d: Nat
  for +n: U32
  for m: Array<U32>
  for a1: Array<U32>
  for a2: Array<U32>
  for a3: Array<U32>
  for +z1: U32
  for +z2: U32
  for +z3: U32
  for room: CRoom(U32.to_nat(n), 0, 0, d, m)
  CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, c3_o1(U32, U32, U32, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3))) & CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, c3_o2(U32, U32, U32, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3))) & CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, c3_o3(U32, U32, U32, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3)))

def c4_o1(-A: Data, -B: Data, -C: Data, -D: Data, r: K.C4<A, B, C, D>) -> Array<A>:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, k}:
      o1

def c4_o2(-A: Data, -B: Data, -C: Data, -D: Data, r: K.C4<A, B, C, D>) -> Array<B>:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, k}:
      o2

def c4_o3(-A: Data, -B: Data, -C: Data, -D: Data, r: K.C4<A, B, C, D>) -> Array<C>:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, k}:
      o3

def c4_o4(-A: Data, -B: Data, -C: Data, -D: Data, r: K.C4<A, B, C, D>) -> Array<D>:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, k}:
      o4

# LAW: Kernel.compact4 IS one Kernel.compact_keep per buffer with the same mask, the mask and inputs
# handed back, the cursor Kernel.popcount of the mask (instance: three word buffers and an f32 one)
law compact4_unfused:
  for +d: Nat
  for +n: U32
  for m: Array<U32>
  for a1: Array<U32>
  for a2: Array<U32>
  for a3: Array<F32>
  for a4: Array<U32>
  for +z1: U32
  for +z2: U32
  for +z3: F32
  for +z4: U32
  {K.Kernel.compact4(~U32, ~U32, ~F32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4) == K.C4{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a1, m, z1)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a2, m, z2)), Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, d, a3, m, z3)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a4, m, z4)), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))} : K.C4<U32, U32, F32, U32>}

# LAW: compact_contents per column for Kernel.compact4 (U32 instance, compact_contents' CRoom)
law compact4_contents:
  for +d: Nat
  for +n: U32
  for m: Array<U32>
  for a1: Array<U32>
  for a2: Array<U32>
  for a3: Array<U32>
  for a4: Array<U32>
  for +z1: U32
  for +z2: U32
  for +z3: U32
  for +z4: U32
  for room: CRoom(U32.to_nat(n), 0, 0, d, m)
  CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, c4_o1(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, c4_o2(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, c4_o3(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & CSpec(U32, U32.to_nat(n), 0, 0, d, a4, m, c4_o4(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4)))

# =====================================================================================
# 21. Chunk trees (v0.2 T5.1, DESIGN.md 16.1 D1): src/chunks.bend's word tree CW (Bool/U32/I32
#     payloads, validity masks, dictionary codes; CF / CS are the same text over F32 / String)
# =====================================================================================
#
# The model is Nat-indexed: crows(t) is the row count, ncell(t, m) the logical cell at row m (a leaf
# reads its buffer at addn(0, m); a node answers its left child below lrows, else its right child at
# m - lrows, a NAT subtraction: no word arithmetic is stated over the trees). WFChunks(t): every leaf
# fits its slots (n <= 2^d) and is a well-formed array; every node's counts are exact: lrows ==
# crows(l) and lrows + crows(r) == rows as natural numbers (so no sum of row counts wrapped).
# TreeAt(t, st, src): row m of t is row st + m of the flat buffer src (the builder's spec; flatten's is
# the same relation read the other way). The claims are the bridge of DESIGN.md 16.6 in offset form:
# builders and flatten in the model, their round trip, rechunk / head / concat preserving WFChunks and
# the logical cells, the per-leaf compaction precondition croom_of_cap, the chunked map's congruence.

def crows(t: CH.CW) -> U32:
  match t:
    case CH.WL{n, d, a}:
      n
    case CH.WN{rows, lrows, l, r}:
      rows

def nrows(t: CH.CW) -> Nat:
  U32.to_nat(crows(t))

def ncell(t: CH.CW, +m: Nat) -> U32:
  match t:
    case CH.WL{n, d, a}:
      rd_at(U32, a, addn(0, m))
    case CH.WN{rows, +lrows, l, r}:
      Bool.pick(U32, Nat.is_lt(m, U32.to_nat(lrows)), ncell(l, m), ncell(r, Nat.sub(m, U32.to_nat(lrows))))

def WFChunks(t: CH.CW) -> Type:
  match t:
    case CH.WL{n, +d, a}:
      {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & WFArray(U32, d, a)
    case CH.WN{rows, +lrows, l, r}:
      {lrows == crows(l) : U32} & {Nat.add(U32.to_nat(lrows), nrows(r)) == U32.to_nat(rows) : Nat} & WFChunks(l) & WFChunks(r)

# row m of t is row st + m of src, for every row of t
def TreeAt(-t: CH.CW, +st: Nat, -src: Array<U32>) -> Type:
  @m: Nat -> {Nat.is_lt(m, nrows(t)) == True{} : Bool} -> {ncell(t, m) == rd_at(U32, src, addn(0, Nat.add(st, m))) : U32}

# LAW (the builder's leaf copy): Ch.rng IS Kernel.range with the source handed back (so one flat buffer
# feeds every leaf of a build; range_cell then gives the leaf's cells)
law ch_rng_range:
  for +n: U32
  for +d: Nat
  for +off: U32
  for a: Array<U32>
  for +z: U32
  {CH.Ch.rng(~U32, n, d, off, a, z) == (K.Kernel.range(~U32, n, d, off, a, z), a) : Array<U32> & Array<U32>}

# LAW (the builder): CW.of builds a well-formed tree of exactly n rows whose row m is row m of the
# source, for any grain (the one-leaf case moves the buffer; the binary-counter case copies the leaves
# with Ch.rng and folds them; no fuel argument: the out-of-fuel branch is correct too)
def OfW(+n: U32, +ds: Nat, +g: Nat, -src: Array<U32>) -> Type:
  &t: CH.CW -> {CH.CW.of(n, ds, g, src) == t : CH.CW} & WFChunks(t) & {crows(t) == n : U32} & TreeAt(t, 0n, src)

law cw_of:
  for +n: U32
  for +ds: Nat
  for +g: Nat
  for src: Array<U32>
  for fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}
  for wf: WFArray(U32, ds, src)
  OfW(n, ds, g, src)

# flatten's answer: a well-formed buffer of 2^dd slots whose row m is row m of t
def FlatW(+dd: Nat, -t: CH.CW) -> Type:
  &o: Array<U32> -> {CH.CW.flatten(dd, t) == o : Array<U32>} & WFArray(U32, dd, o) & (@m: Nat -> {Nat.is_lt(m, nrows(t)) == True{} : Bool} -> {rdN(U32, dd, o, addn(0, m)) == ncell(t, m) : U32})

# LAW (the bridge): flatten (one Kernel.copy_into per leaf, left to right, the right child at
# off + lrows) lays a well-formed tree's rows out in order, ragged and empty leaves included, whenever
# its rows fit the 2^dd slots
law cw_flatten:
  for +dd: Nat
  for t: CH.CW
  for wf: WFChunks(t)
  for fits: {U32.is_le(crows(t), U32.shln(1, dd)) == True{} : Bool}
  FlatW(dd, t)

# LAW (the round trip): flatten(of(src)) is src, row by row (any grain, any n that fits both buffers)
law cw_roundtrip:
  for +n: U32
  for +ds: Nat
  for +g: Nat
  for +dd: Nat
  for src: Array<U32>
  for fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}
  for wf: WFArray(U32, ds, src)
  for fitd: {U32.is_le(n, U32.shln(1, dd)) == True{} : Bool}
  for +j: U32
  for hj: {U32.is_lt(j, n) == True{} : Bool}
  {rdN(U32, dd, CH.CW.flatten(dd, CH.CW.of(n, ds, g, src)), j) == rd_at(U32, src, j) : U32}

# a concat's answer: refused (any error), or the one node over a and b, well formed, within the cap
def ConcatOK(+cap: U32, -a: CH.CW, -b: CH.CW, r: E.ResT(CH.CW)) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{t}:
      {t == CH.WN{U32.add(crows(a), crows(b)), crows(a), a, b} : CH.CW} & WFChunks(t) & {U32.is_le(crows(t), cap) == True{} : Bool}

# LAW (the node smart constructor, concat): an accepted concat is ONE node over the two trees (so its
# rows are a's then b's by ncell's definition), well formed, its exact row sum within the cap (the
# check is wrap-free: b <= cap - a after a <= cap)
law cw_concat:
  for +cap: U32
  for a: CH.CW
  for b: CH.CW
  for wa: WFChunks(a)
  for wb: WFChunks(b)
  ConcatOK(cap, a, b, CH.CW.concat.cap(cap, a, b))

# LAW (cursor capacity, the per-leaf compaction precondition): a leaf's mask of 0/1 words (the P0 mask
# invariant, WFWords with bits) over n <= 2^d rows gives compact_contents' CRoom: the compaction's cursor
# k <= i < n <= 2^d at every step, so a leaf compacts into a leaf of the SAME capacity (no kept + 1 slot).
# Discharges section 11's CRoom hypothesis for compact_contents / compact3_contents / compact4_contents
# at a chunk leaf.
law croom_of_cap:
  for +n: U32
  for +d: Nat
  for mask: Array<U32>
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for bits: WFWords(True{}, d, mask)
  CRoom(U32.to_nat(n), 0, 0, d, mask)

# the shape half of WFChunks: counts exact, leaves fitting their slots (no WFArray of the leaves)
def ShapeWF(t: CH.CW) -> Type:
  match t:
    case CH.WL{n, +d, a}:
      {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
    case CH.WN{rows, +lrows, l, r}:
      {lrows == crows(l) : U32} & {Nat.add(U32.to_nat(lrows), nrows(r)) == U32.to_nat(rows) : Nat} & ShapeWF(l) & ShapeWF(r)

# LAW (the chunked map keeps counts and shape; ported from the W0 spike's cmap_shape): the mask_not
# instance of CW.map, one balanced fork per node
law cmap_shape:
  for t: CH.CW
  for wf: WFChunks(t)
  {crows(CH.CW.map(~(x => U32.xor(x, 1)), t)) == crows(t) : U32} & ShapeWF(CH.CW.map(~(x => U32.xor(x, 1)), t))

# t2 reads, at every leaf, as the flat mask_not of t1's leaf, with the same shape and counts
def Leafwise(t1: CH.CW, t2: CH.CW) -> Type:
  match t1 t2:
    case CH.WL{n1, d1, a1} CH.WL{n2, d2, a2}:
      {n2 == n1 : U32} & {d2 == d1 : Nat} & (@k: U32 -> {U32.is_lt(k, n1) == True{} : Bool} -> {rd_at(U32, a2, k) == U32.xor(rd_at(U32, a1, k), 1) : U32})
    case CH.WN{r1, l1, x1, y1} CH.WN{r2, l2, x2, y2}:
      {r2 == r1 : U32} & {l2 == l1 : U32} & Leafwise(x1, x2) & Leafwise(y1, y2)
    case _ _:
      Empty

# LAW (the chunked map is the flat map leaf by leaf: a node congruence whose leaf lemma is
# PROOF_contents' map_cell, the term behind mask_not_cell; ported from the W0 spike's cmap_leafwise)
law cmap_leafwise:
  for t: CH.CW
  for wf: WFChunks(t)
  Leafwise(t, CH.CW.map(~(x => U32.xor(x, 1)), t))

# rechunk's answer: a well-formed tree with t's rows, row by row
def RechunkW(+g: Nat, -t: CH.CW) -> Type:
  &t2: CH.CW -> {CH.CW.rechunk(g, t) == t2 : CH.CW} & WFChunks(t2) & {crows(t2) == crows(t) : U32} & (@m: Nat -> {Nat.is_lt(m, nrows(t)) == True{} : Bool} -> {ncell(t2, m) == ncell(t, m) : U32})

# LAW (rechunk preserves the logical rows): every subtree whose rows fit 2^g becomes one leaf of 2^g
# slots (CW.flatten of the subtree; the decision read off the parent's exact counts lrows, rows - lrows),
# the rest keeps its nodes: WFChunks, the row count and every logical row are kept, ragged and empty
# leaves included
law cw_rechunk:
  for +g: Nat
  for t: CH.CW
  for wf: WFChunks(t)
  RechunkW(g, t)

# head's answer: well formed, min(h, rows) rows, the first rows of t
def HeadW(-t: CH.CW, +h: U32) -> Type:
  &t2: CH.CW -> {CH.CW.head(t, h) == t2 : CH.CW} & WFChunks(t2) & {nrows(t2) == Nat.min(U32.to_nat(h), nrows(t)) : Nat} & (@m: Nat -> {Nat.is_lt(m, nrows(t2)) == True{} : Bool} -> {ncell(t2, m) == ncell(t, m) : U32})

# LAW (the cut): head drops the leaves past h and shortens the boundary leaf (no row copied): the answer
# is well formed, has min(h, rows) rows and they are t's first rows
law cw_head:
  for t: CH.CW
  for +h: U32
  for wf: WFChunks(t)
  HeadW(t, h)

# a tree's skeleton (shape and counts, no payload): the model CW.skel answers
def skel(t: CH.CW) -> CH.Skel:
  match t:
    case CH.WL{n, d, a}:
      CH.KLeaf{n}
    case CH.WN{rows, lrows, l, r}:
      CH.KNode{rows, lrows, skel(l), skel(r)}

# the lockstep walk's answer: the tree handed back unchanged, and a True verdict only for t's skeleton
def FitsW(-t: CH.CW, -s: CH.Skel) -> Type:
  &t2: CH.CW -> &ok: Bool -> {CH.CW.fits(t, s) == (t2, ok) : CH.CW & Bool} & {t2 == t : CH.CW} & ({ok == True{} : Bool} -> {skel(t) == s : CH.Skel})

# LAW (the WFCFrame lockstep walk is sound): CW.fits hands the tree back and answers True only when the
# tree has exactly the skeleton s (same shape, same rows / lrows at every node, same n at every leaf), so
# two trees accepted against one skeleton pair leaves of equal n in any lockstep leaf walk
law cw_fits:
  for t: CH.CW
  for s: CH.Skel
  FitsW(t, s)

# STATED OPEN in section 21 (no law: tested only, see tests/chunks_*.bend; listed in DESIGN.md section 8):
#  - CW.drop / CW.slice (the front cut: one Kernel.range copy of the boundary leaf, range_cell's leaf
#    lemma; the node bookkeeping is head's with subtraction on the left);
#  - the CF / CS instances (the same generated text over F32 / String; as elsewhere in LAWS the claims are
#    stated at the U32 instance) and the column / frame layer (CColumn.of / to, CFrame.of_frame /
#    to_frame, CFrame.check: per tree they are cw_of, cw_flatten, cw_fits; the frame-level statement
#    over the column list is T5.3's);
#  - the Dictionary concat's code remap (Ch.gat, a gather handing its source back, and the tree walk
#    CW.remap) and the decode walk CS.of_codes;
#  - WFArray of Kernel.map's output inside the chunked map (cmap_shape keeps the shape half only, as the
#    W0 spike did).
# 20. Filter + Select (v0.2 T4.3, DESIGN.md 16.3 F8): the physical step of src/exec.bend
#     (Exec.fs: Eval.filter's predicate, then Frame.select_names on the UNFILTERED frame, then
#     only the selected columns compacted by Exec.fc's compact3 / compact4 groups) against
#     Eval.filter then Exec.select, and Exec.run_phys against Exec.run_pure
# =====================================================================================
#
# The first four claims are TERM equalities over the production functions (the same arrays, not
# only the same cells); filter_select_run is their robs form (section 17), the form run_phys_obs
# and collect_obs (which now cover the Select root too) are stated in.

# a filter's result, then the row filter / the select, as functions of it
def fmres(r: E.ResT(C.Frame), m: Array<U32>, +kept: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      Done{C.Frame.filter_mask(g, m, kept)}

def fsres(r: E.ResT(C.Frame), +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      Q.Exec.select(g, es)

# LAW (F6 + F8's projection): Exec.fc, which compacts AllValid columns of one length four or three
# at a time in one Kernel.compact4 / compact3 loop and every other column with Column.compact, IS
# Frame.filter_mask, for every frame (any dtypes, validity, string storage, lengths), mask and count
law fc_filter_mask:
  for g: C.Frame
  for m: Array<U32>
  for +kept: U32
  {Q.Exec.fc(g, m, kept) == C.Frame.filter_mask(g, m, kept) : C.Frame}

# LAW: selecting by name commutes with the row filter: the same error (DuplicateColumn, then the
# first missing name), or the selected columns compacted (the others are never compacted)
law select_filter_mask:
  for f: C.Frame
  for m: Array<U32>
  for +kept: U32
  for +ns: List<&2, String>
  {C.Frame.select_names(C.Frame.filter_mask(f, m, kept), ns) == fmres(C.Frame.select_names(f, ns), m, kept) : E.ResT(C.Frame)}

# LAW: the fused step IS Eval.filter then Exec.select, for a non-empty list of plain columns (the
# lists Exec.select gives to Frame.select_names): the predicate's errors first (typing, then data),
# then the select's, else the same frame
law filter_select_step:
  for f: C.Frame
  for +pred: X.Expr
  for +es: List<&2, X.Expr>
  for hp: {Q.Exec.plain(es) == True{} : Bool}
  {Q.Exec.fs(f, pred, es) == fsres(V.Eval.filter(f, pred), es) : E.ResT(C.Frame)}

# LAW (production equivalence, plan M_02 D3): the runner collect executes, on Select{es, Filter{pred,
# x}}, gives exactly Exec.run_pure's result, for every column list (plain or not), predicate, plan x
# and environment
law filter_select_run_eq:
  for +es: List<&2, X.Expr>
  for +pred: X.Expr
  for +x: P.Plan
  for env: P.Env
  {Q.Exec.run_phys(P.Select{es, P.Filter{pred, x}}, env) == Q.Exec.run_pure(P.Select{es, P.Filter{pred, x}}, env) : E.ResT(C.Frame)}

# LAW: the same, observed (section 17's robs: the error, or the height and per column name / dtype /
# length / cell at every row k)
law filter_select_run:
  for +es: List<&2, X.Expr>
  for +pred: X.Expr
  for +x: P.Plan
  for env: P.Env
  for +k: U32
  {robs(Q.Exec.run_phys(P.Select{es, P.Filter{pred, x}}, env), k) == robs(Q.Exec.run_pure(P.Select{es, P.Filter{pred, x}}, env), k) : RObs}

# =====================================================================================
# 22. Chunked kernel wrappers (v0.2 T5.2, DESIGN.md 16.1 / 16.3 / 16.4): src/ckernels.bend's recursions
#     over the chunk trees, one balanced fork per node and the flat kernel at each leaf
# =====================================================================================
#
# Every wrapper is generated from one text per kernel (bench/w5/gen_ckernels.py); the laws are stated at
# one instance each (section 10's note: BendTT does not take a template over a quantified cell type) and
# proven by template proofs in PROOF_ckernels.bend, so another instance is a one-line law. The claims:
#  - LEAFWISE: the chunked result IS the flat kernel leaf by leaf (a term equality at every leaf, the
#    node's counts copied), so every flat cell law of sections 11 / 17 applies at each leaf; with the
#    logical-cell model of section 21 (ncell) and the flatten bridge cw_flatten, the chunked map's rows
#    are the flat map's of the tree's rows (ck_map_cells);
#  - UNFUSED / KEEPS: a borrowing wrapper IS the consuming wrapper paired with its operands, or hands
#    every operand back unchanged (an equality of terms: lend / replace leave a frame as it was);
#  - the count and sum COMBINE: the per-leaf counts added at the nodes are the row-order modular sum of
#    the logical cells (U32.add associativity at the nodes, u32_fold_sum / popcount_sum per leaf);
#  - per-leaf compaction into the leaf's own capacity: CRoom at every leaf from croom_of_cap (section
#    21), hence compact_contents' CSpec at every leaf, and the kept count is the leaf mask's popcount.

# ---- maps: the chunked map is Kernel.map leaf by leaf (instance: Bool not, x xor 1) ----------------------

# t2 is the chunked map of t1: at every leaf the flat Kernel.map of that leaf, the counts copied
def LwMap(t1: CH.CW, t2: CH.CW) -> Type:
  match t1 t2:
    case CH.WL{n1, d1, a1} CH.WL{n2, d2, a2}:
      {n2 == n1 : U32} & {d2 == d1 : Nat} & {a2 == K.Kernel.map(~U32, ~U32, ~(x => U32.xor(x, 1)), n1, d1, a1, 0) : Array<U32>}
    case CH.WN{r1, l1, x1, y1} CH.WN{r2, l2, x2, y2}:
      {r2 == r1 : U32} & {l2 == l1 : U32} & LwMap(x1, x2) & LwMap(y1, y2)
    case _ _:
      Empty

# LAW (leafwise): CK.map.ww is Kernel.map at every leaf, no hypothesis
law ck_map_leafwise:
  for t: CH.CW
  LwMap(t, KC.CK.map.ww(~(x => U32.xor(x, 1)), t, 0))

# t2 is the chunked map_p of t1 (instance: x > lit, the F1 comparison)
def LwMapP(+lit: U32, t1: CH.CW, t2: CH.CW) -> Type:
  match t1 t2:
    case CH.WL{n1, d1, a1} CH.WL{n2, d2, a2}:
      {n2 == n1 : U32} & {d2 == d1 : Nat} & {a2 == K.Kernel.map_p(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n1, d1, a1, lit, 0) : Array<U32>}
    case CH.WN{r1, l1, x1, y1} CH.WN{r2, l2, x2, y2}:
      {r2 == r1 : U32} & {l2 == l1 : U32} & LwMapP(lit, x1, x2) & LwMapP(lit, y1, y2)
    case _ _:
      Empty

# LAW (leafwise): CK.mapp.ww is Kernel.map_p at every leaf
law ck_mapp_leafwise:
  for t: CH.CW
  for +lit: U32
  LwMapP(lit, t, KC.CK.mapp.ww(~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), t, lit, 0))

# LAW (F1 over chunks, unfused): the borrowing CK.mappb.ww IS the consuming CK.mapp.ww paired with its
# input tree, unchanged (map_pb_unfused at every leaf)
law ck_mappb_unfused:
  for t: CH.CW
  for +lit: U32
  for +z: U32
  {KC.CK.mappb.ww(~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), t, lit, z) == (KC.CK.mapp.ww(~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), t, lit, z), t) : CH.CW & CH.CW}

# ---- zips: two trees in lockstep (instance: u32 a + b); a shape mismatch answers the empty tree -------------

# o is the chunked zip of a and b: where a and b are both leaves, the flat Kernel.zip of the two leaves (a's
# count, the larger depth); both nodes: a's counts and the children related; a shape mismatch: the empty tree
def LwZip(a: CH.CW, b: CH.CW, o: CH.CW) -> Type:
  match a b o:
    case CH.WL{na, da, xa} CH.WL{nb, db, xb} CH.WL{no, dd, xo}:
      {no == na : U32} & {dd == KC.CK.dmax(da, db) : Nat} & {xo == K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), na, KC.CK.dmax(da, db), xa, xb, 0) : Array<U32>}
    case CH.WL{na, da, xa} CH.WL{nb, db, xb} CH.WN{r3, l3, x3, y3}:
      Empty
    case CH.WN{r1, l1, x1, y1} CH.WN{r2, l2, x2, y2} CH.WN{r3, l3, x3, y3}:
      {r3 == r1 : U32} & {l3 == l1 : U32} & LwZip(x1, x2, x3) & LwZip(y1, y2, y3)
    case CH.WN{r1, l1, x1, y1} CH.WN{r2, l2, x2, y2} CH.WL{no, dd, xo}:
      Empty
    case CH.WL{na, da, xa} CH.WN{r2, l2, x2, y2} o:
      {o == CH.CW.empty() : CH.CW}
    case CH.WN{r1, l1, x1, y1} CH.WL{nb, db, xb} o:
      {o == CH.CW.empty() : CH.CW}

# LAW (leafwise): CK.zip.www is Kernel.zip at every pair of leaves, no hypothesis (a mismatch is empty)
law ck_zip_leafwise:
  for a: CH.CW
  for b: CH.CW
  LwZip(a, b, KC.CK.zip.www(~(x => y => U32.add(x, y)), a, b, 0))

# LAW (F1/F3 over chunks, unfused; instance f32(a) * b): the borrowing CK.zipb.wff IS the consuming
# CK.zip.wff with both operand trees handed back unchanged (zipb_unfused at every leaf)
law ck_zipb_unfused:
  for a: CH.CW
  for b: CH.CF
  for +z: F32
  {KC.CK.zipb.wff(~(x => y => F32.mul(U32.to_f32(x), y)), a, b, z) == KC.CZB{KC.CK.zip.wff(~(x => y => F32.mul(U32.to_f32(x), y)), a, b, z), a, b} : KC.CZB<CH.CW, CH.CF, CH.CF>}

# ---- F2 over chunks: the null-propagating zip with validity (instance: u32 a + b) ---------------------------
#
# The model trees ZvO / ZvVo walk the four operand trees as CK.zipv.www does and build only the output /
# the validity output: at each leaf the flat Kernel.zipv's value output and Kernel.mask_and of the two
# validity leaves (zipv_valid: Eval.vand's pass), at the output depth (the larger operand depth).

def ZvO(a: CH.CW, va: CH.CW, b: CH.CW, vb: CH.CW, +z: U32) -> CH.CW:
  match a va b vb:
    case CH.WL{+n, +d, xa} CH.WL{na, da, xva} CH.WL{nb, +db, xb} CH.WL{nc, dc, xvb}:
      CH.WL{n, KC.CK.dmax(d, db), zv_o(U32, U32, U32, K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, KC.CK.dmax(d, db), xa, xva, xb, xvb, z))}
    case CH.WN{+r1, +l1, a1, a2} CH.WN{r2, l2, va1, va2} CH.WN{r3, l3, b1, b2} CH.WN{r4, l4, vb1, vb2}:
      CH.WN{r1, l1, ZvO(a1, va1, b1, vb1, z), ZvO(a2, va2, b2, vb2, z)}
    case a va b vb:
      CH.CW.empty()

def ZvVo(a: CH.CW, va: CH.CW, b: CH.CW, vb: CH.CW) -> CH.CW:
  match a va b vb:
    case CH.WL{+n, +d, xa} CH.WL{na, da, xva} CH.WL{nb, +db, xb} CH.WL{nc, dc, xvb}:
      CH.WL{n, KC.CK.dmax(d, db), K.Kernel.mask_and(n, KC.CK.dmax(d, db), xva, xvb)}
    case CH.WN{+r1, +l1, a1, a2} CH.WN{r2, l2, va1, va2} CH.WN{r3, l3, b1, b2} CH.WN{r4, l4, vb1, vb2}:
      CH.WN{r1, l1, ZvVo(a1, va1, b1, vb1), ZvVo(a2, va2, b2, vb2)}
    case a va b vb:
      CH.CW.empty()

# LAW (F2 over chunks): CK.zipv.www answers, leaf by leaf, Kernel.zipv's value output and Kernel.mask_and of
# the validity leaves, and hands the four operand trees back unchanged (zipv_valid at every leaf); a shape
# mismatch answers empty outputs and the operands
law ck_zipv:
  for a: CH.CW
  for va: CH.CW
  for b: CH.CW
  for vb: CH.CW
  for +z: U32
  {KC.CK.zipv.www(~(x => y => U32.add(x, y)), a, va, b, vb, z) == KC.CZV{ZvO(a, va, b, vb, z), ZvVo(a, va, b, vb), a, va, b, vb} : KC.CZV<CH.CW, CH.CW, CH.CW>}

# ---- F5 over chunks: the predicate's mask tree and its kept count (instance: q1's ok & (qty > lit)) ---------

def PcM(+lit: U32, a: CH.CW, va: CH.CW, b: CH.CW, vb: CH.CW) -> CH.CW:
  match a va b vb:
    case CH.WL{+n, +d, xa} CH.WL{na, da, xva} CH.WL{nb, +db, xb} CH.WL{nc, dc, xvb}:
      CH.WL{n, KC.CK.dmax(d, db), pc_m(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, KC.CK.dmax(d, db), lit, xa, xva, xb, xvb))}
    case CH.WN{+r1, +l1, a1, a2} CH.WN{r2, l2, va1, va2} CH.WN{r3, l3, b1, b2} CH.WN{r4, l4, vb1, vb2}:
      CH.WN{r1, l1, PcM(lit, a1, va1, b1, vb1), PcM(lit, a2, va2, b2, vb2)}
    case a va b vb:
      CH.CW.empty()

def PcK(+lit: U32, a: CH.CW, va: CH.CW, b: CH.CW, vb: CH.CW) -> U32:
  match a va b vb:
    case CH.WL{+n, +d, xa} CH.WL{na, da, xva} CH.WL{nb, +db, xb} CH.WL{nc, dc, xvb}:
      pc_k(U32, U32, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, KC.CK.dmax(d, db), lit, xa, xva, xb, xvb))
    case CH.WN{+r1, +l1, a1, a2} CH.WN{r2, l2, va1, va2} CH.WN{r3, l3, b1, b2} CH.WN{r4, l4, vb1, vb2}:
      U32.add(PcK(lit, a1, va1, b1, vb1), PcK(lit, a2, va2, b2, vb2))
    case a va b vb:
      0

# LAW (F5 over chunks): CK.pc.ww answers, leaf by leaf, Kernel.pred_count's mask, the per-leaf counts added
# at the nodes, and hands the four operand trees back unchanged (pred_count_keeps at every leaf)
law ck_pc:
  for +lit: U32
  for a: CH.CW
  for va: CH.CW
  for b: CH.CW
  for vb: CH.CW
  {KC.CK.pc.ww(~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), lit, a, va, b, vb) == KC.CPC{PcM(lit, a, va, b, vb), PcK(lit, a, va, b, vb), a, va, b, vb} : KC.CPC<CH.CW, CH.CW>}

# ---- the U32 tree reductions: per-leaf fold, U32.add at the nodes (D4) -------------------------------------

# the modulo-2^32 running sum of the logical rows m .. m + f - 1 of t (section 21's ncell), from acc: res
# is it (FSum of section 11, over the tree's rows instead of an array's slots)
def NSum(f: Nat, +m: Nat, +acc: U32, -t: CH.CW, +res: U32) -> Type:
  match f:
    case 0n:
      {res == acc : U32}
    case 1n+p:
      &x: U32 -> {x == ncell(t, m) : U32} & NSum(p, 1n+m, U32.add(acc, x), t, res)

# the tree's sum as the wrappers combine it: Kernel.popcount (the U32.add fold from 0) at each leaf, U32.add
# at the nodes
def TSum(t: CH.CW) -> U32:
  match t:
    case CH.WL{+n, d, a}:
      Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, a))
    case CH.WN{rows, lrows, l, r}:
      U32.add(TSum(l), TSum(r))

# LAW (the sum / count combine): CK.sum.w (= CK.popcount.w over a mask tree) hands the tree back, answers
# TSum, and TSum is the row-order modulo-2^32 sum of the logical rows (u32_fold_sum at each leaf, U32.add
# associativity at each node)
law ck_sum:
  for t: CH.CW
  for wf: WFChunks(t)
  {Pair.fst(CH.CW, U32, KC.CK.sum.w(t)) == t : CH.CW} & {Pair.snd(CH.CW, U32, KC.CK.sum.w(t)) == TSum(t) : U32} & NSum(nrows(t), 0n, 0, t, TSum(t))

# the leaves' row counts fit the output depth the pred_count wrapper allocates (n <= 2^dmax(d, db) at every
# aligned leaf; WFChunks(a) gives it whenever the operand depths are below 32, as every array's is)
def PcFits(a: CH.CW, va: CH.CW, b: CH.CW, vb: CH.CW) -> Type:
  match a va b vb:
    case CH.WL{n, +d, xa} CH.WL{na, da, xva} CH.WL{nb, db, xb} CH.WL{nc, dc, xvb}:
      {U32.is_le(n, U32.shln(1, KC.CK.dmax(d, db))) == True{} : Bool}
    case CH.WN{r1, l1, a1, a2} CH.WN{r2, l2, va1, va2} CH.WN{r3, l3, b1, b2} CH.WN{r4, l4, vb1, vb2}:
      PcFits(a1, va1, b1, vb1) & PcFits(a2, va2, b2, vb2)
    case a va b vb:
      Unit

# LAW (F5's kept count over chunks): CK.pc.ww's count (PcK, ck_pc) IS the tree sum of its mask tree
# (pred_count_count at every leaf: the leaf's count is Kernel.popcount of the leaf's mask), hence, by ck_sum,
# the row-order count of the set words of the mask tree
law ck_pc_count:
  for +lit: U32
  for a: CH.CW
  for va: CH.CW
  for b: CH.CW
  for vb: CH.CW
  for fits: PcFits(a, va, b, vb)
  {PcK(lit, a, va, b, vb) == TSum(PcM(lit, a, va, b, vb)) : U32}

# ---- per-leaf compaction (F6 over chunks; instance: three word buffers, compact_contents' U32) ---------------

# every leaf of a mask tree fits its slots and holds 0/1 words (the P0 mask invariant, section 9)
def MaskBits(t: CH.CW) -> Type:
  match t:
    case CH.WL{n, +d, a}:
      {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & WFWords(True{}, d, a)
    case CH.WN{rows, lrows, l, r}:
      MaskBits(l) & MaskBits(r)

# o holds, leaf by leaf, the rows of a whose mask word in m is set, in order (compact_contents' CSpec), in a
# leaf of the MASK leaf's capacity 2^d (no kept + 1 slot: croom_of_cap) whose count is the leaf mask's
# popcount; the node counts are the children's (ragged leaves, exact counts)
def CompactT(m: CH.CW, a: CH.CW, o: CH.CW) -> Type:
  match m a o:
    case CH.WL{n, d, mm} CH.WL{na, da, xa} CH.WL{no, dd, xo}:
      {no == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, mm)) : U32} & {dd == d : Nat} & CSpec(U32, U32.to_nat(n), 0, 0, d, xa, mm, xo)
    case CH.WN{r1, l1, m1, m2} CH.WN{r2, l2, a1, a2} CH.WN{r3, l3, o1, o2}:
      {l3 == crows(o1) : U32} & {r3 == U32.add(crows(o1), crows(o2)) : U32} & CompactT(m1, a1, o1) & CompactT(m2, a2, o2)
    case _ _ _:
      Empty

# CK.c3.www's answer: the mask and the three inputs handed back unchanged, three outputs each CompactT of
# its input, the kept count the tree sum of the mask (the cursor at every leaf, U32.add at the nodes)
def C3Spec(-m: CH.CW, -a1: CH.CW, -a2: CH.CW, -a3: CH.CW) -> Type:
  &o1: CH.CW -> &o2: CH.CW -> &o3: CH.CW -> &k: U32 -> {KC.CK.c3.www(m, a1, a2, a3) == KC.CC3{o1, o2, o3, m, a1, a2, a3, k} : KC.CC3<CH.CW, CH.CW, CH.CW>} & CompactT(m, a1, o1) & CompactT(m, a2, o2) & CompactT(m, a3, o3) & {crows(o1) == k : U32} & {crows(o2) == k : U32} & {crows(o3) == k : U32} & {k == TSum(m) : U32}

# LAW (per-leaf compaction of three aligned buffers by one mask tree, one cursor per leaf): over trees of
# the mask's shape (WFCFrame) whose mask leaves fit their slots and hold 0/1 words, every output leaf holds
# exactly the kept rows of its input leaf, in order, in the mask leaf's own capacity (CRoom discharged at
# every leaf by croom_of_cap: no kept + 1 slot), its count the leaf mask's popcount; the inputs come back
law ck_c3:
  for m: CH.CW
  for a1: CH.CW
  for a2: CH.CW
  for a3: CH.CW
  for bits: MaskBits(m)
  for +s1: {skel(a1) == skel(m) : CH.Skel}
  for +s2: {skel(a2) == skel(m) : CH.Skel}
  for +s3: {skel(a3) == skel(m) : CH.Skel}
  C3Spec(m, a1, a2, a3)

# ---- the chunked map's rows: the flat map of the tree's rows, through the flatten bridge -------------------

# CK.map.ww's answer as a witness: well formed (WFArray of every output leaf: Kernel.map writes a fresh
# array of the leaf's depth), the same rows, and row m is the map of row m (ncell, section 21)
def MapC(-t: CH.CW) -> Type:
  &t2: CH.CW -> {KC.CK.map.ww(~(x => U32.xor(x, 1)), t, 0) == t2 : CH.CW} & WFChunks(t2) & {crows(t2) == crows(t) : U32} & (@m: Nat -> {Nat.is_lt(m, nrows(t)) == True{} : Bool} -> {ncell(t2, m) == U32.xor(ncell(t, m), 1) : U32})

# LAW (WFChunks preservation and the logical rows of the chunked map): the leafwise law with mask_not_cell at
# every leaf, the node counts copied
law ck_map_cells:
  for t: CH.CW
  for wf: WFChunks(t)
  MapC(t)

# LAW (the flatten bridge, cw_flatten, over the chunked map): flattening the chunked map gives, row by row,
# the flat map of the tree's logical rows (which are flatten(t)'s rows by cw_flatten)
law ck_map_flat:
  for +dd: Nat
  for t: CH.CW
  for wf: WFChunks(t)
  for fits: {U32.is_le(crows(t), U32.shln(1, dd)) == True{} : Bool}
  for +m: Nat
  for hm: {Nat.is_lt(m, nrows(t)) == True{} : Bool}
  {rdN(U32, dd, CH.CW.flatten(dd, KC.CK.map.ww(~(x => U32.xor(x, 1)), t, 0)), addn(0, m)) == U32.xor(ncell(t, m), 1) : U32}

# the running min of the logical rows m .. m + f - 1 of t from acc (NSum over U32.min)
def NMin(f: Nat, +m: Nat, +acc: U32, -t: CH.CW, +res: U32) -> Type:
  match f:
    case 0n:
      {res == acc : U32}
    case 1n+p:
      &x: U32 -> {x == ncell(t, m) : U32} & NMin(p, 1n+m, U32.min(acc, x), t, res)

# the tree's min as CK.min.w combines it: Kernel.fold with U32.min from 2^32 - 1 at each leaf, U32.min at the nodes
def TMin(t: CH.CW) -> U32:
  match t:
    case CH.WL{+n, d, a}:
      Pair.snd(Array<U32>, U32, K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.min(acc, x)), n, a, 4294967295))
    case CH.WN{rows, lrows, l, r}:
      U32.min(TMin(l), TMin(r))

# LAW (the min combine, D4: a proven min/max combine may tree-reduce): CK.min.w hands the tree back, answers
# TMin, and TMin is the row-order U32.min of the logical rows from 2^32 - 1 (the fold at each leaf, U32.min
# associativity and 2^32 - 1 its identity at each node)
law ck_min:
  for t: CH.CW
  for wf: WFChunks(t)
  {Pair.fst(CH.CW, U32, KC.CK.min.w(t)) == t : CH.CW} & {Pair.snd(CH.CW, U32, KC.CK.min.w(t)) == TMin(t) : U32} & NMin(nrows(t), 0n, 4294967295, t, TMin(t))

# the running max of the logical rows m .. m + f - 1 of t from acc (NSum over U32.max)
def NMax(f: Nat, +m: Nat, +acc: U32, -t: CH.CW, +res: U32) -> Type:
  match f:
    case 0n:
      {res == acc : U32}
    case 1n+p:
      &x: U32 -> {x == ncell(t, m) : U32} & NMax(p, 1n+m, U32.max(acc, x), t, res)

# the tree's max as CK.max.w combines it: Kernel.fold with U32.max from 0 at each leaf, U32.max at the nodes
def TMax(t: CH.CW) -> U32:
  match t:
    case CH.WL{+n, d, a}:
      Pair.snd(Array<U32>, U32, K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.max(acc, x)), n, a, 0))
    case CH.WN{rows, lrows, l, r}:
      U32.max(TMax(l), TMax(r))

# LAW (the max combine, D4: a proven min/max combine may tree-reduce): CK.max.w hands the tree back, answers
# TMax, and TMax is the row-order U32.max of the logical rows from 0 (the fold at each leaf, U32.max
# associativity and 0 its identity at each node)
law ck_max:
  for t: CH.CW
  for wf: WFChunks(t)
  {Pair.fst(CH.CW, U32, KC.CK.max.w(t)) == t : CH.CW} & {Pair.snd(CH.CW, U32, KC.CK.max.w(t)) == TMax(t) : U32} & NMax(nrows(t), 0n, 0, t, TMax(t))

# STATED OPEN in section 22 (no law: tested only, tests/ckernels_*.bend; listed in DESIGN.md section 8):
#  - the other instances of every wrapper (the CF / CS trees and the other template functions): the same
#    generated text (bench/w5/gen_ckernels.py), stated here at one U32 instance each (section 10's note);
#  - CK.ck.X (one-buffer compaction, the count by Kernel.popcount of the handed-back mask) and CK.c4.*: the
#    same per-leaf structure as ck_c3 (compact4_contents and PROOF_fused's c4_sim are the leaf lemmas);
#  - WFArray of compaction outputs (CompactT gives the counts, the contents and the capacity, not WFArray
#    of the compacted leaves);
#  - the sequential walks CK.walk.X, CK.fsum.X / CK.fsumflat.X, CK.fmin.f / CK.fmax.f, CK.imin.w / imax.w:
#    one tail loop over the leaves in row order, the very fold of the flat kernel (floats are tested
#    against the exact reference, DESIGN.md section 8 item 8; the walk's row order is by construction);
#  - the gathers CK.gather.X (the leaf gather fused into the builder: a new range-offset gather loop and
#    cw_of's binary counter) and CK.gatherf.X (cw_flatten, gather_contents and cw_of composed);
#  - CK.ones1 trees are not WFChunks (1-slot leaves read for every row): ck_zipv / ck_pc hold for ANY
#    operand trees; ck_pc_count needs PcFits (the data leaves fit the output depth).
