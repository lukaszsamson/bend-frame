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
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/plan.bend as P
import ./src/exec.bend as Q
import ./src/eval.bend as V
import ./src/dump.bend as DP

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
      {U32.is_le(len, U32.shln(1, depth)) == True{} : Bool} & WFValidT(String, "", depth, valid, data)

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
# out[k]). NOT proven here (M5): that later writes leave earlier slots alone, i.e.
# that two indices below 2^d take different paths; that bit-vector fact over
# Word.and / shr / sub / is_lt is what separates these lemmas from the full
# "out[i] == in[index[i]]" / subsequence theorems.

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

# LAW: Kernel.iota_from writes off + k at every k < n when n <= 2^d (Column.slice's index array)
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
      Bool.pick(D.Scalar, vbit(valid, i), D.SStr{rd_at(String, data, i)}, D.SNull{})

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
# for every k below the slice's length (data through gather_contents / iota_cell, validity
# through the same gather of the mask). The U32 instance stands for the word columns (Bool, I32:
# same buffers); F32 / String need the kernel theorems at those instances
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

# Eval.full / Eval.expr's answer: the frame back unchanged and a column of dtype t with n rows,
# or a failure the analysis allowed
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
# False (a fallible strict cast), with the frame unchanged too
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
