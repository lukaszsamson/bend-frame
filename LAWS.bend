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

# the R1 fragment: a plan in which every Select / WithColumns is a Head barrier
# (the analysis does not certify it: Opt.sinks is False), so Opt.head only ever
# merges adjacent Heads. Head sinking through certified nodes is R3 (plan M_01
# section 6 P3), not claimed here.
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

# LAW G6 on the R1 fragment: the release optimizer preserves the production
# runner's result for every well-typed merge-only plan
law release_merge_only:
  for +p: P.Plan
  for s: List<&2, S.Field>
  for env: P.Env
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for +mo: {merge_only(p) == True{} : Bool}
  {Q.Exec.run_pure(P.Optimize.release(p), env) == Q.Exec.run_pure(p, env) : E.ResT(C.Frame)}

# LAW: the same, observed through the typed oracle (dtypes, ordered names,
# height, validity, cells as DF.dump prints them, or the error)
law release_merge_only_obs:
  for +p: P.Plan
  for s: List<&2, S.Field>
  for env: P.Env
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for +mo: {merge_only(p) == True{} : Bool}
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
  for hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}
  for hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}
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
  {Pair.snd(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, d, src, perm, z)) == perm : Array<U32>}
