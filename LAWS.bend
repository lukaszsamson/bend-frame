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
    case P.GroupBy{ks, ags, mo, x}:
      no_adjacent_filters(x)
    case P.Join{how, lo, ro, l, r}:
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
    case P.GroupBy{ks, ags, mo, x}:
      no_adjacent_heads(x)
    case P.Join{how, lo, ro, l, r}:
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
    case P.GroupBy{ks, ags, mo, x}:
      merge_only(x)
    case P.Join{how, lo, ro, l, r}:
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
