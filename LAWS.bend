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
import ./src/sort.bend as O
import ./src/plan.bend as P

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

# the arithmetic operators that keep their operand type (+ - * /)
def is_arith(op: X.BinOp) -> Bool:
  match op:
    case X.Add{}:
      True{}
    case X.Sub{}:
      True{}
    case X.Mul{}:
      True{}
    case X.Div{}:
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

# LAW: a filter by a non-aggregating bool predicate keeps the schema
law filter_keeps_schema:
  for p: P.Plan
  for +s: List<&2, S.Field>
  for e: X.Expr
  for ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}
  for t: {X.Expr.type(e, s) == Done{D.TBool{}} : E.Res(D.DType)}
  for na: {X.Expr.is_agg(e) == False{} : Bool}
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

# LAW: the head pass (Head merging and sinking) never changes the schema of
# any plan, for any pending row limit
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
