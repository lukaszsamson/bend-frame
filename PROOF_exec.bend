# PROOF_exec.bend -- proofs of LAWS.bend section 8: the production runner
# (src/exec.bend, Exec.run_pure) and the R1 adjacent-Head merge against it.
#
# Shape of the development:
#   * code lemmas (Data): Exec.compile(p, acc) == compile(p, Nil) ++ acc; Exec.mark
#     over an append (Laws.markw); the Sources a code reads (Laws.srcs) decide the
#     marks; Opt.head keeps the Sources (head_pass_keeps_sources).
#   * state lemmas: a runner state Q.St owns frames, so it is affine: a lemma takes
#     it once. Lemmas that rewrite it hand it back as a Sigma witness beside the
#     equation (col/cols/frame_head_w, head_step_w); parallel inductions over code
#     (loop_pre, head_pass_run) consume the state once and pass a continuation
#     hypothesis for the suffix instead of rewriting both sides.
#   * R1: head_merge_run (the rule, any plan), head_pass_run (the pass on the
#     merge-only fragment), release_merge_only (Optimize.release on that fragment),
#     release_merge_only_obs (the same through DF.dump).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/join.bend as J
import ./src/plan.bend as P
import ./src/exec.bend as Q
import ./src/dump.bend as DP
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L

# ---- lists of instructions ------------------------------------------------------------

def app_nil(xs: List<&2, Q.Instr>) -> {List.append(&2, Q.Instr, xs, Nil{}) == xs : List<&2, Q.Instr>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, t, Nil{}), t, app_nil(t)) : {h <> _ == h <> t : List<&2, Q.Instr>}
      {==}

def app_assoc(xs: List<&2, Q.Instr>, +ys: List<&2, Q.Instr>, +zs: List<&2, Q.Instr>) -> {List.append(&2, Q.Instr, List.append(&2, Q.Instr, xs, ys), zs) == List.append(&2, Q.Instr, xs, List.append(&2, Q.Instr, ys, zs)) : List<&2, Q.Instr>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, t, ys), zs), List.append(&2, Q.Instr, t, List.append(&2, Q.Instr, ys, zs)), app_assoc(t, ys, zs)) : {h <> _ == h <> List.append(&2, Q.Instr, t, List.append(&2, Q.Instr, ys, zs)) : List<&2, Q.Instr>}
      {==}

def sapp_assoc(xs: List<&2, String>, +ys: List<&2, String>, +zs: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, ys), zs) == List.append(&2, String, xs, List.append(&2, String, ys, zs)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, t, ys), zs), List.append(&2, String, t, List.append(&2, String, ys, zs)), sapp_assoc(t, ys, zs)) : {h <> _ == h <> List.append(&2, String, t, List.append(&2, String, ys, zs)) : List<&2, String>}
      {==}

# ---- Exec.compile is postfix: the accumulator is appended -------------------------------

def compile_app(p: P.Plan, +acc: List<&2, Q.Instr>) -> {Q.Exec.compile(p, acc) == List.append(&2, Q.Instr, Q.Exec.compile(p, Nil{}), acc) : List<&2, Q.Instr>}:
  match p:
    case P.ScanCsv{path, o, s}:
      {==}
    case P.Source{n, s}:
      {==}
    case P.Select{+es, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.ISelect{es} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISelect{es} <> acc), compile_app(x, Q.ISelect{es} <> acc)) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(x, Q.ISelect{es} <> Nil{}), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.ISelect{es} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISelect{es} <> Nil{}), compile_app(x, Q.ISelect{es} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISelect{es} <> acc) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISelect{es} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.ISelect{es} <> Nil{}, acc)), app_assoc(Q.Exec.compile(x, Nil{}), Q.ISelect{es} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISelect{es} <> acc) == _ : List<&2, Q.Instr>}
      {==}
    case P.WithColumns{+es, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IWith{es} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IWith{es} <> acc), compile_app(x, Q.IWith{es} <> acc)) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(x, Q.IWith{es} <> Nil{}), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IWith{es} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IWith{es} <> Nil{}), compile_app(x, Q.IWith{es} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IWith{es} <> acc) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IWith{es} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IWith{es} <> Nil{}, acc)), app_assoc(Q.Exec.compile(x, Nil{}), Q.IWith{es} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IWith{es} <> acc) == _ : List<&2, Q.Instr>}
      {==}
    case P.Filter{+e, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IFilter{e} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{e} <> acc), compile_app(x, Q.IFilter{e} <> acc)) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(x, Q.IFilter{e} <> Nil{}), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IFilter{e} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{e} <> Nil{}), compile_app(x, Q.IFilter{e} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{e} <> acc) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{e} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IFilter{e} <> Nil{}, acc)), app_assoc(Q.Exec.compile(x, Nil{}), Q.IFilter{e} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IFilter{e} <> acc) == _ : List<&2, Q.Instr>}
      {==}
    case P.Sort{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.ISort{ks} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> acc), compile_app(x, Q.ISort{ks} <> acc)) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(x, Q.ISort{ks} <> Nil{}), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.ISort{ks} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Nil{}), compile_app(x, Q.ISort{ks} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> acc) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.ISort{ks} <> Nil{}, acc)), app_assoc(Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.ISort{ks} <> acc) == _ : List<&2, Q.Instr>}
      {==}
    case P.GroupBy{+ks, +ags, +mo, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IGroupBy{ks, ags, mo} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IGroupBy{ks, ags, mo} <> acc), compile_app(x, Q.IGroupBy{ks, ags, mo} <> acc)) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(x, Q.IGroupBy{ks, ags, mo} <> Nil{}), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IGroupBy{ks, ags, mo} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IGroupBy{ks, ags, mo} <> Nil{}), compile_app(x, Q.IGroupBy{ks, ags, mo} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IGroupBy{ks, ags, mo} <> acc) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IGroupBy{ks, ags, mo} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IGroupBy{ks, ags, mo} <> Nil{}, acc)), app_assoc(Q.Exec.compile(x, Nil{}), Q.IGroupBy{ks, ags, mo} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IGroupBy{ks, ags, mo} <> acc) == _ : List<&2, Q.Instr>}
      {==}
    case P.Head{+n, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IHead{n} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{n} <> acc), compile_app(x, Q.IHead{n} <> acc)) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(x, Q.IHead{n} <> Nil{}), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IHead{n} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{n} <> Nil{}), compile_app(x, Q.IHead{n} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{n} <> acc) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{n} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IHead{n} <> Nil{}, acc)), app_assoc(Q.Exec.compile(x, Nil{}), Q.IHead{n} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{n} <> acc) == _ : List<&2, Q.Instr>}
      {==}
    case P.Join{+how, +lo, +ro, +l, +r}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc)), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc)), compile_app(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))) : {_ == List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> acc), compile_app(r, Q.IJoin{how, lo, ro} <> acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), _) == List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), compile_app(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}))) : {List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> acc)) == List.append(&2, Q.Instr, _, acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> Nil{}), compile_app(r, Q.IJoin{how, lo, ro} <> Nil{})) : {List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> acc)) == List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), _), acc) : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> Nil{})), acc), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> Nil{}), acc)), app_assoc(Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> Nil{}), acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> acc)) == _ : List<&2, Q.Instr>}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> Nil{}), acc), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), List.append(&2, Q.Instr, Q.IJoin{how, lo, ro} <> Nil{}, acc)), app_assoc(Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> Nil{}, acc)) : {List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Nil{}), Q.IJoin{how, lo, ro} <> acc)) == List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), _) : List<&2, Q.Instr>}
      {==}

# a pending Head compiles to the sub-plan's code followed by Laws.hcode(n)
def compile_hwrap(n: Maybe<&2, U32>, -q: P.Plan) -> {Q.Exec.compile(P.Opt.hwrap(n, q), Nil{}) == Q.Exec.compile(q, Laws.hcode(n)) : List<&2, Q.Instr>}:
  match n:
    case None{}:
      {==}
    case Some{k}:
      {==}

# ---- the Sources a code reads decide Exec.mark ---------------------------------------------

def srcs_app(a: List<&2, Q.Instr>, +b: List<&2, Q.Instr>) -> {Laws.srcs(List.append(&2, Q.Instr, a, b)) == List.append(&2, String, Laws.srcs(a), Laws.srcs(b)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Q.ISource{n, s, l} <> t:
      %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, t, b)), List.append(&2, String, Laws.srcs(t), Laws.srcs(b)), srcs_app(t, b)) : {n <> _ == n <> List.append(&2, String, Laws.srcs(t), Laws.srcs(b)) : List<&2, String>}
      {==}
    case Q.IScan{path, o, s} <> t:
      srcs_app(t, b)
    case Q.ISelect{es} <> t:
      srcs_app(t, b)
    case Q.IWith{es} <> t:
      srcs_app(t, b)
    case Q.IFilter{e} <> t:
      srcs_app(t, b)
    case Q.ISort{ks} <> t:
      srcs_app(t, b)
    case Q.IGroupBy{ks, ags, mo} <> t:
      srcs_app(t, b)
    case Q.IJoin{how, lo, ro} <> t:
      srcs_app(t, b)
    case Q.IHead{k} <> t:
      srcs_app(t, b)

# the pending-head code reads no Source
def srcs_hcode(n: Maybe<&2, U32>, -s: List<&2, Q.Instr>) -> {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s)) == Laws.srcs(s) : List<&2, String>}:
  match n:
    case None{}:
      {==}
    case Some{k}:
      {==}

def later_srcs(code: List<&2, Q.Instr>, +nm: String) -> {Q.Exec.later(code, nm) == Laws.has_src(Laws.srcs(code), nm) : Bool}:
  match code:
    case Nil{}:
      {==}
    case Q.ISource{n, s, l} <> t:
      %Equal.sym(Bool, Q.Exec.later(t, nm), Laws.has_src(Laws.srcs(t), nm), later_srcs(t, nm)) : {Bool.or(String.eq(n, nm), _) == Bool.or(String.eq(n, nm), Laws.has_src(Laws.srcs(t), nm)) : Bool}
      {==}
    case Q.IScan{path, o, s} <> t:
      later_srcs(t, nm)
    case Q.ISelect{es} <> t:
      later_srcs(t, nm)
    case Q.IWith{es} <> t:
      later_srcs(t, nm)
    case Q.IFilter{e} <> t:
      later_srcs(t, nm)
    case Q.ISort{ks} <> t:
      later_srcs(t, nm)
    case Q.IGroupBy{ks, ags, mo} <> t:
      later_srcs(t, nm)
    case Q.IJoin{how, lo, ro} <> t:
      later_srcs(t, nm)
    case Q.IHead{k} <> t:
      later_srcs(t, nm)

# two suffixes reading the same Sources are looked up alike
def later_ext(+b: List<&2, Q.Instr>, +b2: List<&2, Q.Instr>, +nm: String, hs: {Laws.srcs(b) == Laws.srcs(b2) : List<&2, String>}) -> {Q.Exec.later(b, nm) == Q.Exec.later(b2, nm) : Bool}:
  %Equal.sym(Bool, Q.Exec.later(b, nm), Laws.has_src(Laws.srcs(b), nm), later_srcs(b, nm)) : {_ == Q.Exec.later(b2, nm) : Bool}
  %Equal.sym(Bool, Q.Exec.later(b2, nm), Laws.has_src(Laws.srcs(b2), nm), later_srcs(b2, nm)) : {Laws.has_src(Laws.srcs(b), nm) == _ : Bool}
  %hs : {Laws.has_src(Laws.srcs(b), nm) == Laws.has_src(_, nm) : Bool}
  {==}

# Exec.mark over an append: the marks of the head part look into the tail
def mark_app(a: List<&2, Q.Instr>, +b: List<&2, Q.Instr>) -> {Q.Exec.mark(List.append(&2, Q.Instr, a, b)) == List.append(&2, Q.Instr, Laws.markw(a, b), Q.Exec.mark(b)) : List<&2, Q.Instr>}:
  match a:
    case Nil{}:
      {==}
    case i <> +t:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, t, b)), List.append(&2, Q.Instr, Laws.markw(t, b), Q.Exec.mark(b)), mark_app(t, b)) : {Q.Exec.mark.i(i, List.append(&2, Q.Instr, t, b)) <> _ == List.append(&2, Q.Instr, Q.Exec.mark.i(i, List.append(&2, Q.Instr, t, b)) <> Laws.markw(t, b), Q.Exec.mark(b)) : List<&2, Q.Instr>}
      {==}

# the marks of a code depend on its suffix only through the Sources the suffix reads
def markw_ext(a: List<&2, Q.Instr>, +b: List<&2, Q.Instr>, +b2: List<&2, Q.Instr>, +hs: {Laws.srcs(b) == Laws.srcs(b2) : List<&2, String>}) -> {Laws.markw(a, b) == Laws.markw(a, b2) : List<&2, Q.Instr>}:
  match a:
    case Nil{}:
      {==}
    case Q.ISource{+n, s, l} <> +t:
      %later_ext(List.append(&2, Q.Instr, t, b), List.append(&2, Q.Instr, t, b2), n, (%Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, t, b)), List.append(&2, String, Laws.srcs(t), Laws.srcs(b)), srcs_app(t, b)) : {_ == Laws.srcs(List.append(&2, Q.Instr, t, b2)) : List<&2, String>}; %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, t, b2)), List.append(&2, String, Laws.srcs(t), Laws.srcs(b2)), srcs_app(t, b2)) : {List.append(&2, String, Laws.srcs(t), Laws.srcs(b)) == _ : List<&2, String>}; %hs : {List.append(&2, String, Laws.srcs(t), Laws.srcs(b)) == List.append(&2, String, Laws.srcs(t), _) : List<&2, String>}; {==})) : {Q.ISource{n, s, Bool.not(Q.Exec.later(List.append(&2, Q.Instr, t, b), n))} <> Laws.markw(t, b) == Q.ISource{n, s, Bool.not(_)} <> Laws.markw(t, b2) : List<&2, Q.Instr>}
      %markw_ext(t, b, b2, hs) : {Q.ISource{n, s, Bool.not(Q.Exec.later(List.append(&2, Q.Instr, t, b), n))} <> Laws.markw(t, b) == Q.ISource{n, s, Bool.not(Q.Exec.later(List.append(&2, Q.Instr, t, b), n))} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.IScan{path, o, s} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.IScan{path, o, s} <> Laws.markw(t, b) == Q.IScan{path, o, s} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.ISelect{es} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.ISelect{es} <> Laws.markw(t, b) == Q.ISelect{es} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.IWith{es} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.IWith{es} <> Laws.markw(t, b) == Q.IWith{es} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.IFilter{e} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.IFilter{e} <> Laws.markw(t, b) == Q.IFilter{e} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.ISort{ks} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.ISort{ks} <> Laws.markw(t, b) == Q.ISort{ks} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.IGroupBy{ks, ags, mo} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.IGroupBy{ks, ags, mo} <> Laws.markw(t, b) == Q.IGroupBy{ks, ags, mo} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.IJoin{how, lo, ro} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.IJoin{how, lo, ro} <> Laws.markw(t, b) == Q.IJoin{how, lo, ro} <> _ : List<&2, Q.Instr>}
      {==}
    case Q.IHead{k} <> +t:
      %markw_ext(t, b, b2, hs) : {Q.IHead{k} <> Laws.markw(t, b) == Q.IHead{k} <> _ : List<&2, Q.Instr>}
      {==}

# ---- Opt.head keeps the Sources ----------------------------------------------------------

# srcs(compile(q, acc)) splits at the accumulator
def srcs_compile(+q: P.Plan, +acc: List<&2, Q.Instr>) -> {Laws.srcs(Q.Exec.compile(q, acc)) == List.append(&2, String, Laws.srcs(Q.Exec.compile(q, Nil{})), Laws.srcs(acc)) : List<&2, String>}:
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(q, acc), List.append(&2, Q.Instr, Q.Exec.compile(q, Nil{}), acc), compile_app(q, acc)) : {Laws.srcs(_) == List.append(&2, String, Laws.srcs(Q.Exec.compile(q, Nil{})), Laws.srcs(acc)) : List<&2, String>}
  srcs_app(Q.Exec.compile(q, Nil{}), acc)

# a pending Head adds no Source: srcs(compile(hwrap(n, q), acc)) == srcs(compile(q, acc))
def srcs_hwrap(+n: Maybe<&2, U32>, +q: P.Plan, +acc: List<&2, Q.Instr>) -> {Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, q), acc)) == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}:
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, q), acc), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hwrap(n, q), Nil{}), acc), compile_app(P.Opt.hwrap(n, q), acc)) : {Laws.srcs(_) == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, q), Nil{}), Q.Exec.compile(q, Laws.hcode(n)), compile_hwrap(n, q)) : {Laws.srcs(List.append(&2, Q.Instr, _, acc)) == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(q, Laws.hcode(n)), List.append(&2, Q.Instr, Q.Exec.compile(q, Nil{}), Laws.hcode(n)), compile_app(q, Laws.hcode(n))) : {Laws.srcs(List.append(&2, Q.Instr, _, acc)) == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}
  %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(q, Nil{}), Laws.hcode(n)), acc), List.append(&2, Q.Instr, Q.Exec.compile(q, Nil{}), List.append(&2, Q.Instr, Laws.hcode(n), acc)), app_assoc(Q.Exec.compile(q, Nil{}), Laws.hcode(n), acc)) : {Laws.srcs(_) == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, Q.Exec.compile(q, Nil{}), List.append(&2, Q.Instr, Laws.hcode(n), acc))), List.append(&2, String, Laws.srcs(Q.Exec.compile(q, Nil{})), Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), acc))), srcs_app(Q.Exec.compile(q, Nil{}), List.append(&2, Q.Instr, Laws.hcode(n), acc))) : {_ == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), acc)), Laws.srcs(acc), srcs_hcode(n, acc)) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(q, Nil{})), _) == Laws.srcs(Q.Exec.compile(q, acc)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(q, acc)), List.append(&2, String, Laws.srcs(Q.Exec.compile(q, Nil{})), Laws.srcs(acc)), srcs_compile(q, acc)) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(q, Nil{})), Laws.srcs(acc)) == _ : List<&2, String>}
  {==}

# one unary node: Opt.head(x, n') below it compiles to the same Sources as x with the pending head
def srcs_unary(+x: P.Plan, +n: Maybe<&2, U32>, +n2: Maybe<&2, U32>, +i: Q.Instr, +acc: List<&2, Q.Instr>,
  ih: {Laws.srcs(Q.Exec.compile(P.Opt.head(x, n2), i <> acc)) == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n2, x), i <> acc)) : List<&2, String>})
  -> {Laws.srcs(Q.Exec.compile(P.Opt.head(x, n2), i <> acc)) == Laws.srcs(Q.Exec.compile(x, i <> acc)) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.head(x, n2), i <> acc)), Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n2, x), i <> acc)), ih) : {_ == Laws.srcs(Q.Exec.compile(x, i <> acc)) : List<&2, String>}
  srcs_hwrap(n2, x, i <> acc)

def Laws.head_pass_keeps_sources(p, n, acc):
  match p:
    case P.ScanCsv{path, o, s}:
      {==}
    case P.Source{nm, s}:
      {==}
    case P.Select{+es, +x}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}), acc)), Laws.srcs(Q.Exec.compile(P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}, acc)), srcs_hwrap(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, x}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, x}), acc)), Laws.srcs(Q.Exec.compile(P.Select{es, x}, acc)), srcs_hwrap(n, P.Select{es, x}, acc)) : {Laws.srcs(Q.Exec.compile(P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)), Q.ISelect{es} <> acc)) == _ : List<&2, String>}
      srcs_unary(x, n, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n), Q.ISelect{es}, acc, Laws.head_pass_keeps_sources(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n), Q.ISelect{es} <> acc))
    case P.WithColumns{+es, +x}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}), acc)), Laws.srcs(Q.Exec.compile(P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}, acc)), srcs_hwrap(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.WithColumns{es, x}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.WithColumns{es, x}), acc)), Laws.srcs(Q.Exec.compile(P.WithColumns{es, x}, acc)), srcs_hwrap(n, P.WithColumns{es, x}, acc)) : {Laws.srcs(Q.Exec.compile(P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)), Q.IWith{es} <> acc)) == _ : List<&2, String>}
      srcs_unary(x, n, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n), Q.IWith{es}, acc, Laws.head_pass_keeps_sources(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n), Q.IWith{es} <> acc))
    case P.Filter{+e, +x}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Filter{e, P.Opt.head(x, None{})}), acc)), Laws.srcs(Q.Exec.compile(P.Filter{e, P.Opt.head(x, None{})}, acc)), srcs_hwrap(n, P.Filter{e, P.Opt.head(x, None{})}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Filter{e, x}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Filter{e, x}), acc)), Laws.srcs(Q.Exec.compile(P.Filter{e, x}, acc)), srcs_hwrap(n, P.Filter{e, x}, acc)) : {Laws.srcs(Q.Exec.compile(P.Opt.head(x, None{}), Q.IFilter{e} <> acc)) == _ : List<&2, String>}
      srcs_unary(x, n, None{}, Q.IFilter{e}, acc, Laws.head_pass_keeps_sources(x, None{}, Q.IFilter{e} <> acc))
    case P.Sort{+ks, +x}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Sort{ks, P.Opt.head(x, None{})}), acc)), Laws.srcs(Q.Exec.compile(P.Sort{ks, P.Opt.head(x, None{})}, acc)), srcs_hwrap(n, P.Sort{ks, P.Opt.head(x, None{})}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Sort{ks, x}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Sort{ks, x}), acc)), Laws.srcs(Q.Exec.compile(P.Sort{ks, x}, acc)), srcs_hwrap(n, P.Sort{ks, x}, acc)) : {Laws.srcs(Q.Exec.compile(P.Opt.head(x, None{}), Q.ISort{ks} <> acc)) == _ : List<&2, String>}
      srcs_unary(x, n, None{}, Q.ISort{ks}, acc, Laws.head_pass_keeps_sources(x, None{}, Q.ISort{ks} <> acc))
    case P.GroupBy{+ks, +ags, +mo, +x}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}), acc)), Laws.srcs(Q.Exec.compile(P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}, acc)), srcs_hwrap(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo, x}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo, x}), acc)), Laws.srcs(Q.Exec.compile(P.GroupBy{ks, ags, mo, x}, acc)), srcs_hwrap(n, P.GroupBy{ks, ags, mo, x}, acc)) : {Laws.srcs(Q.Exec.compile(P.Opt.head(x, None{}), Q.IGroupBy{ks, ags, mo} <> acc)) == _ : List<&2, String>}
      srcs_unary(x, n, None{}, Q.IGroupBy{ks, ags, mo}, acc, Laws.head_pass_keeps_sources(x, None{}, Q.IGroupBy{ks, ags, mo} <> acc))
    case P.Join{+how, +lo, +ro, +l, +r}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}), acc)), Laws.srcs(Q.Exec.compile(P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}, acc)), srcs_hwrap(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Join{how, lo, ro, l, r}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Join{how, lo, ro, l, r}), acc)), Laws.srcs(Q.Exec.compile(P.Join{how, lo, ro, l, r}, acc)), srcs_hwrap(n, P.Join{how, lo, ro, l, r}, acc)) : {Laws.srcs(Q.Exec.compile(P.Opt.head(l, None{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))) == _ : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.head(l, None{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))), Laws.srcs(Q.Exec.compile(P.Opt.hwrap(None{}, l), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))), Laws.head_pass_keeps_sources(l, None{}, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))) : {_ == Laws.srcs(Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(l, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))), List.append(&2, String, Laws.srcs(Q.Exec.compile(l, Nil{})), Laws.srcs(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))), srcs_compile(l, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))) : {_ == Laws.srcs(Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))), List.append(&2, String, Laws.srcs(Q.Exec.compile(l, Nil{})), Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))), srcs_compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(l, Nil{})), Laws.srcs(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc))) == _ : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> acc)), Laws.srcs(Q.Exec.compile(P.Opt.hwrap(None{}, r), Q.IJoin{how, lo, ro} <> acc)), Laws.head_pass_keeps_sources(r, None{}, Q.IJoin{how, lo, ro} <> acc)) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(l, Nil{})), _) == List.append(&2, String, Laws.srcs(Q.Exec.compile(l, Nil{})), Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> acc))) : List<&2, String>}
      {==}
    case P.Head{+m, +x}:
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.head(x, Some{P.Opt.hmin(m, n)}), acc)), Laws.srcs(Q.Exec.compile(P.Opt.hwrap(Some{P.Opt.hmin(m, n)}, x), acc)), Laws.head_pass_keeps_sources(x, Some{P.Opt.hmin(m, n)}, acc)) : {_ == Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Head{m, x}), acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.hwrap(n, P.Head{m, x}), acc)), Laws.srcs(Q.Exec.compile(P.Head{m, x}, acc)), srcs_hwrap(n, P.Head{m, x}, acc)) : {Laws.srcs(Q.Exec.compile(x, Q.IHead{P.Opt.hmin(m, n)} <> acc)) == _ : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(x, Q.IHead{P.Opt.hmin(m, n)} <> acc)), List.append(&2, String, Laws.srcs(Q.Exec.compile(x, Nil{})), Laws.srcs(Q.IHead{P.Opt.hmin(m, n)} <> acc)), srcs_compile(x, Q.IHead{P.Opt.hmin(m, n)} <> acc)) : {_ == Laws.srcs(Q.Exec.compile(x, Q.IHead{m} <> acc)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(x, Q.IHead{m} <> acc)), List.append(&2, String, Laws.srcs(Q.Exec.compile(x, Nil{})), Laws.srcs(Q.IHead{m} <> acc)), srcs_compile(x, Q.IHead{m} <> acc)) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(x, Nil{})), Laws.srcs(acc)) == _ : List<&2, String>}
      {==}

# ---- heads over frames and runner states (Sigma witnesses: the value comes back) ---------

def col_head_w(c: C.Column, +n: U32, +m: U32) -> &c2: C.Column -> {c2 == c : C.Column} & {C.Column.head(C.Column.head(c2, m), n) == C.Column.head(c2, U32.min(n, m)) : C.Column}:
  match c:
    case C.CBool{+len, +depth, valid, data}:
      (C.CBool{len, depth, valid, data}, {==}, (%Laws.u32_min_assoc(n, m, len) : {C.CBool{U32.min(n, U32.min(m, len)), depth, valid, data} == C.CBool{_, depth, valid, data} : C.Column}; {==}))
    case C.CU32{+len, +depth, valid, data}:
      (C.CU32{len, depth, valid, data}, {==}, (%Laws.u32_min_assoc(n, m, len) : {C.CU32{U32.min(n, U32.min(m, len)), depth, valid, data} == C.CU32{_, depth, valid, data} : C.Column}; {==}))
    case C.CI32{+len, +depth, valid, data}:
      (C.CI32{len, depth, valid, data}, {==}, (%Laws.u32_min_assoc(n, m, len) : {C.CI32{U32.min(n, U32.min(m, len)), depth, valid, data} == C.CI32{_, depth, valid, data} : C.Column}; {==}))
    case C.CF32{+len, +depth, valid, data}:
      (C.CF32{len, depth, valid, data}, {==}, (%Laws.u32_min_assoc(n, m, len) : {C.CF32{U32.min(n, U32.min(m, len)), depth, valid, data} == C.CF32{_, depth, valid, data} : C.Column}; {==}))
    case C.CStr{+len, +depth, valid, data}:
      (C.CStr{len, depth, valid, data}, {==}, (%Laws.u32_min_assoc(n, m, len) : {C.CStr{U32.min(n, U32.min(m, len)), depth, valid, data} == C.CStr{_, depth, valid, data} : C.Column}; {==}))

# a computed witness is taken apart in a helper's parameter (never in a let)
def cols_head_cons(+name: String, -col: C.Column, -rest: List<&1, C.Named>, +n: U32, +m: U32,
  wc: &c2: C.Column -> {c2 == col : C.Column} & {C.Column.head(C.Column.head(c2, m), n) == C.Column.head(c2, U32.min(n, m)) : C.Column},
  wcs: &cs: List<&1, C.Named> -> {cs == rest : List<&1, C.Named>} & {C.Cols.head(C.Cols.head(cs, m), n) == C.Cols.head(cs, U32.min(n, m)) : List<&1, C.Named>})
  -> &cs2: List<&1, C.Named> -> {cs2 == C.Named{name, col} <> rest : List<&1, C.Named>} & {C.Cols.head(C.Cols.head(cs2, m), n) == C.Cols.head(cs2, U32.min(n, m)) : List<&1, C.Named>}:
  (c2, ec, hc) = wc
  (cs, ecs, hcs) = wcs
  (C.Named{name, c2} <> cs, (%ec : {C.Named{name, c2} <> cs == C.Named{name, _} <> rest : List<&1, C.Named>}; %ecs : {C.Named{name, c2} <> cs == C.Named{name, c2} <> _ : List<&1, C.Named>}; {==}), (%hc : {C.Named{name, C.Column.head(C.Column.head(c2, m), n)} <> C.Cols.head(C.Cols.head(cs, m), n) == C.Named{name, _} <> C.Cols.head(cs, U32.min(n, m)) : List<&1, C.Named>}; %hcs : {C.Named{name, C.Column.head(C.Column.head(c2, m), n)} <> C.Cols.head(C.Cols.head(cs, m), n) == C.Named{name, C.Column.head(C.Column.head(c2, m), n)} <> _ : List<&1, C.Named>}; {==}))

def cols_head_w(cols: List<&1, C.Named>, +n: U32, +m: U32) -> &cs: List<&1, C.Named> -> {cs == cols : List<&1, C.Named>} & {C.Cols.head(C.Cols.head(cs, m), n) == C.Cols.head(cs, U32.min(n, m)) : List<&1, C.Named>}:
  match cols:
    case Nil{}:
      (Nil{}, {==}, {==})
    case C.Named{+name, col} <> rest:
      cols_head_cons(name, col, rest, n, m, col_head_w(col, n, m), cols_head_w(rest, n, m))

def frame_head_k(+h: U32, -cols: List<&1, C.Named>, +n: U32, +m: U32,
  wcs: &cs: List<&1, C.Named> -> {cs == cols : List<&1, C.Named>} & {C.Cols.head(C.Cols.head(cs, m), n) == C.Cols.head(cs, U32.min(n, m)) : List<&1, C.Named>})
  -> &f2: C.Frame -> {f2 == C.Frame{h, cols} : C.Frame} & {C.Frame.head(C.Frame.head(f2, m), n) == C.Frame.head(f2, U32.min(n, m)) : C.Frame}:
  (cs, ecs, hcs) = wcs
  (C.Frame{h, cs}, (%ecs : {C.Frame{h, cs} == C.Frame{h, _} : C.Frame}; {==}), (%Laws.u32_min_assoc(n, m, h) : {C.Frame{U32.min(n, U32.min(m, h)), C.Cols.head(C.Cols.head(cs, m), n)} == C.Frame{_, C.Cols.head(cs, U32.min(n, m))} : C.Frame}; %hcs : {C.Frame{U32.min(n, U32.min(m, h)), C.Cols.head(C.Cols.head(cs, m), n)} == C.Frame{U32.min(n, U32.min(m, h)), _} : C.Frame}; {==}))

def frame_head_w(f: C.Frame, +n: U32, +m: U32) -> &f2: C.Frame -> {f2 == f : C.Frame} & {C.Frame.head(C.Frame.head(f2, m), n) == C.Frame.head(f2, U32.min(n, m)) : C.Frame}:
  match f:
    case C.Frame{+h, cols}:
      frame_head_k(h, cols, n, m, cols_head_w(cols, n, m))

def frame_head_fin(-f: C.Frame, +n: U32, +m: U32, w: &f2: C.Frame -> {f2 == f : C.Frame} & {C.Frame.head(C.Frame.head(f2, m), n) == C.Frame.head(f2, U32.min(n, m)) : C.Frame}) -> {C.Frame.head(C.Frame.head(f, m), n) == C.Frame.head(f, U32.min(n, m)) : C.Frame}:
  (f2, ef, hf) = w
  %ef : {C.Frame.head(C.Frame.head(_, m), n) == C.Frame.head(_, U32.min(n, m)) : C.Frame}
  hf

def Laws.frame_head_head(f, n, m):
  frame_head_fin(f, n, m, frame_head_w(f, n, m))

def head_step_k(env: P.Env, -f: C.Frame, t: List<&1, C.Frame>, +n: U32, +m: U32,
  wf: &f2: C.Frame -> {f2 == f : C.Frame} & {C.Frame.head(C.Frame.head(f2, m), n) == C.Frame.head(f2, U32.min(n, m)) : C.Frame})
  -> &s: Q.St -> {s == Q.St{env, Done{f <> t}} : Q.St} & {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, s)) == Q.Exec.step(Q.IHead{U32.min(n, m)}, s) : Q.St}:
  (f2, ef, hf) = wf
  (Q.St{env, Done{f2 <> t}}, (%ef : {Q.St{env, Done{f2 <> t}} == Q.St{env, Done{_ <> t}} : Q.St}; {==}), (%hf : {Q.St{env, Done{C.Frame.head(C.Frame.head(f2, m), n) <> t}} == Q.St{env, Done{_ <> t}} : Q.St}; {==}))

# IHead m then IHead n is IHead min(n, m) on any state; the state comes back
def head_step_w(+n: U32, +m: U32, st: Q.St) -> &s: Q.St -> {s == st : Q.St} & {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, s)) == Q.Exec.step(Q.IHead{U32.min(n, m)}, s) : Q.St}:
  match st:
    case Q.St{env, r}:
      match r:
        case Fail{e}:
          (Q.St{env, Fail{e}}, {==}, {==})
        case Done{stack}:
          match stack:
            case Nil{}:
              (Q.St{env, Done{Nil{}}}, {==}, {==})
            case f <> t:
              head_step_k(env, f, t, n, m, frame_head_w(f, n, m))

def head_step_fin(-st: Q.St, +n: U32, +m: U32, w: &s: Q.St -> {s == st : Q.St} & {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, s)) == Q.Exec.step(Q.IHead{U32.min(n, m)}, s) : Q.St}) -> {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, st)) == Q.Exec.step(Q.IHead{U32.min(n, m)}, st) : Q.St}:
  (s, es, hs) = w
  %es : {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, _)) == Q.Exec.step(Q.IHead{U32.min(n, m)}, _) : Q.St}
  hs

def Laws.head_step(n, m, st):
  head_step_fin(st, n, m, head_step_w(n, m, st))

# ---- running two codes after a common prefix: the state is consumed once ---------------------

def loop_pre(w: List<&2, Q.Instr>, +b1: List<&2, Q.Instr>, +b2: List<&2, Q.Instr>, st: Q.St, h: @s: Q.St -> {Q.Exec.loop(b1, s) == Q.Exec.loop(b2, s) : Q.St}) -> {Q.Exec.loop(List.append(&2, Q.Instr, w, b1), st) == Q.Exec.loop(List.append(&2, Q.Instr, w, b2), st) : Q.St}:
  match w:
    case Nil{}:
      h(st)
    case i <> t:
      loop_pre(t, b1, b2, Q.Exec.step(i, st), h)

# the same code for a plan, followed by two suffixes that read the same Sources
# and run alike: the whole runs alike
def run_suffix(+x: P.Plan, +b1: List<&2, Q.Instr>, +b2: List<&2, Q.Instr>, env: P.Env, hs: {Laws.srcs(b1) == Laws.srcs(b2) : List<&2, String>}, h: @s: Q.St -> {Q.Exec.loop(Q.Exec.mark(b1), s) == Q.Exec.loop(Q.Exec.mark(b2), s) : Q.St})
  -> {Q.Exec.run_code(Q.Exec.mark(Q.Exec.compile(x, b1)), env) == Q.Exec.run_code(Q.Exec.mark(Q.Exec.compile(x, b2)), env) : E.ResT(C.Frame)}:
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, b1), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), b1), compile_app(x, b1)) : {Q.Exec.run_code(Q.Exec.mark(_), env) == Q.Exec.run_code(Q.Exec.mark(Q.Exec.compile(x, b2)), env) : E.ResT(C.Frame)}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, b2), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), b2), compile_app(x, b2)) : {Q.Exec.run_code(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), b1)), env) == Q.Exec.run_code(Q.Exec.mark(_), env) : E.ResT(C.Frame)}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), b1)), List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), b1), Q.Exec.mark(b1)), mark_app(Q.Exec.compile(x, Nil{}), b1)) : {Q.Exec.run_code(_, env) == Q.Exec.run_code(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), b2)), env) : E.ResT(C.Frame)}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), b2)), List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), b2), Q.Exec.mark(b2)), mark_app(Q.Exec.compile(x, Nil{}), b2)) : {Q.Exec.run_code(List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), b1), Q.Exec.mark(b1)), env) == Q.Exec.run_code(_, env) : E.ResT(C.Frame)}
  %markw_ext(Q.Exec.compile(x, Nil{}), b1, b2, hs) : {Q.Exec.run_code(List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), b1), Q.Exec.mark(b1)), env) == Q.Exec.run_code(List.append(&2, Q.Instr, _, Q.Exec.mark(b2)), env) : E.ResT(C.Frame)}
  Equal.cong(Q.St, E.ResT(C.Frame), s => Q.Exec.fin(s), Q.Exec.loop(List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), b1), Q.Exec.mark(b1)), Q.St{env, Done{Nil{}}}), Q.Exec.loop(List.append(&2, Q.Instr, Laws.markw(Q.Exec.compile(x, Nil{}), b1), Q.Exec.mark(b2)), Q.St{env, Done{Nil{}}}), loop_pre(Laws.markw(Q.Exec.compile(x, Nil{}), b1), Q.Exec.mark(b1), Q.Exec.mark(b2), Q.St{env, Done{Nil{}}}, h))

# ---- R1, the rule -----------------------------------------------------------------------------

# IHead m then IHead n run as the merged IHead Opt.hmin(m, Some n)
def two_heads(+n: U32, +m: U32, s: Q.St) -> {Q.Exec.loop(Q.IHead{m} <> Q.IHead{n} <> Nil{}, s) == Q.Exec.loop(Q.IHead{P.Opt.hmin(m, Some{n})} <> Nil{}, s) : Q.St}:
  %Laws.u32_min_comm(n, m) : {Q.Exec.step(Q.IHead{n}, Q.Exec.step(Q.IHead{m}, s)) == Q.Exec.step(Q.IHead{_}, s) : Q.St}
  Laws.head_step(n, m, s)

def Laws.head_merge_run(x, n, m, env):
  run_suffix(x, Q.IHead{m} <> Q.IHead{n} <> Nil{}, Q.IHead{P.Opt.hmin(m, Some{n})} <> Nil{}, env, {==}, s => two_heads(n, m, s))

# ---- R1, the pass (merge-only fragment) -------------------------------------------------------

# the step of head_pass_run at a barrier node: the Opt.head output and the plan
# both compile to the sub-plan's code followed by the node's instruction and the
# pending head, so the induction hypothesis applies with a longer suffix
def pass_unary(+x: P.Plan, +n: Maybe<&2, U32>, +i: Q.Instr, +s1: List<&2, Q.Instr>, +s2: List<&2, Q.Instr>, -st: Q.St,
  ih: {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), List.append(&2, Q.Instr, i <> Laws.hcode(n), s1))), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), i <> s2)), st) : Q.St})
  -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), i <> Laws.hcode(n)), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, i <> Nil{}), s2)), st) : Q.St}:
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.head(x, None{}), i <> Laws.hcode(n)), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), i <> Laws.hcode(n)), compile_app(P.Opt.head(x, None{}), i <> Laws.hcode(n))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, i <> Nil{}), s2)), st) : Q.St}
  %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, i <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), i <> Nil{}), compile_app(x, i <> Nil{})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), i <> Laws.hcode(n)), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
  %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), i <> Laws.hcode(n)), s1), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), List.append(&2, Q.Instr, i <> Laws.hcode(n), s1)), app_assoc(Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), i <> Laws.hcode(n), s1)) : {Q.Exec.loop(Q.Exec.mark(_), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), i <> Nil{}), s2)), st) : Q.St}
  %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), i <> Nil{}), s2), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, i <> Nil{}, s2)), app_assoc(Q.Exec.compile(x, Nil{}), i <> Nil{}, s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, None{}), Nil{}), List.append(&2, Q.Instr, i <> Laws.hcode(n), s1))), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
  ih

# the Some{k} case of pass_head_rf: the two heads k and m on the state witness s3 are
# one head min(m, k), then the parent's hypothesis applies after IHead m
def pass_head_some(+k: U32, +m: U32, +s1: List<&2, Q.Instr>, +s2: List<&2, Q.Instr>, -s: Q.St,
  w: &s3: Q.St -> {s3 == s : Q.St} & {Q.Exec.step(Q.IHead{k}, Q.Exec.step(Q.IHead{m}, s3)) == Q.Exec.step(Q.IHead{U32.min(k, m)}, s3) : Q.St},
  rf: @s0: Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.IHead{k} <> Nil{}, s1)), s0) == Q.Exec.loop(Q.Exec.mark(s2), s0) : Q.St})
  -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.IHead{U32.min(m, k)} <> Nil{}, s1)), s) == Q.Exec.loop(Q.Exec.mark(Q.IHead{m} <> s2), s) : Q.St}:
  (s3, es, hs) = w
  %es : {Q.Exec.loop(Q.Exec.mark(s1), Q.Exec.step(Q.IHead{U32.min(m, k)}, _)) == Q.Exec.loop(Q.Exec.mark(s2), Q.Exec.step(Q.IHead{m}, _)) : Q.St}
  %Laws.u32_min_comm(k, m) : {Q.Exec.loop(Q.Exec.mark(s1), Q.Exec.step(Q.IHead{_}, s3)) == Q.Exec.loop(Q.Exec.mark(s2), Q.Exec.step(Q.IHead{m}, s3)) : Q.St}
  %hs : {Q.Exec.loop(Q.Exec.mark(s1), _) == Q.Exec.loop(Q.Exec.mark(s2), Q.Exec.step(Q.IHead{m}, s3)) : Q.St}
  rf(Q.Exec.step(Q.IHead{m}, s3))

# the suffix hypothesis for a Head{m} child: "hcode(Some hmin(m, n)) then s1" runs
# like "IHead m then s2" from any state, given the parent's hypothesis
def pass_head_rf(+n: Maybe<&2, U32>, +m: U32, +s1: List<&2, Q.Instr>, +s2: List<&2, Q.Instr>, s: Q.St,
  rf: @s0: Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), s0) == Q.Exec.loop(Q.Exec.mark(s2), s0) : Q.St})
  -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(Some{P.Opt.hmin(m, n)}), s1)), s) == Q.Exec.loop(Q.Exec.mark(Q.IHead{m} <> s2), s) : Q.St}:
  match n:
    case None{}:
      rf(Q.Exec.step(Q.IHead{m}, s))
    case Some{+k}:
      pass_head_some(k, m, s1, s2, s, head_step_w(k, m, s), rf)

# the Sources hypothesis for a Head{m} child
def pass_head_rs(+n: Maybe<&2, U32>, -m: U32, +s1: List<&2, Q.Instr>, -s2: List<&2, Q.Instr>, rs: {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s1)) == Laws.srcs(s2) : List<&2, String>}) -> {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(Some{P.Opt.hmin(m, n)}), s1)) == Laws.srcs(Q.IHead{m} <> s2) : List<&2, String>}:
  %srcs_hcode(n, s1) : {_ == Laws.srcs(s2) : List<&2, String>}
  rs

# the Sources hypothesis for the left input of a Join: the right input's code
# (rewritten or not) then IJoin, the pending head and the suffix
def pass_join_rs(+r: P.Plan, +how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, +n: Maybe<&2, U32>, +s1: List<&2, Q.Instr>, +s2: List<&2, Q.Instr>, rs: {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s1)) == Laws.srcs(s2) : List<&2, String>})
  -> {Laws.srcs(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)) == Laws.srcs(List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)), List.append(&2, String, Laws.srcs(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), Laws.srcs(s1)), srcs_app(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)) : {_ == Laws.srcs(List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)), List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), Laws.srcs(s2)), srcs_app(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), Laws.srcs(s1)) == _ : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), Laws.srcs(Q.Exec.compile(P.Opt.hwrap(None{}, r), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), Laws.head_pass_keeps_sources(r, None{}, Q.IJoin{how, lo, ro} <> Laws.hcode(n))) : {List.append(&2, String, _, Laws.srcs(s1)) == List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), Laws.srcs(s2)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Laws.hcode(n))), List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(Q.IJoin{how, lo, ro} <> Laws.hcode(n))), srcs_compile(r, Q.IJoin{how, lo, ro} <> Laws.hcode(n))) : {List.append(&2, String, _, Laws.srcs(s1)) == List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), Laws.srcs(s2)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(Q.IJoin{how, lo, ro} <> Nil{})), srcs_compile(r, Q.IJoin{how, lo, ro} <> Nil{})) : {List.append(&2, String, List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(Q.IJoin{how, lo, ro} <> Laws.hcode(n))), Laws.srcs(s1)) == List.append(&2, String, _, Laws.srcs(s2)) : List<&2, String>}
  %Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(Laws.hcode(n))), Laws.srcs(s1)), List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), List.append(&2, String, Laws.srcs(Laws.hcode(n)), Laws.srcs(s1))), sapp_assoc(Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(Laws.hcode(n)), Laws.srcs(s1))) : {_ == List.append(&2, String, List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Nil{}), Laws.srcs(s2)) : List<&2, String>}
  %Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Nil{}), Laws.srcs(s2)), List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), List.append(&2, String, Nil{}, Laws.srcs(s2))), sapp_assoc(Laws.srcs(Q.Exec.compile(r, Nil{})), Nil{}, Laws.srcs(s2))) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), List.append(&2, String, Laws.srcs(Laws.hcode(n)), Laws.srcs(s1))) == _ : List<&2, String>}
  %srcs_app(Laws.hcode(n), s1) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), _) == List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(s2)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s1)), Laws.srcs(s2), rs) : {List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), _) == List.append(&2, String, Laws.srcs(Q.Exec.compile(r, Nil{})), Laws.srcs(s2)) : List<&2, String>}
  {==}

# the Select / WithColumns barrier: Opt.sinks is False, so the pending head stays above
def hstop_barrier(+ok: Bool, +n: Maybe<&2, U32>, nok: {ok == False{} : Bool}) -> {P.Opt.hstop(ok, n) == n : Maybe<&2, U32>}:
  %Equal.sym(Bool, ok, False{}, nok) : {P.Opt.hstop(_, n) == n : Maybe<&2, U32>}
  {==}

def hpass_barrier(+ok: Bool, +n: Maybe<&2, U32>, nok: {ok == False{} : Bool}) -> {P.Opt.hpass(ok, n) == None{} : Maybe<&2, U32>}:
  %Equal.sym(Bool, ok, False{}, nok) : {P.Opt.hpass(_, n) == None{} : Maybe<&2, U32>}
  {==}

# the Opt.sinks certificate of a barrier node is False
def sinks_false(+es: List<&2, X.Expr>, +x: P.Plan, +mo: {Bool.and(Bool.not(P.Opt.sinks(es, P.Plan.schema(x))), Laws.merge_only(x)) == True{} : Bool}) -> {P.Opt.sinks(es, P.Plan.schema(x)) == False{} : Bool}:
  L.not_true(P.Opt.sinks(es, P.Plan.schema(x)), L.and_left(Bool.not(P.Opt.sinks(es, P.Plan.schema(x))), Laws.merge_only(x), mo))

def Laws.head_pass_run(p, n, s1, s2, st, mo, rs, rf):
  match p:
    case P.ScanCsv{path, o, s}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.ScanCsv{path, o, s}), Nil{}), Q.Exec.compile(P.ScanCsv{path, o, s}, Laws.hcode(n)), compile_hwrap(n, P.ScanCsv{path, o, s})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.IScan{path, o, s} <> Nil{}, s2)), st) : Q.St}
      rf(Q.Exec.step(Q.IScan{path, o, s}, st))
    case P.Source{+nm, s}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Source{nm, s}), Nil{}), Q.Exec.compile(P.Source{nm, s}, Laws.hcode(n)), compile_hwrap(n, P.Source{nm, s})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.ISource{nm, s, True{}} <> Nil{}, s2)), st) : Q.St}
      %Equal.sym(Bool, Q.Exec.later(List.append(&2, Q.Instr, Laws.hcode(n), s1), nm), Q.Exec.later(s2, nm), later_ext(List.append(&2, Q.Instr, Laws.hcode(n), s1), s2, nm, rs)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), Q.Exec.step(Q.ISource{nm, s, Bool.not(_)}, st)) == Q.Exec.loop(Q.Exec.mark(s2), Q.Exec.step(Q.ISource{nm, s, Bool.not(Q.Exec.later(s2, nm))}, st)) : Q.St}
      rf(Q.Exec.step(Q.ISource{nm, s, Bool.not(Q.Exec.later(s2, nm))}, st))
    case P.Select{+es, +x}:
      %Equal.sym(Maybe<&2, U32>, P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), n, hstop_barrier(P.Opt.sinks(es, P.Plan.schema(x)), n, sinks_false(es, x, mo))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hwrap(_, P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Select{es, x}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(Maybe<&2, U32>, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n), None{}, hpass_barrier(P.Opt.sinks(es, P.Plan.schema(x)), n, sinks_false(es, x, mo))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, P.Opt.head(x, _)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Select{es, x}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, P.Opt.head(x, None{})}), Nil{}), Q.Exec.compile(P.Select{es, P.Opt.head(x, None{})}, Laws.hcode(n)), compile_hwrap(n, P.Select{es, P.Opt.head(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Select{es, x}, Nil{}), s2)), st) : Q.St}
      pass_unary(x, n, Q.ISelect{es}, s1, s2, st, Laws.head_pass_run(x, None{}, List.append(&2, Q.Instr, Q.ISelect{es} <> Laws.hcode(n), s1), Q.ISelect{es} <> s2, st, L.and_right(Bool.not(P.Opt.sinks(es, P.Plan.schema(x))), Laws.merge_only(x), mo), rs, s0 => rf(Q.Exec.step(Q.ISelect{es}, s0))))
    case P.WithColumns{+es, +x}:
      %Equal.sym(Maybe<&2, U32>, P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), n, hstop_barrier(P.Opt.sinks(es, P.Plan.schema(x)), n, sinks_false(es, x, mo))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hwrap(_, P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.WithColumns{es, x}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(Maybe<&2, U32>, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n), None{}, hpass_barrier(P.Opt.sinks(es, P.Plan.schema(x)), n, sinks_false(es, x, mo))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hwrap(n, P.WithColumns{es, P.Opt.head(x, _)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.WithColumns{es, x}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.WithColumns{es, P.Opt.head(x, None{})}), Nil{}), Q.Exec.compile(P.WithColumns{es, P.Opt.head(x, None{})}, Laws.hcode(n)), compile_hwrap(n, P.WithColumns{es, P.Opt.head(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.WithColumns{es, x}, Nil{}), s2)), st) : Q.St}
      pass_unary(x, n, Q.IWith{es}, s1, s2, st, Laws.head_pass_run(x, None{}, List.append(&2, Q.Instr, Q.IWith{es} <> Laws.hcode(n), s1), Q.IWith{es} <> s2, st, L.and_right(Bool.not(P.Opt.sinks(es, P.Plan.schema(x))), Laws.merge_only(x), mo), rs, s0 => rf(Q.Exec.step(Q.IWith{es}, s0))))
    case P.Filter{+e, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Filter{e, P.Opt.head(x, None{})}), Nil{}), Q.Exec.compile(P.Filter{e, P.Opt.head(x, None{})}, Laws.hcode(n)), compile_hwrap(n, P.Filter{e, P.Opt.head(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Filter{e, x}, Nil{}), s2)), st) : Q.St}
      pass_unary(x, n, Q.IFilter{e}, s1, s2, st, Laws.head_pass_run(x, None{}, List.append(&2, Q.Instr, Q.IFilter{e} <> Laws.hcode(n), s1), Q.IFilter{e} <> s2, st, mo, rs, s0 => rf(Q.Exec.step(Q.IFilter{e}, s0))))
    case P.Sort{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Sort{ks, P.Opt.head(x, None{})}), Nil{}), Q.Exec.compile(P.Sort{ks, P.Opt.head(x, None{})}, Laws.hcode(n)), compile_hwrap(n, P.Sort{ks, P.Opt.head(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Sort{ks, x}, Nil{}), s2)), st) : Q.St}
      pass_unary(x, n, Q.ISort{ks}, s1, s2, st, Laws.head_pass_run(x, None{}, List.append(&2, Q.Instr, Q.ISort{ks} <> Laws.hcode(n), s1), Q.ISort{ks} <> s2, st, mo, rs, s0 => rf(Q.Exec.step(Q.ISort{ks}, s0))))
    case P.GroupBy{+ks, +ags, +mo2, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo2, P.Opt.head(x, None{})}), Nil{}), Q.Exec.compile(P.GroupBy{ks, ags, mo2, P.Opt.head(x, None{})}, Laws.hcode(n)), compile_hwrap(n, P.GroupBy{ks, ags, mo2, P.Opt.head(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.GroupBy{ks, ags, mo2, x}, Nil{}), s2)), st) : Q.St}
      pass_unary(x, n, Q.IGroupBy{ks, ags, mo2}, s1, s2, st, Laws.head_pass_run(x, None{}, List.append(&2, Q.Instr, Q.IGroupBy{ks, ags, mo2} <> Laws.hcode(n), s1), Q.IGroupBy{ks, ags, mo2} <> s2, st, mo, rs, s0 => rf(Q.Exec.step(Q.IGroupBy{ks, ags, mo2}, s0))))
    case P.Join{+how, +lo, +ro, +l, +r}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}), Nil{}), Q.Exec.compile(P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}, Laws.hcode(n)), compile_hwrap(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Join{how, lo, ro, l, r}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.head(l, None{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(l, None{}), Nil{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), compile_app(P.Opt.head(l, None{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), compile_app(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(l, None{}), Nil{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(l, None{}), Nil{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), s1), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)), app_assoc(Q.Exec.compile(P.Opt.head(l, None{}), Nil{}), Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)) : {Q.Exec.loop(Q.Exec.mark(_), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)), app_assoc(Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1))), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      Laws.head_pass_run(l, None{}, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2), st, L.and_left(Laws.merge_only(l), Laws.merge_only(r), mo), pass_join_rs(r, how, lo, ro, n, s1, s2, rs), s0 => pass_unary(r, n, Q.IJoin{how, lo, ro}, s1, s2, s0, Laws.head_pass_run(r, None{}, List.append(&2, Q.Instr, Q.IJoin{how, lo, ro} <> Laws.hcode(n), s1), Q.IJoin{how, lo, ro} <> s2, s0, L.and_right(Laws.merge_only(l), Laws.merge_only(r), mo), rs, s3 => rf(Q.Exec.step(Q.IJoin{how, lo, ro}, s3)))))
    case P.Head{+m, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IHead{m} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}), compile_app(x, Q.IHead{m} <> Nil{})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, Some{P.Opt.hmin(m, n)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}), s2), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IHead{m} <> Nil{}, s2)), app_assoc(Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}, s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(x, Some{P.Opt.hmin(m, n)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      Laws.head_pass_run(x, Some{P.Opt.hmin(m, n)}, s1, Q.IHead{m} <> s2, st, mo, pass_head_rs(n, m, s1, s2, rs), s0 => pass_head_rf(n, m, s1, s2, s0, rf))

# ---- G6 on the R1 fragment ------------------------------------------------------------------------

def Laws.release_merge_only(p, s, env, ok, mo):
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {Q.Exec.run_pure(P.Optimize.release.k(_, p), env) == Q.Exec.run_pure(p, env) : E.ResT(C.Frame)}
  %app_nil(Q.Exec.compile(P.Opt.head(p, None{}), Nil{})) : {Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(_), Q.St{env, Done{Nil{}}})) == Q.Exec.run_pure(p, env) : E.ResT(C.Frame)}
  %app_nil(Q.Exec.compile(p, Nil{})) : {Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(p, None{}), Nil{}), Nil{})), Q.St{env, Done{Nil{}}})) == Q.Exec.fin(Q.Exec.loop(Q.Exec.mark(_), Q.St{env, Done{Nil{}}})) : E.ResT(C.Frame)}
  Equal.cong(Q.St, E.ResT(C.Frame), st => Q.Exec.fin(st), Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.head(p, None{}), Nil{}), Nil{})), Q.St{env, Done{Nil{}}}), Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(p, Nil{}), Nil{})), Q.St{env, Done{Nil{}}}), Laws.head_pass_run(p, None{}, Nil{}, Nil{}, Q.St{env, Done{Nil{}}}, mo, {==}, s0 => {==}))

def Laws.release_merge_only_obs(p, s, env, ok, mo):
  Equal.cong(E.ResT(C.Frame), String, r => DP.Dump.result(r), Q.Exec.run_pure(P.Optimize.release(p), env), Q.Exec.run_pure(p, env), Laws.release_merge_only(p, s, env, ok, mo))
