# T5 mutation (plan M_01 section 4): a disposable copy of the release optimizer's head
# pass Opt.hmerge with the WRONG rule at Select: the pending limit sinks below EVERY
# Select, certificate or not (so Head{0, Select{[sum(a)], x}} would recompute the sum over
# no rows, B01-a / B01-f). The real proof term of LAWS.bend section 8 `hmerge_run`
# (PROOF_exec.bend) must be refused for the mutated pass: Bend answers SOME PROOFS FAIL
# with the mutated plan in `expected` and the Head-above-Select plan the real rule keeps
# in `observed`. The positive control hmerge_run_copy states the theorem over the real
# P.Opt.hmerge with the same term and checks, so only the mutation is reported.
import Base
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../../src/expr.bend as X
import ./../../src/sort.bend as O
import ./../../src/join.bend as J
import ./../../src/plan.bend as P
import ./../../src/exec.bend as Q
import ./../../LAWS.bend as Laws
import ./../../PROOF_lib.bend as L
import ./../../PROOF_exec.bend as PE

# the production pass, as in src/plan.bend
law hmerge_run_copy:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +s1: List<&2, Q.Instr>
  for +s2: List<&2, Q.Instr>
  for st: Q.St
  for +rs: {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s1)) == Laws.srcs(s2) : List<&2, String>}
  for rf: @s: Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), s) == Q.Exec.loop(Q.Exec.mark(s2), s) : Q.St}
  {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(p, n), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(p, Nil{}), s2)), st) : Q.St}

def hmerge_run_copy(p, n, s1, s2, st, rs, rf):
  match p:
    case P.ScanCsv{path, o, s}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.ScanCsv{path, o, s}), Nil{}), Q.Exec.compile(P.ScanCsv{path, o, s}, Laws.hcode(n)), PE.compile_hwrap(n, P.ScanCsv{path, o, s})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.IScan{path, o, s} <> Nil{}, s2)), st) : Q.St}
      rf(Q.Exec.step(Q.IScan{path, o, s}, st))
    case P.Source{+nm, s}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Source{nm, s}), Nil{}), Q.Exec.compile(P.Source{nm, s}, Laws.hcode(n)), PE.compile_hwrap(n, P.Source{nm, s})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.ISource{nm, s, True{}} <> Nil{}, s2)), st) : Q.St}
      %Equal.sym(Bool, Q.Exec.later(List.append(&2, Q.Instr, Laws.hcode(n), s1), nm), Q.Exec.later(s2, nm), PE.later_ext(List.append(&2, Q.Instr, Laws.hcode(n), s1), s2, nm, rs)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), Q.Exec.step(Q.ISource{nm, s, Bool.not(_)}, st)) == Q.Exec.loop(Q.Exec.mark(s2), Q.Exec.step(Q.ISource{nm, s, Bool.not(Q.Exec.later(s2, nm))}, st)) : Q.St}
      rf(Q.Exec.step(Q.ISource{nm, s, Bool.not(Q.Exec.later(s2, nm))}, st))
    case P.Select{+es, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Select{es, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Select{es, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Select{es, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ISelect{es}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ISelect{es} <> Laws.hcode(n), s1), Q.ISelect{es} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ISelect{es}, s0))))
    case P.WithColumns{+es, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.WithColumns{es, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.WithColumns{es, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.WithColumns{es, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.WithColumns{es, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.IWith{es}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.IWith{es} <> Laws.hcode(n), s1), Q.IWith{es} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.IWith{es}, s0))))
    case P.Filter{+e, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Filter{e, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Filter{e, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Filter{e, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Filter{e, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.IFilter{e}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.IFilter{e} <> Laws.hcode(n), s1), Q.IFilter{e} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.IFilter{e}, s0))))
    case P.Sort{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Sort{ks, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Sort{ks, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Sort{ks, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Sort{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ISort{ks}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ISort{ks} <> Laws.hcode(n), s1), Q.ISort{ks} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ISort{ks}, s0))))
    case P.Drop{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Drop{ks, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Drop{ks, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Drop{ks, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Drop{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TDrop{ks}}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TDrop{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TDrop{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TDrop{ks}}, s0))))
    case P.Rename{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Rename{ks, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Rename{ks, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Rename{ks, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Rename{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TRename{ks}}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TRename{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TRename{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TRename{ks}}, s0))))
    case P.Slice{+ks, +kl, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Slice{ks, kl, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Slice{ks, kl, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Slice{ks, kl, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Slice{ks, kl, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TSlice{ks, kl}}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TSlice{ks, kl}} <> Laws.hcode(n), s1), Q.ITable{Q.TSlice{ks, kl}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TSlice{ks, kl}}, s0))))
    case P.Tail{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Tail{ks, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Tail{ks, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Tail{ks, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Tail{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TTail{ks}}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TTail{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TTail{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TTail{ks}}, s0))))
    case P.Unique{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Unique{ks, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Unique{ks, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Unique{ks, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Unique{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TUnique{ks}}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TUnique{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TUnique{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TUnique{ks}}, s0))))
    case P.GroupBy{+ks, +ags, +mo2, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo2, P.Opt.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.GroupBy{ks, ags, mo2, P.Opt.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.GroupBy{ks, ags, mo2, P.Opt.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.GroupBy{ks, ags, mo2, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.IGroupBy{ks, ags, mo2}, s1, s2, st, hmerge_run_copy(x, None{}, List.append(&2, Q.Instr, Q.IGroupBy{ks, ags, mo2} <> Laws.hcode(n), s1), Q.IGroupBy{ks, ags, mo2} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.IGroupBy{ks, ags, mo2}, s0))))
    case P.Join{+how, +lo, +ro, +l, +r}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Join{how, lo, ro, P.Opt.hmerge(l, None{}), P.Opt.hmerge(r, None{})}), Nil{}), Q.Exec.compile(P.Join{how, lo, ro, P.Opt.hmerge(l, None{}), P.Opt.hmerge(r, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Join{how, lo, ro, P.Opt.hmerge(l, None{}), P.Opt.hmerge(r, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Join{how, lo, ro, l, r}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hmerge(l, None{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), PE.compile_app(P.Opt.hmerge(l, None{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), PE.compile_app(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), s1), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)), PE.app_assoc(Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)) : {Q.Exec.loop(Q.Exec.mark(_), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)), PE.app_assoc(Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1))), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      hmerge_run_copy(l, None{}, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2), st, PE.pass_join_rs_m(r, how, lo, ro, n, s1, s2, rs), s0 => PE.pass_unary_m(r, n, Q.IJoin{how, lo, ro}, s1, s2, s0, hmerge_run_copy(r, None{}, List.append(&2, Q.Instr, Q.IJoin{how, lo, ro} <> Laws.hcode(n), s1), Q.IJoin{how, lo, ro} <> s2, s0, rs, s3 => rf(Q.Exec.step(Q.IJoin{how, lo, ro}, s3)))))
    case P.Concat{+ci, +l, +r}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Concat{ci, P.Opt.hmerge(l, None{}), P.Opt.hmerge(r, None{})}), Nil{}), Q.Exec.compile(P.Concat{ci, P.Opt.hmerge(l, None{}), P.Opt.hmerge(r, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Concat{ci, P.Opt.hmerge(l, None{}), P.Opt.hmerge(r, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Concat{ci, l, r}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hmerge(l, None{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), PE.compile_app(P.Opt.hmerge(l, None{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), PE.compile_app(l, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), s1), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1)), PE.app_assoc(Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1)) : {Q.Exec.loop(Q.Exec.mark(_), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), s2), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}), s2)), PE.app_assoc(Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}), s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1))), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      hmerge_run_copy(l, None{}, List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}), s2), st, PE.pass_concat_rs_m(r, ci, n, s1, s2, rs), s0 => PE.pass_unary_m(r, n, Q.IConcat{ci}, s1, s2, s0, hmerge_run_copy(r, None{}, List.append(&2, Q.Instr, Q.IConcat{ci} <> Laws.hcode(n), s1), Q.IConcat{ci} <> s2, s0, rs, s3 => rf(Q.Exec.step(Q.IConcat{ci}, s3)))))
    case P.Head{+m, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IHead{m} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}), PE.compile_app(x, Q.IHead{m} <> Nil{})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(x, Some{P.Opt.hmin(m, n)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}), s2), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IHead{m} <> Nil{}, s2)), PE.app_assoc(Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}, s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hmerge(x, Some{P.Opt.hmin(m, n)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      hmerge_run_copy(x, Some{P.Opt.hmin(m, n)}, s1, Q.IHead{m} <> s2, st, PE.pass_head_rs(n, m, s1, s2, rs), s0 => PE.pass_head_rf(n, m, s1, s2, s0, rf))

# MUTATED copy of Opt.hmerge: a Select never stops the pending limit
def Mut.hmerge(p: P.Plan, n: Maybe<&2, U32>) -> P.Plan:
  match p:
    case P.ScanCsv{path, o, s}:
      P.Opt.hwrap(n, P.ScanCsv{path, o, s})
    case P.Source{nm, s}:
      P.Opt.hwrap(n, P.Source{nm, s})
    case P.Select{es, x}:
      P.Select{es, Mut.hmerge(x, n)}
    case P.WithColumns{es, x}:
      P.Opt.hwrap(n, P.WithColumns{es, Mut.hmerge(x, None{})})
    case P.Filter{e, x}:
      P.Opt.hwrap(n, P.Filter{e, Mut.hmerge(x, None{})})
    case P.Sort{ks, x}:
      P.Opt.hwrap(n, P.Sort{ks, Mut.hmerge(x, None{})})
    case P.GroupBy{ks, as, mo, x}:
      P.Opt.hwrap(n, P.GroupBy{ks, as, mo, Mut.hmerge(x, None{})})
    case P.Join{how, lo, ro, l, r}:
      P.Opt.hwrap(n, P.Join{how, lo, ro, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})})
    case P.Head{m, x}:
      Mut.hmerge(x, Some{P.Opt.hmin(m, n)})
    case P.Drop{ns, x}:
      P.Opt.hwrap(n, P.Drop{ns, Mut.hmerge(x, None{})})
    case P.Rename{ps, x}:
      P.Opt.hwrap(n, P.Rename{ps, Mut.hmerge(x, None{})})
    case P.Slice{o, l, x}:
      P.Opt.hwrap(n, P.Slice{o, l, Mut.hmerge(x, None{})})
    case P.Tail{m, x}:
      P.Opt.hwrap(n, P.Tail{m, Mut.hmerge(x, None{})})
    case P.Unique{ss, x}:
      P.Opt.hwrap(n, P.Unique{ss, Mut.hmerge(x, None{})})
    case P.Concat{i, l, r}:
      P.Opt.hwrap(n, P.Concat{i, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})})

law hmerge_run_mutated:
  for p: P.Plan
  for +n: Maybe<&2, U32>
  for +s1: List<&2, Q.Instr>
  for +s2: List<&2, Q.Instr>
  for st: Q.St
  for +rs: {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s1)) == Laws.srcs(s2) : List<&2, String>}
  for rf: @s: Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), s) == Q.Exec.loop(Q.Exec.mark(s2), s) : Q.St}
  {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(p, n), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(p, Nil{}), s2)), st) : Q.St}

def hmerge_run_mutated(p, n, s1, s2, st, rs, rf):
  match p:
    case P.ScanCsv{path, o, s}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.ScanCsv{path, o, s}), Nil{}), Q.Exec.compile(P.ScanCsv{path, o, s}, Laws.hcode(n)), PE.compile_hwrap(n, P.ScanCsv{path, o, s})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.IScan{path, o, s} <> Nil{}, s2)), st) : Q.St}
      rf(Q.Exec.step(Q.IScan{path, o, s}, st))
    case P.Source{+nm, s}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Source{nm, s}), Nil{}), Q.Exec.compile(P.Source{nm, s}, Laws.hcode(n)), PE.compile_hwrap(n, P.Source{nm, s})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.ISource{nm, s, True{}} <> Nil{}, s2)), st) : Q.St}
      %Equal.sym(Bool, Q.Exec.later(List.append(&2, Q.Instr, Laws.hcode(n), s1), nm), Q.Exec.later(s2, nm), PE.later_ext(List.append(&2, Q.Instr, Laws.hcode(n), s1), s2, nm, rs)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), Q.Exec.step(Q.ISource{nm, s, Bool.not(_)}, st)) == Q.Exec.loop(Q.Exec.mark(s2), Q.Exec.step(Q.ISource{nm, s, Bool.not(Q.Exec.later(s2, nm))}, st)) : Q.St}
      rf(Q.Exec.step(Q.ISource{nm, s, Bool.not(Q.Exec.later(s2, nm))}, st))
    case P.Select{+es, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Select{es, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Select{es, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Select{es, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ISelect{es}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ISelect{es} <> Laws.hcode(n), s1), Q.ISelect{es} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ISelect{es}, s0))))
    case P.WithColumns{+es, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.WithColumns{es, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.WithColumns{es, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.WithColumns{es, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.WithColumns{es, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.IWith{es}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.IWith{es} <> Laws.hcode(n), s1), Q.IWith{es} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.IWith{es}, s0))))
    case P.Filter{+e, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Filter{e, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Filter{e, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Filter{e, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Filter{e, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.IFilter{e}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.IFilter{e} <> Laws.hcode(n), s1), Q.IFilter{e} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.IFilter{e}, s0))))
    case P.Sort{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Sort{ks, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Sort{ks, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Sort{ks, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Sort{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ISort{ks}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ISort{ks} <> Laws.hcode(n), s1), Q.ISort{ks} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ISort{ks}, s0))))
    case P.Drop{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Drop{ks, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Drop{ks, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Drop{ks, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Drop{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TDrop{ks}}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TDrop{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TDrop{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TDrop{ks}}, s0))))
    case P.Rename{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Rename{ks, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Rename{ks, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Rename{ks, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Rename{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TRename{ks}}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TRename{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TRename{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TRename{ks}}, s0))))
    case P.Slice{+ks, +kl, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Slice{ks, kl, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Slice{ks, kl, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Slice{ks, kl, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Slice{ks, kl, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TSlice{ks, kl}}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TSlice{ks, kl}} <> Laws.hcode(n), s1), Q.ITable{Q.TSlice{ks, kl}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TSlice{ks, kl}}, s0))))
    case P.Tail{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Tail{ks, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Tail{ks, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Tail{ks, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Tail{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TTail{ks}}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TTail{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TTail{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TTail{ks}}, s0))))
    case P.Unique{+ks, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Unique{ks, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Unique{ks, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Unique{ks, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Unique{ks, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.ITable{Q.TUnique{ks}}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ITable{Q.TUnique{ks}} <> Laws.hcode(n), s1), Q.ITable{Q.TUnique{ks}} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ITable{Q.TUnique{ks}}, s0))))
    case P.GroupBy{+ks, +ags, +mo2, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo2, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.GroupBy{ks, ags, mo2, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.GroupBy{ks, ags, mo2, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.GroupBy{ks, ags, mo2, x}, Nil{}), s2)), st) : Q.St}
      PE.pass_unary_m(x, n, Q.IGroupBy{ks, ags, mo2}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.IGroupBy{ks, ags, mo2} <> Laws.hcode(n), s1), Q.IGroupBy{ks, ags, mo2} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.IGroupBy{ks, ags, mo2}, s0))))
    case P.Join{+how, +lo, +ro, +l, +r}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Join{how, lo, ro, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})}), Nil{}), Q.Exec.compile(P.Join{how, lo, ro, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Join{how, lo, ro, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Join{how, lo, ro, l, r}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(Mut.hmerge(l, None{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), PE.compile_app(Mut.hmerge(l, None{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), PE.compile_app(l, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n))), s1), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)), PE.app_assoc(Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1)) : {Q.Exec.loop(Q.Exec.mark(_), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{})), s2), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)), PE.app_assoc(Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1))), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      hmerge_run_mutated(l, None{}, List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(r, None{}), Q.IJoin{how, lo, ro} <> Laws.hcode(n)), s1), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IJoin{how, lo, ro} <> Nil{}), s2), st, PE.pass_join_rs_m(r, how, lo, ro, n, s1, s2, rs), s0 => PE.pass_unary_m(r, n, Q.IJoin{how, lo, ro}, s1, s2, s0, hmerge_run_mutated(r, None{}, List.append(&2, Q.Instr, Q.IJoin{how, lo, ro} <> Laws.hcode(n), s1), Q.IJoin{how, lo, ro} <> s2, s0, rs, s3 => rf(Q.Exec.step(Q.IJoin{how, lo, ro}, s3)))))
    case P.Concat{+ci, +l, +r}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Concat{ci, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})}), Nil{}), Q.Exec.compile(P.Concat{ci, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Concat{ci, Mut.hmerge(l, None{}), Mut.hmerge(r, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Concat{ci, l, r}, Nil{}), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(Mut.hmerge(l, None{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), PE.compile_app(Mut.hmerge(l, None{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(l, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(l, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), PE.compile_app(l, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}))) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n))), s1), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1)), PE.app_assoc(Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1)) : {Q.Exec.loop(Q.Exec.mark(_), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{})), s2), List.append(&2, Q.Instr, Q.Exec.compile(l, Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}), s2)), PE.app_assoc(Q.Exec.compile(l, Nil{}), Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}), s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(l, None{}), Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1))), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      hmerge_run_mutated(l, None{}, List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(r, None{}), Q.IConcat{ci} <> Laws.hcode(n)), s1), List.append(&2, Q.Instr, Q.Exec.compile(r, Q.IConcat{ci} <> Nil{}), s2), st, PE.pass_concat_rs_m(r, ci, n, s1, s2, rs), s0 => PE.pass_unary_m(r, n, Q.IConcat{ci}, s1, s2, s0, hmerge_run_mutated(r, None{}, List.append(&2, Q.Instr, Q.IConcat{ci} <> Laws.hcode(n), s1), Q.IConcat{ci} <> s2, s0, rs, s3 => rf(Q.Exec.step(Q.IConcat{ci}, s3)))))
    case P.Head{+m, +x}:
      %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(x, Q.IHead{m} <> Nil{}), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}), PE.compile_app(x, Q.IHead{m} <> Nil{})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(x, Some{P.Opt.hmin(m, n)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s2)), st) : Q.St}
      %Equal.sym(List<&2, Q.Instr>, List.append(&2, Q.Instr, List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}), s2), List.append(&2, Q.Instr, Q.Exec.compile(x, Nil{}), List.append(&2, Q.Instr, Q.IHead{m} <> Nil{}, s2)), PE.app_assoc(Q.Exec.compile(x, Nil{}), Q.IHead{m} <> Nil{}, s2)) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(x, Some{P.Opt.hmin(m, n)}), Nil{}), s1)), st) == Q.Exec.loop(Q.Exec.mark(_), st) : Q.St}
      hmerge_run_mutated(x, Some{P.Opt.hmin(m, n)}, s1, Q.IHead{m} <> s2, st, PE.pass_head_rs(n, m, s1, s2, rs), s0 => PE.pass_head_rf(n, m, s1, s2, s0, rf))

#|SOME PROOFS FAIL
#|Error:
#|- expected : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(Mut.hmerge(x, n), [Q.ISelect{es}]), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, [Q.ISelect{es}]), s2)), st) : Q.St}
#|- observed : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, Mut.hmerge(x, None{})}), []), s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(x, [Q.ISelect{es}]), s2)), st) : Q.St}
#|Context:
#|- es : List<&2, X.Expr>
#|- x  : P.Plan
#|- n  : Maybe<&2, U32>
#|- s1 : List<&2, Q.Instr>
#|- s2 : List<&2, Q.Instr>
#|- st : Q.St
#|- rs : {Laws.srcs(List.append(&2, Q.Instr, Laws.hcode(n), s1)) == Laws.srcs(s2) : List<&2, String>}
#|- rf : @s:Q.St -> {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Laws.hcode(n), s1)), s) == Q.Exec.loop(Q.Exec.mark(s2), s) : Q.St}
#|Location: hmerge_run_mutated
#|144 |     case P.Select{+es, +x}:
#|145>|       %Equal.sym(List<&2, Q.Instr>, Q.Exec.compile(P.Opt.hwrap(n, P.Select{es, Mut.hmerge(x, None{})}), Nil{}), Q.Exec.compile(P.Select{es, Mut.hmerge(x, None{})}, Laws.hcode(n)), PE.compile_hwrap(n, P.Select{es, Mut.hmerge(x, None{})})) : {Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, _, s1)), st) == Q.Exec.loop(Q.Exec.mark(List.append(&2, Q.Instr, Q.Exec.compile(P.Select{es, x}, Nil{}), s2)), st) : Q.St}
#|    |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#|146 |       PE.pass_unary_m(x, n, Q.ISelect{es}, s1, s2, st, hmerge_run_mutated(x, None{}, List.append(&2, Q.Instr, Q.ISelect{es} <> Laws.hcode(n), s1), Q.ISelect{es} <> s2, st, rs, s0 => rf(Q.Exec.step(Q.ISelect{es}, s0))))
