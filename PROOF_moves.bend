# PROOF_moves.bend -- proof of LAWS.bend section 16 (v0.2 T3.1, DESIGN.md 16.2 rule 1): Frame.lend
# (the move / borrow of the liveness pass) observes as Frame.get_cloned, and Frame.replace undoes it.
#
# Shape: the three column walks (Cols.cg.go behind get_cloned, Cols.lend.go behind lend,
# Cols.replace.go behind replace) and Cols.names (behind Frame.info, replace's shape check) are each
# described by one induction over the columns against the pure models of LAWS.bend section 16
# (lastm: the last column named n; holed: the stand-ins in place). The walks keep an accumulator
# and a slot, so each loop lemma is a forall over them (applied once per step: the IH as a
# hypothesis, PROOF_eval's CgRec idiom). The cg and lend walks need no hypothesis; the replace walk
# needs unique names (cols_ok): before the hit it passes columns through, at the hit it puts c in
# the stand-in's place, after it every name differs from n. The column list is affine and every
# lemma matches it, so it is copied first (cols_dup: two copies equal to it, by clone_w per column)
# and each lemma gets its own copy; the goal is rewritten from the original to the copy.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/expr.bend as X
import ./src/eval.bend as V
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_eval.bend as PV

# ---- toolkit ------------------------------------------------------------------------------------

def mdisc(m: Maybe<&1, C.Column>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some1(-x: C.Column, h: {None{} == Some{x} : Maybe<&1, C.Column>}) -> Empty:
  %h : mdisc(_)
  Unit{}

def some_inj1(-x: C.Column, -y: C.Column, e: {Some{x} == Some{y} : Maybe<&1, C.Column>}) -> {x == y : C.Column}:
  Equal.cong(Maybe<&1, C.Column>, C.Column, m => Maybe.default(&1, C.Column, m, x), Some{x}, Some{y}, e)

def or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# two copies of a column list, both equal to it
def ColsDup(-cols: List<&1, C.Named>) -> Type:
  &a: List<&1, C.Named> -> &b: List<&1, C.Named> -> {a == cols : List<&1, C.Named>} & {b == cols : List<&1, C.Named>}

def cols_dup_k(+n: String, -c: C.Column, -rest: List<&1, C.Named>, wc: PV.CloneW(c), wr: ColsDup(rest)) -> ColsDup(C.Named{n, c} <> rest):
  (c1, c2, ec, e1, e2) = wc
  (r1, r2, f1, f2) = wr
  (C.Named{n, c1} <> r1, C.Named{n, c2} <> r2, (%e1 : {C.Named{n, c1} <> r1 == C.Named{n, _} <> rest : List<&1, C.Named>}; %f1 : {C.Named{n, c1} <> r1 == C.Named{n, c1} <> _ : List<&1, C.Named>}; {==}), (%e2 : {C.Named{n, c2} <> r2 == C.Named{n, _} <> rest : List<&1, C.Named>}; %f2 : {C.Named{n, c2} <> r2 == C.Named{n, c2} <> _ : List<&1, C.Named>}; {==}))

def cols_dup(cols: List<&1, C.Named>) -> ColsDup(cols):
  match cols:
    case Nil{}:
      (Nil{}, Nil{}, {==}, {==})
    case C.Named{+n, c} <> rest:
      cols_dup_k(n, c, rest, PV.clone_w(c), cols_dup(rest))

# ---- Cols.cg.go (get_cloned's walk): the list back, the last column named n in the slot ------------

def CgM(-cols: List<&1, C.Named>, +n: String) -> Type:
  @-acc: List<&1, C.Named> -> @-sl: Maybe<&1, C.Column> -> {C.Cols.cg.go(cols, n, (acc, sl)) == (List.reverse.go(&1, C.Named, acc, cols), Laws.lastm(cols, n, sl)) : List<&1, C.Named> & Maybe<&1, C.Column>}

# the hit: the copy c1 goes back into the list, the copy c2 into the slot; both equal col
def cg_hit(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, eb: {String.eq(n, nj) == True{} : Bool}, ih: CgM(rest, n), w: PV.CloneW(col))
  -> {C.Cols.cg.go(C.Named{nj, col} <> rest, n, (acc, sl)) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), Laws.lastm(C.Named{nj, col} <> rest, n, sl)) : List<&1, C.Named> & Maybe<&1, C.Column>}:
  (c1, c2, ec, e1, e2) = w
  %Equal.sym(Bool, String.eq(n, nj), True{}, eb) : {C.Cols.cg.go(rest, n, C.Cols.cg.step(_, nj, col, (acc, sl))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), Laws.lastm(rest, n, Laws.lastm.k(_, col, sl))) : List<&1, C.Named> & Maybe<&1, C.Column>}
  %Equal.sym(C.Column & C.Column, C.Column.clone(col), (c1, c2), ec) : {C.Cols.cg.go(rest, n, C.Cols.cg.cl(nj, acc, _)) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), Laws.lastm(rest, n, Some{col})) : List<&1, C.Named> & Maybe<&1, C.Column>}
  %e1 : {C.Cols.cg.go(rest, n, C.Cols.cg.cl(nj, acc, (c1, c2))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, _} <> rest), Laws.lastm(rest, n, Some{col})) : List<&1, C.Named> & Maybe<&1, C.Column>}
  %e2 : {C.Cols.cg.go(rest, n, C.Cols.cg.cl(nj, acc, (c1, c2))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, c1} <> rest), Laws.lastm(rest, n, Some{_})) : List<&1, C.Named> & Maybe<&1, C.Column>}
  ih(C.Named{nj, c1} <> acc, Some{c2})

def cg_cons_b(+n: String, +nj: String, b: Bool, eb: {String.eq(n, nj) == b : Bool}, col: C.Column, -rest: List<&1, C.Named>, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, ih: CgM(rest, n))
  -> {C.Cols.cg.go(C.Named{nj, col} <> rest, n, (acc, sl)) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), Laws.lastm(C.Named{nj, col} <> rest, n, sl)) : List<&1, C.Named> & Maybe<&1, C.Column>}:
  match b:
    case True{}:
      cg_hit(n, nj, col, rest, acc, sl, eb, ih, PV.clone_w(col))
    case False{}:
      %Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {C.Cols.cg.go(rest, n, C.Cols.cg.step(_, nj, col, (acc, sl))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), Laws.lastm(rest, n, Laws.lastm.k(_, col, sl))) : List<&1, C.Named> & Maybe<&1, C.Column>}
      ih(C.Named{nj, col} <> acc, sl)

def cg_cons(+n: String, +nj: String, col: C.Column, -rest: List<&1, C.Named>, ih: CgM(rest, n)) -> CgM(C.Named{nj, col} <> rest, n):
  acc => sl => cg_cons_b(n, nj, String.eq(n, nj), {==}, col, rest, acc, sl, ih)

def cg_model(cols: List<&1, C.Named>, +n: String) -> CgM(cols, n):
  match cols:
    case Nil{}:
      acc => sl => {==}
    case C.Named{+nj, col} <> rest:
      cg_cons(n, nj, col, rest, cg_model(rest, n))

# ---- Cols.lend.go (lend's walk): the stand-ins in place, the last column named n in the slot ---------

def hollow_w(c: C.Column) -> {C.Column.hollow(c) == (Laws.hollowm(c), c) : C.Column & C.Column}:
  match c:
    case C.CBool{len, depth, valid, data}:
      {==}
    case C.CU32{len, depth, valid, data}:
      {==}
    case C.CI32{len, depth, valid, data}:
      {==}
    case C.CF32{len, depth, valid, data}:
      {==}
    case C.CStr{len, depth, valid, data}:
      {==}

def LendM(-cols: List<&1, C.Named>, +n: String) -> Type:
  @-acc: List<&1, C.Named> -> @-sl: Maybe<&1, C.Column> -> {C.Cols.lend.go(cols, n, (acc, sl)) == (List.reverse.go(&1, C.Named, acc, Laws.holed(cols, n)), Laws.lastm(cols, n, sl)) : List<&1, C.Named> & Maybe<&1, C.Column>}

def lend_cons_b(+n: String, +nj: String, b: Bool, eb: {String.eq(n, nj) == b : Bool}, col: C.Column, -rest: List<&1, C.Named>, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, ih: LendM(rest, n))
  -> {C.Cols.lend.go(C.Named{nj, col} <> rest, n, (acc, sl)) == (List.reverse.go(&1, C.Named, acc, Laws.holed(C.Named{nj, col} <> rest, n)), Laws.lastm(C.Named{nj, col} <> rest, n, sl)) : List<&1, C.Named> & Maybe<&1, C.Column>}:
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(n, nj), True{}, eb) : {C.Cols.lend.go(rest, n, C.Cols.lend.step(_, nj, col, (acc, sl))) == (List.reverse.go(&1, C.Named, acc, Laws.holed.k(_, nj, col) <> Laws.holed(rest, n)), Laws.lastm(rest, n, Laws.lastm.k(_, col, sl))) : List<&1, C.Named> & Maybe<&1, C.Column>}
      %Equal.sym(C.Column & C.Column, C.Column.hollow(col), (Laws.hollowm(col), col), hollow_w(col)) : {C.Cols.lend.go(rest, n, C.Cols.lend.k(nj, acc, _)) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, Laws.hollowm(col)} <> Laws.holed(rest, n)), Laws.lastm(rest, n, Some{col})) : List<&1, C.Named> & Maybe<&1, C.Column>}
      ih(C.Named{nj, Laws.hollowm(col)} <> acc, Some{col})
    case False{}:
      %Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {C.Cols.lend.go(rest, n, C.Cols.lend.step(_, nj, col, (acc, sl))) == (List.reverse.go(&1, C.Named, acc, Laws.holed.k(_, nj, col) <> Laws.holed(rest, n)), Laws.lastm(rest, n, Laws.lastm.k(_, col, sl))) : List<&1, C.Named> & Maybe<&1, C.Column>}
      ih(C.Named{nj, col} <> acc, sl)

def lend_cons(+n: String, +nj: String, col: C.Column, -rest: List<&1, C.Named>, ih: LendM(rest, n)) -> LendM(C.Named{nj, col} <> rest, n):
  acc => sl => lend_cons_b(n, nj, String.eq(n, nj), {==}, col, rest, acc, sl, ih)

def lend_model(cols: List<&1, C.Named>, +n: String) -> LendM(cols, n):
  match cols:
    case Nil{}:
      acc => sl => {==}
    case C.Named{+nj, col} <> rest:
      lend_cons(n, nj, col, rest, lend_model(rest, n))

# ---- Cols.names over the lent list (Frame.info in replace's shape check) ---------------------------

def NamesW(-cols: List<&1, C.Named>, +n: String) -> Type:
  &ns: List<&2, String> -> {C.Cols.names(Laws.holed(cols, n)) == (Laws.holed(cols, n), ns) : List<&1, C.Named> & List<&2, String>}

def names_cons(+n: String, +nj: String, b: Bool, eb: {String.eq(n, nj) == b : Bool}, -col: C.Column, -rest: List<&1, C.Named>, ih: NamesW(rest, n)) -> NamesW(C.Named{nj, col} <> rest, n):
  match b:
    case True{}:
      (ns, e) = ih
      %Equal.sym(Bool, String.eq(n, nj), True{}, eb) : &ns2: List<&2, String> -> {C.Cols.names(Laws.holed.k(_, nj, col) <> Laws.holed(rest, n)) == (Laws.holed.k(_, nj, col) <> Laws.holed(rest, n), ns2) : List<&1, C.Named> & List<&2, String>}
      %Equal.sym(List<&1, C.Named> & List<&2, String>, C.Cols.names(Laws.holed(rest, n)), (Laws.holed(rest, n), ns), e) : &ns2: List<&2, String> -> {C.Cols.names.k(nj, Laws.hollowm(col), _) == (C.Named{nj, Laws.hollowm(col)} <> Laws.holed(rest, n), ns2) : List<&1, C.Named> & List<&2, String>}
      (nj <> ns, {==})
    case False{}:
      (ns, e) = ih
      %Equal.sym(Bool, String.eq(n, nj), False{}, eb) : &ns2: List<&2, String> -> {C.Cols.names(Laws.holed.k(_, nj, col) <> Laws.holed(rest, n)) == (Laws.holed.k(_, nj, col) <> Laws.holed(rest, n), ns2) : List<&1, C.Named> & List<&2, String>}
      %Equal.sym(List<&1, C.Named> & List<&2, String>, C.Cols.names(Laws.holed(rest, n)), (Laws.holed(rest, n), ns), e) : &ns2: List<&2, String> -> {C.Cols.names.k(nj, col, _) == (C.Named{nj, col} <> Laws.holed(rest, n), ns2) : List<&1, C.Named> & List<&2, String>}
      (nj <> ns, {==})

def names_w(cols: List<&1, C.Named>, +n: String) -> NamesW(cols, n):
  match cols:
    case Nil{}:
      (Nil{}, {==})
    case C.Named{+nj, col} <> rest:
      names_cons(n, nj, String.eq(n, nj), {==}, col, rest, names_w(rest, n))

# ---- Cols.replace.go over the lent list (replace's walk): unique names put c back in place ------------
#
# One induction with the walk's state as a Bool: dn = False while the stand-in is still ahead (the
# slot holds c, n is not among the names seen, and c is the last column named n of the rest);
# dn = True once it has been replaced (the slot is empty, n is among the names seen, so no later name
# is n: those columns pass unchanged and leave lastm's slot alone).

def RepHyp(dn: Bool, -cols: List<&1, C.Named>, +n: String, +seen: List<&2, String>, -c: C.Column) -> Type:
  match dn:
    case False{}:
      {C.Names.has(seen, n) == False{} : Bool} & {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>}
    case True{}:
      {C.Names.has(seen, n) == True{} : Bool}

def RepRes(dn: Bool, -cols: List<&1, C.Named>, +n: String, +h: U32, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, -c: C.Column) -> Type:
  match dn:
    case False{}:
      {C.Cols.replace.go(Laws.holed(cols, n), n, (acc, Some{c})) == (List.reverse.go(&1, C.Named, acc, cols), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>} & {U32.is_eq(Laws.clen(c), h) == True{} : Bool}
    case True{}:
      {C.Cols.replace.go(Laws.holed(cols, n), n, (acc, None{})) == (List.reverse.go(&1, C.Named, acc, cols), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>} & {Laws.lastm(cols, n, sl) == sl : Maybe<&1, C.Column>}

def RepG(-cols: List<&1, C.Named>, +n: String, +h: U32, +seen: List<&2, String>) -> Type:
  @dn: Bool -> @-acc: List<&1, C.Named> -> @-sl: Maybe<&1, C.Column> -> @-c: C.Column -> @hok: {Laws.cols_ok(h, cols, seen) == True{} : Bool} -> @hy: RepHyp(dn, cols, n, seen, c) -> RepRes(dn, cols, n, h, acc, sl, c)

def rep_nil(+n: String, +h: U32, +seen: List<&2, String>, dn: Bool, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, -c: C.Column, hy: RepHyp(dn, Nil{}, n, seen, c)) -> RepRes(dn, Nil{}, n, h, acc, sl, c):
  match dn:
    case False{}:
      (hn, hc) = hy
      Empty.absurd(RepRes(False{}, Nil{}, n, h, acc, sl, c), none_some1(c, hc))
    case True{}:
      ({==}, {==})

# the column's facts out of cols_ok, with its length as the Data value k
def ok_hd(+h: U32, +seen: List<&2, String>, +nj: String, +k: U32, -rest: List<&1, C.Named>, +hok: {Bool.and(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen))) == True{} : Bool}) -> {C.Names.has(seen, nj) == False{} : Bool}:
  L.not_true(C.Names.has(seen, nj), PV.and_l(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen)), hok))

def ok_len(+h: U32, +seen: List<&2, String>, +nj: String, +k: U32, -rest: List<&1, C.Named>, +hok: {Bool.and(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen))) == True{} : Bool}) -> {U32.is_eq(k, h) == True{} : Bool}:
  PV.and_l(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen), L.and_right(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen)), hok))

def ok_rest(+h: U32, +seen: List<&2, String>, +nj: String, +k: U32, -rest: List<&1, C.Named>, +hok: {Bool.and(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen))) == True{} : Bool}) -> {Laws.cols_ok(h, rest, nj <> seen) == True{} : Bool}:
  L.and_right(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen), L.and_right(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen)), hok))

# the hit with col == c: the stand-in's place gets c, the rest passes unchanged
def rep_hit_e(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, +h: U32, -acc: List<&1, C.Named>, -c: C.Column, +eb: {String.eq(n, nj) == True{} : Bool},
  hl: {U32.is_eq(Laws.clen(col), h) == True{} : Bool},
  r1: {C.Cols.replace.go(Laws.holed(rest, n), n, (C.Named{nj, c} <> acc, None{})) == (List.reverse.go(&1, C.Named, C.Named{nj, c} <> acc, rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>},
  +e: {col == c : C.Column}) -> RepRes(False{}, C.Named{nj, col} <> rest, n, h, acc, None{}, c):
  ((%Equal.sym(Bool, String.eq(n, nj), True{}, eb) : {C.Cols.replace.go(Laws.holed.k(_, nj, col) <> Laws.holed(rest, n), n, (acc, Some{c})) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    %Equal.sym(Bool, String.eq(n, nj), True{}, eb) : {C.Cols.replace.go(Laws.holed(rest, n), n, C.Cols.replace.step(_, nj, Laws.hollowm(col), (acc, Some{c}))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    %Equal.sym(C.Column, col, c, e) : {C.Cols.replace.go(Laws.holed(rest, n), n, (C.Named{nj, c} <> acc, None{})) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, _} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    r1),
   (%e : {U32.is_eq(Laws.clen(_), h) == True{} : Bool}; hl))

# searching, the hit: c is col (lastm of the rest after the hit keeps its slot), the stand-in gets c
def rep_hit_fin(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, +h: U32, -acc: List<&1, C.Named>, -c: C.Column, +eb: {String.eq(n, nj) == True{} : Bool},
  hc: {Laws.lastm(rest, n, Some{col}) == Some{c} : Maybe<&1, C.Column>}, hl: {U32.is_eq(Laws.clen(col), h) == True{} : Bool},
  r: RepRes(True{}, rest, n, h, C.Named{nj, c} <> acc, Some{col}, c)) -> RepRes(False{}, C.Named{nj, col} <> rest, n, h, acc, None{}, c):
  (r1, r2) = r
  rep_hit_e(n, nj, col, rest, h, acc, c, eb, hl, r1, some_inj1(col, c, Equal.trans(Maybe<&1, C.Column>, Some{col}, Laws.lastm(rest, n, Some{col}), Some{c}, Equal.sym(Maybe<&1, C.Column>, Laws.lastm(rest, n, Some{col}), Some{col}, r2), hc)))


# searching, a miss: the stand-in is further on; the IH's slot facts move along
def rep_miss_fin(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, +h: U32, -acc: List<&1, C.Named>, -c: C.Column, +eb: {String.eq(n, nj) == False{} : Bool},
  r: RepRes(False{}, rest, n, h, C.Named{nj, col} <> acc, None{}, c)) -> RepRes(False{}, C.Named{nj, col} <> rest, n, h, acc, None{}, c):
  (r1, r2) = r
  ((%Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {C.Cols.replace.go(Laws.holed.k(_, nj, col) <> Laws.holed(rest, n), n, (acc, Some{c})) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    %Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {C.Cols.replace.go(Laws.holed(rest, n), n, C.Cols.replace.step(_, nj, col, (acc, Some{c}))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    r1),
   r2)

# done: every later column passes unchanged and keeps lastm's slot
def rep_done_fin(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, +h: U32, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, -c: C.Column, +eb: {String.eq(n, nj) == False{} : Bool},
  r: RepRes(True{}, rest, n, h, C.Named{nj, col} <> acc, sl, c)) -> RepRes(True{}, C.Named{nj, col} <> rest, n, h, acc, sl, c):
  (r1, r2) = r
  ((%Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {C.Cols.replace.go(Laws.holed.k(_, nj, col) <> Laws.holed(rest, n), n, (acc, None{})) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    %Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {C.Cols.replace.go(Laws.holed(rest, n), n, C.Cols.replace.step(_, nj, col, (acc, None{}))) == (List.reverse.go(&1, C.Named, acc, C.Named{nj, col} <> rest), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>};
    r1),
   (%Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {Laws.lastm(rest, n, Laws.lastm.k(_, col, sl)) == sl : Maybe<&1, C.Column>}; r2))

def rep_cons_b(+n: String, +nj: String, dn: Bool, b: Bool, +eb: {String.eq(n, nj) == b : Bool}, -col: C.Column, +k: U32, -rest: List<&1, C.Named>, +h: U32, +seen: List<&2, String>, -acc: List<&1, C.Named>, -sl: Maybe<&1, C.Column>, -c: C.Column,
  +ek: {k == Laws.clen(col) : U32},
  +hok: {Bool.and(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(k, h), Laws.cols_ok(h, rest, nj <> seen))) == True{} : Bool},
  hy: RepHyp(dn, C.Named{nj, col} <> rest, n, seen, c), ih: RepG(rest, n, h, nj <> seen)) -> RepRes(dn, C.Named{nj, col} <> rest, n, h, acc, sl, c):
  match dn b:
    case False{} True{}:
      (hn, hc) = hy
      rep_hit_fin(n, nj, col, rest, h, acc, c, eb,
        (%eb : {Laws.lastm(rest, n, Laws.lastm.k(_, col, None{})) == Some{c} : Maybe<&1, C.Column>}; hc),
        (%ek : {U32.is_eq(_, h) == True{} : Bool}; ok_len(h, seen, nj, k, rest, hok)),
        ih(True{}, C.Named{nj, c} <> acc, Some{col}, c, ok_rest(h, seen, nj, k, rest, hok), (%Equal.sym(Bool, String.eq(n, nj), True{}, eb) : {Bool.or(_, C.Names.has(seen, n)) == True{} : Bool}; {==})))
    case False{} False{}:
      (hn, hc) = hy
      rep_miss_fin(n, nj, col, rest, h, acc, c, eb,
        ih(False{}, C.Named{nj, col} <> acc, None{}, c, ok_rest(h, seen, nj, k, rest, hok),
          ((%Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {Bool.or(_, C.Names.has(seen, n)) == False{} : Bool}; hn),
           (%eb : {Laws.lastm(rest, n, Laws.lastm.k(_, col, None{})) == Some{c} : Maybe<&1, C.Column>}; hc))))
    case True{} True{}:
      PV.true_false_any(RepRes(True{}, C.Named{nj, col} <> rest, n, h, acc, sl, c), Equal.trans(Bool, True{}, C.Names.has(seen, n), False{}, Equal.sym(Bool, C.Names.has(seen, n), True{}, hy), (%Equal.sym(String, n, nj, Laws.str_eq_sound(n, nj, eb)) : {C.Names.has(seen, _) == False{} : Bool}; ok_hd(h, seen, nj, k, rest, hok))))
    case True{} False{}:
      rep_done_fin(n, nj, col, rest, h, acc, sl, c, eb,
        ih(True{}, C.Named{nj, col} <> acc, sl, c, ok_rest(h, seen, nj, k, rest, hok), (%Equal.sym(Bool, String.eq(n, nj), False{}, eb) : {Bool.or(_, C.Names.has(seen, n)) == True{} : Bool}; hy)))

def rep_cons_l(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, +h: U32, +seen: List<&2, String>, +k: U32, +ek: {k == Laws.clen(col) : U32}, ih: RepG(rest, n, h, nj <> seen)) -> RepG(C.Named{nj, col} <> rest, n, h, seen):
  dn => acc => sl => c => hok => hy => rep_cons_b(n, nj, dn, String.eq(n, nj), {==}, col, k, rest, h, seen, acc, sl, c, ek, (%Equal.sym(U32, k, Laws.clen(col), ek) : {Bool.and(Bool.not(C.Names.has(seen, nj)), Bool.and(U32.is_eq(_, h), Laws.cols_ok(h, rest, nj <> seen))) == True{} : Bool}; hok), hy, ih)

# the cons step: the column's length as the Data value k (col_dup2), so cols_ok's facts hold Data only
def rep_cons(+n: String, +nj: String, -col: C.Column, -rest: List<&1, C.Named>, +h: U32, +seen: List<&2, String>,
  wd: &c2: C.Column -> &k: U32 -> &dt: D.DType -> {c2 == col : C.Column} & {dt == Laws.cdtype(col) : D.DType} & {k == Laws.clen(col) : U32}, ih: RepG(rest, n, h, nj <> seen)) -> RepG(C.Named{nj, col} <> rest, n, h, seen):
  (c2, +k, dt, ec, edt, ek) = wd
  rep_cons_l(n, nj, col, rest, h, seen, k, ek, ih)

def rep_g(cols: List<&1, C.Named>, +n: String, +h: U32, +seen: List<&2, String>) -> RepG(cols, n, h, seen):
  match cols:
    case Nil{}:
      dn => acc => sl => c => hok => hy => rep_nil(n, h, seen, dn, acc, sl, c, hy)
    case C.Named{+nj, col} <> rest:
      rep_cons(n, nj, col, rest, h, seen, PV.col_dup2(col), rep_g(rest, n, h, nj <> seen))

# ---- the law: one copy of the column list per walk ----------------------------------------------------

# Column.len pinned: the column back as it is, its length as the Data value k
def len_pin(c: C.Column) -> &k: U32 -> {C.Column.len(c) == (c, k) : C.Column & U32} & {k == Laws.clen(c) : U32}:
  match c:
    case C.CBool{+len, depth, valid, data}:
      (len, {==}, {==})
    case C.CU32{+len, depth, valid, data}:
      (len, {==}, {==})
    case C.CI32{+len, depth, valid, data}:
      (len, {==}, {==})
    case C.CF32{+len, depth, valid, data}:
      (len, {==}, {==})
    case C.CStr{+len, depth, valid, data}:
      (len, {==}, {==})

def part_get_k(+h2: U32, -a: List<&1, C.Named>, +n: String, -c: C.Column, ha: {Laws.lastm(a, n, None{}) == Some{c} : Maybe<&1, C.Column>}, w: CgM(a, n))
  -> {C.Frame.get_cloned(C.Frame{h2, a}, n) == (C.Frame{h2, a}, Done{c}) : C.Frame & E.ResT(C.Column)}:
  %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.cg.go(a, n, (Nil{}, None{})), (List.reverse.go(&1, C.Named, Nil{}, a), Laws.lastm(a, n, None{})), w(Nil{}, None{})) : {C.Frame.get_cloned.k(h2, n, _) == (C.Frame{h2, a}, Done{c}) : C.Frame & E.ResT(C.Column)}
  %Equal.sym(Maybe<&1, C.Column>, Laws.lastm(a, n, None{}), Some{c}, ha) : {C.Frame.get_cloned.k(h2, n, (List.reverse.go(&1, C.Named, Nil{}, a), _)) == (C.Frame{h2, a}, Done{c}) : C.Frame & E.ResT(C.Column)}
  {==}

# get_cloned answers the frame unchanged and the column named n (copy a of the columns)
def part_get(+h2: U32, -cols: List<&1, C.Named>, +n: String, -c: C.Column, a: List<&1, C.Named>, +ea: {a == cols : List<&1, C.Named>}, hc: {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>})
  -> {C.Frame.get_cloned(C.Frame{h2, cols}, n) == (C.Frame{h2, cols}, Done{c}) : C.Frame & E.ResT(C.Column)}:
  %ea : {C.Frame.get_cloned(C.Frame{h2, _}, n) == (C.Frame{h2, _}, Done{c}) : C.Frame & E.ResT(C.Column)}
  part_get_k(h2, a, n, c, (%Equal.sym(List<&1, C.Named>, a, cols, ea) : {Laws.lastm(_, n, None{}) == Some{c} : Maybe<&1, C.Column>}; hc), cg_model(a, n))

def part_lend_k(+h2: U32, -b: List<&1, C.Named>, +n: String, -c: C.Column, hb: {Laws.lastm(b, n, None{}) == Some{c} : Maybe<&1, C.Column>}, w: LendM(b, n))
  -> {C.Frame.lend(C.Frame{h2, b}, n) == (Laws.holedf(C.Frame{h2, b}, n), Done{c}) : C.Frame & E.ResT(C.Column)}:
  %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.lend.go(b, n, (Nil{}, None{})), (List.reverse.go(&1, C.Named, Nil{}, Laws.holed(b, n)), Laws.lastm(b, n, None{})), w(Nil{}, None{})) : {C.Frame.lend.k(h2, n, _) == (C.Frame{h2, Laws.holed(b, n)}, Done{c}) : C.Frame & E.ResT(C.Column)}
  %Equal.sym(Maybe<&1, C.Column>, Laws.lastm(b, n, None{}), Some{c}, hb) : {C.Frame.lend.k(h2, n, (List.reverse.go(&1, C.Named, Nil{}, Laws.holed(b, n)), _)) == (C.Frame{h2, Laws.holed(b, n)}, Done{c}) : C.Frame & E.ResT(C.Column)}
  {==}

# lend answers the same column and the frame with its stand-in (copy b of the columns)
def part_lend(+h2: U32, -cols: List<&1, C.Named>, +n: String, -c: C.Column, b: List<&1, C.Named>, +eb: {b == cols : List<&1, C.Named>}, hc: {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>})
  -> {C.Frame.lend(C.Frame{h2, cols}, n) == (Laws.holedf(C.Frame{h2, cols}, n), Done{c}) : C.Frame & E.ResT(C.Column)}:
  %eb : {C.Frame.lend(C.Frame{h2, _}, n) == (Laws.holedf(C.Frame{h2, _}, n), Done{c}) : C.Frame & E.ResT(C.Column)}
  part_lend_k(h2, b, n, c, (%Equal.sym(List<&1, C.Named>, b, cols, eb) : {Laws.lastm(_, n, None{}) == Some{c} : Maybe<&1, C.Column>}; hc), lend_model(b, n))

# replace over the lent frame: the shape check passes (c has the frame's height), the walk puts c back
def part_rep_f(+h2: U32, -b4: List<&1, C.Named>, +n: String, +h: U32, -c: C.Column, +ns: List<&2, String>, +k: U32,
  en: {C.Cols.names(Laws.holed(b4, n)) == (Laws.holed(b4, n), ns) : List<&1, C.Named> & List<&2, String>},
  el: {C.Column.len(c) == (c, k) : C.Column & U32}, ehk: {h2 == k : U32},
  r1: {C.Cols.replace.go(Laws.holed(b4, n), n, (Nil{}, Some{c})) == (List.reverse.go(&1, C.Named, Nil{}, b4), None{}) : List<&1, C.Named> & Maybe<&1, C.Column>})
  -> {C.Frame.replace(Laws.holedf(C.Frame{h2, b4}, n), n, c) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}:
  %Equal.sym(List<&1, C.Named> & List<&2, String>, C.Cols.names(Laws.holed(b4, n)), (Laws.holed(b4, n), ns), en) : {C.Frame.replace.a(n, C.Frame.info.k(h2, _), C.Column.len(c)) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}
  %Equal.sym(C.Column & U32, C.Column.len(c), (c, k), el) : {C.Frame.replace.a(n, (C.Frame{h2, Laws.holed(b4, n)}, C.FInfo{h2, ns}), _) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}
  %ehk : {C.Frame.replace.b(C.FInfo.shape.k(Bool.or(C.Names.is_empty(ns), U32.is_eq(h2, _)), h2, _), C.Frame{h2, Laws.holed(b4, n)}, n, c, _) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}
  %Equal.sym(Bool, U32.is_eq(h2, h2), True{}, PV.u32_eq_refl(h2)) : {C.Frame.replace.b(C.FInfo.shape.k(Bool.or(C.Names.is_empty(ns), _), h2, h2), C.Frame{h2, Laws.holed(b4, n)}, n, c, h2) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}
  %Equal.sym(Bool, Bool.or(C.Names.is_empty(ns), True{}), True{}, or_true(C.Names.is_empty(ns))) : {C.Frame.replace.b(C.FInfo.shape.k(_, h2, h2), C.Frame{h2, Laws.holed(b4, n)}, n, c, h2) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}
  %Equal.sym(List<&1, C.Named> & Maybe<&1, C.Column>, C.Cols.replace.go(Laws.holed(b4, n), n, (Nil{}, Some{c})), (List.reverse.go(&1, C.Named, Nil{}, b4), None{}), r1) : {Done{C.Frame.replace.d(h2, n, _)} == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}
  {==}

def part_rep_r(+h2: U32, -b4: List<&1, C.Named>, +n: String, +h: U32, -c: C.Column, +ns: List<&2, String>, +hh: {h2 == h : U32},
  en: {C.Cols.names(Laws.holed(b4, n)) == (Laws.holed(b4, n), ns) : List<&1, C.Named> & List<&2, String>},
  r: RepRes(False{}, b4, n, h, Nil{}, None{}, c), wk: &k: U32 -> {C.Column.len(c) == (c, k) : C.Column & U32} & {k == Laws.clen(c) : U32})
  -> {C.Frame.replace(Laws.holedf(C.Frame{h2, b4}, n), n, c) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}:
  (r1, r2) = r
  (+k, el, ek) = wk
  part_rep_f(h2, b4, n, h, c, ns, k, en, el, Equal.trans(U32, h2, h, k, hh, Equal.sym(U32, k, h, PV.u32_eq_sound(k, h, (%Equal.sym(U32, k, Laws.clen(c), ek) : {U32.is_eq(_, h) == True{} : Bool}; r2)))), r1)

def part_rep_n(+h2: U32, -b4: List<&1, C.Named>, +n: String, +h: U32, c: C.Column, +hh: {h2 == h : U32}, w: NamesW(b4, n), r: RepRes(False{}, b4, n, h, Nil{}, None{}, c))
  -> {C.Frame.replace(Laws.holedf(C.Frame{h2, b4}, n), n, c) == Done{C.Frame{h2, b4}} : E.ResT(C.Frame)}:
  (+ns, en) = w
  part_rep_r(h2, b4, n, h, c, ns, hh, en, r, len_pin(c))

def rep_app(-b4: List<&1, C.Named>, +n: String, +h: U32, -c: C.Column, w: RepG(b4, n, h, Nil{}), hok: {Laws.cols_ok(h, b4, Nil{}) == True{} : Bool}, hc: {Laws.lastm(b4, n, None{}) == Some{c} : Maybe<&1, C.Column>}) -> RepRes(False{}, b4, n, h, Nil{}, None{}, c):
  w(False{}, Nil{}, None{}, c, hok, ({==}, hc))

# replace gives the frame back (copies b3 for the names, b4 for the walk)
def part_rep(+h2: U32, -cols: List<&1, C.Named>, +n: String, +h: U32, c: C.Column, +hh: {h2 == h : U32}, hok: {Laws.cols_ok(h, cols, Nil{}) == True{} : Bool}, hc: {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>},
  b3: List<&1, C.Named>, +e3: {b3 == cols : List<&1, C.Named>}, b4: List<&1, C.Named>, +e4: {b4 == cols : List<&1, C.Named>})
  -> {C.Frame.replace(Laws.holedf(C.Frame{h2, cols}, n), n, c) == Done{C.Frame{h2, cols}} : E.ResT(C.Frame)}:
  %e4 : {C.Frame.replace(Laws.holedf(C.Frame{h2, _}, n), n, c) == Done{C.Frame{h2, _}} : E.ResT(C.Frame)}
  part_rep_n(h2, b4, n, h, c, hh,
    (%Equal.trans(List<&1, C.Named>, b3, cols, b4, e3, Equal.sym(List<&1, C.Named>, b4, cols, e4)) : NamesW(_, n); names_w(b3, n)),
    rep_app(b4, n, h, c, rep_g(b4, n, h, Nil{}),
      (%Equal.sym(List<&1, C.Named>, b4, cols, e4) : {Laws.cols_ok(h, _, Nil{}) == True{} : Bool}; hok),
      (%Equal.sym(List<&1, C.Named>, b4, cols, e4) : {Laws.lastm(_, n, None{}) == Some{c} : Maybe<&1, C.Column>}; hc)))

def lend_obs_k3(+h2: U32, -cols: List<&1, C.Named>, +n: String, +h: U32, c: C.Column, +hf: {Laws.frame_ok(h, C.Frame{h2, cols}) == True{} : Bool}, +hc: {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>},
  a: List<&1, C.Named>, +ea: {a == cols : List<&1, C.Named>}, b1: List<&1, C.Named>, +e1: {b1 == cols : List<&1, C.Named>}, -b2: List<&1, C.Named>, +e2: {b2 == cols : List<&1, C.Named>}, w: ColsDup(b2))
  -> Laws.LendObs(C.Frame{h2, cols}, n, c):
  (b3, b4, +e3, e4) = w
  (part_lend(h2, cols, n, c, b1, e1, hc),
   part_get(h2, cols, n, c, a, ea, hc),
   part_rep(h2, cols, n, h, c, PV.u32_eq_sound(h2, h, PV.and_l(U32.is_eq(h2, h), Laws.cols_ok(h, cols, Nil{}), hf)), L.and_right(U32.is_eq(h2, h), Laws.cols_ok(h, cols, Nil{}), hf), hc,
     b3, Equal.trans(List<&1, C.Named>, b3, b2, cols, e3, e2), b4, Equal.trans(List<&1, C.Named>, b4, b2, cols, e4, e2)))

def lend_obs_k2(+h2: U32, -cols: List<&1, C.Named>, +n: String, +h: U32, c: C.Column, +hf: {Laws.frame_ok(h, C.Frame{h2, cols}) == True{} : Bool}, +hc: {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>},
  a: List<&1, C.Named>, +ea: {a == cols : List<&1, C.Named>}, -b: List<&1, C.Named>, +eb: {b == cols : List<&1, C.Named>}, w: ColsDup(b))
  -> Laws.LendObs(C.Frame{h2, cols}, n, c):
  (b1, b2, +e1, e2) = w
  lend_obs_k3(h2, cols, n, h, c, hf, hc, a, ea, b1, Equal.trans(List<&1, C.Named>, b1, b, cols, e1, eb), b2, Equal.trans(List<&1, C.Named>, b2, b, cols, e2, eb), cols_dup(b2))

def lend_obs_k(+h2: U32, -cols: List<&1, C.Named>, +n: String, +h: U32, c: C.Column, +hf: {Laws.frame_ok(h, C.Frame{h2, cols}) == True{} : Bool}, +hc: {Laws.lastm(cols, n, None{}) == Some{c} : Maybe<&1, C.Column>}, w: ColsDup(cols))
  -> Laws.LendObs(C.Frame{h2, cols}, n, c):
  (a, b, +ea, eb) = w
  lend_obs_k2(h2, cols, n, h, c, hf, hc, a, ea, b, eb, cols_dup(b))

def Laws.lend_observes(f, n, h, c, hf, hc):
  match f:
    case C.Frame{+h2, cols}:
      lend_obs_k(h2, cols, n, h, c, hf, hc, cols_dup(cols))

# ---- the liveness pass: Eval.mark changes no read, and every move it makes is the last read ----------
#
# Inductions over the code (one case per instruction: a `case other` does not refine the goal) and
# over the expression (Eval.compile). Generated by gen_mark.py (scratchpad of T3.1); the case lists
# are mechanical.

# mark.c's instruction reads n whichever it is
def mr_c(b: Bool, +n: String, -mt: List<&2, V.Instr>) -> {V.Eval.reads(V.Eval.mark.c(b, n) <> mt) == n <> V.Eval.reads(mt) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.mark_reads(code, all, dead, later):
  match code:
    case Nil{}:
      {==}
    case V.IConst{v, ty} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.ICol{+n} <> +t:
      %Laws.mark_reads(t, all, dead, later) : {V.Eval.reads(V.Eval.mark.c(Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(V.Eval.reads(t), n)))), n) <> V.Eval.mark(t, all, dead, later)) == n <> _ : List<&2, String>}
      mr_c(Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(V.Eval.reads(t), n)))), n, V.Eval.mark(t, all, dead, later))
    case V.IUn{op} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IBin{op} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.ICast{to} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.ITry{to} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IFill{} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IAgg{op} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IWhen{} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IIsIn{vs} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IClip{lo, hi} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IStr{op, pat} <> +t:
      Laws.mark_reads(t, all, dead, later)
    case V.IMove{n} <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, x => n <> x, V.Eval.reads(V.Eval.mark(t, all, dead, later)), V.Eval.reads(t), Laws.mark_reads(t, all, dead, later))

# the marked ICol: a move (cond True) is allowed and last, by the condition itself and mark_reads
def mmo_c(b: Bool, +n: String, +t: List<&2, V.Instr>, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>, eb: {Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(V.Eval.reads(t), n)))) == b : Bool},
  ih: {Laws.moves_ok(V.Eval.mark(t, all, dead, later), all, dead, later) == True{} : Bool})
  -> {Laws.moves_ok(V.Eval.mark.c(b, n) <> V.Eval.mark(t, all, dead, later), all, dead, later) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, String>, V.Eval.reads(V.Eval.mark(t, all, dead, later)), V.Eval.reads(t), Laws.mark_reads(t, all, dead, later)) : {Bool.and(Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(_, n)))), Laws.moves_ok(V.Eval.mark(t, all, dead, later), all, dead, later)) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(V.Eval.reads(t), n)))), True{}, eb) : {Bool.and(_, Laws.moves_ok(V.Eval.mark(t, all, dead, later), all, dead, later)) == True{} : Bool}
      ih
    case False{}:
      ih

def Laws.mark_moves_ok(code, all, dead, later, h):
  match code:
    case Nil{}:
      {==}
    case V.IConst{v, ty} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.ICol{+n} <> +t:
      mmo_c(Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(V.Eval.reads(t), n)))), n, t, all, dead, later, {==}, Laws.mark_moves_ok(t, all, dead, later, h))
    case V.IUn{op} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IBin{op} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.ICast{to} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.ITry{to} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IFill{} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IAgg{op} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IWhen{} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IIsIn{vs} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IClip{lo, hi} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IStr{op, pat} <> +t:
      Laws.mark_moves_ok(t, all, dead, later, h)
    case V.IMove{n} <> t:
      Empty.absurd({Laws.moves_ok(V.Eval.mark(V.IMove{n} <> t, all, dead, later), all, dead, later) == True{} : Bool}, L.false_true(h))

# a typed null literal compiles to IConst, otherwise to the operand's code: no move either way
def cn_cast(b: Bool, +to: D.DType, +acc: List<&2, V.Instr>, -code: List<&2, V.Instr>, h: {Laws.nomove(acc) == True{} : Bool}, ih: {Laws.nomove(code) == True{} : Bool})
  -> {Laws.nomove(V.Eval.compile.cast(b, to, acc, code)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      ih

def Laws.compile_nomove(e, acc, h):
  match e:
    case X.Col{n}:
      h
    case X.Lit{v}:
      h
    case X.Alias{e2, n}:
      Laws.compile_nomove(e2, acc, h)
    case X.Cast{+e2, +to}:
      cn_cast(X.Expr.is_null_lit(e2), to, acc, V.Eval.compile(e2, V.ICast{to} <> acc), h, Laws.compile_nomove(e2, V.ICast{to} <> acc, h))
    case X.TryCast{+e2, +to}:
      cn_cast(X.Expr.is_null_lit(e2), to, acc, V.Eval.compile(e2, V.ITry{to} <> acc), h, Laws.compile_nomove(e2, V.ITry{to} <> acc, h))
    case X.Un{+op, e2}:
      Laws.compile_nomove(e2, V.IUn{op} <> acc, h)
    case X.Bin{+op, a, +b}:
      Laws.compile_nomove(a, V.Eval.compile(b, V.IBin{op} <> acc), Laws.compile_nomove(b, V.IBin{op} <> acc, h))
    case X.FillNull{e2, +v}:
      Laws.compile_nomove(e2, V.Eval.compile(v, V.IFill{} <> acc), Laws.compile_nomove(v, V.IFill{} <> acc, h))
    case X.Agg{+op, e2}:
      Laws.compile_nomove(e2, V.IAgg{op} <> acc, h)
    case X.When{c, +a, +b}:
      Laws.compile_nomove(c, V.Eval.compile(a, V.Eval.compile(b, V.IWhen{} <> acc)), Laws.compile_nomove(a, V.Eval.compile(b, V.IWhen{} <> acc), Laws.compile_nomove(b, V.IWhen{} <> acc, h)))
    case X.IsIn{e2, +vs}:
      Laws.compile_nomove(e2, V.IIsIn{vs} <> acc, h)
    case X.Clip{e2, +lo, +hi}:
      Laws.compile_nomove(e2, V.IClip{lo, hi} <> acc, h)
    case X.StrPred{+op, e2, +p}:
      Laws.compile_nomove(e2, V.IStr{op, p} <> acc, h)

# a typed null literal reads nothing
def nl_refs(e2: X.Expr, -x: List<&2, String>, h: {X.Expr.is_null_lit(e2) == True{} : Bool}) -> {X.Expr.refs.go(e2, x) == x : List<&2, String>}:
  match e2:
    case X.Col{n}:
      Empty.absurd({X.Expr.refs.go(X.Col{n}, x) == x : List<&2, String>}, L.false_true(h))
    case X.Lit{v}:
      {==}
    case X.Alias{e2, n}:
      Empty.absurd({X.Expr.refs.go(X.Alias{e2, n}, x) == x : List<&2, String>}, L.false_true(h))
    case X.Cast{e2, to}:
      Empty.absurd({X.Expr.refs.go(X.Cast{e2, to}, x) == x : List<&2, String>}, L.false_true(h))
    case X.TryCast{e2, to}:
      Empty.absurd({X.Expr.refs.go(X.TryCast{e2, to}, x) == x : List<&2, String>}, L.false_true(h))
    case X.Un{op, e2}:
      Empty.absurd({X.Expr.refs.go(X.Un{op, e2}, x) == x : List<&2, String>}, L.false_true(h))
    case X.Bin{op, a, b}:
      Empty.absurd({X.Expr.refs.go(X.Bin{op, a, b}, x) == x : List<&2, String>}, L.false_true(h))
    case X.FillNull{e2, v}:
      Empty.absurd({X.Expr.refs.go(X.FillNull{e2, v}, x) == x : List<&2, String>}, L.false_true(h))
    case X.Agg{op, e2}:
      Empty.absurd({X.Expr.refs.go(X.Agg{op, e2}, x) == x : List<&2, String>}, L.false_true(h))
    case X.When{c, a, b}:
      Empty.absurd({X.Expr.refs.go(X.When{c, a, b}, x) == x : List<&2, String>}, L.false_true(h))
    case X.IsIn{e2, vs}:
      Empty.absurd({X.Expr.refs.go(X.IsIn{e2, vs}, x) == x : List<&2, String>}, L.false_true(h))
    case X.Clip{e2, lo, hi}:
      Empty.absurd({X.Expr.refs.go(X.Clip{e2, lo, hi}, x) == x : List<&2, String>}, L.false_true(h))
    case X.StrPred{op, e2, p}:
      Empty.absurd({X.Expr.refs.go(X.StrPred{op, e2, p}, x) == x : List<&2, String>}, L.false_true(h))

def cr_cast(e2: X.Expr, b: Bool, eb: {X.Expr.is_null_lit(e2) == b : Bool}, +to: D.DType, +acc: List<&2, V.Instr>, -code: List<&2, V.Instr>,
  ih: {V.Eval.reads(code) == X.Expr.refs.go(e2, V.Eval.reads(acc)) : List<&2, String>})
  -> {V.Eval.reads(V.Eval.compile.cast(b, to, acc, code)) == X.Expr.refs.go(e2, V.Eval.reads(acc)) : List<&2, String>}:
  match b:
    case True{}:
      Equal.sym(List<&2, String>, X.Expr.refs.go(e2, V.Eval.reads(acc)), V.Eval.reads(acc), nl_refs(e2, V.Eval.reads(acc), eb))
    case False{}:
      ih

def Laws.compile_reads(e, acc):
  match e:
    case X.Col{n}:
      {==}
    case X.Lit{v}:
      {==}
    case X.Alias{e2, n}:
      Laws.compile_reads(e2, acc)
    case X.Cast{+e2, +to}:
      cr_cast(e2, X.Expr.is_null_lit(e2), {==}, to, acc, V.Eval.compile(e2, V.ICast{to} <> acc), Laws.compile_reads(e2, V.ICast{to} <> acc))
    case X.TryCast{+e2, +to}:
      cr_cast(e2, X.Expr.is_null_lit(e2), {==}, to, acc, V.Eval.compile(e2, V.ITry{to} <> acc), Laws.compile_reads(e2, V.ITry{to} <> acc))
    case X.Un{+op, e2}:
      Laws.compile_reads(e2, V.IUn{op} <> acc)
    case X.Bin{+op, +a, +b}:
      %Laws.compile_reads(b, V.IBin{op} <> acc) : {V.Eval.reads(V.Eval.compile(a, V.Eval.compile(b, V.IBin{op} <> acc))) == X.Expr.refs.go(a, _) : List<&2, String>}
      Laws.compile_reads(a, V.Eval.compile(b, V.IBin{op} <> acc))
    case X.FillNull{+e2, +v}:
      %Laws.compile_reads(v, V.IFill{} <> acc) : {V.Eval.reads(V.Eval.compile(e2, V.Eval.compile(v, V.IFill{} <> acc))) == X.Expr.refs.go(e2, _) : List<&2, String>}
      Laws.compile_reads(e2, V.Eval.compile(v, V.IFill{} <> acc))
    case X.Agg{+op, e2}:
      Laws.compile_reads(e2, V.IAgg{op} <> acc)
    case X.When{+c, +a, +b}:
      %Laws.compile_reads(b, V.IWhen{} <> acc) : {V.Eval.reads(V.Eval.compile(c, V.Eval.compile(a, V.Eval.compile(b, V.IWhen{} <> acc)))) == X.Expr.refs.go(c, X.Expr.refs.go(a, _)) : List<&2, String>}
      %Laws.compile_reads(a, V.Eval.compile(b, V.IWhen{} <> acc)) : {V.Eval.reads(V.Eval.compile(c, V.Eval.compile(a, V.Eval.compile(b, V.IWhen{} <> acc)))) == X.Expr.refs.go(c, _) : List<&2, String>}
      Laws.compile_reads(c, V.Eval.compile(a, V.Eval.compile(b, V.IWhen{} <> acc)))
    case X.IsIn{e2, +vs}:
      Laws.compile_reads(e2, V.IIsIn{vs} <> acc)
    case X.Clip{e2, +lo, +hi}:
      Laws.compile_reads(e2, V.IClip{lo, hi} <> acc)
    case X.StrPred{+op, e2, +p}:
      Laws.compile_reads(e2, V.IStr{op, p} <> acc)

