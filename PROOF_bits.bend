# PROOF_bits.bend -- the bit-vector toolkit behind the P1 content theorems (M5):
# single-bit words (2^d as Array.size computes it), "below 2^d" as a predicate on
# the bits, the comparison / subtraction / masking facts the production index
# arithmetic of Array.get and Array.set relies on, and the U32 <-> Nat bridge
# (Word.to_nat) for the kernels' Nat fuel. Every lemma is an induction over the
# word length (or over a Nat), no axiom. See PROOF_lib.bend for the toolkit.
import Base
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L

# ---- words: a single bit, c-then-zeros, the low mask ---------------------------------------

# the bit at position p of an n-bit word (zero when p >= n): U32.shln(1, d) is bitw(32n, d)
def bitw(n: Nat, p: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+q:
      match p:
        case 0n:
          WCon{True{}, Word.zero(q)}
        case 1n+r:
          WCon{False{}, bitw(q, r)}

# the ones below position d (all ones when d >= n): U32.sub(2^d, 1)
def lowmask(n: Nat, d: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+q:
      match d:
        case 0n:
          Word.zero(1n+q)
        case 1n+r:
          WCon{True{}, lowmask(q, r)}

# all ones
def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+q:
      WCon{True{}, ones(q)}

# c then zeros, at any length (WNil at length 0)
def putz(q: Nat, c: Bool) -> Word(q):
  match q:
    case 0n:
      WNil{}
    case 1n+r:
      WCon{c, Word.zero(r)}

# the bits at positions >= d are zero: the word is below 2^d
def Zabove(d: Nat, n: Nat, w: Word(n)) -> Type:
  match d n:
    case 0n _:
      {w == Word.zero(n) : Word(n)}
    case 1n+r 0n:
      Unit
    case 1n+r 1n+p:
      match w:
        case WCon{b, t}:
          Zabove(r, p, t)

# ---- shl / shr / pad of these words ----------------------------------------------------------

def putz_f(q: Nat) -> {putz(q, False{}) == Word.zero(q) : Word(q)}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def put_zero(q: Nat, c: Bool) -> {Word.shl.put(q, c, Word.zero(q)) == putz(q, c) : Word(q)}:
  match q:
    case 0n:
      {==}
    case 1n++r:
      %putz_f(r) : {WCon{c, Word.shl.put(r, False{}, Word.zero(r))} == WCon{c, _} : Word(1n+r)}
      %put_zero(r, False{}) : {WCon{c, Word.shl.put(r, False{}, Word.zero(r))} == WCon{c, _} : Word(1n+r)}
      {==}

def put_f(n: Nat, w: Word(n)) -> {Word.shl.put(n, False{}, w) == Word.shl(n, w) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          {==}

def put_f_cong(n: Nat, w: Word(n)) -> {WCon{False{}, Word.shl.put(n, False{}, w)} == WCon{False{}, Word.shl(n, w)} : Word(1n+n)}:
  %put_f(n, w) : {WCon{False{}, Word.shl.put(n, False{}, w)} == WCon{False{}, _} : Word(1n+n)}
  {==}

def shl_bit0(q: Nat) -> {Word.shl(1n+q, WCon{True{}, Word.zero(q)}) == bitw(1n+q, 1n) : Word(1n+q)}:
  match q:
    case 0n:
      {==}
    case 1n++r:
      %put_zero(1n+r, True{}) : {WCon{False{}, Word.shl.put(1n+r, True{}, Word.zero(1n+r))} == WCon{False{}, _} : Word(2n+r)}
      {==}

# shl moves the bit up one position
def shl_bitw(n: Nat, p: Nat) -> {Word.shl(n, bitw(n, p)) == bitw(n, 1n+p) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      match p:
        case 0n:
          shl_bit0(q)
        case 1n++r:
          %shl_bitw(q, r) : {WCon{False{}, Word.shl.put(q, False{}, bitw(q, r))} == WCon{False{}, _} : Word(1n+q)}
          put_f_cong(q, bitw(q, r))

# U32.shln(1, d) is the single bit at position d
def shln_bitw(d: Nat) -> {U32.shln(1, d) == U32{bitw(32n, d)} : U32}:
  match d:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(U32, U32.shln(1, p), U32{bitw(32n, p)}, shln_bitw(p)) : {U32.shl(_) == U32{WCon{False{}, bitw(31n, p)}} : U32}
      %Equal.sym(Word(32n), Word.shl(32n, bitw(32n, p)), bitw(32n, 1n+p), shl_bitw(32n, p)) : {U32{_} == U32{WCon{False{}, bitw(31n, p)}} : U32}
      {==}

def pad_zero(m: Nat) -> {Word.shr.pad(m, Word.zero(m)) == Word.zero(1n+m) : Word(1n+m)}:
  match m:
    case 0n:
      {==}
    case 1n++r:
      %pad_zero(r) : {WCon{False{}, Word.shr.pad(r, Word.zero(r))} == WCon{False{}, _} : Word(2n+r)}
      {==}

# shr of a single bit: the bit one position down, or zero when the bit was absent
def HalfSpec(b: Bool, n: Nat, p: Nat) -> Type:
  match b:
    case True{}:
      {Word.shr.pad(n, bitw(n, p)) == bitw(1n+n, p) : Word(1n+n)}
    case False{}:
      {bitw(n, p) == Word.zero(n) : Word(n)}

def pad_bitw_k(b: Bool, +m: Nat, +r: Nat, h: HalfSpec(b, m, r)) -> HalfSpec(b, 1n+m, 1n+r):
  match b:
    case True{}:
      %h : {WCon{False{}, Word.shr.pad(m, bitw(m, r))} == WCon{False{}, _} : Word(2n+m)}
      {==}
    case False{}:
      %h : {WCon{False{}, bitw(m, r)} == WCon{False{}, _} : Word(1n+m)}
      {==}

def pad_bitw_fin(+m: Nat, +r: Nat, w: &b: Bool -> HalfSpec(b, m, r)) -> &b2: Bool -> HalfSpec(b2, 1n+m, 1n+r):
  (+b, h) = w
  (b, pad_bitw_k(b, m, r, h))

def pad_bitw(n: Nat, p: Nat) -> &b: Bool -> HalfSpec(b, n, p):
  match n:
    case 0n:
      (False{}, {==})
    case 1n++m:
      match p:
        case 0n:
          (True{}, (%pad_zero(m) : {WCon{True{}, Word.shr.pad(m, Word.zero(m))} == WCon{True{}, _} : Word(2n+m)}; {==}))
        case 1n++r:
          pad_bitw_fin(m, r, pad_bitw(m, r))

# the same for U32.shr(U32.shln(1, 1+p)): either U32.shln(1, p), or shln(1, 1+p) was already 0
def ShrSpec(b: Bool, p: Nat) -> Type:
  match b:
    case True{}:
      {U32.shr(U32.shln(1, 1n+p)) == U32.shln(1, p) : U32}
    case False{}:
      {U32.shln(1, 1n+p) == 0 : U32}

def shr_shln_k(b: Bool, +p: Nat, h: HalfSpec(b, 31n, p)) -> ShrSpec(b, p):
  match b:
    case True{}:
      %Equal.sym(U32, U32.shln(1, 1n+p), U32{bitw(32n, 1n+p)}, shln_bitw(1n+p)) : {U32.shr(_) == U32.shln(1, p) : U32}
      %Equal.sym(U32, U32.shln(1, p), U32{bitw(32n, p)}, shln_bitw(p)) : {U32.shr(U32{bitw(32n, 1n+p)}) == _ : U32}
      %Equal.sym(Word(32n), Word.shr.pad(31n, bitw(31n, p)), bitw(32n, p), h) : {U32{_} == U32{bitw(32n, p)} : U32}
      {==}
    case False{}:
      %Equal.sym(U32, U32.shln(1, 1n+p), U32{bitw(32n, 1n+p)}, shln_bitw(1n+p)) : {_ == 0 : U32}
      %Equal.sym(Word(31n), bitw(31n, p), Word.zero(31n), h) : {U32{WCon{False{}, _}} == 0 : U32}
      {==}

def shr_shln_fin(+p: Nat, w: &b: Bool -> HalfSpec(b, 31n, p)) -> &b2: Bool -> ShrSpec(b2, p):
  (+b, h) = w
  (b, shr_shln_k(b, p, h))

def shr_shln(+p: Nat) -> &b: Bool -> ShrSpec(b, p):
  shr_shln_fin(p, pad_bitw(31n, p))

# ---- comparison with zero and with a single bit -----------------------------------------------

# Cmp.is_lt(c) == True gives c == LT
def is_lt_lt(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, L.false_true(h))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, L.false_true(h))

# Cmp.is_lt(c) == False gives c != LT (as: c == LT refutes)
def is_lt_not(c: Cmp, h: {Cmp.is_lt(c) == False{} : Bool}, e: {c == LT{} : Cmp}) -> Empty:
  match c:
    case LT{}:
      L.true_false(h)
    case EQ{}:
      L.eq_lt(e)
    case GT{}:
      L.gt_lt(e)

# nothing is below zero: the tail step with c = cmp(t, zero)
def lt_zero_k(a: Bool, c: Cmp, -p: Nat, -t: Word(p), e: {Word.cmp(p, t, Word.zero(p)) == c : Cmp}, h: {Word.cmp.fin(a, False{}, c) == LT{} : Cmp}, ih: {Word.cmp(p, t, Word.zero(p)) == LT{} : Cmp} -> Empty) -> Empty:
  match a c:
    case _ LT{}:
      ih(e)
    case False{} EQ{}:
      L.eq_lt(h)
    case True{} EQ{}:
      L.gt_lt(h)
    case _ GT{}:
      L.gt_lt(h)

def lt_zero(n: Nat, w: Word(n), h: {Word.cmp(n, w, Word.zero(n)) == LT{} : Cmp}) -> Empty:
  match n:
    case 0n:
      L.eq_lt(h)
    case 1n++p:
      match w:
        case WCon{a, +t}:
          lt_zero_k(a, Word.cmp(p, t, Word.zero(p)), p, t, {==}, h, e => lt_zero(p, t, e))

# below the lowest bit (1) means zero: the step with c = cmp(t, zero)
def lt_one_k(a: Bool, c: Cmp, +p: Nat, +t: Word(p), e: {Word.cmp(p, t, Word.zero(p)) == c : Cmp}, h: {Word.cmp.fin(a, True{}, c) == LT{} : Cmp}) -> {WCon{a, t} == WCon{False{}, Word.zero(p)} : Word(1n+p)}:
  match a c:
    case _ LT{}:
      Empty.absurd({WCon{a, t} == WCon{False{}, Word.zero(p)} : Word(1n+p)}, lt_zero(p, t, e))
    case False{} EQ{}:
      %Equal.sym(Word(p), t, Word.zero(p), L.word_cmp_eq(p, t, Word.zero(p), e)) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
      {==}
    case True{} EQ{}:
      Empty.absurd({WCon{True{}, t} == WCon{False{}, Word.zero(p)} : Word(1n+p)}, L.eq_lt(h))
    case _ GT{}:
      Empty.absurd({WCon{a, t} == WCon{False{}, Word.zero(p)} : Word(1n+p)}, L.gt_lt(h))

# below the bit at position 1+r: the step with c = cmp(t, bitw(p, r))
def lt_bit_k(a: Bool, c: Cmp, -p: Nat, -r: Nat, -t: Word(p), e: {Word.cmp(p, t, bitw(p, r)) == c : Cmp}, h: {Word.cmp.fin(a, False{}, c) == LT{} : Cmp}, ih: {Word.cmp(p, t, bitw(p, r)) == LT{} : Cmp} -> Zabove(r, p, t)) -> Zabove(r, p, t):
  match a c:
    case _ LT{}:
      ih(e)
    case False{} EQ{}:
      Empty.absurd(Zabove(r, p, t), L.eq_lt(h))
    case True{} EQ{}:
      Empty.absurd(Zabove(r, p, t), L.gt_lt(h))
    case _ GT{}:
      Empty.absurd(Zabove(r, p, t), L.gt_lt(h))

# a word below 2^q has its bits >= q clear
def lt_bitw_zabove(n: Nat, q: Nat, w: Word(n), h: {Word.cmp(n, w, bitw(n, q)) == LT{} : Cmp}) -> Zabove(q, n, w):
  match n:
    case 0n:
      Empty.absurd(Zabove(q, 0n, w), L.eq_lt(h))
    case 1n++p:
      match q:
        case 0n:
          match w:
            case WCon{a, +t}:
              lt_one_k(a, Word.cmp(p, t, Word.zero(p)), p, t, {==}, h)
        case 1n++r:
          match w:
            case WCon{a, +t}:
              lt_bit_k(a, Word.cmp(p, t, bitw(p, r)), p, r, t, {==}, h, e => lt_bitw_zabove(p, r, t, e))

# ---- subtraction: self, cancellation, clearing the top bit ------------------------------------

# w - w == 0 (Word.sub is adc with the complement and carry 1)
def sub_self(n: Nat, w: Word(n)) -> {Word.adc(n, w, w, True{}, True{}) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          %sub_self(p, t) : {WCon{False{}, Word.adc(p, t, t, True{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %sub_self(p, t) : {WCon{False{}, Word.adc(p, t, t, True{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}

# (w - h) + h == w, with the carries generalised: adc(adc(w, h, T, c), h, F, not c) == w
def cancel_go(n: Nat, w: Word(n), h: Word(n), c: Bool) -> {Word.adc(n, Word.adc(n, w, h, True{}, c), h, False{}, Bool.not(c)) == w : Word(n)}:
  match n:
    case 0n:
      match w h:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match w h c:
        case WCon{False{}, +t} WCon{False{}, +u} False{}:
          %cancel_go(p, t, u, False{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, True{}, False{}), u, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} WCon{False{}, +u} True{}:
          %cancel_go(p, t, u, True{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, True{}, True{}), u, False{}, False{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} WCon{True{}, +u} False{}:
          %cancel_go(p, t, u, False{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, True{}, False{}), u, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} WCon{True{}, +u} True{}:
          %cancel_go(p, t, u, False{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, True{}, False{}), u, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{False{}, +u} False{}:
          %cancel_go(p, t, u, True{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, True{}, True{}), u, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{False{}, +u} True{}:
          %cancel_go(p, t, u, True{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, True{}, True{}), u, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{True{}, +u} False{}:
          %cancel_go(p, t, u, False{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, True{}, False{}), u, False{}, True{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{True{}, +u} True{}:
          %cancel_go(p, t, u, True{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, True{}, True{}), u, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}

def add_sub(n: Nat, w: Word(n), h: Word(n)) -> {Word.add(n, Word.sub(n, w, h), h) == w : Word(n)}:
  cancel_go(n, w, h, True{})

# subtracting the same word from two words that agree afterwards: they were equal
def sub_inj(+n: Nat, +w: Word(n), +v: Word(n), +h: Word(n), e: {Word.sub(n, w, h) == Word.sub(n, v, h) : Word(n)}) -> {w == v : Word(n)}:
  %add_sub(n, w, h) : {_ == v : Word(n)}
  %add_sub(n, v, h) : {Word.add(n, Word.sub(n, w, h), h) == _ : Word(n)}
  %Equal.sym(Word(n), Word.sub(n, w, h), Word.sub(n, v, h), e) : {Word.add(n, _, h) == Word.add(n, Word.sub(n, v, h), h) : Word(n)}
  {==}

# the lowest-bit case of sub_bit: w = WCon{a, t} with t = 0 and NOT w < 1 gives a = T, w - 1 = 0
def sub_one_k(a: Bool, +m: Nat, nlt: {Cmp.is_lt(Word.cmp.fin(a, True{}, EQ{})) == False{} : Bool}) -> {Word.adc(1n+m, WCon{a, Word.zero(m)}, WCon{True{}, Word.zero(m)}, True{}, True{}) == Word.zero(1n+m) : Word(1n+m)}:
  match a:
    case False{}:
      Empty.absurd({Word.adc(1n+m, WCon{False{}, Word.zero(m)}, WCon{True{}, Word.zero(m)}, True{}, True{}) == Word.zero(1n+m) : Word(1n+m)}, L.true_false(nlt))
    case True{}:
      %sub_self(m, Word.zero(m)) : {WCon{False{}, Word.adc(m, Word.zero(m), Word.zero(m), True{}, True{})} == WCon{False{}, _} : Word(1n+m)}
      {==}

# the tail step of sub_bit: NOT (fin(a, F, c) is LT) gives NOT (c is LT)
def not_lt_tail(a: Bool, c: Cmp, h: {Cmp.is_lt(Word.cmp.fin(a, False{}, c)) == False{} : Bool}) -> {Cmp.is_lt(c) == False{} : Bool}:
  match c:
    case LT{}:
      h
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the lowest-bit case of sub_bit over the whole word: t = 0 moves into the goal first
def sub_bit_one(a: Bool, +m: Nat, -t: Word(m), hz: {t == Word.zero(m) : Word(m)}) -> {Cmp.is_lt(Word.cmp(1n+m, WCon{a, t}, WCon{True{}, Word.zero(m)})) == False{} : Bool} -> {Word.sub(1n+m, WCon{a, t}, WCon{True{}, Word.zero(m)}) == Word.zero(1n+m) : Word(1n+m)}:
  %Equal.sym(Word(m), t, Word.zero(m), hz) : {Cmp.is_lt(Word.cmp(1n+m, WCon{a, _}, WCon{True{}, Word.zero(m)})) == False{} : Bool} -> {Word.sub(1n+m, WCon{a, _}, WCon{True{}, Word.zero(m)}) == Word.zero(1n+m) : Word(1n+m)}
  %Equal.sym(Cmp, Word.cmp(m, Word.zero(m), Word.zero(m)), EQ{}, L.word_cmp_refl(m, Word.zero(m))) : {Cmp.is_lt(Word.cmp.fin(a, True{}, _)) == False{} : Bool} -> {Word.sub(1n+m, WCon{a, Word.zero(m)}, WCon{True{}, Word.zero(m)}) == Word.zero(1n+m) : Word(1n+m)}
  nlt => sub_one_k(a, m, nlt)

# a word below 2^(1+p) that is not below 2^p: clearing bit p (subtracting it) lands below 2^p
def sub_bit(n: Nat, p: Nat, w: Word(n), hz: Zabove(1n+p, n, w), nlt: {Cmp.is_lt(Word.cmp(n, w, bitw(n, p))) == False{} : Bool}) -> Zabove(p, n, Word.sub(n, w, bitw(n, p))):
  match n:
    case 0n:
      match p:
        case 0n:
          {==}
        case 1n+r:
          Unit{}
    case 1n++m:
      match p:
        case 0n:
          match w:
            case WCon{a, t}:
              sub_bit_one(a, m, t, hz)(nlt)
        case 1n++r:
          match w:
            case WCon{False{}, +t}:
              sub_bit(m, r, t, hz, not_lt_tail(False{}, Word.cmp(m, t, bitw(m, r)), nlt))
            case WCon{True{}, +t}:
              sub_bit(m, r, t, hz, not_lt_tail(True{}, Word.cmp(m, t, bitw(m, r)), nlt))

# ---- the mask Array.get / Array.set apply: i & (2^d - 1) == i below 2^d ----------------------------

def and_zero_l(n: Nat, x: Word(n)) -> {Word.and(n, Word.zero(n), x) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n++p:
      match x:
        case WCon{b, t}:
          %and_zero_l(p, t) : {WCon{False{}, Word.and(p, Word.zero(p), t)} == WCon{False{}, _} : Word(1n+p)}
          {==}

def and_true_r(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# 2^r - 1 with the borrow already taken: adc(bitw, 0, T, F) is the low mask
def dec_bitw(m: Nat, r: Nat) -> {Word.adc(m, bitw(m, r), Word.zero(m), True{}, False{}) == lowmask(m, r) : Word(m)}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      match r:
        case 0n:
          %sub_self(q, Word.zero(q)) : {WCon{False{}, Word.adc(q, Word.zero(q), Word.zero(q), True{}, True{})} == WCon{False{}, _} : Word(1n+q)}
          {==}
        case 1n++r2:
          %dec_bitw(q, r2) : {WCon{True{}, Word.adc(q, bitw(q, r2), Word.zero(q), True{}, False{})} == WCon{True{}, _} : Word(1n+q)}
          {==}

# 2^d - 1 is the low mask (U32.sub(U32.shln(1, d), 1) in Array.get.at / Array.swap.at)
def sub_bitw_one(n: Nat, d: Nat) -> {Word.sub(n, bitw(n, d), bitw(n, 0n)) == lowmask(n, d) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      match d:
        case 0n:
          sub_self(1n+q, WCon{True{}, Word.zero(q)})
        case 1n++r:
          %dec_bitw(q, r) : {WCon{True{}, Word.adc(q, bitw(q, r), Word.zero(q), True{}, False{})} == WCon{True{}, _} : Word(1n+q)}
          {==}

# a word below 2^d is unchanged by the low mask
def and_lowmask(d: Nat, +n: Nat, w: Word(n), hz: Zabove(d, n, w)) -> {Word.and(n, w, lowmask(n, d)) == w : Word(n)}:
  match d n:
    case 0n _:
      %Equal.sym(Word(n), w, Word.zero(n), hz) : {Word.and(n, _, lowmask(n, 0n)) == _ : Word(n)}
      and_zero_l(n, lowmask(n, 0n))
    case 1n+r 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++r 1n++p:
      match w:
        case WCon{+b, +t}:
          %and_true_r(b) : {WCon{Bool.and(b, True{}), Word.and(p, t, lowmask(p, r))} == WCon{_, t} : Word(1n+p)}
          %and_lowmask(r, p, t, hz) : {WCon{Bool.and(b, True{}), Word.and(p, t, lowmask(p, r))} == WCon{Bool.and(b, True{}), _} : Word(1n+p)}
          {==}

# the U32 form: i & (U32.shln(1, d) - 1) == i for i below 2^d
def mask_id(+d: Nat, +i: Word(32n), hz: Zabove(d, 32n, i)) -> {U32.and(U32{i}, U32.sub(U32.shln(1, d), 1)) == U32{i} : U32}:
  %Equal.sym(U32, U32.shln(1, d), U32{bitw(32n, d)}, shln_bitw(d)) : {U32.and(U32{i}, U32.sub(_, 1)) == U32{i} : U32}
  %Equal.sym(Word(32n), Word.sub(32n, bitw(32n, d), bitw(32n, 0n)), lowmask(32n, d), sub_bitw_one(32n, d)) : {U32.and(U32{i}, U32{_}) == U32{i} : U32}
  %and_lowmask(d, 32n, i, hz) : {U32{Word.and(32n, i, lowmask(32n, d))} == U32{_} : U32}
  {==}

# ---- k < inc(j) is k < j or k == j (for every word: inc(ones) is 0 and nothing is below 0) ----------

def IncLt(b: Bool, n: Nat, k: Word(n), j: Word(n)) -> Type:
  match b:
    case True{}:
      {Word.cmp(n, k, j) == LT{} : Cmp}
    case False{}:
      {k == j : Word(n)}

# j = WCon{F, u}, inc j = WCon{T, u}; c = cmp(t, u)
def inc_lt_lo(a: Bool, c: Cmp, +p: Nat, +t: Word(p), +u: Word(p), e: {Word.cmp(p, t, u) == c : Cmp}, h: {Word.cmp.fin(a, True{}, c) == LT{} : Cmp}) -> &b: Bool -> IncLt(b, 1n+p, WCon{a, t}, WCon{False{}, u}):
  match a c:
    case _ LT{}:
      (True{}, (%Equal.sym(Cmp, Word.cmp(p, t, u), LT{}, e) : {Word.cmp.fin(a, False{}, _) == LT{} : Cmp}; {==}))
    case False{} EQ{}:
      (False{}, (%Equal.sym(Word(p), t, u, L.word_cmp_eq(p, t, u, e)) : {WCon{False{}, _} == WCon{False{}, u} : Word(1n+p)}; {==}))
    case True{} EQ{}:
      Empty.absurd(&b: Bool -> IncLt(b, 1n+p, WCon{True{}, t}, WCon{False{}, u}), L.eq_lt(h))
    case _ GT{}:
      Empty.absurd(&b: Bool -> IncLt(b, 1n+p, WCon{a, t}, WCon{False{}, u}), L.gt_lt(h))

# j = WCon{T, u}, inc j = WCon{F, inc u}; the induction hypothesis decided t against u
def inc_lt_hi_k(a: Bool, b: Bool, +p: Nat, +t: Word(p), +u: Word(p), s: IncLt(b, p, t, u)) -> &b2: Bool -> IncLt(b2, 1n+p, WCon{a, t}, WCon{True{}, u}):
  match a b:
    case _ True{}:
      (True{}, (%Equal.sym(Cmp, Word.cmp(p, t, u), LT{}, s) : {Word.cmp.fin(a, True{}, _) == LT{} : Cmp}; {==}))
    case False{} False{}:
      (True{}, (%Equal.sym(Word(p), t, u, s) : {Word.cmp.fin(False{}, True{}, Word.cmp(p, _, u)) == LT{} : Cmp}; %Equal.sym(Cmp, Word.cmp(p, u, u), EQ{}, L.word_cmp_refl(p, u)) : {Word.cmp.fin(False{}, True{}, _) == LT{} : Cmp}; {==}))
    case True{} False{}:
      (False{}, (%Equal.sym(Word(p), t, u, s) : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}; {==}))

def inc_lt_hi_fin(a: Bool, +p: Nat, +t: Word(p), +u: Word(p), w: &b: Bool -> IncLt(b, p, t, u)) -> &b2: Bool -> IncLt(b2, 1n+p, WCon{a, t}, WCon{True{}, u}):
  (+b, s) = w
  inc_lt_hi_k(a, b, p, t, u, s)

def inc_lt_hi(a: Bool, c: Cmp, +p: Nat, +t: Word(p), +u: Word(p), e: {Word.cmp(p, t, Word.inc(p, u)) == c : Cmp}, h: {Word.cmp.fin(a, False{}, c) == LT{} : Cmp}, ih: {Word.cmp(p, t, Word.inc(p, u)) == LT{} : Cmp} -> &b: Bool -> IncLt(b, p, t, u)) -> &b2: Bool -> IncLt(b2, 1n+p, WCon{a, t}, WCon{True{}, u}):
  match a c:
    case _ LT{}:
      inc_lt_hi_fin(a, p, t, u, ih(e))
    case False{} EQ{}:
      Empty.absurd(&b2: Bool -> IncLt(b2, 1n+p, WCon{False{}, t}, WCon{True{}, u}), L.eq_lt(h))
    case True{} EQ{}:
      Empty.absurd(&b2: Bool -> IncLt(b2, 1n+p, WCon{True{}, t}, WCon{True{}, u}), L.gt_lt(h))
    case _ GT{}:
      Empty.absurd(&b2: Bool -> IncLt(b2, 1n+p, WCon{a, t}, WCon{True{}, u}), L.gt_lt(h))

def inc_lt(n: Nat, k: Word(n), j: Word(n), h: {Word.cmp(n, k, Word.inc(n, j)) == LT{} : Cmp}) -> &b: Bool -> IncLt(b, n, k, j):
  match n:
    case 0n:
      Empty.absurd(&b: Bool -> IncLt(b, 0n, k, j), L.eq_lt(h))
    case 1n++p:
      match k j:
        case WCon{a, +t} WCon{False{}, +u}:
          inc_lt_lo(a, Word.cmp(p, t, u), p, t, u, {==}, h)
        case WCon{a, +t} WCon{True{}, +u}:
          inc_lt_hi(a, Word.cmp(p, t, Word.inc(p, u)), p, t, u, {==}, h, e => inc_lt(p, t, u, e))

# ---- the U32 <-> Nat bridge for the kernels' Nat fuel (Word.to_nat) ---------------------------------

# the loop counter after f increments, over words
def waddn(+n: Nat, w: Word(n), f: Nat) -> Word(n):
  match f:
    case 0n:
      w
    case 1n+p:
      Word.inc(n, waddn(n, w, p))

def addn_word(+w: Word(32n), f: Nat) -> {Laws.addn(U32{w}, f) == U32{waddn(32n, w, f)} : U32}:
  match f:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(U32, Laws.addn(U32{w}, p), U32{waddn(32n, w, p)}, addn_word(w, p)) : {U32.inc(_) == U32{Word.inc(32n, waddn(32n, w, p))} : U32}
      {==}

# two increments at the bottom are one increment of the tail
def inc_inc(+m: Nat, c: Bool, +u: Word(m)) -> {Word.inc(1n+m, Word.inc(1n+m, WCon{c, u})) == WCon{c, Word.inc(m, u)} : Word(1n+m)}:
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# 2k increments at the bottom are k increments of the tail
def waddn_double(+m: Nat, +c: Bool, +u: Word(m), k: Nat) -> {waddn(1n+m, WCon{c, u}, Nat.double(k)) == WCon{c, waddn(m, u, k)} : Word(1n+m)}:
  match k:
    case 0n:
      {==}
    case 1n++q:
      %Equal.sym(Word(1n+m), waddn(1n+m, WCon{c, u}, Nat.double(q)), WCon{c, waddn(m, u, q)}, waddn_double(m, c, u, q)) : {Word.inc(1n+m, Word.inc(1n+m, _)) == WCon{c, Word.inc(m, waddn(m, u, q))} : Word(1n+m)}
      inc_inc(m, c, waddn(m, u, q))

# to_nat increments from zero rebuild the word
def from_to(+n: Nat, w: Word(n)) -> {waddn(n, Word.zero(n), Word.to_nat(n, w)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++m:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Word(1n+m), waddn(1n+m, WCon{False{}, Word.zero(m)}, Nat.double(Word.to_nat(m, t))), WCon{False{}, waddn(m, Word.zero(m), Word.to_nat(m, t))}, waddn_double(m, False{}, Word.zero(m), Word.to_nat(m, t))) : {_ == WCon{False{}, t} : Word(1n+m)}
          %Equal.sym(Word(m), waddn(m, Word.zero(m), Word.to_nat(m, t)), t, from_to(m, t)) : {WCon{False{}, _} == WCon{False{}, t} : Word(1n+m)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(1n+m), waddn(1n+m, WCon{False{}, Word.zero(m)}, Nat.double(Word.to_nat(m, t))), WCon{False{}, waddn(m, Word.zero(m), Word.to_nat(m, t))}, waddn_double(m, False{}, Word.zero(m), Word.to_nat(m, t))) : {Word.inc(1n+m, _) == WCon{True{}, t} : Word(1n+m)}
          %Equal.sym(Word(m), waddn(m, Word.zero(m), Word.to_nat(m, t)), t, from_to(m, t)) : {Word.inc(1n+m, WCon{False{}, _}) == WCon{True{}, t} : Word(1n+m)}
          {==}

# R1: U32.to_nat(n) increments from 0 reach n
def addn_to_nat(n: U32) -> {Laws.addn(0, U32.to_nat(n)) == n : U32}:
  match n:
    case U32{+w}:
      %Equal.sym(U32, Laws.addn(U32{Word.zero(32n)}, Word.to_nat(32n, w)), U32{waddn(32n, Word.zero(32n), Word.to_nat(32n, w))}, addn_word(Word.zero(32n), Word.to_nat(32n, w))) : {_ == U32{w} : U32}
      %Equal.sym(Word(32n), waddn(32n, Word.zero(32n), Word.to_nat(32n, w)), w, from_to(32n, w)) : {U32{_} == U32{w} : U32}
      {==}

# ---- comparison through to_nat --------------------------------------------------------------------

# the value of a bit over a doubled tail (Word.to_nat's two cases)
def dbl(a: Bool, k: Nat) -> Nat:
  match a:
    case False{}:
      Nat.double(k)
    case True{}:
      1n+Nat.double(k)

def cmp_lt_small(a: Bool, b: Bool, +k: Nat) -> {Nat.cmp(dbl(a, 0n), dbl(b, 1n+k)) == LT{} : Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def cmp_gt_small(a: Bool, b: Bool, +k: Nat) -> {Nat.cmp(dbl(a, 1n+k), dbl(b, 0n)) == GT{} : Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# comparing bit-over-doubles is Word.cmp.fin of the tails' comparison
def cmp_dbl(k1: Nat, k2: Nat, +a: Bool, +b: Bool) -> {Nat.cmp(dbl(a, k1), dbl(b, k2)) == Word.cmp.fin(a, b, Nat.cmp(k1, k2)) : Cmp}:
  match k1 k2:
    case 0n 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q2:
      cmp_lt_small(a, b, q2)
    case 1n+q1 0n:
      cmp_gt_small(a, b, q1)
    case 1n++q1 1n++q2:
      match a b:
        case False{} False{}:
          cmp_dbl(q1, q2, False{}, False{})
        case False{} True{}:
          cmp_dbl(q1, q2, False{}, True{})
        case True{} False{}:
          cmp_dbl(q1, q2, True{}, False{})
        case True{} True{}:
          cmp_dbl(q1, q2, True{}, True{})

# Word.cmp is Nat.cmp of the values
def cmp_nat(+n: Nat, x: Word(n), y: Word(n)) -> {Word.cmp(n, x, y) == Nat.cmp(Word.to_nat(n, x), Word.to_nat(n, y)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match x y:
        case WCon{False{}, +t} WCon{False{}, +u}:
          %Equal.sym(Cmp, Word.cmp(p, t, u), Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u)), cmp_nat(p, t, u)) : {Word.cmp.fin(False{}, False{}, _) == Nat.cmp(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, u))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(dbl(False{}, Word.to_nat(p, t)), dbl(False{}, Word.to_nat(p, u))), Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u))), cmp_dbl(Word.to_nat(p, t), Word.to_nat(p, u), False{}, False{}))
        case WCon{False{}, +t} WCon{True{}, +u}:
          %Equal.sym(Cmp, Word.cmp(p, t, u), Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u)), cmp_nat(p, t, u)) : {Word.cmp.fin(False{}, True{}, _) == Nat.cmp(Nat.double(Word.to_nat(p, t)), 1n+Nat.double(Word.to_nat(p, u))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(dbl(False{}, Word.to_nat(p, t)), dbl(True{}, Word.to_nat(p, u))), Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u))), cmp_dbl(Word.to_nat(p, t), Word.to_nat(p, u), False{}, True{}))
        case WCon{True{}, +t} WCon{False{}, +u}:
          %Equal.sym(Cmp, Word.cmp(p, t, u), Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u)), cmp_nat(p, t, u)) : {Word.cmp.fin(True{}, False{}, _) == Nat.cmp(1n+Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, u))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(dbl(True{}, Word.to_nat(p, t)), dbl(False{}, Word.to_nat(p, u))), Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u))), cmp_dbl(Word.to_nat(p, t), Word.to_nat(p, u), True{}, False{}))
        case WCon{True{}, +t} WCon{True{}, +u}:
          %Equal.sym(Cmp, Word.cmp(p, t, u), Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u)), cmp_nat(p, t, u)) : {Word.cmp.fin(True{}, True{}, _) == Nat.cmp(1n+Nat.double(Word.to_nat(p, t)), 1n+Nat.double(Word.to_nat(p, u))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(dbl(True{}, Word.to_nat(p, t)), dbl(True{}, Word.to_nat(p, u))), Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(p, t), Word.to_nat(p, u))), cmp_dbl(Word.to_nat(p, t), Word.to_nat(p, u), True{}, True{}))

def cmp_nat_u(a: U32, b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}:
  match a b:
    case U32{x} U32{y}:
      cmp_nat(32n, x, y)

# U32.is_le gives Nat.is_le of the values
def le_nat_u(+a: U32, +b: U32, h: {U32.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}:
  %cmp_nat_u(a, b) : {Cmp.is_le(_) == True{} : Bool}
  h

# Nat.is_lt of the values gives U32.is_lt
def lt_of_nat_u(+a: U32, +b: U32, h: {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == True{} : Bool}) -> {U32.is_lt(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), cmp_nat_u(a, b)) : {Cmp.is_lt(_) == True{} : Bool}
  h

# ---- inc through to_nat: one more, unless the word is maximal (then inc wraps) -----------------------
# (an all-ones 32-bit word is never written down: its Nat value would be normalised to 2^32 - 1
# successors; "maximal" is stated as "nothing compares GT to it")

def IncSpec(b: Bool, n: Nat, +x: Word(n)) -> Type:
  match b:
    case True{}:
      {Word.to_nat(n, Word.inc(n, x)) == 1n+Word.to_nat(n, x) : Nat}
    case False{}:
      @y: Word(n) -> {Word.cmp(n, y, x) == GT{} : Cmp} -> Empty

# the refutations of == GT
def cmp_disc_gt(c: Cmp) -> Type:
  match c:
    case GT{}:
      Empty
    case o:
      Unit

def lt_gt(h: {LT{} == GT{} : Cmp}) -> Empty:
  %h : cmp_disc_gt(_)
  Unit{}

def eq_gt(h: {EQ{} == GT{} : Cmp}) -> Empty:
  %h : cmp_disc_gt(_)
  Unit{}

# WCon{T, t} is maximal when t is: the step with c = cmp(u, t)
def max_step(a: Bool, c: Cmp, -p: Nat, -t: Word(p), u: Word(p), e: {Word.cmp(p, u, t) == c : Cmp}, h: {Word.cmp.fin(a, True{}, c) == GT{} : Cmp}, s: @y: Word(p) -> {Word.cmp(p, y, t) == GT{} : Cmp} -> Empty) -> Empty:
  match a c:
    case _ GT{}:
      s(u)(e)
    case False{} EQ{}:
      lt_gt(h)
    case True{} EQ{}:
      eq_gt(h)
    case _ LT{}:
      lt_gt(h)

def max_cons(+p: Nat, +t: Word(p), s: @y: Word(p) -> {Word.cmp(p, y, t) == GT{} : Cmp} -> Empty, y: Word(1n+p), h: {Word.cmp(1n+p, y, WCon{True{}, t}) == GT{} : Cmp}) -> Empty:
  match y:
    case WCon{a, +u}:
      max_step(a, Word.cmp(p, u, t), p, t, u, {==}, h, s)

def inc_nat_k(b: Bool, +p: Nat, +t: Word(p), s: IncSpec(b, p, t)) -> &b2: Bool -> IncSpec(b2, 1n+p, WCon{True{}, t}):
  match b:
    case True{}:
      (True{}, (%Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), s) : {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}; {==}))
    case False{}:
      (False{}, y => h => max_cons(p, t, s, y, h))

def inc_nat_fin(+p: Nat, +t: Word(p), w: &b: Bool -> IncSpec(b, p, t)) -> &b2: Bool -> IncSpec(b2, 1n+p, WCon{True{}, t}):
  (+b, s) = w
  inc_nat_k(b, p, t, s)

def inc_nat(+n: Nat, x: Word(n)) -> &b: Bool -> IncSpec(b, n, x):
  match n:
    case 0n:
      match x:
        case WNil{}:
          (False{}, y => h => eq_gt(h))
    case 1n++p:
      match x:
        case WCon{False{}, t}:
          (True{}, {==})
        case WCon{True{}, +t}:
          inc_nat_fin(p, t, inc_nat(p, t))

def IncSpecU(b: Bool, +j: U32) -> Type:
  match b:
    case True{}:
      {U32.to_nat(U32.inc(j)) == 1n+U32.to_nat(j) : Nat}
    case False{}:
      @y: U32 -> {U32.cmp(y, j) == GT{} : Cmp} -> Empty

def max_u(-x: Word(32n), s: @y: Word(32n) -> {Word.cmp(32n, y, x) == GT{} : Cmp} -> Empty, y: U32, h: {U32.cmp(y, U32{x}) == GT{} : Cmp}) -> Empty:
  match y:
    case U32{w}:
      s(w)(h)

def inc_nat_u_k(b: Bool, +x: Word(32n), s: IncSpec(b, 32n, x)) -> IncSpecU(b, U32{x}):
  match b:
    case True{}:
      s
    case False{}:
      y => h => max_u(x, s, y, h)

def inc_nat_u_fin(+x: Word(32n), w: &b: Bool -> IncSpec(b, 32n, x)) -> &b2: Bool -> IncSpecU(b2, U32{x}):
  (+b, s) = w
  (b, inc_nat_u_k(b, x, s))

def inc_nat_u(j: U32) -> &b: Bool -> IncSpecU(b, j):
  match j:
    case U32{+x}:
      inc_nat_u_fin(x, inc_nat(32n, x))

# a < b gives cmp(b, a) == GT
def gt_of_lt_u(a: U32, b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> {U32.cmp(b, a) == GT{} : Cmp}:
  match a b:
    case U32{+x} U32{+y}:
      L.word_lt_gt(32n, y, x, is_lt_lt(Word.cmp(32n, x, y), h))

# ---- Nat facts ---------------------------------------------------------------------------------------

def add_succ(a: Nat, +p: Nat) -> {Nat.add(a, 1n+p) == 1n+Nat.add(a, p) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++q:
      %Equal.sym(Nat, Nat.add(q, 1n+p), 1n+Nat.add(q, p), add_succ(q, p)) : {1n+_ == 2n+Nat.add(q, p) : Nat}
      {==}

# a + (1 + p) <= b gives a < b
def lt_of_le_add(a: Nat, +p: Nat, b: Nat, h: {Nat.is_le(Nat.add(a, 1n+p), b) == True{} : Bool}) -> {Cmp.is_lt(Nat.cmp(a, b)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 0n)) == True{} : Bool}, L.false_true(h))
    case 0n 1n+bq:
      {==}
    case 1n+aq 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(1n+aq, 0n)) == True{} : Bool}, L.false_true(h))
    case 1n+aq 1n+bq:
      lt_of_le_add(aq, p, bq, h)

# ---- R2: the first to_nat(n) write indices from 0 fit below 2^d when n <= 2^d --------------------------

# the node step, by whether inc wraps
def room_step(+d: Nat, +j: U32, +p: Nat, b: Bool, s: IncSpecU(b, j), ih: @j2: U32 -> {Nat.is_le(Nat.add(U32.to_nat(j2), p), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, j2, p))
  -> {Nat.is_le(Nat.add(U32.to_nat(j), 1n+p), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, U32.inc(j), p):
  match b:
    case True{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(j), 1n+p), 1n+Nat.add(U32.to_nat(j), p), add_succ(U32.to_nat(j), p)) : {Nat.is_le(_, U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, U32.inc(j), p)
      %s : {Nat.is_le(Nat.add(_, p), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, U32.inc(j), p)
      ih(U32.inc(j))
    case False{}:
      h => Empty.absurd(Laws.Room(d, U32.inc(j), p), s(U32.shln(1, d))(gt_of_lt_u(j, U32.shln(1, d), lt_of_nat_u(j, U32.shln(1, d), lt_of_le_add(U32.to_nat(j), p, U32.to_nat(U32.shln(1, d)), h)))))

def room_step_fin(+d: Nat, +j: U32, +p: Nat, w: &b: Bool -> IncSpecU(b, j), ih: @j2: U32 -> {Nat.is_le(Nat.add(U32.to_nat(j2), p), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, j2, p))
  -> {Nat.is_le(Nat.add(U32.to_nat(j), 1n+p), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, U32.inc(j), p):
  (b, s) = w
  room_step(d, j, p, b, s, ih)

# to_nat(j) + f <= to_nat(2^d): the next f indices from j are below 2^d (the fuel first: it shrinks)
def room_of(f: Nat, +d: Nat, +j: U32) -> {Nat.is_le(Nat.add(U32.to_nat(j), f), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.Room(d, j, f):
  match f:
    case 0n:
      h => Unit{}
    case 1n++p:
      +h => (lt_of_nat_u(j, U32.shln(1, d), lt_of_le_add(U32.to_nat(j), p, U32.to_nat(U32.shln(1, d)), h)), room_step_fin(d, j, p, inc_nat_u(j), j2 => room_of(p, d, j2))(h))

# n <= 2^d: the first to_nat(n) indices from 0 are below 2^d
def room_from(+d: Nat, +n: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}) -> Laws.Room(d, 0, U32.to_nat(n)):
  room_of(U32.to_nat(n), d, 0)(le_nat_u(n, U32.shln(1, d), fits))
