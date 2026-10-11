# W2.4 joinstress: string-key joins through the packed table (H.Hc.code.pk / H.Hc.find.pk) on
# every storage pairing (Raw x Raw, Dict x Dict, Raw x Dict, Dict x Raw) and every kind (inner,
# left, semi, anti): duplicate keys on both sides, null keys (never match; "" is a key), misses,
# empty sides, all-null keys, "" keys, long shared prefixes, Unicode and NUL extensions, a self
# join, and two-key joins with the string key first and second. Each line prints the row count and
# an FNV-1a hash of DF.dump of the result (values, validity, order, names; a Dictionary column
# dumps like a Raw one, so the four pairings print the same line).
# The "collide" block runs the same joins through Join.run.h with a constant hash (every probe of
# the table collides and every match is decided by the string compare): it must print exactly the
# lines of the identity hash.
# Expected values: produced by the pre-W2.4 join (v0.1's string table, commit e7e4b17) on the same
# frames, every Join.run.h replaced by Join.run; the new code must reproduce them.
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/join.bend as J
import ./lib/w2gen.bend as G

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

# a key column: row i holds Gen.key(sh, off + i mod md), null when i mod nm = nr (nm = 0: never)
type KS is Data:
  KS{sh: G.Shape, off: U32, md: U32, nm: U32, nr: U32}

def key(+ks: KS, +i: U32) -> D.Scalar:
  match ks:
    case KS{+sh, +off, +md, +nm, +nr}:
      Bool.pick(D.Scalar, Bool.and(U32.is_ne(nm, 0), U32.is_eq(U32.mod(i, U32.max(nm, 1)), nr)), D.SNull{}, D.SStr{G.Gen.key(sh, U32.add(off, U32.mod(i, md)))})

def keys.go(+ks: KS, n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +j = U32.sub(i, 1)
      keys.go(ks, p, j, key(ks, j) <> acc)

def keys(+ks: KS, +n: U32) -> List<&2, D.Scalar>:
  keys.go(ks, U32.to_nat(n), n, Nil{})

# u32 column: a * i + b mod m
def nums.go(+a: U32, +b: U32, +m: U32, n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +j = U32.sub(i, 1)
      nums.go(a, b, m, p, j, D.SU32{U32.mod(U32.add(U32.mul(a, j), b), m)} <> acc)

def nums(+a: U32, +b: U32, +m: U32, +n: U32) -> List<&2, D.Scalar>:
  nums.go(a, b, m, U32.to_nat(n), n, Nil{})

# left: k, v (= i), j (= i mod 3); right: k, w (= 3i + 1), j (= i mod 3)
def lf(+ks: KS, +n: U32) -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", keys(ks, n), D.TStr{}), mk("v", nums(1, 0, 4294967295, n), D.TU32{}), mk("j", nums(1, 0, 3, n), D.TU32{})])

def rf(+ks: KS, +n: U32) -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", keys(ks, n), D.TStr{}), mk("w", nums(3, 1, 4294967295, n), D.TU32{}), mk("j", nums(1, 0, 3, n), D.TU32{})])

def enc(+dict: Bool, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{C.Frame.encode(f, dict)}

# the hash template of the collide block
def Mix.c(+h: U32) -> U32:
  7

# a join: c = False the identity hash (Join.run), True the constant one (Join.run.h)
def jn.c(c: Bool, +how: J.JoinHow, l: C.Frame, r: C.Frame, +lo: List<&2, String>, +ro: List<&2, String>) -> E.ResT(C.Frame):
  match c:
    case False{}:
      J.Join.run(how, l, r, lo, ro)
    case True{}:
      J.Join.run.h(~(h => Mix.c(h)), how, l, r, lo, ro)

def jn.b(+c: Bool, +how: J.JoinHow, l: C.Frame, r: E.ResT(C.Frame), +lo: List<&2, String>, +ro: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rf}:
      jn.c(c, how, l, rf, lo, ro)

def jn(+c: Bool, +how: J.JoinHow, l: E.ResT(C.Frame), r: E.ResT(C.Frame), +lo: List<&2, String>, +ro: List<&2, String>) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{lf}:
      jn.b(c, how, lf, r, lo, ro)

def sum.k(r: C.Frame & U32) -> String:
  (f, +h) = r
  "h=" ++ U32.show(h) ++ " hash=" ++ U32.show(J.Str.hash(DF.dump(Done{f}), 0))

def sum(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      sum.k(C.Frame.height(f))

def hows() -> List<&2, J.JoinHow>:
  [J.Inner{}, J.Left{}, J.Semi{}, J.Anti{}]

# the four kinds, one storage pairing (ld / rd: Dictionary-encode the left / right frame)
def kinds(+c: Bool, +ld: Bool, +rd: Bool, +lk: KS, +nl: U32, +rk: KS, +nr: U32, hs: List<&2, J.JoinHow>) -> String:
  match hs:
    case Nil{}:
      ""
    case +h <> t:
      " " ++ J.JoinHow.show(h) ++ "[" ++ sum(jn(c, h, enc(ld, lf(lk, nl)), enc(rd, rf(rk, nr)), ["k"], ["k"])) ++ "]" ++ kinds(c, ld, rd, lk, nl, rk, nr, t)

# Raw x Raw, then the three other pairings must print the same text: "same" or the difference
def cs.k(+name: String, +rr: String, +dd: String, +rd: String, +dr: String) -> String:
  name ++ ":" ++ rr ++ Bool.pick(String, Bool.and(String.eq(rr, dd), Bool.and(String.eq(rr, rd), String.eq(rr, dr))), " | dict pairings same", " | DIFFER dd=" ++ dd ++ " rd=" ++ rd ++ " dr=" ++ dr)

def cs(+c: Bool, +name: String, +lk: KS, +nl: U32, +rk: KS, +nr: U32) -> String:
  cs.k(name, kinds(c, False{}, False{}, lk, nl, rk, nr, hows()), kinds(c, True{}, True{}, lk, nl, rk, nr, hows()), kinds(c, False{}, True{}, lk, nl, rk, nr, hows()), kinds(c, True{}, False{}, lk, nl, rk, nr, hows()))

# a two-key join: (k, j) or (j, k)
def two(+c: Bool, +name: String, +lk: KS, +nl: U32, +rk: KS, +nr: U32, +lo: List<&2, String>, +ro: List<&2, String>) -> String:
  name ++ ": inner[" ++ sum(jn(c, J.Inner{}, lf(lk, nl), rf(rk, nr), lo, ro)) ++ "] left[" ++ sum(jn(c, J.Left{}, enc(True{}, lf(lk, nl)), rf(rk, nr), lo, ro)) ++ "] anti[" ++ sum(jn(c, J.Anti{}, lf(lk, nl), enc(True{}, rf(rk, nr)), lo, ro)) ++ "]"

# a self join: the same frame on both sides (a clone)
def slf.k(+c: Bool, +how: J.JoinHow, r: C.Frame & C.Frame) -> String:
  (a, b) = r
  sum(jn(c, how, Done{a}, Done{b}, ["k"], ["k"]))

def slf.b(+c: Bool, +how: J.JoinHow, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      slf.k(c, how, C.Frame.clone(f))

def slf(+c: Bool, +name: String, +ks: KS, +n: U32) -> String:
  name ++ ": inner[" ++ slf.b(c, J.Inner{}, lf(ks, n)) ++ "] left[" ++ slf.b(c, J.Left{}, enc(True{}, lf(ks, n))) ++ "]"

def block(+c: Bool) -> IO(Unit):
  do IO<Unit>:
    IO.print(cs(c, "distinct overlap", KS{G.ShD{}, 0, 100000, 0, 0}, 200, KS{G.ShD{}, 50, 100000, 0, 0}, 180))
    IO.print(cs(c, "dups both sides, nulls both", KS{G.ShD{}, 0, 13, 5, 2}, 120, KS{G.ShD{}, 6, 11, 7, 3}, 90))
    IO.print(cs(c, "equal key", KS{G.ShE{}, 0, 100000, 4, 1}, 40, KS{G.ShE{}, 0, 100000, 0, 0}, 25))
    IO.print(cs(c, "empty-string keys", KS{G.ShZ{}, 0, 100000, 4, 0}, 60, KS{G.ShZ{}, 2, 100000, 5, 4}, 50))
    IO.print(cs(c, "all-null left", KS{G.ShD{}, 0, 100000, 1, 0}, 40, KS{G.ShD{}, 0, 100000, 0, 0}, 30))
    IO.print(cs(c, "all-null right", KS{G.ShD{}, 0, 100000, 0, 0}, 40, KS{G.ShD{}, 0, 100000, 1, 0}, 30))
    IO.print(cs(c, "empty right", KS{G.ShL{}, 0, 100000, 3, 1}, 30, KS{G.ShL{}, 0, 100000, 0, 0}, 0))
    IO.print(cs(c, "empty left", KS{G.ShL{}, 0, 100000, 0, 0}, 0, KS{G.ShL{}, 0, 100000, 0, 0}, 30))
    IO.print(cs(c, "both empty", KS{G.ShL{}, 0, 100000, 0, 0}, 0, KS{G.ShL{}, 0, 100000, 0, 0}, 0))
    IO.print(cs(c, "all misses", KS{G.ShD{}, 0, 100000, 0, 0}, 50, KS{G.ShD{}, 1000, 100000, 0, 0}, 50))
    IO.print(cs(c, "long shared prefix", KS{G.ShP{}, 0, 100000, 6, 5}, 150, KS{G.ShP{}, 75, 100000, 0, 0}, 150))
    IO.print(cs(c, "longer prefix, dups", KS{G.ShQ{}, 0, 40, 0, 0}, 100, KS{G.ShQ{}, 20, 30, 9, 0}, 80))
    IO.print(cs(c, "unicode", KS{G.ShU{}, 0, 100000, 0, 0}, 300, KS{G.ShU{}, 150, 100000, 0, 0}, 300))
    IO.print(cs(c, "nul extensions", KS{G.ShN{}, 0, 100000, 0, 0}, 150, KS{G.ShN{}, 40, 100000, 0, 0}, 150))
    IO.print(cs(c, "aligned prefixes", KS{G.ShM{}, 0, 100000, 0, 0}, 120, KS{G.ShM{}, 35, 100000, 0, 0}, 120))
    IO.print(cs(c, "skew, low", KS{G.ShS{}, 0, 100000, 0, 0}, 200, KS{G.ShL{}, 0, 100000, 0, 0}, 200))
    IO.print(two(c, "two keys (k, j)", KS{G.ShD{}, 0, 9, 8, 7}, 90, KS{G.ShD{}, 3, 9, 10, 1}, 70, ["k", "j"], ["k", "j"]))
    IO.print(two(c, "two keys (j, k)", KS{G.ShD{}, 0, 9, 8, 7}, 90, KS{G.ShD{}, 3, 9, 10, 1}, 70, ["j", "k"], ["j", "k"]))
    IO.print(slf(c, "self join, dups and nulls", KS{G.ShZ{}, 0, 100000, 7, 3}, 70))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- identity hash")
    block(False{})
    IO.print("-- collide (constant hash)")
    block(True{})
#|-- identity hash
#|distinct overlap: inner[h=150 hash=928414998] left[h=200 hash=2943614880] semi[h=150 hash=1274818094] anti[h=50 hash=918987518] | dict pairings same
#|dups both sides, nulls both: inner[h=357 hash=1082525006] left[h=427 hash=23504436] semi[h=50 hash=763704077] anti[h=70 hash=2980468102] | dict pairings same
#|equal key: inner[h=750 hash=367556244] left[h=760 hash=2065051177] semi[h=30 hash=3649771149] anti[h=10 hash=467129656] | dict pairings same
#|empty-string keys: inner[h=350 hash=1095020132] left[h=365 hash=4133316103] semi[h=45 hash=1000857638] anti[h=15 hash=3462318588] | dict pairings same
#|all-null left: inner[h=0 hash=3167310641] left[h=40 hash=1938116002] semi[h=0 hash=1036881557] anti[h=40 hash=2285470938] | dict pairings same
#|all-null right: inner[h=0 hash=3167310641] left[h=40 hash=2420031705] semi[h=0 hash=1036881557] anti[h=40 hash=2857960097] | dict pairings same
#|empty right: inner[h=0 hash=3167310641] left[h=30 hash=3714685025] semi[h=0 hash=1036881557] anti[h=30 hash=3575210381] | dict pairings same
#|empty left: inner[h=0 hash=3167310641] left[h=0 hash=3167310641] semi[h=0 hash=1036881557] anti[h=0 hash=1036881557] | dict pairings same
#|both empty: inner[h=0 hash=3167310641] left[h=0 hash=3167310641] semi[h=0 hash=1036881557] anti[h=0 hash=1036881557] | dict pairings same
#|all misses: inner[h=0 hash=3167310641] left[h=50 hash=818525650] semi[h=0 hash=1036881557] anti[h=50 hash=918987518] | dict pairings same
#|long shared prefix: inner[h=62 hash=1394729208] left[h=150 hash=2343749742] semi[h=62 hash=2848676359] anti[h=88 hash=252372443] | dict pairings same
#|longer prefix, dups: inner[h=106 hash=69391993] left[h=166 hash=1063507947] semi[h=40 hash=3244208648] anti[h=60 hash=4089763549] | dict pairings same
#|unicode: inner[h=158 hash=2303421232] left[h=305 hash=2166217484] semi[h=153 hash=2631593505] anti[h=147 hash=277120381] | dict pairings same
#|nul extensions: inner[h=180 hash=1884376503] left[h=180 hash=1884376503] semi[h=150 hash=3270044004] anti[h=0 hash=1036881557] | dict pairings same
#|aligned prefixes: inner[h=135 hash=1019401798] left[h=135 hash=1019401798] semi[h=120 hash=2153550745] anti[h=0 hash=1036881557] | dict pairings same
#|skew, low: inner[h=0 hash=3167310641] left[h=200 hash=591046127] semi[h=0 hash=1036881557] anti[h=200 hash=3134644759] | dict pairings same
#|two keys (k, j): inner[h=373 hash=3826538963] left[h=411 hash=1602976003] anti[h=38 hash=1857404567]
#|two keys (j, k): inner[h=373 hash=3826538963] left[h=411 hash=1602976003] anti[h=38 hash=1857404567]
#|self join, dups and nulls: inner[h=678 hash=242573590] left[h=688 hash=38977369]
#|-- collide (constant hash)
#|distinct overlap: inner[h=150 hash=928414998] left[h=200 hash=2943614880] semi[h=150 hash=1274818094] anti[h=50 hash=918987518] | dict pairings same
#|dups both sides, nulls both: inner[h=357 hash=1082525006] left[h=427 hash=23504436] semi[h=50 hash=763704077] anti[h=70 hash=2980468102] | dict pairings same
#|equal key: inner[h=750 hash=367556244] left[h=760 hash=2065051177] semi[h=30 hash=3649771149] anti[h=10 hash=467129656] | dict pairings same
#|empty-string keys: inner[h=350 hash=1095020132] left[h=365 hash=4133316103] semi[h=45 hash=1000857638] anti[h=15 hash=3462318588] | dict pairings same
#|all-null left: inner[h=0 hash=3167310641] left[h=40 hash=1938116002] semi[h=0 hash=1036881557] anti[h=40 hash=2285470938] | dict pairings same
#|all-null right: inner[h=0 hash=3167310641] left[h=40 hash=2420031705] semi[h=0 hash=1036881557] anti[h=40 hash=2857960097] | dict pairings same
#|empty right: inner[h=0 hash=3167310641] left[h=30 hash=3714685025] semi[h=0 hash=1036881557] anti[h=30 hash=3575210381] | dict pairings same
#|empty left: inner[h=0 hash=3167310641] left[h=0 hash=3167310641] semi[h=0 hash=1036881557] anti[h=0 hash=1036881557] | dict pairings same
#|both empty: inner[h=0 hash=3167310641] left[h=0 hash=3167310641] semi[h=0 hash=1036881557] anti[h=0 hash=1036881557] | dict pairings same
#|all misses: inner[h=0 hash=3167310641] left[h=50 hash=818525650] semi[h=0 hash=1036881557] anti[h=50 hash=918987518] | dict pairings same
#|long shared prefix: inner[h=62 hash=1394729208] left[h=150 hash=2343749742] semi[h=62 hash=2848676359] anti[h=88 hash=252372443] | dict pairings same
#|longer prefix, dups: inner[h=106 hash=69391993] left[h=166 hash=1063507947] semi[h=40 hash=3244208648] anti[h=60 hash=4089763549] | dict pairings same
#|unicode: inner[h=158 hash=2303421232] left[h=305 hash=2166217484] semi[h=153 hash=2631593505] anti[h=147 hash=277120381] | dict pairings same
#|nul extensions: inner[h=180 hash=1884376503] left[h=180 hash=1884376503] semi[h=150 hash=3270044004] anti[h=0 hash=1036881557] | dict pairings same
#|aligned prefixes: inner[h=135 hash=1019401798] left[h=135 hash=1019401798] semi[h=120 hash=2153550745] anti[h=0 hash=1036881557] | dict pairings same
#|skew, low: inner[h=0 hash=3167310641] left[h=200 hash=591046127] semi[h=0 hash=1036881557] anti[h=200 hash=3134644759] | dict pairings same
#|two keys (k, j): inner[h=373 hash=3826538963] left[h=411 hash=1602976003] anti[h=38 hash=1857404567]
#|two keys (j, k): inner[h=373 hash=3826538963] left[h=411 hash=1602976003] anti[h=38 hash=1857404567]
#|self join, dups and nulls: inner[h=678 hash=242573590] left[h=688 hash=38977369]
