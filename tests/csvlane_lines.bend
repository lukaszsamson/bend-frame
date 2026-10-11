# W6.2: the `lines` array of a lane (the physical line of every kept row, DESIGN 15.6.2: "1-based
# physical line of the record's first line", every LF counting, also inside quotes and blank lines)
# against the reference parser's record lines (csvparse `CsvRec.line` of the records after the header,
# blank records dropped when the width is above 1): the same row count and the same line of every
# row, for every adversarial file of tests/csvadv read in pieces of 1, 3, 7, 64, 4096 and 1048576
# bytes. A file the reference parser rejects, with a ragged record or no data (the lane's rows are
# not meaningful there) prints `n/a`.
import Base
import ./../src/err.bend as E
import ./../bench/w6/cases.bend as CS
import ./../bench/w6/rd.bend as R

# the pieces still to run, the first difference from the answer at 1 MiB
type RP is Data:
  RP{ps: List<&2, U32>, v: String, go: Bool}

def Ln.next(+ps: List<&2, U32>, +p: U32, +base: String, +v: String) -> RP:
  Bool.pick(RP, String.eq(v, base), RP{ps, "", True{}}, RP{ps, "piece " ++ U32.show(p) ++ ": " ++ v ++ " (at 1 MiB: " ++ base ++ ")", False{}})

def Ln.loop(f: Nat, +path: String, +hdr: Bool, +sep: U32, +schema: String, +base: String, st: RP) -> IO(RP):
  match f st:
    case 0n _:
      IO.pure(RP, st)
    case _ RP{ps, v, False{}}:
      IO.pure(RP, RP{ps, v, False{}})
    case _ RP{Nil{}, v, True{}}:
      IO.pure(RP, RP{Nil{}, v, False{}})
    case 1n+p RP{+q <> t, v, True{}}:
      do IO<RP>:
        v2 : String <- R.Hr.linesig(path, hdr, sep, schema, q)
        Ln.loop(p, path, hdr, sep, schema, base, Ln.next(t, q, base, v2))

def Ln.fin(+base: String, rp: RP) -> String:
  match rp:
    case RP{ps, +v, go}:
      Bool.pick(String, String.is_empty(v), base, v)

def Case.run(+path: String, +hdr: Bool, +sep: U32, +schema: String, +base: String) -> IO(String):
  do IO<String>:
    rp : RP <- Ln.loop(10n, path, hdr, sep, schema, base, RP{[1, 3, 7, 64, 4096], "", True{}})
    return Ln.fin(base, rp)

def Case.one.k(+name: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    +path : String = "tests/csvadv/" ++ name ++ ".csv"
    +base : String <- R.Hr.linesig(path, hdr, sep, schema, 1048576)
    v : String <- Case.run(path, hdr, sep, schema, base)
    return name ++ ": " ++ v

# `only` (the first program argument, "" for every case) selects a case
def Case.one(+only: String, c: CS.Mf) -> IO(String):
  match c:
    case CS.Mf{+name, schema, +hdr, +sep}:
      Bool.pick(IO(String), Bool.or(String.is_empty(only), String.eq(only, name)), Case.one.k(name, hdr, sep, schema), IO.pure(String, ""))

def Case.print(+s: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(s), IO.pure(Unit, Unit{}), IO.print(s))

def Case.loop(+only: String, cs: List<&2, CS.Mf>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> t:
      do IO<Unit>:
        s : String <- Case.one(only, c)
        Case.print(s)
        Case.loop(only, t)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    Case.loop(Maybe.default(&2, String, List.get(&2, String, as, 1n), ""), CS.Cases.all())
#|quoted_nl: ok 120
#|quoted_nl_crlf: ok 120
#|quoted_nl_nofinal: ok 120
#|cr_soup: ok 4
#|cr_only_data: ok 1
#|crlf_plain: ok 150
#|utf8_typed: ok 120
#|utf8_bare: ok 150
#|long_records: ok 12
#|huge_record: ok 3
#|blanks_w2: ok 2
#|blanks_w1: ok 5
#|blanks_w1_str: ok 7
#|blanks_only: n/a
#|lead_blank: ok 1
#|lead_blank_nohdr: ok 2
#|empty: n/a
#|header_only: ok 0
#|header_only_nonl: ok 0
#|no_final_nl: ok 2
#|final_sep: ok 2
#|headerless: ok 3
#|bad_utf8: ok 6
#|mal_bare_quote_late: n/a
#|mal_after_close: n/a
#|mal_unclosed: n/a
#|mal_unclosed_eof_q: n/a
#|mal_cr_quote: n/a
#|mal_closing_cr_text: n/a
#|mal_and_ragged: n/a
#|mal_in_second_half: n/a
#|ragged_short: n/a
#|ragged_long_first: n/a
#|ragged_after_bad: n/a
#|ragged_w1: n/a
#|ragged_blank_ok: n/a
#|bad_cols: ok 163
#|bad_cols_later_row: ok 202
#|bad_cols_earlier_other: ok 202
#|bad_quoted_text: ok 2
#|bad_i32_text: ok 2
#|f32_edges: ok 49
#|f32_one0: ok 2
#|f32_one1: ok 2
#|f32_one2: ok 2
#|f32_one3: ok 2
#|f32_one4: ok 2
#|f32_one5: ok 2
#|f32_one6: ok 2
#|f32_one7: ok 2
#|f32_one8: ok 2
#|f32_one9: ok 2
#|f32_one10: ok 2
#|f32_one11: ok 2
#|f32_one12: ok 2
#|f32_one13: ok 2
#|f32_one14: ok 2
#|f32_one15: ok 2
#|f32_one16: ok 2
#|f32_one17: ok 2
#|f32_random_fast: ok 1500
#|u32_ok: ok 8
#|u32_bad0: ok 2
#|u32_bad1: ok 2
#|u32_bad2: ok 2
#|u32_bad3: ok 2
#|u32_bad4: ok 2
#|u32_bad5: ok 2
#|u32_bad6: ok 2
#|u32_bad7: ok 2
#|i32_ok: ok 12
#|u32_overflow: ok 2
#|u32_plus: ok 2
#|u32_sign: ok 2
#|u32_unicode_digit: ok 2
#|i32_edges: ok 14
#|i32_bad0: ok 2
#|i32_bad1: ok 2
#|i32_bad2: ok 2
#|i32_bad3: ok 2
#|i32_bad4: ok 2
#|i32_bad5: ok 2
#|i32_bad6: ok 2
#|i32_bad7: ok 2
#|i32_bad8: ok 2
#|i32_bad9: ok 2
#|bool_edges: ok 8
#|bool_bad: ok 2
#|bool_bad2: ok 2
#|bool_bad3: ok 2
#|escaped_numeric: ok 1
#|escaped_f32_bad: ok 1
#|nulls_all_types: ok 4
#|quote_edges: ok 120
#|fnv_collide: ok 160
#|fnv_collide_q: ok 120
#|wide: ok 60
#|tab_sep: ok 80
#|semicolon: ok 80
#|sep_dot: ok 60
#|sep_minus: ok 60
#|sep_pipe: ok 2
