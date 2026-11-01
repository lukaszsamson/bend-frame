#! native  (built with `bend -o`: the interpreter lane is 3-7x slower since Bend 2.0.37, bendlang/bend#1983)
# W6.2: the CSV lane (src/csvlane.bend) behind the producer (src/csvprod.bend), against the v0.1
# reader (Csv.read_full: csvparse + the Csv conversions), at the DF.dump level: names, dtypes,
# every value, validity, F32 bit patterns, string contents (UTF-8 decoding included), dictionary
# merge results, and the first error of the v0.1 order with its physical line and text.
#
# Every adversarial file of tests/csvadv (bench/w6/gen_adv.py) is read with an explicit schema by
# bench/w6/rd.bend (header step, Pr.regions, one Ln.lane per region, malformed / ragged / bad
# cell / concatenation / Dictionary merge) in pieces of 1, 2, 3, 4, 5, 7, 8, 13, 16, 31, 64, 97,
# 256, 4096 and 1048576 bytes (Str columns as per-region Dictionaries, TyS) and at 7 and 4096
# bytes with Str columns as raw rows (TyR). The line is `<case>: <what v0.1 answers>` when every
# run gave the same dump, else the first run that differs and its first differing line.
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/csv.bend as V
import ./../bench/w6/hx.bend as X
import ./../bench/w6/cmp.bend as M
import ./../bench/w6/cases.bend as CS
import ./../bench/w6/rd.bend as R

# the v0.1 reader's dump
def Ref.dump(+path: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- V.Csv.read_full(path, V.CsvOpts{Chr{sep}, hdr, 100}, R.Hr.dts(schema), ST.EncRaw{}, 1048576, 8388608)
    return DF.dump(r)

# one candidate run: "" when its dump equals ref
def Cand.one(+path: String, +hdr: Bool, +sep: U32, +schema: String, +piece: U32, +raw: Bool, ref: String) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- R.Hr.read(path, hdr, sep, schema, piece, raw)
    return M.Cmp.diff(ref, DF.dump(r))

# the pieces still to run, the first difference
type RP is Data:
  RP{ps: List<&2, U32>, v: String, go: Bool}

def Cand.next(+ps: List<&2, U32>, +p: U32, +raw: Bool, +v: String) -> RP:
  Bool.pick(RP, String.is_empty(v), RP{ps, v, True{}}, RP{ps, Bool.pick(String, raw, "raw rows, ", "dictionary, ") ++ "piece " ++ U32.show(p) ++ ": " ++ v, False{}})

def Cand.loop(f: Nat, +path: String, +hdr: Bool, +sep: U32, +schema: String, +raw: Bool, +ref: String, st: RP) -> IO(RP):
  match f st:
    case 0n _:
      IO.pure(RP, st)
    case _ RP{ps, v, False{}}:
      IO.pure(RP, RP{ps, v, False{}})
    case _ RP{Nil{}, v, True{}}:
      IO.pure(RP, RP{Nil{}, v, False{}})
    case 1n+p RP{+q <> t, v, True{}}:
      do IO<RP>:
        v2 : String <- Cand.one(path, hdr, sep, schema, q, raw, ref)
        Cand.loop(p, path, hdr, sep, schema, raw, ref, Cand.next(t, q, raw, v2))

def Cand.fin(rp: RP) -> String:
  match rp:
    case RP{ps, v, go}:
      v

def Cand.run(+path: String, +hdr: Bool, +sep: U32, +schema: String, +raw: Bool, +ref: String, ps: List<&2, U32>) -> IO(String):
  do IO<String>:
    rp : RP <- Cand.loop(20n, path, hdr, sep, schema, raw, ref, RP{ps, "", True{}})
    return Cand.fin(rp)

def Case.join(+a: String, +b: String, +out: String) -> String:
  Bool.pick(String, String.is_empty(a), Bool.pick(String, String.is_empty(b), out, b), a)

def Case.run(+path: String, +hdr: Bool, +sep: U32, +schema: String, +ref: String) -> IO(String):
  do IO<String>:
    +a : String <- Cand.run(path, hdr, sep, schema, False{}, ref, X.Hx.pieces())
    +b : String <- Cand.run(path, hdr, sep, schema, True{}, ref, [7, 4096])
    return Case.join(a, b, M.Cmp.outcome(ref))

def Case.one.k(+name: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    +path : String = "tests/csvadv/" ++ name ++ ".csv"
    +ref : String <- Ref.dump(path, hdr, sep, schema)
    v : String <- Case.run(path, hdr, sep, schema, ref)
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
#|quoted_nl: frame| height 120| width 3
#|quoted_nl_crlf: frame| height 120| width 3
#|quoted_nl_nofinal: frame| height 120| width 3
#|cr_soup: frame| height 4| width 2
#|cr_only_data: frame| height 1| width 2
#|crlf_plain: frame| height 150| width 3
#|utf8_typed: frame| height 120| width 4
#|utf8_bare: frame| height 150| width 2
#|long_records: frame| height 12| width 2
#|huge_record: frame| height 3| width 2
#|blanks_w2: frame| height 2| width 2
#|blanks_w1: frame| height 5| width 1
#|blanks_w1_str: frame| height 7| width 1
#|blanks_only: error InvalidOperation: csv schema: 1 dtypes for 0 columns
#|lead_blank: frame| height 1| width 2
#|lead_blank_nohdr: frame| height 2| width 2
#|empty: error InvalidOperation: csv schema: 2 dtypes for 0 columns
#|header_only: frame| height 0| width 2
#|header_only_nonl: frame| height 0| width 2
#|no_final_nl: frame| height 2| width 2
#|final_sep: frame| height 2| width 2
#|headerless: frame| height 3| width 2
#|bad_utf8: frame| height 6| width 2
#|mal_bare_quote_late: error ParseError at line 0: malformed csv
#|mal_after_close: error ParseError at line 0: malformed csv
#|mal_unclosed: error ParseError at line 0: malformed csv
#|mal_unclosed_eof_q: error ParseError at line 0: malformed csv
#|mal_cr_quote: error ParseError at line 0: malformed csv
#|mal_closing_cr_text: error ParseError at line 0: malformed csv
#|mal_and_ragged: error ParseError at line 0: malformed csv
#|mal_in_second_half: error ParseError at line 0: malformed csv
#|ragged_short: error ParseError at line 122: expected 3 fields, got 2
#|ragged_long_first: error ParseError at line 42: expected 3 fields, got 4
#|ragged_after_bad: error ParseError at line 153: expected 2 fields, got 3
#|ragged_w1: error ParseError at line 3: expected 1 fields, got 2
#|ragged_blank_ok: error ParseError at line 4: expected 2 fields, got 1
#|bad_cols: error ParseError at line 163: column a: cannot parse "q" as u32
#|bad_cols_later_row: error ParseError at line 202: column a: cannot parse "x" as u32
#|bad_cols_earlier_other: error ParseError at line 203: column a: cannot parse "x" as u32
#|bad_quoted_text: error ParseError at line 3: column a: cannot parse "1"2" as u32
#|bad_i32_text: error ParseError at line 3: column a: cannot parse "-" as i32
#|f32_edges: frame| height 49| width 1
#|f32_one0: error ParseError at line 3: column x: cannot parse "." as f32
#|f32_one1: error ParseError at line 3: column x: cannot parse "+" as f32
#|f32_one2: error ParseError at line 3: column x: cannot parse "-" as f32
#|f32_one3: error ParseError at line 3: column x: cannot parse "1.5e" as f32
#|f32_one4: error ParseError at line 3: column x: cannot parse "e5" as f32
#|f32_one5: error ParseError at line 3: column x: cannot parse "0x10" as f32
#|f32_one6: error ParseError at line 3: column x: cannot parse "1_0" as f32
#|f32_one7: error ParseError at line 3: column x: cannot parse "٣" as f32
#|f32_one8: error ParseError at line 3: column x: cannot parse "1 2" as f32
#|f32_one9: error ParseError at line 3: column x: cannot parse "1.2.3" as f32
#|f32_one10: error ParseError at line 3: column x: cannot parse "--1" as f32
#|f32_one11: error ParseError at line 3: column x: cannot parse "+-1" as f32
#|f32_one12: error ParseError at line 3: column x: cannot parse "1e" as f32
#|f32_one13: error ParseError at line 3: column x: cannot parse "nan(0x1)" as f32
#|f32_one14: error ParseError at line 3: column x: cannot parse "infinity1" as f32
#|f32_one15: error ParseError at line 3: column x: cannot parse "- 1" as f32
#|f32_one16: frame| height 2| width 1
#|f32_one17: error ParseError at line 3: column x: cannot parse ".e3" as f32
#|f32_random_fast: frame| height 1500| width 1
#|u32_ok: frame| height 8| width 1
#|u32_bad0: error ParseError at line 3: column x: cannot parse "4294967296" as u32
#|u32_bad1: error ParseError at line 3: column x: cannot parse "5-" as u32
#|u32_bad2: error ParseError at line 3: column x: cannot parse "1 2" as u32
#|u32_bad3: error ParseError at line 3: column x: cannot parse "9999999999" as u32
#|u32_bad4: error ParseError at line 3: column x: cannot parse "1.0" as u32
#|u32_bad5: error ParseError at line 3: column x: cannot parse "0x1" as u32
#|u32_bad6: error ParseError at line 3: column x: cannot parse "-5" as u32
#|u32_bad7: error ParseError at line 3: column x: cannot parse "+5" as u32
#|i32_ok: frame| height 12| width 1
#|u32_overflow: error ParseError at line 3: column x: cannot parse "4294967296" as u32
#|u32_plus: error ParseError at line 3: column x: cannot parse "+5" as u32
#|u32_sign: error ParseError at line 3: column x: cannot parse "-5" as u32
#|u32_unicode_digit: error ParseError at line 3: column x: cannot parse "٣" as u32
#|i32_edges: error ParseError at line 4: column x: cannot parse "2147483648" as i32
#|i32_bad0: error ParseError at line 3: column x: cannot parse "-" as i32
#|i32_bad1: error ParseError at line 3: column x: cannot parse "+5" as i32
#|i32_bad2: error ParseError at line 3: column x: cannot parse "--5" as i32
#|i32_bad3: error ParseError at line 3: column x: cannot parse "- 5" as i32
#|i32_bad4: error ParseError at line 3: column x: cannot parse "-5x" as i32
#|i32_bad5: error ParseError at line 3: column x: cannot parse "5-" as i32
#|i32_bad6: error ParseError at line 3: column x: cannot parse "- " as i32
#|i32_bad7: error ParseError at line 3: column x: cannot parse "1 2" as i32
#|i32_bad8: error ParseError at line 3: column x: cannot parse "-4294967296" as i32
#|i32_bad9: error ParseError at line 3: column x: cannot parse "٣" as i32
#|bool_edges: frame| height 8| width 1
#|bool_bad: error ParseError at line 3: column x: cannot parse "TRUE" as bool
#|bool_bad2: error ParseError at line 3: column x: cannot parse "true1" as bool
#|bool_bad3: error ParseError at line 3: column x: cannot parse "1" as bool
#|escaped_numeric: frame| height 1| width 2
#|escaped_f32_bad: error ParseError at line 2: column y: cannot parse "1"2" as f32
#|nulls_all_types: frame| height 4| width 5
#|quote_edges: frame| height 120| width 2
#|fnv_collide: frame| height 160| width 2
#|fnv_collide_q: frame| height 120| width 2
#|wide: frame| height 60| width 12
#|tab_sep: frame| height 80| width 3
#|semicolon: frame| height 80| width 2
#|sep_dot: frame| height 60| width 2
#|sep_minus: frame| height 60| width 2
#|sep_pipe: frame| height 2| width 2
