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
# Since the v0.1 reader's removal (DESIGN.md 14 "Pre-release") the reference is the reader at 1 MiB pieces;
# `ref <hash>` pins every reference text to the one the v0.1 reader gave (the goldens were frozen from it).
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
import ./lib/v02cmp.bend as T

# the reference dump (the reader at 1 MiB pieces)
def Ref.dump(+path: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- V.Csv.read_v02_full(path, V.CsvOpts{Chr{sep}, hdr, 100}, R.Hr.dts(schema), ST.EncRaw{}, 1048576, 8388608)
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
    return Case.join(a, b, "ref " ++ U32.show(T.Sg.hash(ref, 2166136261)) ++ " | " ++ M.Cmp.outcome(ref))

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
#|quoted_nl: ref 2408788435 | frame| height 120| width 3
#|quoted_nl_crlf: ref 2408788435 | frame| height 120| width 3
#|quoted_nl_nofinal: ref 2408788435 | frame| height 120| width 3
#|cr_soup: ref 2505366303 | frame| height 4| width 2
#|cr_only_data: ref 3272500093 | frame| height 1| width 2
#|crlf_plain: ref 1574014495 | frame| height 150| width 3
#|utf8_typed: ref 2412095001 | frame| height 120| width 4
#|utf8_bare: ref 1029129410 | frame| height 150| width 2
#|long_records: ref 1155004198 | frame| height 12| width 2
#|huge_record: ref 3235146755 | frame| height 3| width 2
#|blanks_w2: ref 2389949239 | frame| height 2| width 2
#|blanks_w1: ref 497000859 | frame| height 5| width 1
#|blanks_w1_str: ref 3407496863 | frame| height 7| width 1
#|blanks_only: ref 1727989111 | error InvalidOperation: csv schema: 1 dtypes for 0 columns
#|lead_blank: ref 3536430010 | frame| height 1| width 2
#|lead_blank_nohdr: ref 1742631888 | frame| height 2| width 2
#|empty: ref 3494314430 | error InvalidOperation: csv schema: 2 dtypes for 0 columns
#|header_only: ref 3374570125 | frame| height 0| width 2
#|header_only_nonl: ref 3374570125 | frame| height 0| width 2
#|no_final_nl: ref 3083105936 | frame| height 2| width 2
#|final_sep: ref 410419651 | frame| height 2| width 2
#|headerless: ref 1632471512 | frame| height 3| width 2
#|bad_utf8: ref 1401029303 | frame| height 6| width 2
#|mal_bare_quote_late: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_after_close: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_unclosed: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_unclosed_eof_q: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_cr_quote: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_closing_cr_text: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_and_ragged: ref 4208228921 | error ParseError at line 0: malformed csv
#|mal_in_second_half: ref 4208228921 | error ParseError at line 0: malformed csv
#|ragged_short: ref 3317402217 | error ParseError at line 122: expected 3 fields, got 2
#|ragged_long_first: ref 197586712 | error ParseError at line 42: expected 3 fields, got 4
#|ragged_after_bad: ref 1090459529 | error ParseError at line 153: expected 2 fields, got 3
#|ragged_w1: ref 1580789173 | error ParseError at line 3: expected 1 fields, got 2
#|ragged_blank_ok: ref 4019227910 | error ParseError at line 4: expected 2 fields, got 1
#|bad_cols: ref 3160780378 | error ParseError at line 163: column a: cannot parse "q" as u32
#|bad_cols_later_row: ref 756334547 | error ParseError at line 202: column a: cannot parse "x" as u32
#|bad_cols_earlier_other: ref 3750714012 | error ParseError at line 203: column a: cannot parse "x" as u32
#|bad_quoted_text: ref 2110806703 | error ParseError at line 3: column a: cannot parse "1"2" as u32
#|bad_i32_text: ref 3386169695 | error ParseError at line 3: column a: cannot parse "-" as i32
#|f32_edges: ref 3654339547 | frame| height 49| width 1
#|f32_one0: ref 270317588 | error ParseError at line 3: column x: cannot parse "." as f32
#|f32_one1: ref 2650881037 | error ParseError at line 3: column x: cannot parse "+" as f32
#|f32_one2: ref 3010876187 | error ParseError at line 3: column x: cannot parse "-" as f32
#|f32_one3: ref 2794311319 | error ParseError at line 3: column x: cannot parse "1.5e" as f32
#|f32_one4: ref 120312278 | error ParseError at line 3: column x: cannot parse "e5" as f32
#|f32_one5: ref 2324172147 | error ParseError at line 3: column x: cannot parse "0x10" as f32
#|f32_one6: ref 2065739842 | error ParseError at line 3: column x: cannot parse "1_0" as f32
#|f32_one7: ref 2277219429 | error ParseError at line 3: column x: cannot parse "٣" as f32
#|f32_one8: ref 2194317173 | error ParseError at line 3: column x: cannot parse "1 2" as f32
#|f32_one9: ref 1001657466 | error ParseError at line 3: column x: cannot parse "1.2.3" as f32
#|f32_one10: ref 3284424609 | error ParseError at line 3: column x: cannot parse "--1" as f32
#|f32_one11: ref 3027361691 | error ParseError at line 3: column x: cannot parse "+-1" as f32
#|f32_one12: ref 3243516682 | error ParseError at line 3: column x: cannot parse "1e" as f32
#|f32_one13: ref 2694262315 | error ParseError at line 3: column x: cannot parse "nan(0x1)" as f32
#|f32_one14: ref 1051274375 | error ParseError at line 3: column x: cannot parse "infinity1" as f32
#|f32_one15: ref 1041713262 | error ParseError at line 3: column x: cannot parse "- 1" as f32
#|f32_one16: ref 954662096 | frame| height 2| width 1
#|f32_one17: ref 1042950428 | error ParseError at line 3: column x: cannot parse ".e3" as f32
#|f32_random_fast: ref 1499820388 | frame| height 1500| width 1
#|u32_ok: ref 1348524450 | frame| height 8| width 1
#|u32_bad0: ref 1754370713 | error ParseError at line 3: column x: cannot parse "4294967296" as u32
#|u32_bad1: ref 562958181 | error ParseError at line 3: column x: cannot parse "5-" as u32
#|u32_bad2: ref 1311578190 | error ParseError at line 3: column x: cannot parse "1 2" as u32
#|u32_bad3: ref 523879205 | error ParseError at line 3: column x: cannot parse "9999999999" as u32
#|u32_bad4: ref 275727990 | error ParseError at line 3: column x: cannot parse "1.0" as u32
#|u32_bad5: ref 835614020 | error ParseError at line 3: column x: cannot parse "0x1" as u32
#|u32_bad6: ref 3847330325 | error ParseError at line 3: column x: cannot parse "-5" as u32
#|u32_bad7: ref 2113703735 | error ParseError at line 3: column x: cannot parse "+5" as u32
#|i32_ok: ref 597960152 | frame| height 12| width 1
#|u32_overflow: ref 1754370713 | error ParseError at line 3: column x: cannot parse "4294967296" as u32
#|u32_plus: ref 2113703735 | error ParseError at line 3: column x: cannot parse "+5" as u32
#|u32_sign: ref 3847330325 | error ParseError at line 3: column x: cannot parse "-5" as u32
#|u32_unicode_digit: ref 2444505054 | error ParseError at line 3: column x: cannot parse "٣" as u32
#|i32_edges: ref 1637692299 | error ParseError at line 4: column x: cannot parse "2147483648" as i32
#|i32_bad0: ref 1264398508 | error ParseError at line 3: column x: cannot parse "-" as i32
#|i32_bad1: ref 3579729987 | error ParseError at line 3: column x: cannot parse "+5" as i32
#|i32_bad2: ref 2487050802 | error ParseError at line 3: column x: cannot parse "--5" as i32
#|i32_bad3: ref 4033468181 | error ParseError at line 3: column x: cannot parse "- 5" as i32
#|i32_bad4: ref 1657349099 | error ParseError at line 3: column x: cannot parse "-5x" as i32
#|i32_bad5: ref 1694694585 | error ParseError at line 3: column x: cannot parse "5-" as i32
#|i32_bad6: ref 1422856696 | error ParseError at line 3: column x: cannot parse "- " as i32
#|i32_bad7: ref 1106327954 | error ParseError at line 3: column x: cannot parse "1 2" as i32
#|i32_bad8: ref 458567002 | error ParseError at line 3: column x: cannot parse "-4294967296" as i32
#|i32_bad9: ref 1168441858 | error ParseError at line 3: column x: cannot parse "٣" as i32
#|bool_edges: ref 2460918928 | frame| height 8| width 1
#|bool_bad: ref 115001779 | error ParseError at line 3: column x: cannot parse "TRUE" as bool
#|bool_bad2: ref 4183685022 | error ParseError at line 3: column x: cannot parse "true1" as bool
#|bool_bad3: ref 2531266834 | error ParseError at line 3: column x: cannot parse "1" as bool
#|escaped_numeric: ref 2785480714 | frame| height 1| width 2
#|escaped_f32_bad: ref 2090369811 | error ParseError at line 2: column y: cannot parse "1"2" as f32
#|nulls_all_types: ref 2106357271 | frame| height 4| width 5
#|quote_edges: ref 2226055551 | frame| height 120| width 2
#|fnv_collide: ref 1791752462 | frame| height 160| width 2
#|fnv_collide_q: ref 2826378180 | frame| height 120| width 2
#|wide: ref 4268502874 | frame| height 60| width 12
#|tab_sep: ref 3613255923 | frame| height 80| width 3
#|semicolon: ref 318575104 | frame| height 80| width 2
#|sep_dot: ref 3804495737 | frame| height 60| width 2
#|sep_minus: ref 379324704 | frame| height 60| width 2
#|sep_pipe: ref 2774151476 | frame| height 2| width 2
#|v03_late_null: ref 1877621265 | frame| height 400| width 5
#|v03_valid_masked_valid: ref 176425353 | frame| height 300| width 2
#|v03_quoted_empty_late: ref 3350035363 | frame| height 260| width 2
#|v03_all_null_col: ref 2479663649 | frame| height 120| width 2
