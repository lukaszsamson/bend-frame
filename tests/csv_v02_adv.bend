# W6.3: the v0.2 reader (Csv.read_v02_full: header step, producer, one fork of lanes, combine) against
# the v0.1 reader (Csv.read_full) on every adversarial file of tests/csvadv (bench/w6/gen_adv.py), at
# the DF.dump level AND the storage of every Str column (Raw / Dictionary size / a hash of the codes).
# Per file, configurations x piece sizes:
#   explicit schema, EncAuto           pieces 1, 3, 7, 64, 4096, 245760
#   explicit schema, EncRaw            pieces 7, 4096
#   explicit schema, EncDict           piece 13
#   explicit schema, EncAutoAt{2, 4}   pieces 5, 4096 (the Raw fall back at a row of the file)
#   explicit schema, EncAutoAt{0, 1}   pieces 3, 4096 (a fall back decided at the very first rows)
#   explicit schema, EncAutoAt{3, 2}   piece 7
#   one dtype too many                 piece 64 (the count error after malformed / ragged)
#   explicit schema, row cap 3         piece 31
# The line is `<case>: ok <runs> | <the v0.1 outcome of the first configuration>` when every run gave
# v0.1's dump and storage, else the first run that differs.
import Base
import ./../src/strs.bend as ST
import ./../bench/w6/cases.bend as CS
import ./lib/v02cmp.bend as T

def Adv.cfgs(+schema: String, +hdr: Bool, +sep: U32) -> List<&2, T.CP>:
  [T.CP{T.Cf{"auto", schema, hdr, sep, 100, ST.EncAuto{}, 8388608}, [1, 3, 7, 64, 4096, 245760]},
   T.CP{T.Cf{"raw", schema, hdr, sep, 100, ST.EncRaw{}, 8388608}, [7, 4096]},
   T.CP{T.Cf{"dict", schema, hdr, sep, 100, ST.EncDict{}, 8388608}, [13]},
   T.CP{T.Cf{"autoat", schema, hdr, sep, 100, ST.EncAutoAt{2, 4}, 8388608}, [5, 4096]},
   T.CP{T.Cf{"autoat 0 1", schema, hdr, sep, 100, ST.EncAutoAt{0, 1}, 8388608}, [3, 4096]},
   T.CP{T.Cf{"autoat 3 2", schema, hdr, sep, 100, ST.EncAutoAt{3, 2}, 8388608}, [7]},
   T.CP{T.Cf{"extra dtype", schema ++ "U", hdr, sep, 100, ST.EncAuto{}, 8388608}, [64]},
   T.CP{T.Cf{"cap 3", schema, hdr, sep, 100, ST.EncAuto{}, 3}, [31]}]

def Adv.one(+only: String, c: CS.Mf) -> IO(String):
  match c:
    case CS.Mf{+name, +schema, +hdr, +sep}:
      Bool.pick(IO(String), Bool.or(String.is_empty(only), String.eq(only, name)), T.Run.file(name, "tests/csvadv/" ++ name ++ ".csv", T.Cf{"auto", schema, hdr, sep, 100, ST.EncAuto{}, 8388608}, Adv.cfgs(schema, hdr, sep)), IO.pure(String, ""))

def Adv.loop(+only: String, cs: List<&2, CS.Mf>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> t:
      do IO<Unit>:
        s : String <- Adv.one(only, c)
        T.Run.print(s)
        Adv.loop(only, t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Adv.loop(T.Run.only(args), CS.Cases.all())
#|quoted_nl: ok 16 | frame| height 120| width 3
#|quoted_nl_crlf: ok 16 | frame| height 120| width 3
#|quoted_nl_nofinal: ok 16 | frame| height 120| width 3
#|cr_soup: ok 16 | frame| height 4| width 2
#|cr_only_data: ok 16 | frame| height 1| width 2
#|crlf_plain: ok 16 | frame| height 150| width 3
#|utf8_typed: ok 16 | frame| height 120| width 4
#|utf8_bare: ok 16 | frame| height 150| width 2
#|long_records: ok 16 | frame| height 12| width 2
#|huge_record: ok 16 | frame| height 3| width 2
#|blanks_w2: ok 16 | frame| height 2| width 2
#|blanks_w1: ok 16 | frame| height 5| width 1
#|blanks_w1_str: ok 16 | frame| height 7| width 1
#|blanks_only: ok 16 | error InvalidOperation: csv schema: 1 dtypes for 0 columns
#|lead_blank: ok 16 | frame| height 1| width 2
#|lead_blank_nohdr: ok 16 | frame| height 2| width 2
#|empty: ok 16 | error InvalidOperation: csv schema: 2 dtypes for 0 columns
#|header_only: ok 16 | frame| height 0| width 2
#|header_only_nonl: ok 16 | frame| height 0| width 2
#|no_final_nl: ok 16 | frame| height 2| width 2
#|final_sep: ok 16 | frame| height 2| width 2
#|headerless: ok 16 | frame| height 3| width 2
#|bad_utf8: ok 16 | frame| height 6| width 2
#|mal_bare_quote_late: ok 16 | error ParseError at line 0: malformed csv
#|mal_after_close: ok 16 | error ParseError at line 0: malformed csv
#|mal_unclosed: ok 16 | error ParseError at line 0: malformed csv
#|mal_unclosed_eof_q: ok 16 | error ParseError at line 0: malformed csv
#|mal_cr_quote: ok 16 | error ParseError at line 0: malformed csv
#|mal_closing_cr_text: ok 16 | error ParseError at line 0: malformed csv
#|mal_and_ragged: ok 16 | error ParseError at line 0: malformed csv
#|mal_in_second_half: ok 16 | error ParseError at line 0: malformed csv
#|ragged_short: ok 16 | error ParseError at line 122: expected 3 fields, got 2
#|ragged_long_first: ok 16 | error ParseError at line 42: expected 3 fields, got 4
#|ragged_after_bad: ok 16 | error ParseError at line 153: expected 2 fields, got 3
#|ragged_w1: ok 16 | error ParseError at line 3: expected 1 fields, got 2
#|ragged_blank_ok: ok 16 | error ParseError at line 4: expected 2 fields, got 1
#|bad_cols: ok 16 | error ParseError at line 163: column a: cannot parse "q" as u32
#|bad_cols_later_row: ok 16 | error ParseError at line 202: column a: cannot parse "x" as u32
#|bad_cols_earlier_other: ok 16 | error ParseError at line 203: column a: cannot parse "x" as u32
#|bad_quoted_text: ok 16 | error ParseError at line 3: column a: cannot parse "1"2" as u32
#|bad_i32_text: ok 16 | error ParseError at line 3: column a: cannot parse "-" as i32
#|f32_edges: ok 16 | frame| height 49| width 1
#|f32_one0: ok 16 | error ParseError at line 3: column x: cannot parse "." as f32
#|f32_one1: ok 16 | error ParseError at line 3: column x: cannot parse "+" as f32
#|f32_one2: ok 16 | error ParseError at line 3: column x: cannot parse "-" as f32
#|f32_one3: ok 16 | error ParseError at line 3: column x: cannot parse "1.5e" as f32
#|f32_one4: ok 16 | error ParseError at line 3: column x: cannot parse "e5" as f32
#|f32_one5: ok 16 | error ParseError at line 3: column x: cannot parse "0x10" as f32
#|f32_one6: ok 16 | error ParseError at line 3: column x: cannot parse "1_0" as f32
#|f32_one7: ok 16 | error ParseError at line 3: column x: cannot parse "٣" as f32
#|f32_one8: ok 16 | error ParseError at line 3: column x: cannot parse "1 2" as f32
#|f32_one9: ok 16 | error ParseError at line 3: column x: cannot parse "1.2.3" as f32
#|f32_one10: ok 16 | error ParseError at line 3: column x: cannot parse "--1" as f32
#|f32_one11: ok 16 | error ParseError at line 3: column x: cannot parse "+-1" as f32
#|f32_one12: ok 16 | error ParseError at line 3: column x: cannot parse "1e" as f32
#|f32_one13: ok 16 | error ParseError at line 3: column x: cannot parse "nan(0x1)" as f32
#|f32_one14: ok 16 | error ParseError at line 3: column x: cannot parse "infinity1" as f32
#|f32_one15: ok 16 | error ParseError at line 3: column x: cannot parse "- 1" as f32
#|f32_one16: ok 16 | frame| height 2| width 1
#|f32_one17: ok 16 | error ParseError at line 3: column x: cannot parse ".e3" as f32
#|f32_random_fast: ok 16 | frame| height 1500| width 1
#|u32_ok: ok 16 | frame| height 8| width 1
#|u32_bad0: ok 16 | error ParseError at line 3: column x: cannot parse "4294967296" as u32
#|u32_bad1: ok 16 | error ParseError at line 3: column x: cannot parse "5-" as u32
#|u32_bad2: ok 16 | error ParseError at line 3: column x: cannot parse "1 2" as u32
#|u32_bad3: ok 16 | error ParseError at line 3: column x: cannot parse "9999999999" as u32
#|u32_bad4: ok 16 | error ParseError at line 3: column x: cannot parse "1.0" as u32
#|u32_bad5: ok 16 | error ParseError at line 3: column x: cannot parse "0x1" as u32
#|u32_bad6: ok 16 | error ParseError at line 3: column x: cannot parse "-5" as u32
#|u32_bad7: ok 16 | error ParseError at line 3: column x: cannot parse "+5" as u32
#|i32_ok: ok 16 | frame| height 12| width 1
#|u32_overflow: ok 16 | error ParseError at line 3: column x: cannot parse "4294967296" as u32
#|u32_plus: ok 16 | error ParseError at line 3: column x: cannot parse "+5" as u32
#|u32_sign: ok 16 | error ParseError at line 3: column x: cannot parse "-5" as u32
#|u32_unicode_digit: ok 16 | error ParseError at line 3: column x: cannot parse "٣" as u32
#|i32_edges: ok 16 | error ParseError at line 4: column x: cannot parse "2147483648" as i32
#|i32_bad0: ok 16 | error ParseError at line 3: column x: cannot parse "-" as i32
#|i32_bad1: ok 16 | error ParseError at line 3: column x: cannot parse "+5" as i32
#|i32_bad2: ok 16 | error ParseError at line 3: column x: cannot parse "--5" as i32
#|i32_bad3: ok 16 | error ParseError at line 3: column x: cannot parse "- 5" as i32
#|i32_bad4: ok 16 | error ParseError at line 3: column x: cannot parse "-5x" as i32
#|i32_bad5: ok 16 | error ParseError at line 3: column x: cannot parse "5-" as i32
#|i32_bad6: ok 16 | error ParseError at line 3: column x: cannot parse "- " as i32
#|i32_bad7: ok 16 | error ParseError at line 3: column x: cannot parse "1 2" as i32
#|i32_bad8: ok 16 | error ParseError at line 3: column x: cannot parse "-4294967296" as i32
#|i32_bad9: ok 16 | error ParseError at line 3: column x: cannot parse "٣" as i32
#|bool_edges: ok 16 | frame| height 8| width 1
#|bool_bad: ok 16 | error ParseError at line 3: column x: cannot parse "TRUE" as bool
#|bool_bad2: ok 16 | error ParseError at line 3: column x: cannot parse "true1" as bool
#|bool_bad3: ok 16 | error ParseError at line 3: column x: cannot parse "1" as bool
#|escaped_numeric: ok 16 | frame| height 1| width 2
#|escaped_f32_bad: ok 16 | error ParseError at line 2: column y: cannot parse "1"2" as f32
#|nulls_all_types: ok 16 | frame| height 4| width 5
#|quote_edges: ok 16 | frame| height 120| width 2
#|fnv_collide: ok 16 | frame| height 160| width 2
#|fnv_collide_q: ok 16 | frame| height 120| width 2
#|wide: ok 16 | frame| height 60| width 12
#|tab_sep: ok 16 | frame| height 80| width 3
#|semicolon: ok 16 | frame| height 80| width 2
#|sep_dot: ok 16 | frame| height 60| width 2
#|sep_minus: ok 16 | frame| height 60| width 2
#|sep_pipe: ok 16 | frame| height 2| width 2
#|v03_late_null: ok 16 | frame| height 400| width 5
#|v03_valid_masked_valid: ok 16 | frame| height 300| width 2
#|v03_quoted_empty_late: ok 16 | frame| height 260| width 2
#|v03_all_null_col: ok 16 | frame| height 120| width 2
