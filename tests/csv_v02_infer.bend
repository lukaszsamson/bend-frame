# W6.3: inference (header step + classification), header-less reads and the row cap of the v0.2 reader
# against the v0.1 reader on every adversarial file of tests/csvadv, at the DF.dump level and the
# storage of every Str column (tests/lib/v02cmp.bend). Per file, configurations x piece sizes:
#   infer_rows 100, EncAuto            pieces 1, 7, 64, 245760   (the head path: leading regions)
#   infer_rows 0 (all rows)            pieces 3, 4096            (the forked classification pass)
#   infer_rows 1                       pieces 2, 4096
#   infer_rows 3                       pieces 1, 97
#   infer_rows 2, 5, 10                pieces 7, 13 / 13, 31 / 31, 64 (a limit inside a classified region)
#   infer_rows 70000                   piece 64                  (above the head bound: forked pass)
#   infer_rows 100, EncRaw             piece 7
#   infer_rows 100, EncAutoAt{1, 8}    piece 7
#   header flipped, infer_rows 100     pieces 5, 4096
#   header flipped, the file's schema  piece 64
#   infer_rows 100, row cap 3          piece 64
# The line is `<case>: ok <runs> | <the v0.1 outcome of the first configuration>`, else the first run
# that differs.
import Base
import ./../src/strs.bend as ST
import ./../bench/w6/cases.bend as CS
import ./lib/v02cmp.bend as T

def Inf.cfgs(+schema: String, +hdr: Bool, +sep: U32) -> List<&2, T.CP>:
  [T.CP{T.Cf{"infer 100", "", hdr, sep, 100, ST.EncAuto{}, 8388608}, [1, 7, 64, 245760]},
   T.CP{T.Cf{"infer all", "", hdr, sep, 0, ST.EncAuto{}, 8388608}, [3, 4096]},
   T.CP{T.Cf{"infer 1", "", hdr, sep, 1, ST.EncAuto{}, 8388608}, [2, 4096]},
   T.CP{T.Cf{"infer 3", "", hdr, sep, 3, ST.EncAuto{}, 8388608}, [1, 97]},
   T.CP{T.Cf{"infer 2", "", hdr, sep, 2, ST.EncAuto{}, 8388608}, [7, 13]},
   T.CP{T.Cf{"infer 5", "", hdr, sep, 5, ST.EncAuto{}, 8388608}, [13, 31]},
   T.CP{T.Cf{"infer 10", "", hdr, sep, 10, ST.EncAuto{}, 8388608}, [31, 64]},
   T.CP{T.Cf{"infer 70000", "", hdr, sep, 70000, ST.EncAuto{}, 8388608}, [64]},
   T.CP{T.Cf{"infer raw", "", hdr, sep, 100, ST.EncRaw{}, 8388608}, [7]},
   T.CP{T.Cf{"infer autoat", "", hdr, sep, 100, ST.EncAutoAt{1, 8}, 8388608}, [7]},
   T.CP{T.Cf{"flipped header", "", Bool.not(hdr), sep, 100, ST.EncAuto{}, 8388608}, [5, 4096]},
   T.CP{T.Cf{"flipped header, schema", schema, Bool.not(hdr), sep, 100, ST.EncAuto{}, 8388608}, [64]},
   T.CP{T.Cf{"infer cap 3", "", hdr, sep, 100, ST.EncAuto{}, 3}, [64]}]

def Inf.one(+only: String, c: CS.Mf) -> IO(String):
  match c:
    case CS.Mf{+name, +schema, +hdr, +sep}:
      Bool.pick(IO(String), Bool.or(String.is_empty(only), String.eq(only, name)), T.Run.file(name, "tests/csvadv/" ++ name ++ ".csv", T.Cf{"infer 100", "", hdr, sep, 100, ST.EncAuto{}, 8388608}, Inf.cfgs(schema, hdr, sep)), IO.pure(String, ""))

def Inf.loop(+only: String, cs: List<&2, CS.Mf>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> t:
      do IO<Unit>:
        s : String <- Inf.one(only, c)
        T.Run.print(s)
        Inf.loop(only, t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Inf.loop(T.Run.only(args), CS.Cases.all())
#|quoted_nl: ok 23 | frame| height 120| width 3
#|quoted_nl_crlf: ok 23 | frame| height 120| width 3
#|quoted_nl_nofinal: ok 23 | frame| height 120| width 3
#|cr_soup: ok 23 | frame| height 4| width 2
#|cr_only_data: ok 23 | frame| height 1| width 2
#|crlf_plain: ok 23 | frame| height 150| width 3
#|utf8_typed: ok 23 | frame| height 120| width 4
#|utf8_bare: ok 23 | frame| height 150| width 2
#|long_records: ok 23 | frame| height 12| width 2
#|huge_record: ok 23 | frame| height 3| width 2
#|blanks_w2: ok 23 | frame| height 2| width 2
#|blanks_w1: ok 23 | frame| height 5| width 1
#|blanks_w1_str: ok 23 | frame| height 7| width 1
#|blanks_only: ok 23 | frame| height 0| width 0
#|lead_blank: ok 23 | frame| height 1| width 2
#|lead_blank_nohdr: ok 23 | frame| height 2| width 2
#|empty: ok 23 | frame| height 0| width 0
#|header_only: ok 23 | frame| height 0| width 2
#|header_only_nonl: ok 23 | frame| height 0| width 2
#|no_final_nl: ok 23 | frame| height 2| width 2
#|final_sep: ok 23 | frame| height 2| width 2
#|headerless: ok 23 | frame| height 3| width 2
#|bad_utf8: ok 23 | frame| height 6| width 2
#|mal_bare_quote_late: ok 23 | error ParseError at line 0: malformed csv
#|mal_after_close: ok 23 | error ParseError at line 0: malformed csv
#|mal_unclosed: ok 23 | error ParseError at line 0: malformed csv
#|mal_unclosed_eof_q: ok 23 | error ParseError at line 0: malformed csv
#|mal_cr_quote: ok 23 | error ParseError at line 0: malformed csv
#|mal_closing_cr_text: ok 23 | error ParseError at line 0: malformed csv
#|mal_and_ragged: ok 23 | error ParseError at line 0: malformed csv
#|mal_in_second_half: ok 23 | error ParseError at line 0: malformed csv
#|ragged_short: ok 23 | error ParseError at line 122: expected 3 fields, got 2
#|ragged_long_first: ok 23 | error ParseError at line 42: expected 3 fields, got 4
#|ragged_after_bad: ok 23 | error ParseError at line 153: expected 2 fields, got 3
#|ragged_w1: ok 23 | error ParseError at line 3: expected 1 fields, got 2
#|ragged_blank_ok: ok 23 | error ParseError at line 4: expected 2 fields, got 1
#|bad_cols: ok 23 | error ParseError at line 163: column a: cannot parse "q" as u32
#|bad_cols_later_row: ok 23 | error ParseError at line 202: column a: cannot parse "x" as u32
#|bad_cols_earlier_other: ok 23 | error ParseError at line 203: column a: cannot parse "x" as u32
#|bad_quoted_text: ok 23 | frame| height 2| width 2
#|bad_i32_text: ok 23 | frame| height 2| width 1
#|f32_edges: ok 23 | frame| height 49| width 1
#|f32_one0: ok 23 | frame| height 2| width 1
#|f32_one1: ok 23 | frame| height 2| width 1
#|f32_one2: ok 23 | frame| height 2| width 1
#|f32_one3: ok 23 | frame| height 2| width 1
#|f32_one4: ok 23 | frame| height 2| width 1
#|f32_one5: ok 23 | frame| height 2| width 1
#|f32_one6: ok 23 | frame| height 2| width 1
#|f32_one7: ok 23 | frame| height 2| width 1
#|f32_one8: ok 23 | frame| height 2| width 1
#|f32_one9: ok 23 | frame| height 2| width 1
#|f32_one10: ok 23 | frame| height 2| width 1
#|f32_one11: ok 23 | frame| height 2| width 1
#|f32_one12: ok 23 | frame| height 2| width 1
#|f32_one13: ok 23 | frame| height 2| width 1
#|f32_one14: ok 23 | frame| height 2| width 1
#|f32_one15: ok 23 | frame| height 2| width 1
#|f32_one16: ok 23 | frame| height 2| width 1
#|f32_one17: ok 23 | frame| height 2| width 1
#|f32_random_fast: ok 23 | frame| height 1500| width 1
#|u32_ok: ok 23 | frame| height 8| width 1
#|u32_bad0: ok 23 | frame| height 2| width 1
#|u32_bad1: ok 23 | frame| height 2| width 1
#|u32_bad2: ok 23 | frame| height 2| width 1
#|u32_bad3: ok 23 | frame| height 2| width 1
#|u32_bad4: ok 23 | frame| height 2| width 1
#|u32_bad5: ok 23 | frame| height 2| width 1
#|u32_bad6: ok 23 | frame| height 2| width 1
#|u32_bad7: ok 23 | frame| height 2| width 1
#|i32_ok: ok 23 | frame| height 12| width 1
#|u32_overflow: ok 23 | frame| height 2| width 1
#|u32_plus: ok 23 | frame| height 2| width 1
#|u32_sign: ok 23 | frame| height 2| width 1
#|u32_unicode_digit: ok 23 | frame| height 2| width 1
#|i32_edges: ok 23 | frame| height 14| width 1
#|i32_bad0: ok 23 | frame| height 2| width 1
#|i32_bad1: ok 23 | frame| height 2| width 1
#|i32_bad2: ok 23 | frame| height 2| width 1
#|i32_bad3: ok 23 | frame| height 2| width 1
#|i32_bad4: ok 23 | frame| height 2| width 1
#|i32_bad5: ok 23 | frame| height 2| width 1
#|i32_bad6: ok 23 | frame| height 2| width 1
#|i32_bad7: ok 23 | frame| height 2| width 1
#|i32_bad8: ok 23 | frame| height 2| width 1
#|i32_bad9: ok 23 | frame| height 2| width 1
#|bool_edges: ok 23 | frame| height 8| width 1
#|bool_bad: ok 23 | frame| height 2| width 1
#|bool_bad2: ok 23 | frame| height 2| width 1
#|bool_bad3: ok 23 | frame| height 2| width 1
#|escaped_numeric: ok 23 | frame| height 1| width 2
#|escaped_f32_bad: ok 23 | frame| height 1| width 2
#|nulls_all_types: ok 23 | frame| height 4| width 5
#|quote_edges: ok 23 | frame| height 120| width 2
#|fnv_collide: ok 23 | frame| height 160| width 2
#|fnv_collide_q: ok 23 | frame| height 120| width 2
#|wide: ok 23 | frame| height 60| width 12
#|tab_sep: ok 23 | frame| height 80| width 3
#|semicolon: ok 23 | frame| height 80| width 2
#|sep_dot: ok 23 | frame| height 60| width 2
#|sep_minus: ok 23 | frame| height 60| width 2
#|sep_pipe: ok 23 | frame| height 2| width 2
#|v03_late_null: ok 23 | frame| height 400| width 5
#|v03_valid_masked_valid: ok 23 | frame| height 300| width 2
#|v03_quoted_empty_late: ok 23 | frame| height 260| width 2
#|v03_all_null_col: ok 23 | frame| height 120| width 2
