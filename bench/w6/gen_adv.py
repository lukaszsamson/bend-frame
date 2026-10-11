"""W6.1 / W6.2 adversarial CSV fixtures: writes tests/csvadv/<case>.csv and tests/csvadv/MANIFEST.

    python3 bench/w6/gen_adv.py            # from the repository root

Every case is a CSV (bytes) plus a MANIFEST line `name schema header sep`: schema letters U u32,
I i32, F f32, B bool, S str; header 1 / 0; sep the separator's code point. tests/csvprod.bend
(region starts == the reference parser's record starts, every piece size) and tests/csvlane.bend
(typed columns, errors and lines == the v0.1 reader, every piece size) read the MANIFEST; the
expected values are NEVER stored: the reference is Csv.read_full / csvparse at test time. The
cases are the W0 spike's tools/adv.py set (T5b) plus the W6 additions (CRLF split at every
offset, multibyte UTF-8 everywhere, doubled quotes at piece edges, i32 edges, blank-line and
single-column cases, other separators, a record far longer than any piece, unterminated last
records). Generation is deterministic (seeded); the files are committed.
"""
import os
import random

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tests", "csvadv")


def rnd_str(r, n):
    alpha = "abcxyz ,\"\r\né日\U0001F600"
    return "".join(r.choice(alpha) for _ in range(n))


def q(s):
    return '"' + s.replace('"', '""') + '"'


def plain(r, n):
    # no separator, quote, CR or LF: usable bare
    alpha = "abcxyz é日\U0001F600"
    return "".join(r.choice(alpha) for _ in range(n))


def cases():
    r = random.Random(7)
    c = {}  # name -> (bytes or str, schema, header, sep)

    def add(name, data, schema, header=1, sep=44):
        c[name] = (data, schema, header, sep)

    # quoted newlines in every record, doubled quotes everywhere, CRLF inside quotes, multibyte
    rows = ["a,b,c"]
    for i in range(120):
        rows.append(",".join([q(rnd_str(r, r.randint(0, 12))), q('x""y' * (i % 3)), q(f"line{i}\nnext\r\nend")]))
    add("quoted_nl", "\n".join(rows) + "\n", "SSS")
    add("quoted_nl_crlf", "\r\n".join(rows) + "\r\n", "SSS")
    add("quoted_nl_nofinal", "\n".join(rows), "SSS")
    # bare fields with CR content, lone CR, CR before LF, final CR without LF
    add("cr_soup", "a,b\nx\r,y\n\r,z\nq\r\r,w\r\r\nlast,one\r", "SS")
    add("cr_only_data", "a,b\n1\r2,3\r", "SS")
    # CRLF everywhere: a CR | LF split at every piece offset, numeric columns
    rows = ["a,b,c"] + [f"{i},{i * 7 - 300}.5,{'true' if i % 2 else 'false'}" for i in range(150)]
    add("crlf_plain", "\r\n".join(rows) + "\r\n", "UFB")
    # UTF-8: 2/3/4-byte sequences in every field, typed columns with spaces
    rows = ["s,u,f,b"]
    for i in range(120):
        rows.append(f"{plain(r, 5)},  {i} , {i}.25 ,{' true ' if i % 2 else 'False'}")
    add("utf8_typed", "\n".join(rows) + "\n", "SUFB")
    rows = ["s,t"]
    for i in range(150):
        rows.append(f"{plain(r, r.randint(1, 9))},{plain(r, r.randint(0, 6))}")
    add("utf8_bare", "\n".join(rows) + "\n", "SS")
    # records longer than many pieces
    rows = ["k,v"]
    for i in range(12):
        rows.append(q(("long field " * 30 + "\n") * 3) + "," + str(i))
    add("long_records", "\n".join(rows), "SU")
    # one record of ~7 KB inside quotes with newlines and doubled quotes (longer than every piece
    # up to 4096), then small records. (DF.dump of a longer string overflows the stack of
    # `bend file.bend` when two dumps are live; the producer test handles 58 KB records.)
    big = "".join(("chunk\"\" %d\n" % i) for i in range(500))
    add("huge_record", "a,b\n1,x\n" + q(big) + ",y\n2,z\n", "SS", 1)
    # blank lines between records (w > 1: skipped), at the end, single-column nulls
    add("blanks_w2", "a,b\n1,x\n\n\r\n2,y\n\n", "US")
    add("blanks_w1", "a\n1\n\n2\n\r\n3\n", "U")
    add("blanks_w1_str", "a\nx\n\n\"\"\n\ny\n\n\n", "S")
    add("blanks_only", "\n\n\r\n\n", "U")
    add("lead_blank", "\n\n\r\na,b\n1,2\n", "UU")
    add("lead_blank_nohdr", "\n\n1,2\n\n3,4\n", "UU", 0)
    add("empty", "", "UU")
    add("header_only", "a,b\n", "US")
    add("header_only_nonl", "a,b", "US")
    add("no_final_nl", "a,b\n1,2\n3,4", "UU")
    add("final_sep", "a,b\n1,2\n3,", "UU")
    add("headerless", "1,2\n3,4\n5,6\n", "UU", 0)
    # invalid UTF-8 bytes: distinct byte keys decoding to the same string (U+FFFD)
    add("bad_utf8", b"s,u\n\xff,1\n\xfe,2\n\xc3,3\n\xe2\x82,4\n\xff,5\n\xef\xbf\xbd,6\n", "SU")
    # malformed quoting at various places (malformed wins over everything)
    add("mal_bare_quote_late", "a,b\n" + "1,x\n" * 100 + 'x"y,2\n' + "3,z\n" * 50, "SS")
    add("mal_after_close", "a,b\n" + "1,x\n" * 100 + '"ab"c,2\n', "SS")
    add("mal_unclosed", "a,b\n" + "1,x\n" * 100 + '"never closed,2\n3,4\n', "SS")
    add("mal_unclosed_eof_q", 'a,b\n1,x\n2,"y', "SS")
    add("mal_cr_quote", "a,b\n1,\r\"x\"\n", "SS")
    add("mal_closing_cr_text", 'a,b\n1,"x"\rz\n', "SS")
    add("mal_and_ragged", "a,b\n1\n" + "1,x\n" * 100 + 'q"q,2\n', "SS")
    add("mal_in_second_half", "a,b\n" + "1,x\n" * 300 + '2,"y"z\n' + "9,9\n" * 100, "SS")
    # ragged: the first one wins (short and long), with a bad cell earlier
    add("ragged_short", "a,b,c\n" + "1,2,3\n" * 120 + "1,2\n" + "1,2,3,4\n", "UUU")
    add("ragged_long_first", "a,b,c\n" + "1,2,3\n" * 40 + "1,2,3,4\n" + "1,2\n", "UUU")
    add("ragged_after_bad", "a,b\n" + "x,2\n" + "1,2\n" * 150 + "1,2,3\n", "UU")
    add("ragged_w1", "a\n1\n2,3\n4\n", "U")
    add("ragged_blank_ok", "a,b\n1,2\n\n3\n", "UU")
    # bad cells: the first COLUMN in column order wins, at its first row
    add("bad_cols", "a,b,c\n" + "1,2.5,true\n" * 80 + "1,zz,true\n" + "1,2.5,true\n" * 80 + "q,2.5,true\n" + "1,2.5,maybe\n", "UFB")
    add("bad_cols_later_row", "a,b\n" + "1,2\n" * 200 + "x,2\n" + "1,y\n", "UU")
    add("bad_cols_earlier_other", "a,b\n" + "1,2\n" * 200 + "1,y\n" + "x,2\n", "UU")
    add("bad_quoted_text", 'a,b\n1,2\n"1""2",3\n', "UU")
    add("bad_i32_text", 'a\n1\n-\n', "I")
    # numeric edge cases (fast path vs F32.read slow path, U32.read, I32.read)
    fl = ["1e3", ".5", "5.", "+5", "-0", "nan", "inf", "-inf", " 1.5 ", "0.1000000000001", "16777217",
          "16777216", "3.4028235e38", "1e-45", "394.47", "0.06", "-12.75", "1.0000000001", '"7.5"', '""', "  ",
          "-.5", "+.5", "0.00000000001", "1e+3", "-1E-3", "-0.0", "00.5", "123456789", "0.0000000001",
          "9999999.5", "16777215.5", "NaN", "Infinity", "-INF", "1e39", "-1e39", "1e-46", "0.1", "0.3", "2.5e-3",
          "100000000.0", "0.000000000012345", "33554433", "4.0000001", "123.456789012", "+0", "-5.", "+.5e1"]
    add("f32_edges", "x\n" + "\n".join(fl) + "\n", "F")
    # one value per file: a questionable text decides the whole read (the frame or the error)
    for k, t in enumerate([".", "+", "-", "1.5e", "e5", "0x10", "1_0", "\u0663", "1 2", "1.2.3", "--1", "+-1", "1e", "nan(0x1)", "infinity1", "- 1", "1.e3", ".e3"]):
        add("f32_one%d" % k, "x\n1\n" + t + "\n", "F")
    vals = []
    for i in range(1500):
        m = r.randint(0, 16777216 if i % 2 else 99999)
        fd = r.randint(0, 10)
        s = str(m).rjust(fd + 1, "0")
        vals.append((r.choice(["", "-", "+"]) + s[:len(s) - fd] + "." + s[len(s) - fd:]) if fd else str(m))
    add("f32_random_fast", "x\n" + "\n".join(vals) + "\n", "F")
    us = ["4294967295", "007", " 12 ", '"42"', '""', "0", "123456789", " \t 5\r"]
    add("u32_ok", "x\n" + "\n".join(us) + "\n", "U")
    for k, bad in enumerate(["4294967296", "5-", "1 2", "9999999999", "1.0", "0x1", "-5", "+5"]):
        add("u32_bad%d" % k, "x\n1\n" + bad + "\n", "U")
    add("i32_ok", "x\n" + "\n".join(["-2147483648", "2147483647", "-0", "0", " -7 ", "42", "", '""', "  ", "-1", "2147483646", "-2147483647"]) + "\n", "I")
    add("u32_overflow", "x\n1\n4294967296\n", "U")
    add("u32_plus", "x\n1\n+5\n", "U")
    add("u32_sign", "x\n1\n-5\n", "U")
    add("u32_unicode_digit", "x\n1\n٣\n", "U")
    i32s = ["-2147483648", "2147483647", "2147483648", "-2147483649", "-0", "0", " -7 ", "42", "4294967295", "-4294967295",
            "5000000000", "", '""', "  "]
    add("i32_edges", "x\n" + "\n".join(i32s) + "\n", "I")
    for k, bad in enumerate(["-", "+5", "--5", "- 5", "-5x", "5-", "- ", "1 2", "-4294967296", "٣"]):
        add("i32_bad%d" % k, "x\n1\n" + bad + "\n", "I")
    bs = ["true", "True", "false", "False", " true ", '"false"', "", "\t\r True \t"]
    add("bool_edges", "x\n" + "\n".join(bs) + "\n", "B")
    add("bool_bad", "x\ntrue\nTRUE\n", "B")
    add("bool_bad2", "x\ntrue\ntrue1\n", "B")
    add("bool_bad3", "x\ntrue\n1\n", "B")
    add("escaped_numeric", 'x,y\n"1""2",1\n', "SU")
    add("escaped_f32_bad", 'x,y\na,"1""2"\n', "SF")
    add("nulls_all_types", "u,i,f,b,s\n,,,,\n1,-1,1.5,true,x\n\"\",\"\",\"\",\"\",\"\"\n  ,  ,  ,  ,  \n", "UIFBS")
    # quote characters at every offset of a piece: "" pairs straddling piece edges
    rows = ["a,b"]
    for i in range(120):
        rows.append(q('"' * (i % 7) + "v" + '"' * (i % 5)) + "," + q('"' * (i % 3)))
    add("quote_edges", "\n".join(rows) + "\n", "SS")
    # real FNV-1a 32-bit collisions (the lane's string coder hashes content bytes with FNV-1a): pairs of
    # different short strings with the same hash must stay different entries (the coder compares the
    # bytes on a hash hit); found by a seeded birthday search
    def fnv(b):
        h = 2166136261
        for ch in b:
            h = ((h ^ ch) * 16777619) & 0xFFFFFFFF
        return h

    rs = random.Random(99)
    seen = {}
    pairs = []
    while len(pairs) < 4:
        w = "".join(rs.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(6))
        h = fnv(w.encode())
        if h in seen and seen[h] != w:
            pairs.append((seen[h], w))
        seen[h] = w
    rows = ["s,n"]
    for i in range(80):
        a, b = pairs[i % 4]
        rows.append("%s,%d" % (a if (i // 4) % 2 == 0 else b, i))
        rows.append("%s,%d" % (b if (i // 4) % 2 == 0 else a, i))
    add("fnv_collide", "\n".join(rows) + "\n", "SU")
    # the same collisions with a doubled quote inside (hash and compare read `""` as one byte)
    rows = ["s,n"]
    for i in range(40):
        a, b = pairs[i % 4]
        rows.append('"%s",%d' % (a[:3] + '""' + a[3:], i))
        rows.append('"%s",%d' % (b[:3] + '""' + b[3:], i))
        rows.append("%s,%d" % (a[:3] + '"' + a[3:] if False else a, i))
    add("fnv_collide_q", "\n".join(rows) + "\n", "SU")
    # wide records, mixed types, other separators
    rows = ["c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11"]
    for i in range(60):
        rows.append(",".join([str(i), str(-i), f"{i}.5", "true", plain(r, 3), "", q("a\nb"), "9", "-9", "0.25", "False", "z"]))
    add("wide", "\n".join(rows) + "\n", "UIFBSSSUIFBS")
    rows = ["a\tb\tc"] + [f"{i}\t{plain(r, 4)}\t{i}.5" for i in range(80)]
    add("tab_sep", "\n".join(rows) + "\n", "USF", 1, 9)
    rows = ["a;b"] + [f"{i};{q(plain(r, 3) + ';' + plain(r, 2))}" for i in range(80)]
    add("semicolon", "\n".join(rows) + "\n", "US", 1, 59)
    # separators that also occur in numbers: the cells that hold them are quoted (15.6.5 round trip)
    rows = ["a.b"] + ['"%d.5".%s' % (i, plain(r, 3)) for i in range(60)]
    add("sep_dot", "\n".join(rows) + "\n", "FS", 1, 46)
    rows = ["a-b"] + ['"-%d"-"%s"' % (i, plain(r, 3)) for i in range(60)]
    add("sep_minus", "\n".join(rows) + "\n", "IS", 1, 45)
    # a bare comma is content under another separator, a quote is not
    add("sep_pipe", "a|b\n1,5|x,y\n2|\"q|r\"\n", "SS", 1, 124)
    return c


def main():
    os.makedirs(ROOT, exist_ok=True)
    for f in os.listdir(ROOT):
        os.remove(os.path.join(ROOT, f))
    man = []
    for name, (data, schema, header, sep) in cases().items():
        raw = data if isinstance(data, bytes) else data.encode("utf-8")
        with open(os.path.join(ROOT, name + ".csv"), "wb") as f:
            f.write(raw)
        man.append(f"{name} {schema} {header} {sep}")
    with open(os.path.join(ROOT, "MANIFEST"), "w") as f:
        f.write("\n".join(man) + "\n")
    # the same list as Bend source: bench/w6/cases.bend (imported by the tests)
    items = []
    for line in man:
        name, schema, header, sep = line.split()
        items.append('Mf{"%s", "%s", %s{}, %s}' % (name, schema, "True" if header == "1" else "False", sep))
    src = ["# GENERATED by bench/w6/gen_adv.py: the adversarial cases of tests/csvadv (name, schema letters",
           "# U u32 I i32 F f32 B bool S str, header line or not, separator code point). Do not edit.",
           "import Base", "", "type Mf is Data:", "  Mf{name: String, schema: String, hdr: Bool, sep: U32}", "",
           "def Cases.all() -> List<&2, Mf>:", "  [" + ",\n   ".join(items) + "]", ""]
    with open(os.path.join(ROOT, "..", "..", "bench", "w6", "cases.bend"), "w") as f:
        f.write("\n".join(src))
    print(len(man), "cases in", ROOT)


if __name__ == "__main__":
    main()
