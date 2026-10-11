"""Generates `Tk.go2`, the tokenizer loop of src/csvlane.bend (W6.2), and splices it between the markers
`# BEGIN GENERATED Tk.go2` / `# END GENERATED Tk.go2` of that file.

    python3 bench/w6/gen_tk.py            # rewrite the section in src/csvlane.bend
    python3 bench/w6/gen_tk.py --print    # print it

Why generated: the loop must be ONE flat def (one `match` on (fuel, mode, class of the byte), every arm a
tail call), so that the Bend compiler emits one native loop (`spin_N` with WL_AGAIN) whose state lives in
registers: a def per transition rebuilt a 16-field record per byte and ran 2.5x slower (W6.2 notes in
IMPLEMENTING.md). A flat def cannot share code between arms, so the bookkeeping that ends a field (3
arms) and a record (4 arms) is repeated; this script writes it once. The modes are the reference
parser's (src/csvparse.bend `go`): MS field start, MB bare field, ME in quotes, MQ right after a quote
in a quoted field, MQC a CR after it; the class of a byte is LF / CR / separator / quote / other (KT) /
end of input (KEnd). A bare field keeps its CRs and drops the one right before the LF that ends it
(`cr` = the previous byte was a CR); a rejecting byte sets `rej` (the lane stops being meaningful: the
caller reports malformed quoting) and the loop goes on, so no early exit is needed.
"""
import os
import re
import sys

PARAMS = ("f: Nat, m: Md, nx: NX, +cr: U32, +fi: U32, +r: U32, +ln: U32, +rl: U32, +fs0: U32, +qe: U32, "
          "+esc: U32, +rag: U32, +rgn: U32, +rej: U32, +w: U32, +sep: U32, +n: U32, fs: Array<U32>, fe: Array<U32>, "
          "fq: Array<U32>, lines: Array<U32>")

NEXT = "Tk.nx(sep, n, i1, Array.get(U32, a, U32.div(i1, 4)))"
SKIPB = "Tk.skipb(U32.to_nat(U32.sub(n, i1)), sep, n, " + NEXT + ")"
SKIPQ = "Tk.skipq(U32.to_nat(U32.sub(n, i1)), sep, n, " + NEXT + ")"
QF = "U32.add(1, U32.mul(esc, 2))"


def call(mode, nx=NEXT, cr="cr", fi="fi", r="r", ln="ln", rl="rl", fs0="fs0", qe="qe", esc="esc", rag="rag", rgn="rgn",
         rej="rej", fs="fs", fe="fe", fq="fq", lines="lines"):
    return (f"Tk.go2(q, {mode}, {nx}, {cr}, {fi}, {r}, {ln}, {rl}, {fs0}, {qe}, {esc}, {rag}, {rgn}, {rej}, "
            f"w, sep, n, {fs}, {fe}, {fq}, {lines})")


def arm(mode, cls, body, lets=()):
    pat_k = f"K{cls}{{}}" if cls else "_"
    out = [f"    case 1n+q {mode}{{}} NX{{a, {pat_k}, +i}}:", "      +i1 = U32.inc(i)"]
    out += ["      " + l for l in lets]
    out.append("      " + body)
    return "\n".join(out)


def fld(e, qf):
    """the field [fs0, e) with flags qf ends at the separator at i (not the last of its record)"""
    lets = ["+slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))"]
    body = call("MS{}", cr="0", fi="U32.inc(fi)", fs0="i1", esc="0",
                fs="Array.set(U32, fs, slot, fs0)", fe=f"Array.set(U32, fe, slot, {e})", fq=f"Array.set(U32, fq, slot, {qf})")
    return lets, body


def rec(e, qf):
    """the field [fs0, e) with flags qf and its record end at the LF at i. A blank record (one empty
    unquoted field) is skipped when w > 1; a record of another width is ragged (the first one's line and
    width are kept) and dropped; a kept record counts into r (its line goes to lines[r], which a dropped
    record leaves to be overwritten)"""
    blank = f"U32.is_eq(nf, 1), U32.is_eq({e}, fs0)" if qf == "0" else f"U32.is_eq(nf, 1), Bool.and(U32.is_eq({qf}, 0), U32.is_eq({e}, fs0))"
    blank_expr = f"Bool.and({blank})"
    lets = [
        "+slot = U32.add(U32.mul(r, w), U32.min(fi, U32.sub(w, 1)))",
        "+nf = U32.inc(fi)",
        f"+blank = {blank_expr}",
        "+skip = Bool.and(blank, U32.is_gt(w, 1))",
        "+keep = Bool.and(Bool.not(skip), U32.is_eq(nf, w))",
        "+ragd = Bool.and(Bool.not(skip), U32.is_ne(nf, w))",
        "+first = Bool.and(ragd, U32.is_eq(rag, 0))",
        "+ln2 = U32.inc(ln)",
    ]
    body = call("MS{}", cr="0", fi="0", r="U32.add(r, Bool.to_u32(keep))", ln="ln2", rl="U32.inc(ln2)", fs0="i1", esc="0",
                rag="Ln.sel(first, rl, rag)", rgn="Ln.sel(first, nf, rgn)",
                fs="Array.set(U32, fs, slot, fs0)", fe=f"Array.set(U32, fe, slot, {e})", fq=f"Array.set(U32, fq, slot, {qf})",
                lines="Array.set(U32, lines, r, rl)")
    return lets, body


def generate():
    arms = []
    head = [f"def Tk.go2({PARAMS}) -> Array<U32> & TK:",
            "  match f m nx:",
            "    case 0n m0 NX{a, k, i}:",
            "      (a, TK{m0, cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})",
            "    case 1n+q m0 NX{a, KEnd{}, i}:",
            "      (a, TK{m0, cr, fi, r, ln, rl, fs0, qe, esc, rag, rgn, rej, fs, fe, fq, lines})"]
    # MS: at a field start
    l, b = rec("i", "0")
    arms.append(arm("MS", "Lf", b, l))
    arms.append(arm("MS", "Cr", call("MB{}", cr="1")))
    l, b = fld("i", "0")
    arms.append(arm("MS", "Sep", b, l))
    arms.append(arm("MS", "Q", call("ME{}", cr="0", fs0="i1", esc="0")))
    arms.append(arm("MS", "T", call("MB{}", nx=SKIPB, cr="0")))
    # MB: in a bare field
    l, b = rec("U32.sub(i, cr)", "0")
    arms.append(arm("MB", "Lf", b, l))
    arms.append(arm("MB", "Cr", call("MB{}", cr="1")))
    l, b = fld("i", "0")
    arms.append(arm("MB", "Sep", b, l))
    arms.append(arm("MB", "Q", call("MB{}", rej="1")))
    arms.append(arm("MB", "T", call("MB{}", nx=SKIPB, cr="0")))
    # ME: in quotes (only a quote or an LF matters)
    arms.append(arm("ME", "Q", call("MQ{}", cr="0", qe="i")))
    arms.append(arm("ME", "Lf", call("ME{}", cr="0", ln="U32.inc(ln)")))
    arms.append(arm("ME", None, call("ME{}", nx=SKIPQ, cr="0")))
    # MQ: right after a quote in a quoted field
    arms.append(arm("MQ", "Q", call("ME{}", cr="0", esc="1")))
    l, b = rec("qe", QF)
    arms.append(arm("MQ", "Lf", b, l))
    arms.append(arm("MQ", "Cr", call("MQC{}", cr="0")))
    l, b = fld("qe", QF)
    arms.append(arm("MQ", "Sep", b, l))
    arms.append(arm("MQ", "T", call("MQ{}", rej="1")))
    # MQC: a CR after the closing quote must be followed by an LF
    l, b = rec("qe", QF)
    arms.append(arm("MQC", "Lf", b, l))
    arms.append(arm("MQC", None, call("MQC{}", rej="1")))
    return "\n".join(head) + "\n" + "\n".join(arms) + "\n"


def main():
    text = generate()
    if "--print" in sys.argv:
        print(text)
        return
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "src", "csvlane.bend")
    s = open(path).read()
    a = s.index("# BEGIN GENERATED Tk.go2")
    b = s.index("# END GENERATED Tk.go2")
    a_end = s.index("\n", a) + 1
    s = s[:a_end] + text + s[b:]
    open(path, "w").write(s)
    print("rewrote Tk.go2 in", os.path.normpath(path))


main()
