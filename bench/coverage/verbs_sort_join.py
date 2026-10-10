"""Polars 2.0.0 twin of tests/coverage/verbs_sort_join.bend (see fx.py)."""
import polars as pl
from fx import NAN, err, frame, show


def m():
    return frame([
        ("id", "u32", [1, 2, 3, 4, 5, 6, 7]),
        ("g", "str", ["x", "y", "x", None, "y", "x", None]),
        ("v", "f32", [1.5, None, 3.0, NAN, NAN, 0.0, -0.0]),
        ("k", "bool", [True, False, None, True, None, False, True]),
    ])


def l():
    return frame([("id", "u32", [1, 2, 3, 4, 5, 6]), ("key", "str", ["a", "b", "a", None, "c", "b"]),
                  ("f", "f32", [1.5, 2.5, None, 4.5, 5.5, 6.5])])


def r():
    return frame([("key", "str", ["a", "b", "a", None, "d"]), ("g", "i32", [10, 20, 30, 40, 50]),
                  ("f", "f32", [None, 0.5, 1.5, 2.5, 3.5]), ("rid", "u32", [1, 2, 3, None, 9])])


def srt(tag, by, desc=False, nl=False, base=m):
    by = [by] if isinstance(by, str) else by
    desc = desc if isinstance(desc, list) else [desc] * len(by)
    nl = nl if isinstance(nl, list) else [nl] * len(by)
    show(tag, base().sort(by, descending=desc, nulls_last=nl, maintain_order=True))


srt("sort ascending by f32: nulls first, NaN last, -0.0 ties 0.0", "v")
srt("sort descending by f32: nulls still first", "v", True)
srt("sort ascending, nulls last", "v", False, True)
srt("sort descending, nulls last", "v", True, True)
srt("sort by str then id descending", ["g", "id"], [False, True])
srt("sort by str descending, nulls last, then bool", ["g", "k"], [True, False], [True, False])
srt("sort by bool", "k")
show("sort by no key is the identity", m())  # D: sort([]) is the identity (Polars refuses an empty `by`)
srt("sort on zero rows", ["v", "g"], [False, True], base=lambda: m().clear())
show("sort on zero columns", m().head(3).drop("id", "g", "v", "k"))
T = "TypeMismatch in "
err("invalid sort missing column", "ColumnNotFound: nope", lambda: m().sort(["v", "nope"]))
err("invalid sort first missing key wins", "ColumnNotFound: nope2", lambda: m().sort(["nope2", "nope"]))


def join(how, a, b, lk, rk):
    return a.join(b, left_on=lk, right_on=rk, how=how, maintain_order="left_right", suffix="_right")


def lo(tag, lk, rk):
    for how in ["inner", "left", "semi", "anti"]:
        show(tag + " " + how, join(how, l(), r(), lk, rk))


lo("on a str key", ["key"], ["key"])
lo("on a u32 key against another name", ["id"], ["rid"])
lo("on two keys", ["key", "id"], ["key", "rid"])
rz, lz = r().clear(), l().clear()
for how in ["inner", "left", "semi", "anti"]:
    show("%s join, zero rows on the right" % how, join(how, l(), rz, ["key"], ["key"]))
for how in ["inner", "left", "semi", "anti"]:
    show("%s join, zero rows on the left" % how, join(how, lz, r(), ["key"], ["key"]))
show("join after drop and rename keeps the keys", join("inner", l().drop("f"), r().rename({"g": "g2"}), ["key"], ["key"]))
err("invalid inner join missing left key", "ColumnNotFound: nope", lambda: join("inner", l(), r(), ["nope"], ["key"]))
err("invalid left join missing right key", "ColumnNotFound: nope", lambda: join("left", l(), r(), ["key"], ["nope"]))
err("invalid semi join key dtype mismatch", T + "join: expected str, got u32", lambda: join("semi", l(), r(), ["key"], ["rid"]))
err("invalid anti join no keys", "InvalidOperation: join: no key columns", lambda: join("anti", l(), r(), [], []))
err("invalid inner join key lists of different lengths", "InvalidOperation: join: left_on and right_on must have the same length", lambda: join("inner", l(), r(), ["key", "id"], ["key"]))
err("invalid left join f32 against u32 keys", T + "join: expected f32, got u32", lambda: join("left", l(), r(), ["f"], ["rid"]))
err("invalid inner join column collides after the suffix", "DuplicateColumn: f_right", lambda: join("inner", l(), r().rename({"g": "f_right"}), ["key"], ["key"]))
