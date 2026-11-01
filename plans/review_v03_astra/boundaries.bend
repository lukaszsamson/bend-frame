import Base

import ./../../frame.bend as DF

import ./../../src/dtype.bend as D

import ./../../tests/regress/lib/rx.bend as R

def l0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0)], D.TU32{}), R.mk("q", [R.u(2)], D.TU32{}), R.mk("li", [R.u(0)], D.TU32{})])

def r0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0), R.null(), R.u(0), R.u(0), R.u(0), R.u(1), R.u(2)], D.TU32{}), R.mk("q", [R.u(1), R.u(1), R.null(), R.null(), R.u(0), R.u(1), R.u(0)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def l1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(2), R.u(0), R.null(), R.null(), R.u(0), R.null(), R.u(0)], D.TU32{}), R.mk("q", [R.u(0), R.u(2), R.u(1), R.u(1), R.u(2), R.u(2), R.u(0)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def r1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(1)], D.TU32{}), R.mk("q", [R.u(1)], D.TU32{}), R.mk("ri", [R.u(0)], D.TU32{})])

def l2() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("li", [], D.TU32{})])

def r2() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(1), R.null(), R.u(2), R.u(2)], D.TU32{}), R.mk("q", [R.u(1), R.null(), R.null(), R.u(0)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def l3() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0), R.null(), R.null(), R.u(1)], D.TU32{}), R.mk("q", [R.u(2), R.null(), R.u(1), R.null()], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def r3() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("ri", [], D.TU32{})])

def l4() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.null(), R.u(0), R.null(), R.u(1), R.null()], D.TU32{}), R.mk("q", [R.u(1), R.u(1), R.u(0), R.u(1), R.u(2)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4)], D.TU32{})])

def r4() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.null(), R.u(0), R.u(0), R.u(1), R.u(1), R.null(), R.u(1), R.null(), R.null()], D.TU32{}), R.mk("q", [R.null(), R.null(), R.u(2), R.u(0), R.u(0), R.u(1), R.u(2), R.u(2), R.u(2)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8)], D.TU32{})])

def l5() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0)], D.TU32{}), R.mk("q", [R.null()], D.TU32{}), R.mk("li", [R.u(0)], D.TU32{})])

def r5() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(2), R.u(2), R.u(2), R.null(), R.null(), R.u(1), R.u(0)], D.TU32{}), R.mk("q", [R.u(2), R.u(1), R.null(), R.u(1), R.null(), R.u(0), R.u(0)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def l6() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(1), R.u(0), R.null(), R.u(1), R.u(0), R.u(2), R.u(2)], D.TU32{}), R.mk("q", [R.u(0), R.null(), R.u(1), R.u(1), R.u(0), R.null(), R.u(2)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def r6() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(2)], D.TU32{}), R.mk("q", [R.u(1)], D.TU32{}), R.mk("ri", [R.u(0)], D.TU32{})])

def l7() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("li", [], D.TU32{})])

def r7() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0), R.null(), R.null(), R.u(2)], D.TU32{}), R.mk("q", [R.null(), R.null(), R.null(), R.null()], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def l8() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(1), R.u(1), R.u(0), R.u(0)], D.TU32{}), R.mk("q", [R.u(0), R.null(), R.u(1), R.u(0)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def r8() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("ri", [], D.TU32{})])

def l9() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.null(), R.u(0), R.u(0), R.null(), R.u(0)], D.TU32{}), R.mk("q", [R.u(1), R.u(2), R.null(), R.u(0), R.u(1)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4)], D.TU32{})])

def r9() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(1), R.null(), R.u(2), R.u(2), R.u(0), R.u(0), R.null(), R.u(1), R.u(0)], D.TU32{}), R.mk("q", [R.u(1), R.u(0), R.u(1), R.u(0), R.null(), R.null(), R.u(2), R.u(1), R.u(0)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8)], D.TU32{})])

def l10() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(4294967295)], D.TU32{}), R.mk("q", [R.null()], D.TU32{}), R.mk("li", [R.u(0)], D.TU32{})])

def r10() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65536), R.u(4294967295), R.u(4294967295), R.u(0), R.u(65536), R.null(), R.u(0)], D.TU32{}), R.mk("q", [R.u(65536), R.u(65536), R.u(0), R.u(65535), R.u(65535), R.u(65536), R.null()], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def l11() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.null(), R.null(), R.null(), R.u(0), R.u(4294967295), R.u(4294967295), R.null()], D.TU32{}), R.mk("q", [R.null(), R.u(0), R.u(65535), R.null(), R.u(0), R.u(65536), R.u(65535)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def r11() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0)], D.TU32{}), R.mk("q", [R.u(4294967295)], D.TU32{}), R.mk("ri", [R.u(0)], D.TU32{})])

def l12() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("li", [], D.TU32{})])

def r12() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(4294967295), R.u(4294967295), R.u(4294967295), R.null()], D.TU32{}), R.mk("q", [R.u(65536), R.null(), R.u(65536), R.null()], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def l13() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(4294967295), R.u(4294967295), R.u(4294967295), R.u(4294967295)], D.TU32{}), R.mk("q", [R.null(), R.u(4294967295), R.u(65535), R.u(0)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def r13() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("ri", [], D.TU32{})])

def l14() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65535), R.u(65536), R.u(65536), R.u(4294967295), R.u(4294967295)], D.TU32{}), R.mk("q", [R.u(65536), R.u(65535), R.u(0), R.u(4294967295), R.u(65536)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4)], D.TU32{})])

def r14() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65536), R.u(65536), R.u(0), R.u(65535), R.u(0), R.null(), R.null(), R.u(0), R.u(65535)], D.TU32{}), R.mk("q", [R.null(), R.u(65536), R.u(65536), R.u(65536), R.u(0), R.null(), R.u(65536), R.u(0), R.u(65535)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8)], D.TU32{})])

def l15() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65535)], D.TU32{}), R.mk("q", [R.u(65536)], D.TU32{}), R.mk("li", [R.u(0)], D.TU32{})])

def r15() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.null(), R.null(), R.u(65536), R.u(65535), R.u(0), R.null(), R.null()], D.TU32{}), R.mk("q", [R.u(65535), R.u(65536), R.u(4294967295), R.u(65536), R.u(4294967295), R.u(4294967295), R.null()], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def l16() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(0), R.u(65536), R.u(4294967295), R.u(0), R.u(65535), R.u(4294967295), R.u(65535)], D.TU32{}), R.mk("q", [R.u(65536), R.u(4294967295), R.u(65535), R.null(), R.u(4294967295), R.u(65535), R.null()], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def r16() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65536)], D.TU32{}), R.mk("q", [R.u(0)], D.TU32{}), R.mk("ri", [R.u(0)], D.TU32{})])

def l17() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("li", [], D.TU32{})])

def r17() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(4294967295), R.u(65536), R.u(65536), R.u(65535)], D.TU32{}), R.mk("q", [R.u(0), R.u(65535), R.u(0), R.u(65535)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def l18() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65536), R.null(), R.null(), R.u(65536)], D.TU32{}), R.mk("q", [R.u(0), R.u(65536), R.u(4294967295), R.u(4294967295)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3)], D.TU32{})])

def r18() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [], D.TU32{}), R.mk("q", [], D.TU32{}), R.mk("ri", [], D.TU32{})])

def l19() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65535), R.u(65536), R.null(), R.u(0), R.null()], D.TU32{}), R.mk("q", [R.u(65536), R.u(0), R.u(65535), R.u(65536), R.u(0)], D.TU32{}), R.mk("li", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4)], D.TU32{})])

def r19() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("k", [R.u(65536), R.null(), R.u(4294967295), R.null(), R.u(65535), R.null(), R.u(4294967295), R.u(0), R.u(4294967295)], D.TU32{}), R.mk("q", [R.null(), R.u(65536), R.u(4294967295), R.u(65535), R.u(0), R.u(0), R.u(65536), R.u(0), R.u(65536)], D.TU32{}), R.mk("ri", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8)], D.TU32{})])

def f0_0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [], D.TU32{}), R.mk("v", [], D.TU32{})])

def f1_0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0)], D.TU32{}), R.mk("v", [R.null()], D.TU32{})])

def f1_1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0)], D.TU32{}), R.mk("v", [R.null()], D.TU32{})])

def f8_0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7)], D.TU32{})])

def f8_1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7)], D.TU32{})])

def f8_2() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7)], D.TU32{})])

def f8_8() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7)], D.TU32{})])

def f16_0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null()], D.TU32{})])

def f16_1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null()], D.TU32{})])

def f16_2() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null()], D.TU32{})])

def f16_3() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null()], D.TU32{})])

def f16_16() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null()], D.TU32{})])

def f32_0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31)], D.TU32{})])

def f32_1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31)], D.TU32{})])

def f32_4() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31)], D.TU32{})])

def f32_5() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31)], D.TU32{})])

def f32_32() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31)], D.TU32{})])

def f64_0() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31), R.u(32), R.u(33), R.u(34), R.u(35), R.u(36), R.u(37), R.u(38), R.u(39), R.u(40), R.u(41), R.u(42), R.u(43), R.u(44), R.u(45), R.u(46), R.u(47), R.u(48), R.u(49), R.u(50), R.u(51), R.u(52), R.u(53), R.u(54), R.u(55), R.u(56), R.u(57), R.u(58), R.u(59), R.u(60), R.u(61), R.u(62), R.u(63)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31), R.u(32), R.null(), R.u(34), R.u(35), R.null(), R.u(37), R.u(38), R.null(), R.u(40), R.u(41), R.null(), R.u(43), R.u(44), R.null(), R.u(46), R.u(47), R.null(), R.u(49), R.u(50), R.null(), R.u(52), R.u(53), R.null(), R.u(55), R.u(56), R.null(), R.u(58), R.u(59), R.null(), R.u(61), R.u(62), R.null()], D.TU32{})])

def f64_1() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31), R.u(32), R.u(33), R.u(34), R.u(35), R.u(36), R.u(37), R.u(38), R.u(39), R.u(40), R.u(41), R.u(42), R.u(43), R.u(44), R.u(45), R.u(46), R.u(47), R.u(48), R.u(49), R.u(50), R.u(51), R.u(52), R.u(53), R.u(54), R.u(55), R.u(56), R.u(57), R.u(58), R.u(59), R.u(60), R.u(61), R.u(62), R.u(63)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31), R.u(32), R.null(), R.u(34), R.u(35), R.null(), R.u(37), R.u(38), R.null(), R.u(40), R.u(41), R.null(), R.u(43), R.u(44), R.null(), R.u(46), R.u(47), R.null(), R.u(49), R.u(50), R.null(), R.u(52), R.u(53), R.null(), R.u(55), R.u(56), R.null(), R.u(58), R.u(59), R.null(), R.u(61), R.u(62), R.null()], D.TU32{})])

def f64_8() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31), R.u(32), R.u(33), R.u(34), R.u(35), R.u(36), R.u(37), R.u(38), R.u(39), R.u(40), R.u(41), R.u(42), R.u(43), R.u(44), R.u(45), R.u(46), R.u(47), R.u(48), R.u(49), R.u(50), R.u(51), R.u(52), R.u(53), R.u(54), R.u(55), R.u(56), R.u(57), R.u(58), R.u(59), R.u(60), R.u(61), R.u(62), R.u(63)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31), R.u(32), R.null(), R.u(34), R.u(35), R.null(), R.u(37), R.u(38), R.null(), R.u(40), R.u(41), R.null(), R.u(43), R.u(44), R.null(), R.u(46), R.u(47), R.null(), R.u(49), R.u(50), R.null(), R.u(52), R.u(53), R.null(), R.u(55), R.u(56), R.null(), R.u(58), R.u(59), R.null(), R.u(61), R.u(62), R.null()], D.TU32{})])

def f64_9() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31), R.u(32), R.u(33), R.u(34), R.u(35), R.u(36), R.u(37), R.u(38), R.u(39), R.u(40), R.u(41), R.u(42), R.u(43), R.u(44), R.u(45), R.u(46), R.u(47), R.u(48), R.u(49), R.u(50), R.u(51), R.u(52), R.u(53), R.u(54), R.u(55), R.u(56), R.u(57), R.u(58), R.u(59), R.u(60), R.u(61), R.u(62), R.u(63)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31), R.u(32), R.null(), R.u(34), R.u(35), R.null(), R.u(37), R.u(38), R.null(), R.u(40), R.u(41), R.null(), R.u(43), R.u(44), R.null(), R.u(46), R.u(47), R.null(), R.u(49), R.u(50), R.null(), R.u(52), R.u(53), R.null(), R.u(55), R.u(56), R.null(), R.u(58), R.u(59), R.null(), R.u(61), R.u(62), R.null()], D.TU32{})])

def f64_64() -> DF.ResT(DF.Frame()):
  R.frame([R.mk("id", [R.u(0), R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7), R.u(8), R.u(9), R.u(10), R.u(11), R.u(12), R.u(13), R.u(14), R.u(15), R.u(16), R.u(17), R.u(18), R.u(19), R.u(20), R.u(21), R.u(22), R.u(23), R.u(24), R.u(25), R.u(26), R.u(27), R.u(28), R.u(29), R.u(30), R.u(31), R.u(32), R.u(33), R.u(34), R.u(35), R.u(36), R.u(37), R.u(38), R.u(39), R.u(40), R.u(41), R.u(42), R.u(43), R.u(44), R.u(45), R.u(46), R.u(47), R.u(48), R.u(49), R.u(50), R.u(51), R.u(52), R.u(53), R.u(54), R.u(55), R.u(56), R.u(57), R.u(58), R.u(59), R.u(60), R.u(61), R.u(62), R.u(63)], D.TU32{}), R.mk("v", [R.null(), R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.null(), R.u(7), R.u(8), R.null(), R.u(10), R.u(11), R.null(), R.u(13), R.u(14), R.null(), R.u(16), R.u(17), R.null(), R.u(19), R.u(20), R.null(), R.u(22), R.u(23), R.null(), R.u(25), R.u(26), R.null(), R.u(28), R.u(29), R.null(), R.u(31), R.u(32), R.null(), R.u(34), R.u(35), R.null(), R.u(37), R.u(38), R.null(), R.u(40), R.u(41), R.null(), R.u(43), R.u(44), R.null(), R.u(46), R.u(47), R.null(), R.u(49), R.u(50), R.null(), R.u(52), R.u(53), R.null(), R.u(55), R.u(56), R.null(), R.u(58), R.u(59), R.null(), R.u(61), R.u(62), R.null()], D.TU32{})])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("CASE j0_inner\n" ++ DF.dump(DF.then(DF.then(l0(), l => DF.then(r0(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j0_left\n" ++ DF.dump(DF.then(DF.then(l0(), l => DF.then(r0(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j0_semi\n" ++ DF.dump(DF.then(DF.then(l0(), l => DF.then(r0(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j0_anti\n" ++ DF.dump(DF.then(DF.then(l0(), l => DF.then(r0(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j1_inner\n" ++ DF.dump(DF.then(DF.then(l1(), l => DF.then(r1(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j1_left\n" ++ DF.dump(DF.then(DF.then(l1(), l => DF.then(r1(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j1_semi\n" ++ DF.dump(DF.then(DF.then(l1(), l => DF.then(r1(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j1_anti\n" ++ DF.dump(DF.then(DF.then(l1(), l => DF.then(r1(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j2_inner\n" ++ DF.dump(DF.then(DF.then(l2(), l => DF.then(r2(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j2_left\n" ++ DF.dump(DF.then(DF.then(l2(), l => DF.then(r2(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j2_semi\n" ++ DF.dump(DF.then(DF.then(l2(), l => DF.then(r2(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j2_anti\n" ++ DF.dump(DF.then(DF.then(l2(), l => DF.then(r2(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j3_inner\n" ++ DF.dump(DF.then(DF.then(l3(), l => DF.then(r3(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j3_left\n" ++ DF.dump(DF.then(DF.then(l3(), l => DF.then(r3(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j3_semi\n" ++ DF.dump(DF.then(DF.then(l3(), l => DF.then(r3(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j3_anti\n" ++ DF.dump(DF.then(DF.then(l3(), l => DF.then(r3(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j4_inner\n" ++ DF.dump(DF.then(DF.then(l4(), l => DF.then(r4(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j4_left\n" ++ DF.dump(DF.then(DF.then(l4(), l => DF.then(r4(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j4_semi\n" ++ DF.dump(DF.then(DF.then(l4(), l => DF.then(r4(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j4_anti\n" ++ DF.dump(DF.then(DF.then(l4(), l => DF.then(r4(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j5_inner\n" ++ DF.dump(DF.then(DF.then(l5(), l => DF.then(r5(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j5_left\n" ++ DF.dump(DF.then(DF.then(l5(), l => DF.then(r5(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j5_semi\n" ++ DF.dump(DF.then(DF.then(l5(), l => DF.then(r5(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j5_anti\n" ++ DF.dump(DF.then(DF.then(l5(), l => DF.then(r5(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j6_inner\n" ++ DF.dump(DF.then(DF.then(l6(), l => DF.then(r6(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j6_left\n" ++ DF.dump(DF.then(DF.then(l6(), l => DF.then(r6(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j6_semi\n" ++ DF.dump(DF.then(DF.then(l6(), l => DF.then(r6(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j6_anti\n" ++ DF.dump(DF.then(DF.then(l6(), l => DF.then(r6(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j7_inner\n" ++ DF.dump(DF.then(DF.then(l7(), l => DF.then(r7(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j7_left\n" ++ DF.dump(DF.then(DF.then(l7(), l => DF.then(r7(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j7_semi\n" ++ DF.dump(DF.then(DF.then(l7(), l => DF.then(r7(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j7_anti\n" ++ DF.dump(DF.then(DF.then(l7(), l => DF.then(r7(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j8_inner\n" ++ DF.dump(DF.then(DF.then(l8(), l => DF.then(r8(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j8_left\n" ++ DF.dump(DF.then(DF.then(l8(), l => DF.then(r8(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j8_semi\n" ++ DF.dump(DF.then(DF.then(l8(), l => DF.then(r8(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j8_anti\n" ++ DF.dump(DF.then(DF.then(l8(), l => DF.then(r8(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j9_inner\n" ++ DF.dump(DF.then(DF.then(l9(), l => DF.then(r9(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j9_left\n" ++ DF.dump(DF.then(DF.then(l9(), l => DF.then(r9(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j9_semi\n" ++ DF.dump(DF.then(DF.then(l9(), l => DF.then(r9(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j9_anti\n" ++ DF.dump(DF.then(DF.then(l9(), l => DF.then(r9(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j10_inner\n" ++ DF.dump(DF.then(DF.then(l10(), l => DF.then(r10(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j10_left\n" ++ DF.dump(DF.then(DF.then(l10(), l => DF.then(r10(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j10_semi\n" ++ DF.dump(DF.then(DF.then(l10(), l => DF.then(r10(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j10_anti\n" ++ DF.dump(DF.then(DF.then(l10(), l => DF.then(r10(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j11_inner\n" ++ DF.dump(DF.then(DF.then(l11(), l => DF.then(r11(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j11_left\n" ++ DF.dump(DF.then(DF.then(l11(), l => DF.then(r11(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j11_semi\n" ++ DF.dump(DF.then(DF.then(l11(), l => DF.then(r11(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j11_anti\n" ++ DF.dump(DF.then(DF.then(l11(), l => DF.then(r11(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j12_inner\n" ++ DF.dump(DF.then(DF.then(l12(), l => DF.then(r12(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j12_left\n" ++ DF.dump(DF.then(DF.then(l12(), l => DF.then(r12(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j12_semi\n" ++ DF.dump(DF.then(DF.then(l12(), l => DF.then(r12(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j12_anti\n" ++ DF.dump(DF.then(DF.then(l12(), l => DF.then(r12(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j13_inner\n" ++ DF.dump(DF.then(DF.then(l13(), l => DF.then(r13(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j13_left\n" ++ DF.dump(DF.then(DF.then(l13(), l => DF.then(r13(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j13_semi\n" ++ DF.dump(DF.then(DF.then(l13(), l => DF.then(r13(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j13_anti\n" ++ DF.dump(DF.then(DF.then(l13(), l => DF.then(r13(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j14_inner\n" ++ DF.dump(DF.then(DF.then(l14(), l => DF.then(r14(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j14_left\n" ++ DF.dump(DF.then(DF.then(l14(), l => DF.then(r14(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j14_semi\n" ++ DF.dump(DF.then(DF.then(l14(), l => DF.then(r14(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j14_anti\n" ++ DF.dump(DF.then(DF.then(l14(), l => DF.then(r14(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j15_inner\n" ++ DF.dump(DF.then(DF.then(l15(), l => DF.then(r15(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j15_left\n" ++ DF.dump(DF.then(DF.then(l15(), l => DF.then(r15(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j15_semi\n" ++ DF.dump(DF.then(DF.then(l15(), l => DF.then(r15(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j15_anti\n" ++ DF.dump(DF.then(DF.then(l15(), l => DF.then(r15(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j16_inner\n" ++ DF.dump(DF.then(DF.then(l16(), l => DF.then(r16(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j16_left\n" ++ DF.dump(DF.then(DF.then(l16(), l => DF.then(r16(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j16_semi\n" ++ DF.dump(DF.then(DF.then(l16(), l => DF.then(r16(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j16_anti\n" ++ DF.dump(DF.then(DF.then(l16(), l => DF.then(r16(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j17_inner\n" ++ DF.dump(DF.then(DF.then(l17(), l => DF.then(r17(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j17_left\n" ++ DF.dump(DF.then(DF.then(l17(), l => DF.then(r17(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j17_semi\n" ++ DF.dump(DF.then(DF.then(l17(), l => DF.then(r17(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j17_anti\n" ++ DF.dump(DF.then(DF.then(l17(), l => DF.then(r17(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j18_inner\n" ++ DF.dump(DF.then(DF.then(l18(), l => DF.then(r18(), r => DF.inner_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j18_left\n" ++ DF.dump(DF.then(DF.then(l18(), l => DF.then(r18(), r => DF.left_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j18_semi\n" ++ DF.dump(DF.then(DF.then(l18(), l => DF.then(r18(), r => DF.semi_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j18_anti\n" ++ DF.dump(DF.then(DF.then(l18(), l => DF.then(r18(), r => DF.anti_join(l, r, ["k", "q"], ["k", "q"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j19_inner\n" ++ DF.dump(DF.then(DF.then(l19(), l => DF.then(r19(), r => DF.inner_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j19_left\n" ++ DF.dump(DF.then(DF.then(l19(), l => DF.then(r19(), r => DF.left_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li"), DF.col("ri")]))))
    IO.print("CASE j19_semi\n" ++ DF.dump(DF.then(DF.then(l19(), l => DF.then(r19(), r => DF.semi_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE j19_anti\n" ++ DF.dump(DF.then(DF.then(l19(), l => DF.then(r19(), r => DF.anti_join(l, r, ["k"], ["k"]))), f => DF.select(f, [DF.col("li")]))))
    IO.print("CASE f0_0\n" ++ DF.dump(DF.then(f0_0(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(0))))))
    IO.print("CASE f1_0\n" ++ DF.dump(DF.then(f1_0(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(0))))))
    IO.print("CASE f1_1\n" ++ DF.dump(DF.then(f1_1(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(1))))))
    IO.print("CASE f8_0\n" ++ DF.dump(DF.then(f8_0(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(0))))))
    IO.print("CASE f8_1\n" ++ DF.dump(DF.then(f8_1(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(1))))))
    IO.print("CASE f8_2\n" ++ DF.dump(DF.then(f8_2(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(2))))))
    IO.print("CASE f8_8\n" ++ DF.dump(DF.then(f8_8(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(8))))))
    IO.print("CASE f16_0\n" ++ DF.dump(DF.then(f16_0(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(0))))))
    IO.print("CASE f16_1\n" ++ DF.dump(DF.then(f16_1(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(1))))))
    IO.print("CASE f16_2\n" ++ DF.dump(DF.then(f16_2(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(2))))))
    IO.print("CASE f16_3\n" ++ DF.dump(DF.then(f16_3(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(3))))))
    IO.print("CASE f16_16\n" ++ DF.dump(DF.then(f16_16(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(16))))))
    IO.print("CASE f32_0\n" ++ DF.dump(DF.then(f32_0(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(0))))))
    IO.print("CASE f32_1\n" ++ DF.dump(DF.then(f32_1(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(1))))))
    IO.print("CASE f32_4\n" ++ DF.dump(DF.then(f32_4(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(4))))))
    IO.print("CASE f32_5\n" ++ DF.dump(DF.then(f32_5(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(5))))))
    IO.print("CASE f32_32\n" ++ DF.dump(DF.then(f32_32(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(32))))))
    IO.print("CASE f64_0\n" ++ DF.dump(DF.then(f64_0(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(0))))))
    IO.print("CASE f64_1\n" ++ DF.dump(DF.then(f64_1(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(1))))))
    IO.print("CASE f64_8\n" ++ DF.dump(DF.then(f64_8(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(8))))))
    IO.print("CASE f64_9\n" ++ DF.dump(DF.then(f64_9(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(9))))))
    IO.print("CASE f64_64\n" ++ DF.dump(DF.then(f64_64(), f => DF.filter(f, DF.lt(DF.col("id"), DF.lit_u32(64))))))
