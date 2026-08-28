#!/usr/bin/env python3
"""Generate ajave's own Java verification benchmarks, in SV-COMP task format.

Why this exists
---------------
Every signal we currently steer on comes from `sv-benchmarks/`, which is also
what we score on (issue #47). Issue #48 showed the cost concretely: 22 JDK
methods had been allowlisted as non-throwing because the corpus never exercised
them, which is a reachable wrong TRUE on any program that does.

These benchmarks are deliberately *narrow*. Each one isolates a single JVM
semantic rule or a single capability of one of our engines, and its verdict is
known by construction rather than by asking the tool. That makes a wrong answer
diagnostic: it names the feature that broke, instead of telling us some large
program changed verdict.

Each case is emitted twice where it makes sense — a `-true` variant where the
property holds and a `-false` variant where it is violated — because a tool that
answers TRUE for everything and a tool that answers FALSE for everything both
score well on a one-sided suite.

Layout matches sv-benchmarks so existing tooling works unchanged:

    ajave-benchmarks/
      properties/{valid-assert,no-runtime-exception}.prp
      common/org/sosy_lab/sv_benchmarks/Verifier.java   (symlinked)
      <category>/<Name>/Main.java
      <category>/<Name>.yml

Usage: python3 tools/gen_own_benchmarks.py [--out ajave-benchmarks]
"""

import argparse
import os
import shutil
import sys

# ---------------------------------------------------------------------------
# Benchmark definitions.
#
# Each entry: (category, name, assert_verdict, nre_verdict, body)
#   assert_verdict / nre_verdict: True = property holds, False = violated,
#                                 None = omit this property from the task
# `body` is the contents of `Main.main`, plus optional extra class members via
# a `%%MEMBERS%%` split marker.
# ---------------------------------------------------------------------------

V = "org.sosy_lab.sv_benchmarks.Verifier"

CASES = []


def case(cat, name, assert_v, nre_v, body, members=""):
    CASES.append((cat, name, assert_v, nre_v, body, members))


# ── JVM integer semantics ──────────────────────────────────────────────────
case("jvm-integers", "IntOverflowWraps", True, True, f"""
    // JVM int arithmetic wraps on overflow rather than throwing.
    int x = Integer.MAX_VALUE;
    int y = x + 1;
    assert y == Integer.MIN_VALUE;
""")

case("jvm-integers", "IntOverflowWrapsViolated", False, True, f"""
    // Same wraparound, asserted incorrectly: overflow does not saturate.
    int x = Integer.MAX_VALUE;
    int y = x + 1;
    assert y == Integer.MAX_VALUE;
""")

case("jvm-integers", "MinValueDivMinusOne", True, True, f"""
    // Integer.MIN_VALUE / -1 overflows and wraps back to MIN_VALUE.
    // It does NOT throw, unlike division by zero.
    int x = Integer.MIN_VALUE;
    int y = x / -1;
    assert y == Integer.MIN_VALUE;
""")

case("jvm-integers", "DivByZeroThrows", None, False, f"""
    // ArithmeticException is a RuntimeException: NRE must be violated.
    int d = {V}.nondetInt();
    {V}.assume(d == 0);
    int y = 10 / d;
    assert y != 0;
""")

case("jvm-integers", "RemainderSignFollowsDividend", True, True, f"""
    // Java's % takes the sign of the dividend, unlike floorMod.
    assert (-7 % 3) == -1;
    assert (7 % -3) == 1;
""")

case("jvm-integers", "ShiftDistanceIsMasked", True, True, f"""
    // Shift distances are masked to 5 bits for int, 6 for long.
    int x = 1;
    assert (x << 32) == 1;
    long l = 1L;
    assert (l << 64) == 1L;
""")

case("jvm-integers", "UnsignedShiftDiffersFromSigned", True, True, f"""
    int x = -1;
    assert (x >> 1) == -1;
    assert (x >>> 1) == Integer.MAX_VALUE;
""")

case("jvm-integers", "NarrowingCastTruncates", True, True, f"""
    int big = 300;
    byte b = (byte) big;
    assert b == 44;
    char c = (char) -1;
    assert c == 65535;
""")

# ── JVM floating point ─────────────────────────────────────────────────────
case("jvm-floats", "NaNNotEqualItself", True, True, f"""
    double nan = 0.0 / 0.0;
    assert nan != nan;
    assert Double.isNaN(nan);
""")

case("jvm-floats", "NegativeZeroEqualsZero", True, True, f"""
    // -0.0 == 0.0 is true, but they differ under Double.compare.
    double negZero = -0.0;
    assert negZero == 0.0;
    assert Double.compare(negZero, 0.0) < 0;
""")

case("jvm-floats", "FloatDivByZeroIsInfinity", True, True, f"""
    // Floating-point division by zero yields Infinity, not an exception.
    double d = 1.0 / 0.0;
    assert Double.isInfinite(d);
""")

case("jvm-floats", "AdditionNotAssociative", True, True, f"""
    double a = 1e16, b = -1e16, c = 1.0;
    assert ((a + b) + c) == 1.0;
    assert (a + (b + c)) == 0.0;
""")

# ── Null dereference ───────────────────────────────────────────────────────
case("jvm-null", "NullFieldDeref", None, False, """
    Node n = null;
    int v = n.value;
    assert v == 0;
""", members="""
  static class Node { int value; }
""")

case("jvm-null", "NonNullAfterConstructor", None, True, """
    Node n = new Node();
    int v = n.value;
    assert v == 0;
""", members="""
  static class Node { int value; }
""")

case("jvm-null", "NullGuardedByBranch", None, True, f"""
    Node n = {V}.nondetBoolean() ? new Node() : null;
    if (n != null) {{
      int v = n.value;
      assert v == 0;
    }}
""", members="""
  static class Node { int value; }
""")

case("jvm-null", "NullChainedDeref", None, False, f"""
    // The outer object is non-null but its field is not.
    Holder h = new Holder();
    int v = h.inner.value;
    assert v == 0;
""", members="""
  static class Node { int value; }
  static class Holder { Node inner; }
""")

# ── Arrays ─────────────────────────────────────────────────────────────────
case("jvm-arrays", "ConstantIndexInBounds", None, True, """
    // Length is a constant, indices are constants: provable without solving.
    int[] a = new int[3];
    a[0] = 1; a[1] = 2; a[2] = 3;
    assert a.length == 3;
""")

case("jvm-arrays", "ConstantIndexOutOfBounds", None, False, """
    int[] a = new int[3];
    a[3] = 1;
    assert a[0] == 0;
""")

case("jvm-arrays", "NegativeArraySize", None, False, f"""
    int n = {V}.nondetInt();
    {V}.assume(n < 0);
    int[] a = new int[n];
    assert a.length >= 0;
""")

case("jvm-arrays", "LoopBoundedByLength", None, True, """
    // Requires relating the loop counter to the array length.
    int[] a = new int[10];
    for (int i = 0; i < a.length; i++) {
      a[i] = i;
    }
    assert a[9] == 9;
""")

case("jvm-arrays", "OffByOneInLoop", None, False, """
    int[] a = new int[10];
    for (int i = 0; i <= a.length; i++) {
      a[i] = i;
    }
    assert a[0] == 0;
""")

# ── Exception control flow ─────────────────────────────────────────────────
case("jvm-exceptions", "CaughtExceptionNotPropagated", None, True, """
    // The NPE is caught, so no RuntimeException escapes main.
    try {
      String s = null;
      s.length();
    } catch (NullPointerException e) {
      // handled
    }
""")

case("jvm-exceptions", "AssertionInCatchBlock", False, None, """
    // The assertion is reachable only via the exception edge out of a call.
    try {
      thrower();
      assert true;
    } catch (RuntimeException e) {
      assert false;
    }
""", members="""
  static void thrower() { throw new IllegalStateException("boom"); }
""")

case("jvm-exceptions", "FinallyRunsOnException", True, None, """
    int[] state = new int[1];
    try {
      throw new IllegalStateException();
    } catch (RuntimeException e) {
      state[0] = 1;
    } finally {
      state[0] = state[0] + 10;
    }
    assert state[0] == 11;
""")

case("jvm-exceptions", "CheckedHandlerDoesNotCatchRuntime", None, False, """
    // Catching a checked exception must not mask the NPE.
    try {
      maybeIo();
      String s = null;
      s.length();
    } catch (java.io.IOException e) {
      // does not catch NullPointerException
    }
""", members="""
  static void maybeIo() throws java.io.IOException { }
""")

# ── Class/type semantics ───────────────────────────────────────────────────
case("jvm-types", "ClassCastOnBadDowncast", None, False, """
    Object o = "a string";
    Integer i = (Integer) o;
    assert i != null;
""")

case("jvm-types", "InstanceOfGuardsCast", None, True, """
    Object o = "a string";
    if (o instanceof Integer) {
      Integer i = (Integer) o;
      assert i != null;
    }
""")

case("jvm-types", "VirtualDispatchPicksOverride", True, True, """
    Base b = new Derived();
    assert b.value() == 2;
""", members="""
  static class Base { int value() { return 1; } }
  static class Derived extends Base { int value() { return 2; } }
""")

case("jvm-types", "StaticInitRunsBeforeAccess", True, True, """
    assert Config.LIMIT == 42;
""", members="""
  static class Config {
    static final int LIMIT;
    static { LIMIT = 42; }
  }
""")

# ── Boxing / caching ───────────────────────────────────────────────────────
case("jvm-boxing", "IntegerCacheIdentity", True, True, """
    // Values in [-128, 127] are cached, so == compares equal by identity.
    Integer a = 127, b = 127;
    assert a == b;
""")

case("jvm-boxing", "OutsideCacheUseEquals", True, True, """
    // Outside the cache range identity is not guaranteed, but equals holds.
    Integer a = 1000, b = 1000;
    assert a.equals(b);
""")

case("jvm-boxing", "UnboxingNullThrows", None, False, """
    Integer boxed = null;
    int raw = boxed;
    assert raw == 0;
""")

# ── Strings ────────────────────────────────────────────────────────────────
case("jvm-strings", "LiteralsAreInterned", True, True, """
    String a = "hello", b = "hello";
    assert a == b;
""")

case("jvm-strings", "ConcatCreatesNewObject", True, True, """
    String a = "hel";
    String b = a + "lo";
    assert b.equals("hello");
""")

case("jvm-strings", "CharAtOutOfBounds", None, False, """
    String s = "abc";
    char c = s.charAt(5);
    assert c == 'a';
""")

case("jvm-strings", "SubstringOutOfBounds", None, False, """
    String s = "abc";
    String t = s.substring(4);
    assert t != null;
""")

# ── JDK methods our allowlist makes claims about (issue #48) ───────────────
case("jdk-contracts", "ListGetOutOfBounds", None, False, """
    java.util.List<String> l = new java.util.ArrayList<String>();
    String s = l.get(0);
    assert s != null;
""")

case("jdk-contracts", "IteratorNextOnEmpty", None, False, """
    java.util.Iterator<String> it = new java.util.ArrayList<String>().iterator();
    String s = it.next();
    assert s != null;
""")

case("jdk-contracts", "MathAddExactOverflows", None, False, """
    int x = Math.addExact(Integer.MAX_VALUE, 1);
    assert x != 0;
""")

case("jdk-contracts", "MathAbsDoesNotThrow", None, True, """
    // Math.abs(MIN_VALUE) returns MIN_VALUE rather than throwing.
    int x = Math.abs(Integer.MIN_VALUE);
    assert x == Integer.MIN_VALUE;
""")

case("jdk-contracts", "IntegerValueOfStringThrows", None, False, """
    Integer i = Integer.valueOf("not a number");
    assert i != null;
""")

case("jdk-contracts", "IntegerValueOfIntIsTotal", None, True, """
    Integer i = Integer.valueOf(Integer.MIN_VALUE);
    assert i.intValue() == Integer.MIN_VALUE;
""")

case("jdk-contracts", "ArraycopyOutOfBounds", None, False, """
    int[] src = new int[1], dst = new int[1];
    System.arraycopy(src, 0, dst, 0, 5);
    assert dst[0] == 0;
""")

case("jdk-contracts", "StringBuilderNegativeCapacity", None, False, """
    StringBuilder sb = new StringBuilder(-1);
    assert sb != null;
""")

# ── Engine-targeted: abstract interpretation ───────────────────────────────
case("engine-ai", "IntervalNarrowingProvesAssert", True, True, f"""
    // Provable by the interval domain alone, no solver needed.
    int x = {V}.nondetInt();
    {V}.assume(x > 5);
    assert x > 3;
""")

case("engine-ai", "UnboundedLoopNeedsWidening", True, True, f"""
    // The trip count is not statically known, so the analysis only converges
    // if widening is applied at the loop header.
    int n = {V}.nondetInt();
    {V}.assume(n > 0);
    int i = 0;
    while (i < n) {{ i++; }}
    assert i >= 0;
""")

case("engine-ai", "BitwiseAndOfComparisons", True, True, f"""
    // javac lowers && over comparisons into a bitwise & of 0/1 values.
    int i = {V}.nondetInt();
    {V}.assume(i >= 0 && i < 10);
    assert i >= 0 & i < 10;
""")

case("engine-ai", "FieldValueSurvivesCall", True, True, """
    // Requires knowing that pureCall() does not write the field.
    Counter c = new Counter();
    c.n = 5;
    pureCall();
    assert c.n == 5;
""", members="""
  static class Counter { int n; }
  static void pureCall() { }
""")

case("engine-ai", "FieldClobberedByCall", True, True, """
    // The callee does write the field, so the analysis must not assume 5.
    Counter c = new Counter();
    c.n = 5;
    bump(c);
    assert c.n == 6;
""", members="""
  static class Counter { int n; }
  static void bump(Counter c) { c.n = c.n + 1; }
""")

# ── Engine-targeted: bounded model checking / falsification ────────────────
case("engine-bmc", "DeepPathToViolation", False, None, f"""
    // A specific input is needed; reachable only by solving, not by probing.
    int x = {V}.nondetInt();
    if (x > 1000 && x < 1010 && x % 7 == 3) {{
      assert false;
    }}
""")

case("engine-bmc", "NoInputReachesViolation", True, None, f"""
    // The guard is unsatisfiable, so the assertion is unreachable.
    int x = {V}.nondetInt();
    if (x > 10 && x < 5) {{
      assert false;
    }}
""")

case("engine-bmc", "PathExplosionBounded", True, None, f"""
    // 2^8 paths: exercises merging rather than raw enumeration.
    int sum = 0;
    for (int i = 0; i < 8; i++) {{
      if ({V}.nondetBoolean()) {{ sum++; }}
    }}
    assert sum >= 0 && sum <= 8;
""")

# ── Engine-targeted: recursion / CHC ───────────────────────────────────────
case("engine-recursion", "FactorialPositive", True, True, f"""
    int n = {V}.nondetInt();
    {V}.assume(n >= 0 && n <= 6);
    assert fact(n) >= 1;
""", members="""
  static int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
""")

case("engine-recursion", "MutualRecursionParity", True, True, f"""
    int n = {V}.nondetInt();
    {V}.assume(n >= 0 && n <= 10);
    assert isEven(n) != isOdd(n);
""", members="""
  static boolean isEven(int n) { return n == 0 ? true : isOdd(n - 1); }
  static boolean isOdd(int n) { return n == 0 ? false : isEven(n - 1); }
""")

# ── Witness replay ─────────────────────────────────────────────────────────
case("witness", "SingleIntWitness", False, None, f"""
    // A FALSE verdict here must come with a replayable witness value.
    int x = {V}.nondetInt();
    if (x == 42) {{
      assert false;
    }}
""")

case("witness", "TwoIntWitnessOrdering", False, None, f"""
    // Two nondet reads: the witness must preserve their order.
    int a = {V}.nondetInt();
    int b = {V}.nondetInt();
    if (a == 1 && b == 2) {{
      assert false;
    }}
""")

case("witness", "BooleanWitness", False, None, f"""
    boolean p = {V}.nondetBoolean();
    boolean q = {V}.nondetBoolean();
    if (p && !q) {{
      assert false;
    }}
""")


# ---------------------------------------------------------------------------
# Emission
# ---------------------------------------------------------------------------

MAIN_TEMPLATE = """// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: {name}
// Expected: valid-assert={av}, no-runtime-exception={nv}

public class Main {{
{members}
  public static void main(String[] args) {{{body}  }}
}}
"""

YML_TEMPLATE = """format_version: "2.0"
input_files:
  - ../common/
  - {name}/
properties:
{props}options:
  language: Java
"""


def verdict_str(v):
    return "true" if v else "false"


def emit(out_dir):
    n_written = 0
    for cat, name, av, nv, body, members in CASES:
        cat_dir = os.path.join(out_dir, cat)
        src_dir = os.path.join(cat_dir, name)
        os.makedirs(src_dir, exist_ok=True)

        with open(os.path.join(src_dir, "Main.java"), "w") as f:
            f.write(MAIN_TEMPLATE.format(
                name=name,
                av=("n/a" if av is None else verdict_str(av)),
                nv=("n/a" if nv is None else verdict_str(nv)),
                members=members.rstrip("\n"),
                body=body if body.startswith("\n") else "\n" + body,
            ))

        props = ""
        if av is not None:
            props += ("  - property_file: ../../properties/valid-assert.prp\n"
                      f"    expected_verdict: {verdict_str(av)}\n")
        if nv is not None:
            props += ("  - property_file: ../../properties/no-runtime-exception.prp\n"
                      f"    expected_verdict: {verdict_str(nv)}\n")

        with open(os.path.join(cat_dir, name + ".yml"), "w") as f:
            f.write(YML_TEMPLATE.format(name=name, props=props))
        n_written += 1
    return n_written


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="ajave-benchmarks")
    args = ap.parse_args()
    out = args.out

    os.makedirs(out, exist_ok=True)

    # Properties: copy from sv-benchmarks so the definitions stay identical.
    props_out = os.path.join(out, "properties")
    os.makedirs(props_out, exist_ok=True)
    for p in ("valid-assert.prp", "no-runtime-exception.prp"):
        src = os.path.join("sv-benchmarks", "properties", p)
        if os.path.exists(src):
            shutil.copy(src, os.path.join(props_out, p))

    # Common: the Verifier stub, copied so the suite is self-contained.
    common_out = os.path.join(out, "common")
    src_common = os.path.join("sv-benchmarks", "common")
    if os.path.isdir(src_common) and not os.path.isdir(common_out):
        shutil.copytree(src_common, common_out)

    n = emit(out)

    cats = sorted({c for c, *_ in CASES})
    both = sum(1 for _c, _n, a, v, *_ in CASES if a is not None and v is not None)
    only_assert = sum(1 for _c, _n, a, v, *_ in CASES if a is not None and v is None)
    only_nre = sum(1 for _c, _n, a, v, *_ in CASES if a is None and v is not None)

    print(f"wrote {n} benchmarks across {len(cats)} categories -> {out}/")
    for c in cats:
        k = sum(1 for cc, *_ in CASES if cc == c)
        print(f"  {c:<20s} {k:3d}")
    print(f"\nproperty coverage: both={both}  assert-only={only_assert}  nre-only={only_nre}")

    # A one-sided suite is easy to game, so report the true/false balance.
    a_true = sum(1 for _c, _n, a, *_ in CASES if a is True)
    a_false = sum(1 for _c, _n, a, *_ in CASES if a is False)
    n_true = sum(1 for _c, _n, _a, v, *_ in CASES if v is True)
    n_false = sum(1 for _c, _n, _a, v, *_ in CASES if v is False)
    print(f"valid-assert:          TRUE={a_true}  FALSE={a_false}")
    print(f"no-runtime-exception:  TRUE={n_true}  FALSE={n_false}")


if __name__ == "__main__":
    main()
