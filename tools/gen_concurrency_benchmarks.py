#!/usr/bin/env python3
"""Generate ajave's concurrency litmus benchmarks, in SV-COMP task format.

These are written *before* the concurrency engine exists, deliberately. Every
capability this session added was validated by a benchmark that already existed
and could name the broken feature; building the engine first would leave us
grading its output against our own intuitions.

Ground truth here cannot be established the way it is for the sequential suite.
`tools/validate_own_benchmarks.py` runs a program and observes what happens, but
for a concurrent program:

  * a racy execution need not manifest the race on any given run, so observing
    no failure proves nothing; and
  * a *safe* program passing a thousand runs still proves nothing.

So each benchmark carries an explicit `justification` recorded in the generated
source, stating why the expected verdict holds by construction. That comment is
the ground truth. A JVM run can *refute* an expected-TRUE (if it ever fails, the
program is not safe) but can never confirm one — which is exactly the asymmetry
`validate_concurrency_benchmarks.py` enforces.

Layout matches `benchmarks/ajave/` so existing tooling works unchanged.

Usage: python3 tools/gen_concurrency_benchmarks.py [--out benchmarks/ajave]
"""

import argparse
import os
import shutil

V = "org.sosy_lab.sv_benchmarks.Verifier"

CASES = []


def case(name, assert_v, nre_v, justification, body, members="", deadlock_v=None):
    """assert_v / nre_v / deadlock_v: True (holds), False (violated), None (omit)."""
    CASES.append((name, assert_v, nre_v, justification, body, members, deadlock_v))


# ── Thread lifecycle ────────────────────────────────────────────────────────

case("ThreadBodyThrows", None, False,
     "The Runnable dereferences null unconditionally. Whatever the schedule, "
     "run() executes and raises NullPointerException. This is the defect that "
     "motivated the whole plan: `Thread` was in PURE_OWNERS, so start() was "
     "erased and the body never analysed, giving a wrong TRUE.",
     """
    Thread t = new Thread(new Boom());
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
""",
     """
  static class Boom implements Runnable {
    public void run() {
      String s = null;
      s.length();
    }
  }
""")

case("ThreadBodySafe", None, True,
     "run() performs only local arithmetic on a local variable. No shared "
     "state, no partial function, no schedule can make it throw.",
     """
    Thread t = new Thread(new Quiet());
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
""",
     """
  static class Quiet implements Runnable {
    public void run() {
      int x = 0;
      for (int i = 0; i < 3; i++) x += i;
    }
  }
""")

case("JoinOrdersWrite", True, None,
     "join() establishes happens-before between the thread's final action and "
     "the joiner's next action (JLS 17.4.5). The write in run() is therefore "
     "visible and complete before the assert, under every schedule.",
     """
    Setter s = new Setter();
    Thread t = new Thread(s);
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
    assert s.value == 42;
""",
     """
  static class Setter implements Runnable {
    int value = 0;
    public void run() { value = 42; }
  }
""")

case("NoJoinNoOrdering", None, True,
     "Without join() the main thread may read `value` before or after the "
     "write, so both 0 and 42 are legal outcomes. The program asserts nothing "
     "about which, and no read here can throw — so it is NRE-safe while being "
     "genuinely nondeterministic. A verifier that reports a violation is "
     "wrong; one that reports TRUE for valid-assert without reasoning about "
     "the interleaving is guessing.",
     """
    Setter s = new Setter();
    new Thread(s).start();
    int observed = s.value;
    assert observed == 0 || observed == 42;
""",
     """
  static class Setter implements Runnable {
    int value = 0;
    public void run() { value = 42; }
  }
""")

# ── Monitors and mutual exclusion ───────────────────────────────────────────

case("SynchronizedCounter", True, True,
     "Both increments hold the same monitor, so the read-modify-write is "
     "atomic and the two increments are ordered by the monitor's "
     "synchronizes-with edge. The total is 2 under every schedule.",
     """
    Counter c = new Counter();
    Thread t = new Thread(new Inc(c));
    t.start();
    c.inc();
    try { t.join(); } catch (InterruptedException e) { }
    assert c.n == 2;
""",
     """
  static class Counter {
    int n = 0;
    synchronized void inc() { n = n + 1; }
  }
  static class Inc implements Runnable {
    final Counter c;
    Inc(Counter c) { this.c = c; }
    public void run() { c.inc(); }
  }
""")

case("UnsynchronizedCounter", False, None,
     "The increments are not atomic: both threads can read 0, both write 1, "
     "and the total is 1 rather than 2. That interleaving is permitted, so the "
     "assertion is violable. NOTE the asymmetry — this is expected FALSE, but "
     "a single execution will usually print 2, so running it is not evidence "
     "either way.",
     """
    Counter c = new Counter();
    Thread t = new Thread(new Inc(c));
    t.start();
    c.inc();
    try { t.join(); } catch (InterruptedException e) { }
    assert c.n == 2;
""",
     """
  static class Counter {
    int n = 0;
    void inc() { n = n + 1; }
  }
  static class Inc implements Runnable {
    final Counter c;
    Inc(Counter c) { this.c = c; }
    public void run() { c.inc(); }
  }
""")

case("MutualExclusionHolds", True, None,
     "Both threads increment under the same lock, so at most one is inside the "
     "critical section. The invariant `flag == 0` on entry cannot be observed "
     "broken.",
     """
    Guard g = new Guard();
    Thread t = new Thread(new Enter(g));
    t.start();
    g.enter();
    try { t.join(); } catch (InterruptedException e) { }
    assert g.violations == 0;
""",
     """
  static class Guard {
    int flag = 0;
    int violations = 0;
    synchronized void enter() {
      if (flag != 0) violations++;
      flag = 1;
      flag = 0;
    }
  }
  static class Enter implements Runnable {
    final Guard g;
    Enter(Guard g) { this.g = g; }
    public void run() { g.enter(); }
  }
""")

# ── Deadlock ────────────────────────────────────────────────────────────────

case("LockOrderInversion", None, None,
     "Classic AB/BA deadlock: main takes a then b, the other thread takes b "
     "then a. An interleaving exists where each holds one and waits for the "
     "other. Neither valid-assert nor no-runtime-exception is violated by a "
     "deadlock — the program hangs rather than failing — so both properties "
     "are omitted and this benchmark exists for the no-deadlock property, "
     "which SV-COMP defines but no Java category uses.",
     """
    Locks l = new Locks();
    Thread t = new Thread(new BA(l));
    t.start();
    synchronized (l.a) {
      synchronized (l.b) { }
    }
    try { t.join(); } catch (InterruptedException e) { }
""",
     """
  static class Locks {
    final Object a = new Object();
    final Object b = new Object();
  }
  static class BA implements Runnable {
    final Locks l;
    BA(Locks l) { this.l = l; }
    public void run() {
      synchronized (l.b) {
        synchronized (l.a) { }
      }
    }
  }
""")

case("ConsistentLockOrder", True, None,
     "Both threads acquire a before b, so no cycle in the wait-for graph is "
     "possible and the program terminates. The assertion is on a value written "
     "under the lock and read after join.",
     """
    Locks l = new Locks();
    Thread t = new Thread(new AB(l));
    t.start();
    synchronized (l.a) {
      synchronized (l.b) { l.n++; }
    }
    try { t.join(); } catch (InterruptedException e) { }
    assert l.n == 2;
""",
     """
  static class Locks {
    final Object a = new Object();
    final Object b = new Object();
    int n = 0;
  }
  static class AB implements Runnable {
    final Locks l;
    AB(Locks l) { this.l = l; }
    public void run() {
      synchronized (l.a) {
        synchronized (l.b) { l.n++; }
      }
    }
  }
""")

# ── Visibility ──────────────────────────────────────────────────────────────

case("VolatileVisibility", None, True,
     "A volatile write happens-before every subsequent volatile read of the "
     "same field (JLS 17.4.4), so the reader either sees 0 or 1 and never a "
     "torn value. No read here can throw regardless.",
     """
    Flag f = new Flag();
    Thread t = new Thread(new Setter(f));
    t.start();
    int seen = f.ready;
    try { t.join(); } catch (InterruptedException e) { }
    assert seen == 0 || seen == 1;
""",
     """
  static class Flag {
    volatile int ready = 0;
  }
  static class Setter implements Runnable {
    final Flag f;
    Setter(Flag f) { this.f = f; }
    public void run() { f.ready = 1; }
  }
""")

case("NonVolatileNoGuarantee", None, True,
     "Without volatile there is no happens-before edge, so the main thread may "
     "never observe the write at all — a legal outcome under the JMM, not a "
     "bug. Included to check we do not report a violation for a program that "
     "is merely nondeterministic. Nothing here can throw.",
     """
    Flag f = new Flag();
    Thread t = new Thread(new Setter(f));
    t.start();
    int seen = f.ready;
    try { t.join(); } catch (InterruptedException e) { }
    assert seen == 0 || seen == 1;
""",
     """
  static class Flag {
    int ready = 0;
  }
  static class Setter implements Runnable {
    final Flag f;
    Setter(Flag f) { this.f = f; }
    public void run() { f.ready = 1; }
  }
""")

# ── Shared-state exceptions ─────────────────────────────────────────────────

case("RacyNullDeref", None, False,
     "The worker clears the reference while main dereferences it. An "
     "interleaving exists where the write lands between main's null check and "
     "its use, so NullPointerException is reachable. This is the shape a "
     "concurrency engine must find and a sequential one cannot.",
     """
    Holder h = new Holder();
    Thread t = new Thread(new Clear(h));
    t.start();
    if (h.s != null) {
      h.s.length();
    }
    try { t.join(); } catch (InterruptedException e) { }
""",
     """
  static class Holder {
    String s = "abc";
  }
  static class Clear implements Runnable {
    final Holder h;
    Clear(Holder h) { this.h = h; }
    public void run() { h.s = null; }
  }
""")

case("GuardedNullDeref", None, True,
     "Same shape, but the check and the use are both inside a synchronized "
     "block on the same monitor the writer uses, so no interleaving can place "
     "the write between them.",
     """
    Holder h = new Holder();
    Thread t = new Thread(new Clear(h));
    t.start();
    synchronized (h) {
      if (h.s != null) {
        h.s.length();
      }
    }
    try { t.join(); } catch (InterruptedException e) { }
""",
     """
  static class Holder {
    String s = "abc";
  }
  static class Clear implements Runnable {
    final Holder h;
    Clear(Holder h) { this.h = h; }
    public void run() { synchronized (h) { h.s = null; } }
  }
""")

# ── Interaction with nondeterministic input ─────────────────────────────────

case("ScheduleAndInputBoth", False, None,
     "Requires *both* a specific input and a specific interleaving: the "
     "assertion fails only when the nondet value is 7 and the worker's write "
     "lands first. A witness must therefore record the input sequence and the "
     "schedule — neither alone reproduces it. This is the benchmark that "
     "justifies Witness carrying both.",
     f"""
    Shared s = new Shared();
    Thread t = new Thread(new Bump(s));
    t.start();
    int x = {V}.nondetInt();
    try {{ t.join(); }} catch (InterruptedException e) {{ }}
    if (x == 7) {{
      assert s.n == 0;
    }}
""",
     """
  static class Shared {
    int n = 0;
  }
  static class Bump implements Runnable {
    final Shared s;
    Bump(Shared s) { this.s = s; }
    public void run() { s.n = 1; }
  }
""")


# Deadlock verdicts, attached by name so the positional `case()` signature stays
# readable. LockOrderInversion has a reachable AB/BA cycle; ConsistentLockOrder
# takes both locks in the same order, so no cycle is possible.
DEADLOCK_VERDICTS = {
    "LockOrderInversion": False,
    "ConsistentLockOrder": True,
}

MAIN_TEMPLATE = """// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: {name}
// Expected: valid-assert={av}, no-runtime-exception={nv}
//
// Ground truth (by construction, NOT by observation):
{justification}

public class Main {{
{members}
  public static void main(String[] args) throws Exception {{{body}  }}
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


def wrap(text, width=74, prefix="//   "):
    words, lines, cur = text.split(), [], ""
    for w in words:
        if len(cur) + len(w) + 1 > width:
            lines.append(prefix + cur)
            cur = w
        else:
            cur = (cur + " " + w).strip()
    if cur:
        lines.append(prefix + cur)
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="benchmarks/ajave")
    args = ap.parse_args()
    cat_dir = os.path.join(args.out, "concurrency")
    os.makedirs(cat_dir, exist_ok=True)

    for name, av, nv, just, body, members, _dv in CASES:
        dv = DEADLOCK_VERDICTS.get(name)
        src_dir = os.path.join(cat_dir, name)
        os.makedirs(src_dir, exist_ok=True)
        with open(os.path.join(src_dir, "Main.java"), "w") as f:
            f.write(MAIN_TEMPLATE.format(
                name=name,
                av=("n/a" if av is None else str(av).lower()),
                nv=("n/a" if nv is None else str(nv).lower()),
                justification=wrap(just),
                members=members.rstrip("\n"),
                body=body if body.startswith("\n") else "\n" + body,
            ))
        props = ""
        if av is not None:
            props += ("  - property_file: ../../properties/valid-assert.prp\n"
                      f"    expected_verdict: {str(av).lower()}\n")
        if nv is not None:
            props += ("  - property_file: ../../properties/no-runtime-exception.prp\n"
                      f"    expected_verdict: {str(nv).lower()}\n")
        if dv is not None:
            props += ("  - property_file: ../../properties/no-deadlock.prp\n"
                      f"    expected_verdict: {str(dv).lower()}\n")
        if not props:
            props = ("  # No property applies to this task.\n")
        with open(os.path.join(cat_dir, name + ".yml"), "w") as f:
            f.write(YML_TEMPLATE.format(name=name, props=props))

    d_t = sum(1 for v in DEADLOCK_VERDICTS.values() if v is True)
    d_f = sum(1 for v in DEADLOCK_VERDICTS.values() if v is False)
    a_t = sum(1 for _, a, *_ in CASES if a is True)
    a_f = sum(1 for _, a, *_ in CASES if a is False)
    n_t = sum(1 for _, _, n, *_ in CASES if n is True)
    n_f = sum(1 for _, _, n, *_ in CASES if n is False)
    print(f"wrote {len(CASES)} concurrency benchmarks -> {cat_dir}/")
    print(f"  valid-assert:          TRUE={a_t}  FALSE={a_f}")
    print(f"  no-runtime-exception:  TRUE={n_t}  FALSE={n_f}")
    print(f"  no-deadlock:           TRUE={d_t}  FALSE={d_f}")
    print("\nGround truth is by construction; see the justification comment in each")
    print("Main.java. Observation can refute an expected-TRUE but never confirm one.")


if __name__ == "__main__":
    main()
