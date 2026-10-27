#!/usr/bin/env python3
"""The IR interpreter must terminate the way a real JVM does.

    python3 tools/lifter_differential.py --dir benchmarks/ajave

# What this oracle is

Every engine's correctness begins at the lifter, so a lifter defect is a
*systematic* wrong answer across the whole portfolio, where an engine defect is
localised and usually caught by JVM replay. But a lifter defect is invisible to
the corpus: the verdict is the only thing a benchmark checks, and most defects
in lifting produce UNKNOWN rather than a wrong answer.

So this compares *executions* instead of verdicts:

  1. compile a task, lift it, run `ajave --interpret SEQ` -- the same IR
     interpreter the concrete engine uses, against a fixed nondet sequence
  2. run the compiled program on a real JVM with the same sequence, fed through
     the same deterministic shadow `Verifier` that `JvmReplay` uses
  3. compare how the two terminated

No expected-verdict label is involved, so this holds on programs no benchmark
covers, and it cannot be satisfied by overfitting.

# What it validates, and what it cannot

It validates the **pair** (lifter, interpreter). An identical misunderstanding
in both is invisible to it. It still catches everything where exactly one of
the two is wrong, which is the common case -- the three defects reduced out of
`float-nonlinear-calculation` were all of that shape.

`INCONCLUSIVE` is not agreement. The interpreter ignores `ArrayStore`, returns
`Unknown` for most heap reads, and stops at `Diverge`; counting those as
matches would report a clean run while checking nothing. They are reported as
their own bucket, and that bucket's size is the honest measure of this oracle's
reach.

**stdout is not compared.** The interpreter does not model `System.out` at all
-- a `println` is a havoced call -- so comparing output would flag every
program that prints and say nothing about lifting. Terminating exception class
is the signal.

# Why the exception *family* and not the exact class

Mirrors `JvmReplay`'s accepted sets, and for the same reason: the IR records an
`ObligationKind`, not a class. `ArrayBounds` covers `String.charAt` out of
range, which the JVM reports as `StringIndexOutOfBoundsException`;
`ExplicitThrow` records only that *some* `RuntimeException` subclass was
raised. Demanding the exact name would report divergences that are artefacts of
that coarseness. Where the IR does name a class exactly (`Threw`), the exact
name still has to be in the accepted family.

# Threads

The sequential interpreter deliberately does not model `Thread.start()` -- that
is the concurrency engine's job -- so a threaded program's termination is not
expected to match and a mismatch says nothing about the lifter. Those are
bucketed separately rather than silently skipped.

Exit code 1 if any divergence is found, 2 if the harness could not run.
"""

import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter

import yaml

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from procguard import run_guarded

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AJAVE = os.path.join(ROOT, "target", "release", "ajave")

CONCURRENT = re.compile(
    r"\bnew\s+Thread\b|\.start\s*\(\)|ExecutorService|CompletableFuture"
    r"|ForkJoinPool|\bThread\s*\.\s*ofVirtual\b"
)

# Which JVM exception names confirm an IR-side `ESCAPED <class>`.
#
# Keyed by the class the IR named, because that is what the IR can say. Kept
# deliberately parallel to the `accepted` table in `ajave-core/src/certify.rs`:
# the two answer the same question (does this JVM outcome match what we
# predicted) and a divergence between them would make one of the harnesses
# wrong about the other.
FAMILY = {
    "java.lang.AssertionError": {"java.lang.AssertionError"},
    "java.lang.ArithmeticException": {"java.lang.ArithmeticException"},
    "java.lang.NullPointerException": {"java.lang.NullPointerException"},
    "java.lang.ArrayIndexOutOfBoundsException": {
        "java.lang.ArrayIndexOutOfBoundsException",
        "java.lang.StringIndexOutOfBoundsException",
        "java.lang.IndexOutOfBoundsException",
    },
    "java.lang.NegativeArraySizeException": {
        "java.lang.NegativeArraySizeException",
        # `new StringBuilder(-1)` reports this instead.
        "java.lang.IllegalArgumentException",
    },
    "java.lang.ClassCastException": {"java.lang.ClassCastException"},
}

# `ExplicitThrow` records only that some RuntimeException subclass was raised,
# so the IR says `RuntimeException` and any subclass confirms it.
ANY_RUNTIME = "java.lang.RuntimeException"


def accepted(ir_class, jvm_class):
    if ir_class == jvm_class:
        return True
    if ir_class == ANY_RUNTIME:
        # Not "anything at all": an AssertionError is an Error, and an
        # interpreter that raised one where the JVM raises an exception is a
        # real disagreement.
        return jvm_class.endswith("Exception")
    return jvm_class in FAMILY.get(ir_class, set())


def load_tasks(root):
    """Every benchmark directory, from its own .yml."""
    tasks = []
    for yml in sorted(glob.glob(os.path.join(root, "*", "*.yml"))):
        name = os.path.splitext(os.path.basename(yml))[0]
        src_dir = os.path.join(os.path.dirname(yml), name)
        if os.path.isdir(src_dir):
            tasks.append((name, src_dir))
    return tasks


def build_shadow(workdir):
    """Compile the shadow Verifier ajave itself replays through."""
    src = os.path.join(workdir, "shadow-src")
    out = os.path.join(workdir, "shadow")
    os.makedirs(src, exist_ok=True)
    os.makedirs(out, exist_ok=True)
    r = subprocess.run([AJAVE, "--emit-shadow", src], capture_output=True, text=True)
    if r.returncode != 0:
        return None, f"--emit-shadow failed: {r.stderr.strip()}"
    srcs = glob.glob(os.path.join(src, "**", "*.java"), recursive=True)
    if not srcs:
        return None, "--emit-shadow wrote nothing"
    r = subprocess.run(["javac", "-nowarn", "-d", out] + srcs,
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None, f"shadow Verifier does not compile: {r.stderr[:800]}"
    return out, None


def sequences(trials):
    """The nondet sequences to try, identical on both sides.

    The empty sequence first: both the interpreter and the shadow `Verifier`
    fall back to 0 past the end of what they were given, so it is the all-zero
    probe -- the one the concrete engine itself runs, and the one most likely
    to reach a program's main path.

    The rest are fixed, not random. A differential whose inputs move between
    runs cannot distinguish a new defect from a new input, and CLAUDE.md's
    reproducibility rule applies to a harness as much as to a score. These are
    boundary values, which is where lifting and the JVM are most likely to
    part company: sign, width truncation, and the two's-complement extremes.
    """
    base = [
        [],
        [1] * 8,
        [-1] * 8,
        [2147483647, -2147483648, 0, 1, -1, 2147483647, -2147483648, 42],
        [255, 65535, 128, 32768, 7, 0, -7, 3],
    ]
    return base[:trials]


def interpret(task_dir, common, seq, timeout):
    arg = ",".join(str(v) for v in seq)
    cmd = [AJAVE, "--interpret", arg, common, task_dir]
    r = run_guarded(cmd, timeout=timeout)
    if r.timed_out:
        return "TIMEOUT", None
    for line in reversed(r.stdout.strip().splitlines()):
        line = line.strip()
        if line.startswith("INTERPRET "):
            rest = line[len("INTERPRET "):].strip()
            if rest.startswith("ESCAPED "):
                return "ESCAPED", rest[len("ESCAPED "):].strip()
            return rest, None
    return "NO-OUTPUT", (r.stderr or "")[-400:]


def run_jvm(classes, shadow, seq, timeout):
    """Run `Main` on a real JVM through the deterministic shadow Verifier.

    `-ea` is not optional. The lifter models `Class.desiredAssertionStatus()`
    as true, so `$assertionsDisabled` is false and the IR contains the
    assertion's throw. Running the JVM without `-ea` executes a different
    program, and every asserting benchmark would report a divergence caused by
    the harness.
    """
    cp = shadow + os.pathsep + classes
    cmd = ["java", "-ea", "-cp", cp,
           "-Dajave.seq=" + ",".join(str(v) for v in seq), "Main"]
    r = run_guarded(cmd, timeout=timeout)
    if r.timed_out:
        return "TIMEOUT", None
    m = re.search(r'Exception in thread "main" ([\w.$]+)', r.stderr)
    if m:
        return "ESCAPED", m.group(1)
    if r.returncode == 0:
        return "CLEAN", None
    # `Verifier.assume(false)` calls `Runtime.getRuntime().halt(1)`: a nonzero
    # exit with no exception text. An exception on a *spawned* thread also
    # leaves main's status at 0 and is handled above by reading stderr
    # regardless of exit code.
    other = re.search(r'Exception in thread "[^"]*" ([\w.$]+)', r.stderr)
    if other:
        return "OFF-THREAD", other.group(1)
    return "HALTED", None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="benchmarks/ajave")
    ap.add_argument("--trials", type=int, default=3,
                    help="how many of the fixed nondet sequences to try (max 5)")
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--only", default=None, help="substring filter on task name")
    ap.add_argument("--verbose", action="store_true",
                    help="print every comparison, not only divergences")
    a = ap.parse_args()

    if not os.path.exists(AJAVE):
        print(f"no binary at {AJAVE}; run `cargo build --release` first")
        return 2
    if shutil.which("javac") is None or shutil.which("java") is None:
        print("javac/java not on PATH; this harness compares against a real JVM")
        return 2

    root = a.dir if os.path.isabs(a.dir) else os.path.join(ROOT, a.dir)
    common = os.path.join(root, "common")
    if not os.path.isdir(common):
        print(f"no {common}/ -- expected a suite laid out like benchmarks/ajave")
        return 2
    tasks = load_tasks(root)
    if a.only:
        tasks = [t for t in tasks if a.only in t[0]]
    if not tasks:
        print(f"no tasks found under {root}")
        return 2

    seqs = sequences(max(1, min(a.trials, 5)))
    print(f"lifter differential: {len(tasks)} tasks x {len(seqs)} "
          f"nondet sequence(s) = {len(tasks) * len(seqs)} comparisons\n")

    work = tempfile.mkdtemp(prefix="ajave-lifterdiff-")
    try:
        shadow, err = build_shadow(work)
        if err:
            print(err)
            return 2

        buckets = Counter()
        divergences = []
        thread_mismatch = []
        compile_fail = []

        for name, src_dir in tasks:
            classes = os.path.join(work, "cls", name)
            os.makedirs(classes, exist_ok=True)
            srcs = glob.glob(os.path.join(src_dir, "*.java"))
            text = "".join(open(s).read() for s in srcs)
            threaded = bool(CONCURRENT.search(text))
            r = subprocess.run(
                ["javac", "-nowarn", "-cp", shadow, "-d", classes] + srcs,
                capture_output=True, text=True)
            if r.returncode != 0:
                compile_fail.append((name, r.stderr.strip()[:300]))
                continue

            for seq in seqs:
                ir, ir_detail = interpret(src_dir, common, seq, a.timeout)
                jvm, jvm_detail = run_jvm(classes, shadow, seq, a.timeout)
                label = f"{name} seq={seq if seq else 'all-zero'}"

                if ir == "INCONCLUSIVE":
                    buckets["inconclusive (interpreter does not model it)"] += 1
                    verdict = "skip"
                elif ir == "TIMEOUT" or jvm == "TIMEOUT":
                    buckets["timeout on one side"] += 1
                    verdict = "skip"
                elif ir == "NO-OUTPUT" or ir == "NO-ENTRY":
                    buckets[f"interpreter produced {ir}"] += 1
                    verdict = "skip"
                elif jvm == "OFF-THREAD":
                    # An exception killed a spawned thread; main exited 0. The
                    # sequential interpreter never ran that thread.
                    buckets["off-thread exception (concurrency)"] += 1
                    verdict = "skip"
                elif ir == "ESCAPED" and jvm == "ESCAPED":
                    if accepted(ir_detail, jvm_detail):
                        buckets["agree: same exception family"] += 1
                        verdict = "agree"
                    else:
                        verdict = "DIVERGE"
                elif ir == jvm:
                    buckets[f"agree: {ir.lower()}"] += 1
                    verdict = "agree"
                else:
                    verdict = "DIVERGE"

                if verdict == "DIVERGE":
                    detail = (f"interpreter={ir}"
                              + (f"({ir_detail})" if ir_detail else "")
                              + f" jvm={jvm}"
                              + (f"({jvm_detail})" if jvm_detail else ""))
                    if threaded:
                        buckets["threaded: not modelled sequentially"] += 1
                        thread_mismatch.append((label, detail))
                    else:
                        divergences.append((label, detail))
                if a.verbose:
                    print(f"  {verdict:9} {label}: ir={ir}{ir_detail or ''} "
                          f"jvm={jvm}{jvm_detail or ''}")
    finally:
        shutil.rmtree(work, ignore_errors=True)

    compared = sum(v for k, v in buckets.items() if k.startswith("agree")) \
        + len(divergences) + len(thread_mismatch)
    print(f"compared: {compared}")
    for k in sorted(buckets):
        print(f"  {buckets[k]:5}  {k}")
    if compile_fail:
        print(f"\n{len(compile_fail)} task(s) did not compile:")
        for name, why in compile_fail:
            print(f"  {name}: {why}")
    if thread_mismatch:
        print(f"\n{len(thread_mismatch)} mismatch(es) on threaded programs "
              f"(expected: the sequential interpreter does not run threads):")
        for label, detail in thread_mismatch:
            print(f"  {label}: {detail}")

    print(f"\ndivergences: {len(divergences)}")
    for label, detail in divergences:
        print(f"  {label}: {detail}")
    return 1 if divergences else 0


if __name__ == "__main__":
    sys.exit(main())
