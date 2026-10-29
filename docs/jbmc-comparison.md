# ajave against JBMC on the quantified-array-invariant shape

Measured 2026-10-29. JBMC 6.11.0 (cbmc-6.11.0), installed via Homebrew. JBMC is
the Java frontend of the CBMC family and has won SV-COMP's Java category, so it
is the strongest opponent available locally.

## Result

| benchmark | ajave | JBMC |
|---|---|---|
| **`heap/EveryElementNonNullAfterAFillLoop`** | **TRUE** | **cannot conclude** |
| `heap/ArrayElementNonNullWithAConstantBound` | TRUE | SUCCESSFUL |
| `heap/ArrayElementWrittenThenRead` | TRUE | SUCCESSFUL |
| `heap/TwoObjectsDistinctFieldValues` | TRUE | SUCCESSFUL |
| `engine-chc/FieldWrittenInACalleeIsVisibleToTheCaller` | TRUE | SUCCESSFUL |

**JBMC solves four of the five.** The gap is one program and it is a precise
one.

## The one ajave proves and JBMC does not

```java
int n = Verifier.nondetInt();
if (n < 1 || n > 1000) { return; }
A[] a = new A[n];
for (int i = 0; i < n; i++) { a[i] = new A(); }
for (int i = 0; i < n; i++) { assert a[i] != null; }
```

Proving the second loop needs `∀j. 0 ≤ j < i → a[j] ≠ null`, synthesised from
the first loop and consumed in the second.

- **ajave**: TRUE. With `AJAVE_CHC_QGEN=0` it is UNKNOWN, so the proof is
  specifically Spacer's quantified generalisation.
- **JBMC unbounded**: diverges. Observed past **7,252** unwindings of loop 0
  before being killed; the guard permits a thousand iterations and nothing
  bounds the unwinding.
- **JBMC `--unwind 20`** (with and without `--unwinding-assertions`): the only
  failing property is
  `[java::Main.main…unwind.0] line 45 unwinding assertion loop 0: FAILURE`.

That last point is the important one. **JBMC does not report a violation of the
assertion.** It reports that its unwind bound was insufficient — it declines,
correctly, and never produces a false answer. This is not a JBMC defect; it is
the architectural limit of bounded model checking against a nondeterministic
loop bound. No bound short of the guard's maximum suffices, and a bound is not
a proof.

## Method, and why the controls matter

Both controls were run **before** the benchmark, and the first one caught a
usage error (`--assertions` does not exist; assertions are on by default) that
would otherwise have been misread as a JBMC limitation:

| control | expected | observed |
|---|---|---|
| `int x = 1; assert x == 1;` | SUCCESSFUL | SUCCESSFUL |
| `int x = 1; assert x == 2;` | FAILED | FAILED |

The positive control proves the apparatus can observe a success, so a later
failure is informative. The negative control proves it reports violations, so a
later success is not vacuous. Verdicts were read from the named failing
property, not from the exit code — `VERIFICATION FAILED` on an unwinding
assertion and on a real assertion mean opposite things.

## What this does and does not establish

**Does**: on one shape — a quantified invariant over an array, from a loop with
a nondeterministic bound — ajave proves what JBMC cannot, and the capability
traces to a specific mechanism that can be ablated.

**Does not**: anything about relative overall strength. This is one benchmark,
written here, selected because ajave solves it. It is a capability
demonstration, not a competitive evaluation. The four JBMC successes are the
part that makes the fifth credible: the claim is narrow and the tool is not
being strawmanned.

Two further caveats:

- ajave's TRUE is **not independently certified**. It rests on Spacer answering
  `sat`; `AJAVE_CERTIFY_TRUE` is off by default. The ground truth is sound — the
  benchmark is JVM-validated and argued from the JLS — so the *answer* is right,
  but the *proof* is not double-checked.
- SV-COMP runs JBMC with its own configuration and an incremental unwinding
  strategy. That would hit the same wall, since the limit is the nondeterministic
  bound rather than the chosen `--unwind` value, but this comparison is not the
  competition configuration.

The fair version of this experiment is both tools over a corpus neither authored
— issue #97.
