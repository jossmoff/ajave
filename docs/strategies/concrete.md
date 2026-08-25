# concrete

**Direction:** Under
**Tier:** 2
**Status:** working
**Source:** `ajave-engines/src/concrete.rs`

## What it proves or finds

Bounded concrete execution over a small candidate set (`{0, 1, -1, 2, -2,
i32::MAX, i32::MIN}`, plus `i64` equivalents) for every `Verifier.nondet*`
call, run for real against the lifted IR — not solved for, enumerated. On a
`Check` failure with nothing able to catch it, publishes `Status::Violated`
with the exact value sequence used, which doubles as the witness.

Exceptional control flow is routed properly, not just detected: a `Check`
failure inside a `try` region looks up the enclosing block's exceptional
edges (computed by the frontend, `ajave_frontend::lift`) and transfers
execution to the matching handler rather than reporting a violation directly.
This is what makes `ArithmeticException1` (division-by-zero caught, `assert
false` inside the handler) come out correctly — get this wrong and every
caught-exception task is either a missed bug or, worse, a wrong verdict.

## What it assumes / where it's unsound if the assumption breaks

Under-approximating by construction, so "unsound" isn't really the axis that
applies — a bug this engine reports is real (assuming the interpreter itself
is correct, which is exactly what `JvmReplay` independently confirms). The
axis that matters is **completeness**, not soundness:

- Reference-typed nondet values are always treated as non-null. Misses the
  null-valued branch of any nondet reference entirely — an allowed
  incompleteness for an `Under` engine, not a correctness bug.
- No heap model: field and array writes are dropped (`Stmt::PutField` /
  `Stmt::ArrayStore` are no-ops), and reads (`Rvalue::GetField` /
  `Rvalue::ArrayLoad` / `Rvalue::ArrayLength`) always evaluate to `Unknown`.
  The straightforward consequence is the one you'd expect: any bug that
  depends on a written-then-read value is invisible to this engine.

  The less obvious consequence, found by testing against a real example
  rather than assumed: `Unknown` reaching a **branch** condition has to
  resolve to *some* path to keep the interpreter running, and it resolves to
  the `else` edge (`Value::Unknown.nonzero() == false`). That's a reasonable
  default for *exploring fewer paths* -- but it means any control flow gated
  on an array or field value gets silently steered down whichever branch
  happens to be coded second, independent of what the real value would have
  done. That's not "misses the bug", it's "reaches a specific wrong branch
  deterministically", and it used to be able to manufacture a `Violated`
  report out of it. Two fixes came out of tracking this down:
  - `eval_bin` now propagates `Unknown` through comparisons and arithmetic
    instead of letting `Value::Unknown.as_i64() == 0` leak in as if it were a
    real value (this is what caused a bounds check against an untracked
    `ArrayLength` to read as `idx < 0` -- always false, even for `idx == 0`
    during an array literal's own construction).
  - The `Stmt::Check` site now distinguishes "concretely false" from
    "genuinely unknown" and only the former may produce `Violated`. An
    `Unknown` condition at a check is skipped, not resolved either way.

  Branches into heap-dependent territory can still land on the wrong path
  as a result of the `Unknown -> else` default -- that part is unchanged and
  is a real, open precision gap, tracked here rather than glossed over. What
  changed is that landing on the wrong path can no longer manufacture a
  false `Violated` on its own; it can only make the engine miss a real bug
  by exploring the wrong branch, which is the ordinary, acceptable kind of
  Under-approximation incompleteness. Fixing this properly means real heap
  modelling (concrete arrays and objects, at least for the paths actually
  explored), not patching around `Unknown`'s propagation further.
- `count_nondet_slots` under-counts when the all-zero probe run doesn't hit a
  violation — it falls back to a fixed guess of 3 slots. Under-counting only
  means fewer combinations get tried.

## Known incompleteness

The candidate set is small and fixed. `assert2` in the corpus
(`if (i >= 1000) assert i > 1000`) needs the *exact* value `1000` to trigger,
which isn't in the candidate pool — this engine correctly reports `UNKNOWN`
on it rather than finding the bug. Real BMC (Tier 2/3 proper, solver-backed)
is the fix; this engine is deliberately "enumerate, don't solve" and is
explicit about that trade in its own module doc.

## How it's certified

Every `Violated` status this engine publishes is fed to
`core::certify::JvmReplay` before being reported: a deterministic shadow
`Verifier` (same package, same signatures, pops values from the recorded
sequence instead of calling `Random`) is compiled and run against the actual
task classpath. Only `CertResult::Confirmed` results survive to the final
verdict — an unconfirmed `FALSE` is downgraded to `UNKNOWN` in
`ajave-cli/src/main.rs` rather than reported. This is the one strategy in the
portfolio whose output is fully independently checked end to end.
