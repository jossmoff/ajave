# Proposal: one test runner, one survey tool, and gates that find real bugs

**Status:** proposed
**Date:** 2026-09-06

## Summary

`tools/` holds 31 files and about 5,900 lines. Several do the same job with
different names, one is documented as superseded and still present, and two CI
jobs have been failing since the August rename without anyone noticing. This
proposes:

1. A `just` task runner as the single entry point.
2. One survey tool replacing nine census and profiling scripts, keeping the
   exploratory triage they exist for.
3. Three new gates — mutation testing, differential fuzzing against a real JVM,
   and a CI-enforced determinism check.

## The problem, measured

### Scripts that do the same thing

Six scripts iterate a task set and run the binary. Seven parse engine logs.
Nine of them exist only to answer "run the corpus, then bucket what failed by
some property":

| script | lines | groups failures by |
|---|---|---|
| `engine_census.py` | 209 | which engine could have helped |
| `blocker_census.py` | 173 | which discharge condition refused |
| `pairing_census.py` | 181 | which pair of engines could combine |
| `refutation_sweep.py` | 156 | which library method the refuted witness used |
| `open_obligations.py` | 162 | which obligation stayed open |
| `heap_survey.py` | 165 | which heap feature appeared |
| `blocking_calls.py` | 121 | which call tainted the run |
| `engine_profile.py` | 68 | where wall time went |
| `engine_audit.py` | 60 | which engines ran at all |

That is 1,295 lines whose differences are the **grouping key** and the
**projection**, not the mechanism. Each re-implements task loading, parallel
execution, log parsing, and result formatting, so a fix to any of those reaches
one of nine copies. Three of them acquired the same `ProcessPoolExecutor`
`__main__`-guard bug independently.

### Dead and superseded tooling

`CLAUDE.md` states that `tools/smoke_test.py` "was the old harness and is
superseded by `bench.py`". It is still present, 453 lines, and still mentioned
in three documents.

### CI has been red for weeks

`scripts/check-boundaries.sh` and `scripts/check-strategy-docs.sh` both read
`crates/roast-*`, a path that stopped existing at the 2026-08-25 rename. Both
exit 1 on every run. Two of five CI jobs have therefore been failing
continuously, which is also why nobody noticed that:

- the crate graph had drifted (a new `ajave-opt` crate, unregistered; the CLI
  gained a dependency on `ajave-models`), and
- 7 of 13 registered engines have no strategy doc, the exact rule
  `check-strategy-docs.sh` exists to enforce.

A check that cannot pass is a check nobody reads.

### The gates we have find bugs; the gaps are visible

Ranked by defects actually attributed to them in `changes.md`:

- `bench.py` — the scoring harness, and the thing every measurement rule in
  `CLAUDE.md` was written about.
- `validate_own_benchmarks.py` — establishes ground truth on a real JVM. The
  strongest oracle here, because it does not use an expected-verdict label.
- `metamorphic.py`, `engine_ablation.py` — the two that look *between*
  engines. Also label-free.
- `validate_jdk_allowlist.py` — runs JDK signatures on a real JVM with
  adversarial arguments.

What is missing is anything that asks **"would our tests notice if this were
wrong?"** Every gate above checks the *program under analysis*. None checks the
*test suite*. That gap is why `cargo test -p ajave-engines` could stop
compiling and pass unnoticed for days, and why a dead match arm in the interval
domain (#93) survived until a lint was run.

## Proposal

### 1. `just` as the entry point

A `justfile` at the root, with a `just --list` that is the honest index of what
can be run. Recipes wrap existing tools rather than replacing them, so nothing
changes semantics on day one.

Grouping follows how the work is actually done:

```
just check          # fmt, clippy, tests, boundaries, strategy docs — what CI runs
just smoke          # the mandatory pre-scoring gate
just score          # full VA + NRE, idle-gated
just survey <kind>  # exploratory triage, see below
just oracles        # the label-free differential checks
just mutants        # mutation testing
just fuzz           # differential fuzzing against a real JVM
```

`just check` must be exactly what CI runs, and CI must call `just check`. A
local check that differs from the remote one is how the two drift.

### 2. One survey tool

Replace the nine census scripts with `tools/survey.py`, built as
**collect once, project many**. One corpus pass writes a single JSON record per
(task, property) containing everything the scripts currently re-derive:
verdict, expected verdict, wall time, per-engine timings and discharge counts,
completeness flags, blocker reason, replay census, and the library calls the
sources mention.

Projections then become small and composable:

```
just survey engines      # which engine could have helped
just survey blockers     # which discharge condition refused
just survey pairs        # which engine pairs could combine
just survey refutations  # refuted witnesses, clustered by library method
just survey raw > out.json
```

**This is the exploratory-triage capability, and it gets stronger, not
weaker.** Today each script decides in advance what to keep and discards the
rest, so a question nobody anticipated needs a new script and another full
corpus run — the expensive part. Collecting the union once means an agent can
ask a new question against data already on disk. `just survey raw` dumps
everything for exactly that.

Estimated 1,295 lines to roughly 350, with one implementation of task loading,
parallelism and log parsing.

### 3. Retire what is superseded

Delete `tools/smoke_test.py` and update the three documents that reference it.
Fold `score_full.py`, `score_own.py`, `run_scored.sh` and `timeout_probe.py`
into `bench.py` flags; merge `validate_concurrency_benchmarks.py` into
`validate_own_benchmarks.py` behind a `--dir`.

### 4. New gate: mutation testing (`cargo-mutants`)

The highest-value addition, because of what this project is. A verifier's
tests are supposed to catch *soundness* regressions, and the only way to know
whether they would is to introduce one and see.

Start scoped, not repo-wide:

- `ajave-models::contract_of` — a wrong entry here is a wrong TRUE at −16, and
  `CLAUDE.md` already dedicates a section to how such entries accumulate.
- `ajave-core::blackboard` — direction discipline at publish is the invariant
  the whole architecture rests on.
- `ajave-engines::liveness` — new, and its safety argument ("an imprecise live
  set costs precision, not soundness") is exactly the kind of claim mutation
  testing can probe.

A surviving mutant in those modules is a missing test, and the report names it.
Run nightly rather than per-push; it is minutes, not seconds.

### 5. New gate: differential fuzzing against a real JVM

We already generate Java programs (`gen_own_benchmarks.py`) and already run
programs on a real JVM (`validate_own_benchmarks.py`, `certify::JvmReplay`).
Connecting them gives a label-free oracle that runs forever:

1. Generate a random well-typed Java program from a grammar over the constructs
   the IR models.
2. Run it on a real JVM to get ground truth.
3. Run ajave.
4. **A disagreement is a bug in ajave** — no expected verdict needed.

This directly targets the defect class that has dominated this project: a
divergence between our model of Java and Java. `Math.round`, the float
bit-pattern arithmetic, `String.concat(null)`, the two wrong `Character`
models — every one was a semantic divergence found by accident. A generator
biased toward the constructs whose models are asserted rather than proven
(`contract_of` entries, `Character` classification, radix formatting) would
have found them on purpose.

Second, cheaper target: `cargo-fuzz` on the classfile parser, which consumes
untrusted bytes and should never panic.

### 6. New gate: determinism in CI

`CLAUDE.md` documents that verdicts once depended on `HashMap` iteration order
and cost ±15–30 points of unexplained noise. The rule exists; nothing enforces
it. Add `just determinism`, running the smoke set twice and diffing verdicts,
to the nightly job. A flake is a defect, and this is the cheapest way to catch
the class.

## What this does not propose

- Rewriting `bench.py`. It carries hard-won measurement discipline — binary
  snapshotting, idle gating, per-task timing baselines — and its size is
  mostly that discipline. It gets a `just` front door, not a rewrite.
- Making mutation testing or fuzzing blocking on push. Both are nightly. A
  gate that makes an unrelated change red is a gate people learn to bypass.
- Deleting the census scripts before `survey.py` reproduces their output. The
  replacement lands first, the deletions follow in a separate commit.

## Sequencing

1. Fix the two broken CI scripts and get all five jobs green. *(done)*
2. Add the `justfile`; point CI at `just check`.
3. Build `tools/survey.py`; verify it reproduces each census output; delete the
   nine scripts.
4. Retire `smoke_test.py` and fold the scoring variants into `bench.py`.
5. Add `cargo-mutants` on three modules, nightly.
6. Add the determinism check, nightly.
7. Build the differential fuzzer. Largest item, highest ceiling, and the one
   worth doing slowly.
