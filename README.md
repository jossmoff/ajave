# ajave 🌵

**A**nother **JA**va **VE**rifier — an SV-COMP Java verifier, written in Rust.

Point it at a Java program and it answers one question: can `assert` ever fail,
or can a runtime exception ever escape uncaught? It answers `TRUE`, `FALSE`, or
— when it genuinely doesn't know — `UNKNOWN`.

Every `FALSE` is replayed on a real JVM before it is reported, and a violation
that does not reproduce is downgraded to `UNKNOWN`. `TRUE` has no equivalent
independent check; see [`docs/architecture.md`](docs/architecture.md) for what
that asymmetry does and does not guarantee.

## Requirements

| Requirement | Why |
|---|---|
| Rust 1.98.1 | Pinned in `rust-toolchain.toml` |
| JDK 21 on `PATH` | ajave compiles `.java` sources itself and replays witnesses |
| **Z3 on `PATH`** | Most engines shell out to it |
| [`just`](https://github.com/casey/just) | Task runner (optional, but every workflow uses it) |

Without Z3 the solver-backed engines return `UNKNOWN` and ajave looks broken
rather than saying so. That exact omission kept CI red for weeks, so it is
worth checking first:

```sh
z3 --version && java -version
```

## Building

```sh
just build          # or: cargo build --release
```

## Running

```sh
./target/release/ajave <path>... [--property valid-assert] [--ir] [--trace]
```

Every path is scanned for `.java` and `.class` files, matching how BenchExec
invokes the tool against an SV-COMP task's `input_files` — usually a shared
`common/` directory plus the task's own:

```sh
./target/release/ajave benchmarks/sv-comp/common benchmarks/sv-comp/jbmc-regression/assert2
```

`--ir` prints the lifted intermediate representation, `--trace` the
orchestrator's schedule and every obligation's final status, and
`--show-witness` the nondeterministic values behind a `FALSE`.

Two recipes wrap the common cases:

```sh
just explain <task>   # which engines did what
just witness <task>   # the witness, and how JVM replay judged it
```

## Common tasks

`just --list` is the full index. The ones that matter day to day:

```sh
just check      # everything CI runs: fmt, clippy, test, boundaries, docs
just smoke      # the mandatory gate before any scoring run
just score-all  # full corpus, both properties, idle-gated (~90 min)
just survey     # exploratory triage: run the corpus, then ask it questions
just oracles    # the label-free differential checks
```

CI runs the same `just` recipes, so a local pass and a remote pass cannot
diverge.

## Repository layout

Seven crates under `crates/`, each with an enforced set of things it may depend
on — checked by `just boundaries`, not merely documented. See
[`docs/crates.md`](docs/crates.md).

```
crates/
  ajave-ir/        program representation -- zero dependencies
  ajave-models/    what ajave assumes java.* library calls do
  ajave-frontend/  classfile parsing + bytecode lifter
  ajave-opt/       IR reduction: what the portfolio sees, minus the noise
  ajave-core/      blackboard, CPA substrate, engine/certifier traits
  ajave-engines/   the 13 verification strategies
  ajave-cli/       the `ajave` binary: wires everything together
```

## Status

Thirteen engines, from a trivial constant-folder to abstract interpretation,
bounded model checking, concolic execution, k-induction, CHC and CEGAR. They
cooperate through a blackboard rather than a fixed pipeline, and what each may
conclude is enforced at publish time.

Measured 2026-09-06 over 1,784 property-task pairs, 300s per task:

| property | score | correct | wrong |
|---|---|---|---|
| valid-assert | 862 | 724 / 1013 | 1 |
| no-runtime-exception | 1118 | 567 / 771 | 0 |

Against SV-COMP 2026's published results, ajave solves **27 of the 68 tasks
that no competing verifier solved**, with zero wrong answers on those.

Two caveats, because the number invites a comparison it cannot yet support.
Our raw score sum is **not** the same statistic as SV-COMP's published
*Overall* column: recomputing a raw sum from the competition's own result XML
gives JBMC 1728 against a published 1561, so the formulas differ. And we use
our own JVM replay rather than an external witness validator. Both are
prerequisites for any competitive claim — see
[`docs/assessment-2026-08-31.md`](docs/assessment-2026-08-31.md).

## Documentation

- [`docs/architecture.md`](docs/architecture.md) — the pipeline, the obligation
  lifecycle, the blackboard, the CPA substrate. Read this first.
- [`docs/README.md`](docs/README.md) — the engine registry and how to add a
  strategy.
- [`docs/crates.md`](docs/crates.md) — the isolation boundaries and why they
  are drawn where they are.
- [`docs/strategies/`](docs/strategies/) — one file per technique: what it
  proves, what it assumes, where it is incomplete, how it is certified.
- [`docs/glossary.md`](docs/glossary.md) — definitions for every concept in the
  design, from SV-COMP scoring to JVM bytecode internals.
- [`docs/proposals/`](docs/proposals/) — design proposals, including the
  quality-gate plan behind the `just` recipes above.
- [`changes.md`](changes.md) — a dated record of every notable technique and
  what measuring it actually showed.
