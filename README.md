# roast 🔥

An SV-COMP Java verifier, written in Rust. Point it at a Java program and it
answers one question: can `assert` ever fail, or can a runtime exception ever
escape uncaught? It answers `TRUE`, `FALSE`, or — when it genuinely doesn't
know — `UNKNOWN`, and it never guesses.

The name is the mental model for the engine portfolio: verification runs from
a fast, cheap sweep through to slower, deeper proof — light roast to dark
roast. See [`docs/architecture.md`](docs/architecture.md) §6 for the actual
tiers.

## Building

```sh
cargo build --workspace --release
```

Requires a JDK on `PATH` (`javac`/`java`) — `roast` compiles `.java` task
sources itself and replays every `FALSE` result on a real JVM before
reporting it. See [`docs/architecture.md`](docs/architecture.md) for why
that's not optional.

## Running

```sh
./target/release/roast <path>... [--ir] [--trace]
```

Every path given is scanned for `.java` and `.class` files, matching how
BenchExec invokes the tool against an SV-COMP task's `input_files` list —
usually a shared `common/` directory plus the task's own directory:

```sh
./target/release/roast tasks/common tasks/stage01_nondet
```

`--ir` prints the lifted intermediate representation; `--trace` prints the
orchestrator's schedule and every obligation's final status.

## Repository layout

Six crates under `crates/`, each with a specific job and an enforced set of
things it's allowed to depend on — see [`docs/crates.md`](docs/crates.md).

```
crates/
  roast-ir/        program representation -- zero dependencies
  roast-models/    what roast assumes java.* library calls do
  roast-frontend/  classfile parsing + bytecode lifter
  roast-core/      blackboard, CPA substrate, engine/certifier traits
  roast-engines/   concrete strategies (interval AI, concolic falsifier, ...)
  roast-cli/       the `roast` binary: wires everything together
```

## Documentation

- [`docs/architecture.md`](docs/architecture.md) — the pipeline, the
  obligation lifecycle, the blackboard design, the CPA substrate.
- [`docs/crates.md`](docs/crates.md) — the isolation boundaries and why they're
  drawn where they are.
- [`docs/strategies/`](docs/strategies/) — one file per verification
  technique: what it proves, what it assumes, where it's incomplete, how it's
  certified.
- [`docs/glossary.md`](docs/glossary.md) — ELI5 + real definitions for every
  concept in the design, from SV-COMP scoring to JVM bytecode internals.

## Status

Working, not competitive yet. Two engines (an interval abstract
interpreter and a bounded concolic falsifier) against a real frontend
(full opcode coverage, exception tables, arrays, objects). Verified against
the `jbmc-regression` corpus: zero incorrect verdicts, everything else either
correct or an honest `UNKNOWN`. See [`docs/strategies/README.md`](docs/strategies/README.md)
for what's implemented versus planned.
