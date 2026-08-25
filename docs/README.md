# ajave documentation

- [`architecture.md`](architecture.md) — the tool pipeline, the obligation
  lifecycle, the blackboard/orchestrator design, and the CPA substrate. Read
  this first; everything else assumes it.
- [`crates.md`](crates.md) — what each crate owns, what it's allowed to
  depend on, and why. Enforced by `scripts/check-boundaries.sh` in CI, not
  just written down.
- [`glossary.md`](glossary.md) — ELI5 + real definition for every concept
  used across the design (SV-COMP scoring, soundness/completeness,
  k-induction, CEGAR, the CPA operators, JVM bytecode internals — five parts,
  ~70 entries). The reference for onboarding anyone, including future-you,
  who wasn't in the room when a term got introduced.
- [`strategies/`](strategies/) — one file per verification strategy
  (`ajave-engines/src/*.rs`) and per abstract domain (`ajave-core::cpa` impls).
  **Every strategy that lands in the engine portfolio gets a file here before
  it's registered in `ajave-cli`, not after.** A strategy without a doc is
  effectively unreviewable: nobody else can tell what it's entitled to
  conclude from reading the code alone, and that's exactly the kind of gap
  that produced the `stop_sep` soundness bug during development (see
  `strategies/interval.md`).

## Adding a new strategy

1. Write `docs/strategies/<name>.md` using the template below *before*
   writing the engine. Forces the direction (over/under-approximating) and
   the soundness argument to exist before the code does, rather than being
   reconstructed afterwards.
2. Implement `ajave_core::engine::Engine` or `ajave_core::cpa::Cpa` in
   `ajave-engines/src/<name>.rs`.
3. Register it in `ajave-cli/src/main.rs`'s engine list.
4. Add it to the table in this file and in `architecture.md` §6 if it
   introduces a new tier or a new combination.

### Template

```markdown
# <name>

**Direction:** Over | Under | Exact
**Tier:** (see architecture.md §6)
**Status:** stub | working | tuned

## What it proves or finds
## What it assumes / where it's unsound if the assumption breaks
## Known incompleteness (things it will correctly say UNKNOWN about)
## How it's certified (which `Certifier` checks its output, if any)
```
