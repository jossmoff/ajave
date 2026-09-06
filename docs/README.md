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
- [`sdlc.md`](sdlc.md) — how work moves from issue to merged change.
- [`milestones-and-issues.md`](milestones-and-issues.md) — the planned
  sequence of work and how issues are labelled.
- [`assessment-2026-08-31.md`](assessment-2026-08-31.md) — a point-in-time
  competitive assessment. Dated on purpose: its scores are a snapshot, not
  the current numbers. For those, run `tools/bench.py`.
- [`strategies/`](strategies/) — one file per verification strategy
  (`ajave-engines/src/*.rs`) and per abstract domain (`ajave-core::cpa` impls).
  **Every strategy that lands in the engine portfolio gets a file here before
  it's registered in `ajave-cli`, not after.** A strategy without a doc is
  effectively unreviewable: nobody else can tell what it's entitled to
  conclude from reading the code alone, and that's exactly the kind of gap
  that produced the `stop_sep` soundness bug during development (see
  `strategies/interval.md`).


## The engine portfolio

The registration order in `ajave-cli/src/main.rs` is the source of truth; this
table mirrors it. `Direction` is what the blackboard lets an engine conclude —
`Over` may discharge an obligation, `Under` may report a violation. See
[`architecture.md` §3.1](architecture.md).

| Engine | Direction | Strategy doc | Notes |
|---|---|---|---|
| `presolve` | Over | [presolve.md](strategies/presolve.md) | Constant-condition discharge |
| `concurrency` | Under | [concurrency.md](strategies/concurrency.md) | DPOR over thread interleavings |
| `concrete` | Under | [concrete.md](strategies/concrete.md) | One all-zero probe |
| `concolic` | Under | [concolic.md](strategies/concolic.md) | Concrete run, then flip a branch and solve |
| `nra` | Under | — | Transcendental math through cvc5; falsification only |
| `float_search` | Under | — | Guided search over float inputs |
| `ai` | Over | [ai.md](strategies/ai.md) | Abstract interpretation on the CPA substrate |
| `ranges` | Over | — | Answers `Bounds` queries from Javadoc ranges; off unless `AJAVE_ASK=1` |
| `smt_bmc` | Under | [smt_bmc.md](strategies/smt_bmc.md) | Runs twice: bitvector pass, then FPA |
| `kinduction` | Over | — | Base and step case over a single loop |
| `chc` | Over | — | Horn clauses through Z3's Spacer |
| `imc` | Over | — | Interpolation-based model checking |
| `cegar` | Over | — | Predicate abstraction with refinement |

**7 of the 13 engines have no strategy doc.** That breaks the rule below, which asks
for the doc before registration. Treat the gap as a known debt rather than a
precedent: an engine whose entitlement is only visible in its source is one
nobody else can review.

Shared analyses are not engines and have no strategy doc:
`liveness.rs` (which variables a block needs on entry, used to bound CHC
predicate arity), `smt_encode.rs`, `smt_text.rs`, `body_analysis.rs`.

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
