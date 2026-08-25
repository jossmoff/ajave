# Strategies

Every entry in the engine portfolio (`ajave-engines/src/*.rs`), one file each.
Coverage enforced by `scripts/check-strategy-docs.sh` (CI job
`strategy-docs`) — a module here with no matching doc fails the build.

| Strategy | Direction | Tier | Status | Doc |
|---|---|---|---|---|
| Presolve | Over | 0 | working | [presolve.md](presolve.md) |
| Interval domain | Over | 1 | working | [interval.md](interval.md) |
| — engine wrapper | Over | 1 | working | [ai.md](ai.md) |
| Concrete falsifier | Under | 2 | working | [concrete.md](concrete.md) |

Planned but not yet implemented (tracked in `docs/architecture.md` §6, not
here — they get a file in this directory the day an `Engine`/`Cpa` impl for
them lands, per the workflow in `docs/README.md`):

| Strategy | Direction | Tier | Combination |
|---|---|---|---|
| BMC + SMT | Under | 2/3 | — |
| k-induction | Over | 3 | invariant injection (A), consumes interval's invariants |
| Predicate CEGAR | Over | 4 | trace-guided refinement (B), consumes concrete's traces |
| CHC encoding | Over | 5 | escape hatch (D) |
