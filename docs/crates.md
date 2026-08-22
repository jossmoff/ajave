# Crates

Six crates, dependency edges enforced by `scripts/check-boundaries.sh` (CI job
`boundaries`). If this table and `Cargo.toml` ever disagree, the check fails
the build — treat that as the source of truth, not this file.

```
roast-ir  <---- roast-models
  ^  ^              ^
  |  |              |
  |  +-- roast-frontend
  |  |
  +--+-- roast-core <---- roast-engines
              ^               ^
              |               |
              +----- roast-cli
```

| Crate | Owns | Depends on | Does NOT depend on |
|---|---|---|---|
| `roast-ir` | `Program`, `Body`, `Obligation`, the CFG types, `Verdict` | *(nothing)* | everything else — this is the floor the whole workspace sits on |
| `roast-models` | What roast assumes `java.*` calls do, without analysing their bytecode | `roast-ir` | `roast-core`, `roast-frontend` |
| `roast-frontend` | Classfile parsing, the bytecode lifter | `roast-ir`, `roast-models` | `roast-core` |
| `roast-core` | Blackboard, CPA substrate, `Engine`/`Certifier` traits, orchestrator | `roast-ir`, `roast-models` | `roast-frontend` |
| `roast-engines` | Concrete strategies (interval AI, concolic falsifier, presolve) | `roast-ir`, `roast-models`, `roast-core` | `roast-frontend` |
| `roast` (bin) | CLI driver: compile, lift, run the portfolio, certify, report | all of the above | — |

## Why the graph is shaped like this

**`roast-ir` has zero dependencies.** Every other crate depends on it, never
the reverse. This isn't just tidiness: it's what makes "the representation is
independent of both what produces it and what consumes it" a checkable fact
rather than an aspiration.

It slipped once, during the original single-crate → workspace split: a
`Body::check_point` helper returned a `ProgramPoint`, which is a `roast-core`
type, and would have forced `roast-ir` to depend on `roast-core` and inverted
the whole graph. It was moved to the core side of the boundary, and
`check-boundaries.sh` was written so that the next one fails CI instead of
being caught in review. (The helper itself no longer exists — it never
acquired a caller and was removed. The rule it motivated is the part worth
keeping.)

**`roast-frontend` and `roast-core` don't depend on each other.** Both only need
`roast-ir` and `roast-models`. This is the load-bearing isolation claim in the
whole design: swapping the frontend for a different bytecode format (or
adding a second one) should never require touching the verification core, and
vice versa. If a future change makes one depend on the other, that's a sign
the obligation-based interface between them (defined entirely in `roast-ir`)
wasn't expressive enough, not a reason to just add the edge.

**`roast-engines` depends on `roast-core` but not `roast-frontend`.** An engine
analyses `roast_ir::Program` — it has no business knowing bytecode was ever
involved in producing it. This is what makes `roast-engines` reusable as-is if
`roast-frontend` ever gets a sibling.

**`roast-models` sits underneath both `roast-frontend` and `roast-core`.**
`exception_class` (which obligation kind maps to which Java exception) is
needed by the lifter's exceptional-edge construction *and* by the concrete
engine's handler routing *and* by `JvmReplay`'s certification. Duplicating
that table in two or three places would be the kind of drift this whole
structure exists to prevent, so it's a fourth, minimal crate instead of being
folded into either `roast-frontend` or `roast-core`.

## Adding a crate

New isolation boundary needed? Add the directory under `crates/`, add it to
the `members` list in the workspace `Cargo.toml`, and add its row to both the
table above and the `ALLOWED` map in `scripts/check-boundaries.sh` in the same
PR. The script will fail loudly if you forget the second part.
