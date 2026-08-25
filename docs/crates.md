# Crates

Six crates, dependency edges enforced by `scripts/check-boundaries.sh` (CI job
`boundaries`). If this table and `Cargo.toml` ever disagree, the check fails
the build — treat that as the source of truth, not this file.

```
ajave-ir  <---- ajave-models
  ^  ^              ^
  |  |              |
  |  +-- ajave-frontend
  |  |
  +--+-- ajave-core <---- ajave-engines
              ^               ^
              |               |
              +----- ajave-cli
```

| Crate | Owns | Depends on | Does NOT depend on |
|---|---|---|---|
| `ajave-ir` | `Program`, `Body`, `Obligation`, the CFG types, `Verdict` | *(nothing)* | everything else — this is the floor the whole workspace sits on |
| `ajave-models` | What ajave assumes `java.*` calls do, without analysing their bytecode | `ajave-ir` | `ajave-core`, `ajave-frontend` |
| `ajave-frontend` | Classfile parsing, the bytecode lifter | `ajave-ir`, `ajave-models` | `ajave-core` |
| `ajave-core` | Blackboard, CPA substrate, `Engine`/`Certifier` traits, orchestrator | `ajave-ir`, `ajave-models` | `ajave-frontend` |
| `ajave-engines` | Concrete strategies (interval AI, concolic falsifier, presolve) | `ajave-ir`, `ajave-models`, `ajave-core` | `ajave-frontend` |
| `ajave` (bin) | CLI driver: compile, lift, run the portfolio, certify, report | all of the above | — |

## Why the graph is shaped like this

**`ajave-ir` has zero dependencies.** Every other crate depends on it, never
the reverse. This isn't just tidiness: it's what makes "the representation is
independent of both what produces it and what consumes it" a checkable fact
rather than an aspiration. It slipped once during the workspace split —
`Body::check_point` briefly returned a `ajave-core` type, which would have
forced `ajave-ir` to depend on `ajave-core` and broken the whole graph — and
`check-boundaries.sh` exists specifically because that kind of thing should
fail CI, not get caught in review.

**`ajave-frontend` and `ajave-core` don't depend on each other.** Both only need
`ajave-ir` and `ajave-models`. This is the load-bearing isolation claim in the
whole design: swapping the frontend for a different bytecode format (or
adding a second one) should never require touching the verification core, and
vice versa. If a future change makes one depend on the other, that's a sign
the obligation-based interface between them (defined entirely in `ajave-ir`)
wasn't expressive enough, not a reason to just add the edge.

**`ajave-engines` depends on `ajave-core` but not `ajave-frontend`.** An engine
analyses `ajave_ir::Program` — it has no business knowing bytecode was ever
involved in producing it. This is what makes `ajave-engines` reusable as-is if
`ajave-frontend` ever gets a sibling.

**`ajave-models` sits underneath both `ajave-frontend` and `ajave-core`.**
`exception_class` (which obligation kind maps to which Java exception) is
needed by the lifter's exceptional-edge construction *and* by the concrete
engine's handler routing *and* by `JvmReplay`'s certification. Duplicating
that table in two or three places would be the kind of drift this whole
structure exists to prevent, so it's a fourth, minimal crate instead of being
folded into either `ajave-frontend` or `ajave-core`.

## Adding a crate

New isolation boundary needed? Add the directory under `crates/`, add it to
the `members` list in the workspace `Cargo.toml`, and add its row to both the
table above and the `ALLOWED` map in `scripts/check-boundaries.sh` in the same
PR. The script will fail loudly if you forget the second part.
