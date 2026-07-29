# Contributing

## Before you touch code

Read [`docs/architecture.md`](docs/architecture.md) and
[`docs/crates.md`](docs/crates.md). The crate boundaries are enforced
(`scripts/check-boundaries.sh`, CI job `boundaries`), not just documented —
a PR that adds a dependency edge the docs don't describe will fail CI, not
just review.

## Adding a verification strategy

Every technique in `crates/roast-engines/src/` needs a doc in
`docs/strategies/` before it's registered — enforced by
`scripts/check-strategy-docs.sh` (CI job `strategy-docs`). See
[`docs/README.md`](docs/README.md) for the template and workflow.

## Local checks

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
./scripts/check-boundaries.sh
./scripts/check-strategy-docs.sh
```

All five run in CI (`.github/workflows/ci.yml`); running them locally first
is faster than waiting for the round trip.

## Soundness

If a change touches `roast-core` (the blackboard, the CPA substrate) or any
`Engine`/`Cpa` implementation, state explicitly in the PR description which
direction it approximates in (`Over`/`Under`/`Exact`) and why the change
preserves that. Two real soundness bugs were found during development by
measuring against the `jbmc-regression` corpus rather than trusting hand-picked
test cases — see `docs/strategies/interval.md`'s postmortem section for the
most serious one. Prefer adding a regression test that would have caught it
over a comment explaining why it won't happen again.
