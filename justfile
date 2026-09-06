# ajave task runner.
#
# `just --list` is the index of what can be run. Recipes wrap the tools in
# `tools/` rather than replacing them, so behaviour is unchanged.
#
# See docs/proposals/quality-gates.md for why this exists.

set shell := ["bash", "-uc"]

BIN := "./target/release/ajave"
COMMON := "benchmarks/sv-comp/common"

# Show the available recipes.
default:
    @just --list

# ---------------------------------------------------------------------------
# What CI runs. Keep this identical to .github/workflows/build.yml.
# ---------------------------------------------------------------------------

# Everything CI checks, in the order it fails fastest.
check: fmt-check clippy test boundaries strategy-docs

# Fail if anything is unformatted.
fmt-check:
    cargo fmt --all -- --check

# Reformat in place.
fmt:
    cargo fmt --all

# Lint. CI treats warnings as errors, so this does too.
clippy:
    cargo clippy --workspace --all-targets -- -D warnings

# Unit and integration tests across the workspace. Excludes the corpus test,
# which is `#[ignore]`d because debug-mode engines cannot finish it in CI.
test:
    cargo test --workspace

# The corpus regression test: every task's verdict against its declared ground
# truth. Release, because debug is roughly an order of magnitude too slow.
test-corpus:
    cargo test --release --test corpus -- --ignored --nocapture

# Assert the crate dependency graph matches docs/architecture.md.
boundaries:
    bash scripts/check-boundaries.sh

# Assert every registered engine has a strategy doc, or a recorded gap.
strategy-docs:
    bash scripts/check-strategy-docs.sh

# Release build. Everything below assumes this has run.
build:
    cargo build --release

# ---------------------------------------------------------------------------
# Scoring. CLAUDE.md's measurement rules apply to every recipe here.
# ---------------------------------------------------------------------------

# The mandatory gate before any scoring run. Exit 1 means a regression.
smoke: build
    python3 tools/bench.py --set smoke --check

# Score one property over the full corpus. Refuses to start on a busy machine.
score property="valid-assert": build
    python3 tools/bench.py --set sv-comp --property {{property}} --require-idle

# Score both properties. This is the number to quote, and it takes ~90 minutes.
score-all: build
    ./tools/cleanup.sh
    python3 tools/bench.py --set sv-comp --property valid-assert --require-idle
    python3 tools/bench.py --set sv-comp --property no-runtime-exception --require-idle

# Read CLAUDE.md first: this bakes in whatever is currently true, including
# regressions you have not explained.
# Re-record the smoke baseline.
baseline:
    python3 tools/bench.py --set smoke --update-baseline

# Run this before anything you intend to compare.
# Kill leaked solvers, JVMs and stale scratch directories.
clean-strays:
    ./tools/cleanup.sh

# ---------------------------------------------------------------------------
# Exploratory triage. Run the corpus, then ask questions of what came back.
# ---------------------------------------------------------------------------

# Records verdict, timings, per-engine discharge counts, completeness flags,
# blocker reason, replay census and library calls, into survey.json.
# Collect one triage record per (task, property).
survey-collect set="sv-comp" property="valid-assert": build
    python3 tools/survey.py collect --set {{set}} --property {{property}} --out survey.json

# KIND: engines | blockers | pairs | refutations | obligations | calls |
# timings | raw
# Project a collected survey.
survey kind="engines":
    python3 tools/survey.py report --in survey.json --kind {{kind}}

# Collect and report in one step.
survey-now kind="engines" set="smoke": build
    python3 tools/survey.py collect --set {{set}} --out survey.json
    python3 tools/survey.py report --in survey.json --kind {{kind}}

# ---------------------------------------------------------------------------
# Label-free oracles. None of these use an expected verdict, so they hold on
# programs no benchmark covers.
# ---------------------------------------------------------------------------

# Run every label-free differential oracle.
oracles: metamorphic ablation contracts own-benchmarks

# Meaning-preserving edits must not change a verdict.
metamorphic set="smoke": build
    python3 tools/metamorphic.py --set {{set}}

# Removing an engine may lose an answer; it must never flip TRUE and FALSE.
ablation set="smoke": build
    python3 tools/engine_ablation.py --set {{set}}

# Perturbing one library contract to OPAQUE may only weaken a verdict.
contracts: build
    python3 tools/contract_monotonicity.py

# Check ajave's own benchmarks against a real JVM.
own-benchmarks dir="benchmarks/ajave":
    python3 tools/validate_own_benchmarks.py --dir {{dir}}

# The one gate here that generalises beyond our corpus.
# Check the JDK allowlist on a real JVM with adversarial arguments.
jdk-allowlist:
    python3 tools/validate_jdk_allowlist.py

# ---------------------------------------------------------------------------
# Deeper gates. Nightly, not per-push.
# ---------------------------------------------------------------------------

# A surviving mutant is a missing test. Needs: cargo install cargo-mutants
# Mutation testing where a wrong answer is most expensive.
mutants:
    cargo mutants --package ajave-models --file '**/lib.rs' --timeout 120
    cargo mutants --package ajave-core --file '**/blackboard.rs' --timeout 120
    cargo mutants --package ajave-engines --file '**/liveness.rs' --timeout 120

# Verdicts must not depend on hash iteration order or leftover state; a flake
# here is a defect, not noise.
# Run the smoke set twice and diff the verdicts.
determinism: build
    python3 tools/bench.py --set smoke --repeat 2

# Generates a program, runs it on a real JVM, runs ajave, reports disagreement.
# No expected verdict involved.
# Differential fuzzing against a real JVM.
fuzz count="200": build
    python3 tools/fuzz_differential.py --count {{count}}

# It consumes untrusted bytes and must not panic. Needs: cargo install cargo-fuzz
# Fuzz the classfile parser.
fuzz-parser secs="300":
    cargo fuzz run classfile -- -max_total_time={{secs}}

# ---------------------------------------------------------------------------
# One-off analysis
# ---------------------------------------------------------------------------

# Run one task and show which engines did what.
explain task property="assert": build
    RUST_LOG=info {{BIN}} --property {{property}} {{COMMON}} {{task}} 2>&1 \
      | grep -E "timing step|final verdict|PROGRAM_SHAPE"

# Run one task and show the witness and its JVM replay result.
witness task property="assert": build
    RUST_LOG=ajave_core::certify=debug {{BIN}} --property {{property}} --show-witness \
      {{COMMON}} {{task}} 2>&1 | grep -E "REPLAY_CENSUS|witness|^TRUE|^FALSE|^UNKNOWN"
