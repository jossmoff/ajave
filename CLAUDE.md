# Roast Development Guidelines

## Changes Log
When implementing a new technique, engine, analysis, or any notable architectural decision, add a dated entry to `changes.md` describing what was done and why it's interesting. Focus on what would be worth mentioning in a paper: novel combinations, design trade-offs, performance insights, soundness arguments.

## Smoke Tests — MANDATORY before scoring
Run `python3 tools/smoke_test.py` after building (`cargo build --release`) and BEFORE any full scoring run. Exit code 0 = safe to score, 1 = regressions detected. Takes ~3 minutes.

### When to add a smoke test
Add a new entry to the `TESTS` list in `tools/smoke_test.py` when:
1. **Fixing a wrong answer** — add the benchmark as a canary so it never regresses.
2. **Adding/changing a discharge or soundness condition** — add TRUE and FALSE benchmarks that exercise the new condition.
3. **Modeling a new instruction, method, or type** — add a benchmark that uses it.
4. **Fixing a bug that caused UNKNOWN on a previously-correct benchmark** — add it to prevent re-breakage.

### How to add a smoke test
1. Pick a benchmark `.yml` path from `sv-benchmarks/`.
2. Choose an appropriate category string (e.g., `"exhaust-true"`, `"exceptions"`, `"canary"`, `"string"`, `"autostub"`).
3. Set the expected verdict to the **known-correct** answer (`"TRUE"` or `"FALSE"`).
4. Add the tuple to the `TESTS` list in the appropriate section.
5. Run the smoke test to verify it passes.

Format: `("category", "sv-benchmarks/path/to.yml", "EXPECTED_VERDICT"),`

### Rules
- Keep the suite under 80 tests (~5 min). Quality over quantity.
- Every wrong-answer fix MUST add a canary test.
- The smoke test must pass before full scoring. Do not skip it.

## Design Rules
- **No hardcoded nondet patterns in concrete engine.** Single all-zero probe only. Finding specific input values is the SMT engine's job.
- **Update `changes.md`** whenever implementing a new technique, engine, or notable design decision.
- **Run smoke tests** after any engine change before full scoring.
