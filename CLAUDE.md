# Roast Development Guidelines

## Changes Log
When implementing a new technique, engine, analysis, or any notable architectural decision, add a dated entry to `changes.md` describing what was done and why it's interesting. Focus on what would be worth mentioning in a paper: novel combinations, design trade-offs, performance insights, soundness arguments.

## Smoke Tests — MANDATORY before scoring
Run `python3 tools/smoke_test.py` after building (`cargo build --release`) and
BEFORE any full scoring run. Exit code 0 = safe to score, 1 = regressions
detected. Takes well under a minute.

Note it needs a solver on `PATH` (`z3` by default, or set `ROAST_SMT_SOLVER`)
for the SMT-backed engines to register at all; without one, several tasks come
back UNKNOWN that would otherwise pass.

### When to add a smoke test
Add a new entry to the `TESTS` list in `tools/smoke_test.py` when:
1. **Fixing a wrong answer** — add the benchmark as a canary so it never regresses.
2. **Adding/changing a discharge or soundness condition** — add TRUE and FALSE benchmarks that exercise the new condition.
3. **Modeling a new instruction, method, or type** — add a benchmark that uses it.
4. **Fixing a bug that caused UNKNOWN on a previously-correct benchmark** — add it to prevent re-breakage.

### How to add a smoke test
1. Pick a benchmark `.yml` path under `tasks/` (or `sv-benchmarks/`, if you
   have that corpus checked out alongside).
2. Choose an appropriate category string (e.g., `"exceptions"`, `"arith"`,
   `"loops"`, `"branch"`, `"canary"`, `"string"`).
3. Set the expected verdict to the **known-correct** answer (`"TRUE"` or `"FALSE"`).
4. Add the tuple to the `TESTS` list in the appropriate section.
5. Run the smoke test to verify it passes.

Format: `("category", "tasks/path/to.yml", "EXPECTED_VERDICT"),`

### Rules
- Keep the suite under 80 tests. Quality over quantity.
- Every wrong-answer fix MUST add a canary test.
- The smoke test must pass before full scoring. Do not skip it.
- A task whose correct verdict roast **cannot yet produce** does not go in
  `TESTS` — it goes in `KNOWN_GAPS`, with a one-line note on why. A gate that
  is permanently red is a gate everybody learns to ignore. Promote an entry to
  `TESTS` the moment it starts passing, so it can never silently regress.

### Profiling and scaling the SMT layer
`--profile` breaks a run down per engine: SMT bytes emitted, commands, encode
time against solver time, check-sat count and verdict split. `--profile-json`
writes the same machine-readably.

`python3 tools/smt_scaling.py` generates families of programs parameterised by
size, fits how encoding size and solver time grow, and fails when a family
exceeds its declared growth budget. Fixed benchmarks cannot see a change in
asymptotic behaviour -- an encoder going from linear to exponential output looks
like "a bit slower" on any single task until it stops finishing at all. Run it
after any change to an encoder or to the explorer's merge strategy.

`--self-test` checks the growth classifier against series of known growth;
worth running if you touch the fitting code.

### The other two harnesses
- `cargo test -p roast` runs the full 114-task corpus as integration tests.
  Slower, and it needs a JDK. This is what CI runs.
- `scripts/run-corpus.py` diffs every task against the snapshot in
  `tasks/verdicts.txt` and can rewrite it with `--update`. Bookkeeping, not a gate.

## Design Rules
- **No hardcoded nondet patterns in concrete engine.** Single all-zero probe only. Finding specific input values is the SMT engine's job.
- **Update `changes.md`** whenever implementing a new technique, engine, or notable design decision.
- **Run smoke tests** after any engine change before full scoring.
