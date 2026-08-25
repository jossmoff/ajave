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
- **No hardcoded witness values anywhere.** Engines must discover witness values through formal reasoning (SMT solving, abstract interpretation, symbolic execution), never by embedding benchmark-specific constants (e.g. known trigger strings). If an engine cannot construct a witness through its own analysis, it must not publish a violation.
- **No benchmark-specific pattern matching.** Every engine must be grounded in a well-defined formal method with a soundness argument. If you can't sketch a proof of why the engine's answers are correct in general, it's not a real engine — it's overfitting. Ad-hoc recognizers that work on known benchmarks but break on novel inputs are not acceptable.
- **IR changes must not regress other engines.** Changing the IR representation (e.g. lifting `Havoc` to `Call`) to benefit one analysis must be evaluated for performance impact on ALL engines, especially BMC. Run smoke tests AND check that borderline benchmarks don't timeout.
- **Update `changes.md`** whenever implementing a new technique, engine, or notable design decision.
- **Run smoke tests** after any engine change before full scoring.

## Code Quality Rules
- **FK is a struct, not a tuple.** Use `FK::new(class, name, desc)` for field keys. Never use raw `(String, String, String)` for field identification.
- **Use `ret_width_from_desc()`** to get return type width from JVM descriptors. Don't inline descriptor parsing.
- **Use `Completeness` struct** for tracking exploration completeness. Don't use bare boolean flags for `all_paths_complete`, `all_calls_resolved`, `has_unresolved_in_try`.
- **Solver push/pop must be paired.** Use `check_sat_with_path_and_witness()` which handles push, check, witness extraction, and pop atomically. Never leave a dangling push for the caller to pop.
- **Discharge logic lives in `Completeness::can_discharge()`.** Don't spread discharge criteria across multiple ad-hoc conditionals.

## Issue Labels and Experiment Tracking

### Label taxonomy
Labels follow the pattern `category:value`. Every issue should have at least a `type:` and an `area:` label.

| Category | Purpose | Examples |
|---|---|---|
| `type:` | What kind of change | `feature`, `fix`, `refactor`, `docs`, `test`, `chore`, `ci`, `experiment` |
| `area:` | Which crate/subsystem | `ir`, `models`, `core`, `frontend`, `engines`, `cli`, `benchexec`, `witness` |
| `tier:` | Which engine tier | `0-presolve`, `1-ai`, `2-falsify`, `3-kinduction`, `4-cegar`, `5-chc` |
| `direction:` | Approximation direction | `over`, `under`, `exact` |
| `priority:` | Scheduling urgency | `p0-soundness`, `p1-blocker`, `p2-normal`, `p3-later` |
| `status:` | Experiment outcome | `explored` (tried, net-negative), `blocked` (viable but needs prerequisite) |

### Logging failed experiments
When an experiment is attempted and reverted, file a GitHub issue with:
1. Labels: `type:experiment`, `status:explored` (or `status:blocked`), plus relevant `area:` and `tier:` labels.
2. Body must include: **Hypothesis**, **What was tried**, **Result** (with measured point impact), **Why it failed**, and **Path forward** (prerequisites for revisiting).
3. Cross-reference related issues (e.g., a `status:blocked` experiment should link to its prerequisite).

This prevents re-attempting known-bad approaches and documents the conditions under which they might become viable.
