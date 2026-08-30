# Ajave Development Guidelines

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

## Modelling External Code (JDK) — MANDATORY

Any claim that an unmodelled library method is "safe" is a **soundness
commitment**, not a heuristic. `could_throw_runtime_exception()` returning
`false` lets the BMC treat a havoced call as non-throwing, claim
`all_paths_complete`, and discharge NRE obligations as TRUE. A wrong entry is a
wrong TRUE (−16), not a precision loss.

Issue #48 found 22 wrongly-allowlisted methods that had accumulated because the
list was grown until the benchmark corpus passed. The rules below exist to stop
that recurring.

### Rules for allowlisting library behaviour
1. **Key on the full `(class, name, desc)` signature.** Never on `(class, name)`.
   `Integer.valueOf(int)` is total; `Integer.valueOf(String)` throws
   `NumberFormatException`. `StringBuilder()` is total; `StringBuilder(int)`
   throws `NegativeArraySizeException`. Descriptor-blind matching cannot see
   the difference.
2. **Never allowlist an entire class.** `Math`, `Arrays`, `Collections` and
   `StrictMath` all look total but contain throwing members (`addExact`,
   `copyOfRange`, `max` on an empty collection).
3. **Never allowlist a partial function.** `List.get`, `Iterator.next`,
   `Stack.pop/peek` throw on out-of-range or empty receivers — that *is* their
   specified contract.
4. **Match class names exactly.** A substring test on `"Verifier"` also matches
   a user class called `MyVerifierHelper`.
5. **Justify from the contract, never from observed benchmark behaviour.** The
   question is "does the Javadoc/JLS guarantee this cannot throw for *any*
   input", not "did anything fail when I added it".
6. **Argument nullability counts.** `String.concat/contains/startsWith` and
   `TreeMap.put` throw NPE on null arguments.
7. **When in doubt, leave it out.** Omission costs precision; a wrong entry
   costs correctness.

### Required evidence
Adding or changing an entry requires **both**:
- a case in the Rust tests in `smt_bmc/explore.rs` (`jdk_allowlist_tests`), which
  assert against `is_total_jdk_method` directly, and
- a probe in `tools/validate_jdk_allowlist.py`, which establishes ground truth by
  running the signature on a real JVM with adversarial arguments (empty
  receivers, out-of-range indices, nulls, overflow boundaries).

Do not validate an allowlist by scraping Rust source text — a source-text check
cannot distinguish overloads and will silently pass the very bug it is meant to
catch.

The same standard applies to `is_nonnull_static()` in `interval.rs`: only
`static final` fields with non-null initialisers qualify. `System.out`/`err`/`in`
do **not** — they are mutable via `System.setOut(null)`.

## Measurement Discipline — MANDATORY before quoting any score

Three separate wrong conclusions were reached in one day by measuring badly.
A number produced without these conditions is not evidence.

### Runs must be reproducible
Verdicts once depended on `HashMap` iteration order (Rust seeds hashers per
process) and on stale `/tmp` directories left by earlier runs. That produced
±15-30 points of run-to-run noise on the full corpus, which was mistaken for
timeout variance for a long time.

- Iterating a `HashMap`/`HashSet` to build **anything a solver sees**, or to
  choose **what to explore**, is a bug. Sort it, or use a `BTree*` collection.
- `tools/bench.py --repeat N` must pass before a score is quoted.
- Temp directories come from `ajave_core::scratch::ScratchDir`. Never name one
  after the pid: pids are reused, and `create_dir_all` happily adopts another
  run's leftovers.

### Runs must be on an idle machine
Timeout counts are the largest term in the score and are contention-sensitive.
The same build measured **89 timeouts under load and 43 idle** — about 20
points, which looked exactly like a code regression and was investigated as one.

- `bench.py` prints load and free memory with every result, and `--require-idle`
  refuses to start when the machine is busy. Use it for anything you intend to
  compare.
- Check for strays first: `tools/cleanup.sh`. A leaked solver or JVM holds
  hundreds of megabytes and never exits on its own.

### A regression must be reproduced before it is explained
**A score drop measured on a busy machine, or without a determinism check, is
not a regression.** Reproduce it under the conditions above before looking for a
cause. `CLAUDE.md` already warns that a score improvement without a soundness
argument is a red flag; the converse needs stating too.

## Guarding Against Benchmark Overfitting

Every entry above was added while looking at `sv-benchmarks/`, which is also
what we score on. Treat any tuning that references benchmark outcomes as
suspect:

- **Fitted constants are not results.** `MAX_FORKS`, `MAX_LOOP_UNROLL`,
  `MAX_CALL_DEPTH`, `widen_delay` and friends were chosen by raising them until
  specific benchmarks passed. Record when you do this, and re-check that the
  score is not sensitive to the exact value.
- **A score improvement with no soundness argument is a red flag.** If you
  cannot state why the change is correct on programs you have never seen, it is
  overfitting.
- **Prefer engine-independent evidence.** Tests that exercise real JVM
  behaviour (`tools/validate_jdk_allowlist.py`) generalise; benchmark canaries
  do not.

See issue #47 for the planned metamorphic-testing harness, held-out split, and
constant-sensitivity sweep.

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
