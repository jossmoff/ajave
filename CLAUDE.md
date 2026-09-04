# Ajave Development Guidelines

## Changes Log
When implementing a new technique, engine, analysis, or any notable architectural decision, add a dated entry to `changes.md` describing what was done and why it's interesting. Focus on what would be worth mentioning in a paper: novel combinations, design trade-offs, performance insights, soundness arguments.

## Smoke Tests — MANDATORY before scoring
Run `python3 tools/bench.py --set smoke --check` after building (`cargo build
--release`) and BEFORE any full scoring run. Exit code 0 = safe to score, 1 =
regressions detected. Takes ~1 minute.

(`tools/smoke_test.py` was the old harness and is superseded by `bench.py`; the
canary list now lives in `benchmarks/sets/smoke.set`.)

### When to add a smoke test
Add a new entry to the `TESTS` list in `tools/smoke_test.py` when:
1. **Fixing a wrong answer** — add the benchmark as a canary so it never regresses.
2. **Adding/changing a discharge or soundness condition** — add TRUE and FALSE benchmarks that exercise the new condition.
3. **Modeling a new instruction, method, or type** — add a benchmark that uses it.
4. **Fixing a bug that caused UNKNOWN on a previously-correct benchmark** — add it to prevent re-breakage.

### How to add a smoke test
1. Pick a benchmark `.yml` path under `benchmarks/sv-comp/`.
2. Add a line to `benchmarks/sets/smoke.set` under a comment naming the category.
3. Name the property explicitly — entries are curated one property at a time,
   because letting a task expand to every property it declares doubled the
   runtime and changed what the gate covers.
4. Run `tools/bench.py --set smoke` to verify.

Format: `<path-relative-to-benchmarks>.yml <property>`

The expected verdict comes from the task's own `.yml`, so a canary for a
wrong-answer fix needs no separate assertion: it scores WRONG if the bug
returns, and unproven if the fix is honest but imprecise.

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

### The contract is the only source of truth
Every statement about an external method lives in `ajave_models::contract_of`.
There is no second place: the `match class` that used to answer a third of the
JDK surface inside `smt_bmc/explore.rs` is gone, because an order over library
models is void while most models are answered somewhere else.

Prefer `contract_for`, which is total and defaults to `Contract::OPAQUE`.
`Option` conflates "specified to throw" with "we never said anything", and that
conflation is what let the answers spread out in the first place.

`Contract::at_least_as_conservative_as` states the refinement order: more
preconditions and a wider effect are more conservative, and only movement *up*
it is safe. `tools/contract_monotonicity.py` checks that every consumer respects
it, by perturbing one contract to OPAQUE and requiring that verdicts only weaken
to UNKNOWN.

That harness runs against `benchmarks/sets/contracts.set`, whose programs each
rest their verdict on exactly one contract. **Do not point it at ordinary
benchmarks.** That was tried; their verdicts rarely depend on a single contract,
so every perturbation was inert and the test passed while proving nothing. The
harness exits 2 when all perturbations are inert, so this cannot recur silently.

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

### Per-task timings are recorded; per-task timeouts are not
Baselines carry a wall-clock column, and `--check` flags a task that has become
much slower (default 4x, `--slow-factor`). This catches the regression class
that is otherwise invisible: a task going from 2s to 40s changes nothing
observable until it crosses the timeout, at which point it looks like a verdict
regression with no obvious cause.

`--update-baseline` also warns about tasks that finished within 40% of the
budget. Those are coin-flips, not results — `Optimization1` measured 97s and
253s on consecutive runs against a 60s budget, and one lucky parallel batch got
it baselined as `correct`.

**Do not turn recorded timings into per-task timeouts for a scoring run.**
SV-COMP gives every task the same budget. Granting the slow ones extra time
because we know they need it makes the score stop predicting competition
performance — it is the overfitting this file warns about, moved from the engine
into the harness. Raise the budget uniformly (`--timeout`) if a run needs more.

Timings are noisy, and a baseline recorded on a loaded machine is inflated,
which *masks* future slowdowns. Record baselines on an idle machine for the same
reason scores are.

### Run BOTH properties before believing a discharge change

A change to what may be discharged must be measured on valid-assert *and*
no-runtime-exception. They consume different obligation kinds, so a guard that
is sound for one can be vacuous for the other.

Loosening `all_calls_resolved` scored **NRE 1057 with 0 wrong and VA 680 with 9
wrong** — eight new wrong TRUEs. The NRE run alone looked like a clean +22.

The cause generalises: a guard that says "something else carries this burden" is
only as sound as that thing actually running. Here the flag deciding whether the
obligations were even emitted was computed for a decision record and never
stored, so it sat at its default for every property — and the dependency crossed
a crate boundary where nobody checked it.

### A killed process scores as a wrong-looking verdict, not as a timeout

Contention does not only inflate timeout counts. Under load the harness's own
process-group kills and memory pressure **terminate tasks by signal**, and
`bench.py` scores `returncode < 0` as `ERROR` — which reads as a verdict change,
not as noise.

A valid-assert run scored 807 against 815 with **5 tasks going FALSE → ERROR**,
while the timeout count *fell* (35 vs 39). The usual tell that a run is contended
was therefore absent and it looked exactly like a code regression. All 5
reproduced as FALSE individually; the machine had been at load 7.3 because a
build and other benchmark sets were running alongside. The clean idle-gated
re-run returned exactly 815/672.

So: **run nothing else during a scoring run.** Snapshotting the binary makes a
rebuild safe for *which* build is measured, and does nothing about this.

### The build under test must not change mid-run
A scoring run invokes the binary once per task over many minutes. Rebuilding
during that window swaps it underneath the run, so early tasks measure one build
and later tasks another, and the score describes **no build that ever existed**.

This is invisible — nothing errors, the number just quietly means nothing — and
it cost three measurements in one day, including a full valid-assert run.

`bench.py` now snapshots the binary at start and runs from the copy, so a
rebuild cannot affect a run in flight. The snapshot path travels in each work
item rather than a module global, because worker processes are spawned and
re-import the module. Do not reintroduce a global here.

### A regression must be reproduced before it is explained
**A score drop measured on a busy machine, or without a determinism check, is
not a regression.** Reproduce it under the conditions above before looking for a
cause. `CLAUDE.md` already warns that a score improvement without a soundness
argument is a red flag; the converse needs stating too.

## Every Engine Finding Gets a Minimal Benchmark — MANDATORY

When investigation of an engine turns up a real behaviour — a wrong verdict, a
semantic divergence from the JVM, a witness that cannot replay, a precision loss
with an identifiable cause — **reduce it to a minimal program and add it to
`benchmarks/ajave/` before fixing it.**

This is not the same as the smoke canary rule above. A canary is an existing
SV-COMP task pinned so it cannot regress. This is a *new, minimal* program that
isolates the behaviour, so the next person can see the mechanism in ten lines
instead of rediscovering it in a 60-line benchmark with four confounds.

### The rule
1. Reduce to the smallest program that still exhibits the behaviour.
2. Establish the expected verdict **by construction, from the JLS or the JVMS**,
   and then confirm it by running a real JVM. Never from what ajave currently
   says — that is the thing under test.
3. Put it in the matching `benchmarks/ajave/` category and write the reasoning
   in the header: what the JVM does, what we did, and why they differ.
4. Add it *before* the fix, so the benchmark is demonstrated to reproduce.
5. `tools/validate_own_benchmarks.py` checks the suite against a real JVM; run
   it after adding.

### Why
The corpus tasks are large and confounded. `float-nonlinear-calculation`
concealed three independent defects — no transcendentals in the concrete
evaluator, float arithmetic computed on integer bit patterns, and violations
published from havoced values — and each was only separable once reduced. A
finding that stays in a 60-line benchmark is a finding that gets rediscovered.

`benchmarks/ajave/jvm-floats/NaNComparisonIsAlwaysFalse` is the model: three
lines, ground truth argued from IEEE-754 and the `dcmpg` bytecode, and a header
that states what ajave did wrong and why it did not produce a wrong answer.

## Faults Between Engines — MANDATORY checks

Most defects found on 2026-09-02 were not inside an engine. They were in the
seams, and no benchmark could see them because a benchmark exercises one program
at a time. The recurring shapes:

- **A context-relative identifier used as a global key.** `ObligationId` and
  `BlockId` index into *one* `Body`. `skipped_obligations` and `violated_oids`
  were keyed by id alone, so a violation in one method blocked discharge of an
  unrelated obligation in another — worth 32 points once fixed. `current_block`
  was not restored after inlining, so `self.body.block(bid)` indexed the
  caller's blocks with a callee's id. **Never key a collection by `ObligationId`
  or `BlockId` alone if it outlives one `Body`.** Use `(MethodKey, _)`.
- **Producer and consumer disagreeing about an artifact.** `Bounded { k }` means
  the BMC's `max_depth`, a *path-length* bound; k-induction consumed it as an
  *iteration* count, and never read it. **Every artifact must document what a
  consumer may conclude from it.**
- **A local modelling gap becoming a global failure.** One missing string-array
  model tainted paths, and taint is a whole-run discharge gate, so it blocked
  everything on 12 securibench tasks. Prefer per-obligation facts to whole-run
  flags; `Completeness::discharge_blocker` exists because "which flag is set" and
  "which condition refuses" are different questions.
- **Comments asserting invariants the code does not maintain.** CHC described
  overflow-to-error guards in three places, with `INT_MIN`/`INT_MAX` declared and
  never read. An auditor found a correct soundness argument and no sign its
  premise was unmet. **A comment stating a soundness argument must have a test
  named after it.**
- **Unsoundness masked by an unrelated conservative gate.** k-induction, CHC and
  the StringBuffer model were each harmless only because something starved them.
  Removing a gate does not create these; it reveals them. **Every engine
  publishing `Over` needs a test that would fail if its encoding were unsound,
  independent of blackboard gating** — see
  `interprocedural_encoding_does_not_prove_an_overflowing_property` and
  `step_case_rejects_property_that_fails_after_one_unrolling`.

### The two harnesses that look between engines

Both are stronger oracles than the corpus because neither uses an
expected-verdict label, so they hold on programs no benchmark covers.

```
python3 tools/metamorphic.py      --set smoke   # meaning-preserving edits
python3 tools/engine_ablation.py  --set smoke   # AJAVE_DISABLE=<engine>
```

- **`metamorphic.py`** applies edits that cannot change what is true of a
  program — adding a reachable, always-safe method (which occupies overlapping
  obligation ids, the exact precondition for the collision above), and renaming
  `private static` helpers. A verdict that *flips* is a defect. A verdict that
  merely weakens to UNKNOWN may be a cost effect and is reported, not failed.
  Only `private static` methods are renamed: the first version renamed `run()`
  on a `Runnable`, so the thread body stopped executing and the harness reported
  its own edit as a bug in ajave. **A transformation must preserve meaning, and
  proving that is part of writing one.**
- **`engine_ablation.py`** removes one engine at a time. Removing an engine can
  only remove evidence, so an answer may be lost — but a flip between TRUE and
  FALSE means two engines disagree about the program and one is unsound.

The blackboard also checks itself: `Blackboard::contested()` reports obligations
an Over engine proved *and* an Under engine flagged. That pair is legitimate
until JVM replay confirms the violation, which is why the report fires after
certification rather than at publish — before that, a witness is only a
candidate, which is exactly what `proved_safe` exists to record.

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

## Artifacts: what engines say to each other — MANDATORY

The blackboard is the whole architecture, and it was being used as a mailbox.
Four of its five artifact kinds had **zero producers**, `Blackboard::since` —
the delta-pull mechanism `engine.rs` documents as what makes an engine removable
without the others noticing — had **zero consumers**, and ten of eleven engines
took `_budget` and ignored it. The rules below exist so that does not recur.

### Every artifact kind must have a producer and a consumer
Adding a variant to `Artifact` with neither is not design, it is a comment with
a type. If you cannot name the consumer, the artifact is not ready. `Invariant`,
`Precision`, `Trace` and `Residual` sat unused for months precisely because
nobody had to.

### Every artifact must document what a consumer may conclude from it
Already learned once, expensively: `Bounded { k }` means the BMC's *path-length*
bound, k-induction consumed it as an *iteration* count, and never read it. A
producer and a consumer that disagree about an artifact are worse than no
artifact.

### Two tags, and they answer different questions
- `Direction` — what a consumer may **conclude**. Over may discharge, Under may
  violate. Enforced at publish.
- `Approximations` — what the producer did **not model faithfully**. An engine
  encoding `dmul` as a bitvector multiply is honestly under-approximating a
  program that is not ours.

`open_for(models_faithfully)` returns open obligations plus those closed under
an approximation the caller does not make — and the caller must fix
**everything** that went wrong, not merely something. A better float encoding
does not conjure a model of `Math.sin`; offering it those obligations is pure
cost, and that cost is measurable (see `tools/engine_census.py`).

Declare approximations honestly. Under-declaring means a more faithful engine
never gets the obligation back; over-declaring only wastes time, so when in
doubt, declare.

### Questions are artifacts too
An engine that cannot proceed should `ask` rather than give up. A `Query` costs
nothing and commits to nothing; a `Lemma` answering it is governed by exactly
the discipline that governs a `Status`:

- `Bounds`/`Holds` are claims about **every** execution — `Over` or `Exact` only.
- `SatisfiedBy`/`RefutedBy` are claims about **one** — `Under` or `Exact` only.
- `Unknown` is worth publishing: it stops the scheduler re-asking.

This is what makes a specialised engine a *resource* rather than an
*alternative*. An engine that models transcendentals does not have to
reimplement heaps and inlining to be useful; it answers `sin` queries.

### Claims travel as `core::term::Expr`, never as strings
Keyed on the full `(class, name, desc)` signature for library applications, for
the same reason `contract_of` is. Doubles are bit patterns, because `f64` is
neither `Eq` nor `Hash` and query deduplication depends on both.

If an engine cannot express a claim in `Expr`, it must decline to make it. A
claim nobody can read is worse than no claim.

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
