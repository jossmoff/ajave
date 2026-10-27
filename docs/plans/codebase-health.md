# Long-term codebase health: five workstreams

Plan, 2026-10-26. Written after the structural audit of the same day, which
closed six findings and opened #48.

Each workstream below is **independently executable** — none blocks another,
none shares a branch — and each phase inside one has its own validation gate
with a stated cost. Phases are ordered so that the cheapest evidence comes
first and an expensive step is never taken on an unvalidated premise.

Ordering between workstreams is by value, not dependency:

| | workstream | size | validation cost | starts |
|---|---|---|---|---|
| **A** | The TRUE certifier | weeks | minutes per phase, one corpus run at the end | now |
| **B** | Frontend/IR differential testing | ~1 week | seconds to minutes | now |
| **C** | Narrow the portfolio | ~2 days | one ablation run | now |
| **D** | An independent oracle (JBMC) | ~3 days | minutes | **blocked — #97** |
| **E** | Static contract checks | ~1 day | **seconds**, in CI | now |

**Start with E.** It is a day's work, runs in the existing toolchain-free CI
job, and it is the only item that attacks the *rate* at which these defects
appear rather than individual instances. Then A, which is the one that changes
what the tool is.

---

# Workstream A — The TRUE certifier

## Why

`certify.rs` opens with the project's trust rule: "no artifact reaches the
reporter on an engine's authority alone. FALSE is replayed on a real JVM; TRUE
rests on invariants re-checked by a separate, small, boring pass."

There is exactly one `impl Certifier` in the tree, `JvmReplay`, for FALSE. The
TRUE half was never built. Every FALSE is checked against a real JVM; every
TRUE rests on the authority of the engine that claimed it — and `interval-ai`,
which produced **55 of 57** discharges on the sampled corpus, is the least
independently verified component in the system.

The pipeline is not missing, it is half-built and unenforced:

| piece | state |
|---|---|
| `Invariant { id, at, formula: Expr, status }` | exists |
| `InvStatus::Candidate` — "never enough on its own to discharge" | produced by `ai.rs:492` |
| `InvStatus::Inductive` — "verified initial-and-preserved by the certifier" | **no producer, anywhere** |
| `ProofKind::Invariant(inv_id)` | produced by `ai.rs` |
| `Blackboard::inductive_invariants()` | filters for `Inductive`, so **always empty** |
| enforcement that a Candidate cannot discharge | **none** |

So `ai.rs` discharges against an invariant the type system itself documents as
insufficient, and the accessor meant to consume verified ones is dead.

Every finding from the 2026-10-26 audit is a symptom: #48 (float wrong TRUE),
#43 (IMC's unargued conservatism), #47 (undeclared `EXACT`), and the open p0s
#55, #76, #77 are all "an engine proved something it should not have". A
certifier catches each **without knowing any of them exist**.

## The honest limit, stated up front

A checker that reuses an engine's own transfer function certifies nothing. Full
independence needs a second implementation of JVM semantics, which is the
"multi-year project" `certify.rs` concedes. What A buys is *partial*
independence: a different encoder path, a separate pass, three explicit
obligations. That catches engine-specific defects, which is what every audit
finding was. Say this in the module doc rather than overclaiming.

## A1 — Enforce the existing contract, and measure what breaks

The smallest possible first step, and it establishes the size of everything
after it.

* Reject at publish: `Status::Discharged { proof: ProofKind::Invariant(id) }`
  where invariant `id` is not `InvStatus::Inductive`. This is the rule
  `InvStatus`'s own doc comment states.
* Nothing yet promotes to `Inductive`, so this turns every invariant-backed
  discharge into a rejection. Expected: `interval-ai`'s discharges stop.
* Gate it: `AJAVE_CERTIFY_TRUE=1`, default **off**.

**Validation.** `cargo test` plus two smoke runs, flag off and on. Off must be
byte-identical to today. On must show `interval-ai` losing its discharges and
nothing else changing. ~12 minutes.

**Exit criteria.** The flag-on run quantifies the certifier's scope: how many
points currently rest on unverified invariants. That number is the budget for
A2–A4, and if it is small the whole workstream is cheaper than expected.

## A2 — The checker, offline and testable

A free function, no engine, no blackboard:

```rust
pub fn check_inductive(
    body: &Body, inv: &Invariant, oid: ObligationId, solver: &dyn Solver,
) -> CertResult
```

Three obligations, each a separate solver query, each independently reportable:

1. **Initiation** — `init ⟹ inv` at `inv.at`
2. **Preservation** — `inv ∧ transition ⟹ inv'` for every edge out of `inv.at`
3. **Sufficiency** — `inv ⟹ safety(oid)`

Any `unknown` or any failure is `Inconclusive` or `Refuted`, never `Confirmed`.
Encode via the existing LIA/BV path rather than a new encoder; record in the
doc that this is the shared-encoder limit from "the honest limit" above.

**Validation.** Unit tests only — no corpus, no JVM. Hand-build invariant /
body pairs:

| fixture | expected |
|---|---|
| `x := 0; while (x < 10) x++;` with `inv: 0 ≤ x ≤ 10` | `Confirmed` |
| the same with `inv: 0 ≤ x ≤ 5` | `Refuted` (preservation fails) |
| the same with `inv: true` | `Refuted` (sufficiency fails) |
| an invariant that holds everywhere but not at entry | `Refuted` (initiation fails) |
| a body with a `Diverge` | `Inconclusive` |

Seconds. This is the phase that must be right, and it is the cheapest to
validate — which is why it is separated from everything around it.

## A3 — Promote, and let a promoted invariant discharge

* A new `InvariantCertifier` implementing `Certifier`, calling `check_inductive`.
* On `Confirmed`, republish the invariant with `status: InvStatus::Inductive`.
  Append-only, so this is a new artifact, not a mutation.
* `Blackboard::inductive_invariants()` gets its first real content, and the
  A1 publish rule starts admitting discharges again.

**Validation.** Three tests on the blackboard: a `Candidate` cannot discharge;
the same invariant once `Inductive` can; a `Refuted` one still cannot. Plus the
flag-on smoke run from A1 — `interval-ai` should recover the discharges A1
removed, and **only** those. Any discharge it does *not* recover is either a
certifier gap or an engine that was wrong, and the two are distinguished by
reading the obligation. ~6 minutes.

**Exit criteria.** `AJAVE_CERTIFY_TRUE=1` smoke equals `=0` smoke. If it does
not, the difference is the list of currently-unsound proofs — which is the
point of the whole workstream, and each one gets its own issue.

## A4 — Widen to the other Over engines

`chc`, `kinduction`, `cegar`, `concurrency` and `smt_bmc` publish
`ProofKind::Exhaustive` or `KInduction`, neither of which carries a
certificate. Two options per engine, chosen per engine and recorded:

* **Produce an invariant.** CHC's Spacer answer *is* an inductive invariant; it
  is currently discarded. That makes CHC certifiable almost for free and is the
  highest-value item in this phase.
* **Declare uncertifiable.** `Exhaustive` over a bounded exploration is not an
  invariant and cannot be made into one. For those, the honest move is to admit
  the discharge only when `Completeness::can_discharge` already proves
  exhaustiveness, and record that this class is trusted rather than checked.

**Validation.** Per engine, in isolation: enable certification for that engine
alone and smoke. ~6 minutes each.

## A5 — Make it the default, once

One corpus run, both properties, idle machine, flag on. Compare against the
last clean baseline.

**Expect the score to fall.** Any TRUE that disappears was unverified, and some
were wrong. A lower number that means something is the deliverable. Quote both.

---

# Workstream B — Frontend and IR differential testing

## Why

`ajave-frontend` is 3,387 lines with **1 test**. `ajave-ir` is 1,234 with 1.
Every engine's correctness begins there, and a lifter defect is a *systematic*
wrong answer across the whole portfolio, where an engine defect is localised
and often caught by replay. The test investment is upside-down relative to the
trust structure: `ajave-core` is 92 loc/test and carries a quarter of the risk.

`benchmarks/ajave/` is this process already, done by hand, one finding at a
time.

## B1 — An IR well-formedness validator

Pure structure, no JVM, no solver:

* every `BlockId` referenced by a terminator, exceptional edge or `Edge` is in
  range
* every `VarId` is `< body.vars.len()` and has a `VarInfo`
* every `Stmt::Check(oid)` names an obligation that exists
* `body.entry` is in range; `blocks` is non-empty
* every obligation's `cond` operand references a live var
* no block has both a `Diverge` terminator and successors

Run it as a `debug_assert` at the end of `lift`, so every debug-mode lift of
every benchmark checks itself for free, plus one test that lifts every
classfile under `benchmarks/` and validates.

**Validation.** One test, seconds. Its own worth is demonstrated by the
historical bugs it would catch: `current_block` not restored after inlining
(indexing the caller's blocks with a callee's id) is exactly a range violation.

## B2 — Concrete-execution differential against a real JVM

The IR has a concrete interpreter already: `concrete.rs`'s `run_body`. So:

1. compile a `.java`, lift it, run `run_body` with a fixed nondet sequence
2. run the real JVM with the same sequence via the shadow `Verifier`
3. compare: terminating exception class, and `System.out` if any

Over the existing corpus first — thousands of Java files already present, with
no generator needed.

**Validation.** A harness `tools/lifter_differential.py`, run over
`benchmarks/ajave` (minutes) then `benchmarks/sv-comp` (longer, nightly). A
divergence is a lifter or interpreter bug and gets a minimal benchmark per
CLAUDE.md.

**Exit criteria.** Zero divergences over `benchmarks/ajave`, and a triaged list
over sv-comp. Note honestly: this validates the *pair* (lifter, interpreter) —
an identical misunderstanding in both is invisible. It still catches everything
where exactly one is wrong.

## B3 — A program generator

Only after B2 is clean, because B2 on the existing corpus is strictly cheaper
evidence. Small typed generator: ints, longs, floats, arrays, field access,
loops, exceptions, casts. Feed B2's comparison.

**Validation.** Run count and divergence count. Any divergence is reduced to a
minimal benchmark and added to `benchmarks/ajave/`.

---

# Workstream C — Narrow the portfolio

## Why

Nine engines produce roughly four discharges between them. `cegar` ran on 0 of
121 tasks; `imc` could not run at all until 2026-10-26 and still cannot without
SMTInterpol. Each engine kept is permanent maintenance, review surface, and —
the real cost — another set of declarations that can rot. The 2026-10-26 audit's
defects lived almost entirely in the seams *between* engines, so fewer engines
is a structural reduction in defect surface, not just less code.

The engine census already concluded that unlocking `cegar` and `imc` would
*compete* with `interval-ai` rather than add, because they target obligations it
already attempts.

## C1 — Measure before deleting

`AJAVE_DISABLE` already exists and takes a comma-separated list. Run the full
corpus, both properties, with `AJAVE_DISABLE=cegar,imc` and compare.

**Validation.** One corpus run. If the score is unchanged, the engines
contribute nothing measurable and C2 is justified by evidence rather than by
the census's sample.

## C2 — Delete, with the reasoning preserved

Remove `cegar.rs`, `predicate.rs`, `imc.rs`, `interpolation.rs` and their
registrations. File a `status:explored` issue per engine carrying: what it was,
what it scored, why it was removed, and what would have to change to make it
worth reviving. The code stays in history; the issue is the index into it.

**Validation.** Smoke, plus a corpus run confirming C1's number. `just
boundaries` and `just strategy-docs` must still pass (the latter tracks a
`cegar.md` gap that disappears with the engine).

**Do not delete:** `ranges` (the only `Lemma` answerer, serving the measured
`AJAVE_ASK` loop), `float_search` (found the violation in `FloatIsNotDouble`),
`presolve` (cheap and sound), `concrete`, `nra`.

---

# Workstream D — An independent oracle

**Status: filed as issue #97, `status:blocked`, not started.** `jbmc` is not
installed and that is the only external prerequisite in this plan. The issue
carries the full design; what follows is the summary.

## Why

`metamorphic`, `engine_ablation` and `contract_monotonicity` are all
self-referential: they compare ajave to ajave. Valuable, and structurally
unable to find a defect ajave makes *consistently*. JBMC runs the same corpus
and is a different implementation by different people.

## D1 — The harness

`tools/jbmc_differential.py`: run both tools on each task, bucket by
`(ajave_verdict, jbmc_verdict)`. The interesting cells are TRUE/FALSE and
FALSE/TRUE — one tool is wrong and either answer is a finding. UNKNOWN on
either side is uninformative and reported separately.

**Validation.** Run on `benchmarks/sets/smoke.set`; minutes. The harness is
working when it reproduces the known disagreement on
`svcomp-mislabelled-reverseinterpolator`, where ajave's FALSE is right and the
benchmark's label is wrong.

## D2 — Triage

Every TRUE/FALSE disagreement gets an issue. Expect three buckets: ajave wrong,
JBMC wrong, benchmark mislabelled. The third is already known to exist, which
is why the harness must not assume the label is truth.

**Dependency.** Needs JBMC installed (`jbmc` is not on PATH today). That is the
only external prerequisite in this plan. Tracked as #97.

One constraint worth repeating here because it is easy to get wrong: **the
harness must not treat the benchmark label as the referee.** `ReverseInterpolator`
is a task where ajave's FALSE is correct and the declared TRUE is wrong, costing
−32. A differential that scored against the label would read that as an ajave
defect and send someone to break a correct answer.

---

# Workstream E — Static contract checks

## Why

The 2026-10-26 session surfaced roughly eight instances of one shape: a
mechanism that exists, is correct, and is never reached. An engine that could
not run; an escalation pass that retired before its input existed; an interest
declared for a kind nobody produces while omitting the one it needed; a lemma
on a dead term; four flags dead by their own criteria; and two of the session's
own tests that passed vacuously.

This is the failure mode of a portfolio where everything communicates
indirectly. It is also mechanically detectable. These checks attack the *rate*,
which nothing else in this plan does.

They belong in CI's existing `quick` job: pure bash or python, no toolchain, no
build, seconds. `scripts/check-boundaries.sh` and
`scripts/check-strategy-docs.sh` are the precedent and the template.

## The checks

| id | check | would have caught |
|---|---|---|
| E1 | every `Interest` bit an engine declares has a producer | #37's `PRECISION` |
| E2 | every `Artifact` variant has a producer *and* a consumer, or a declared `Parked` reason | `Invariant`/`Precision`/`Trace`/`Residual` sitting unused for months |
| E3 | every `bb.ask` `Want` has an answerer, and every asker a consumer | #40's CEGAR asker |
| E4 | every defaulted trait method is overridden by at least one impl | `Cpa::prec` and `Cpa::stop` |
| E5 | every `impl AbstractDomain` has a `check_lattice_laws` call in its crate | a third domain silently skipping the laws |
| E6 | no `Progress::Exhausted` returned on a condition that later artifacts can change | the FPA pass retiring in round 0 |

## Validation — the part that matters

**Each check must be demonstrated to fail on its motivating instance.** Revert
the fix in a scratch commit, run the check, confirm it fails, discard. A check
that does not catch the bug it was written for is itself an instance of the
class it is meant to detect — which is precisely the mistake made twice on
2026-10-26, where a test passed because its premise was unsatisfiable.

Record the demonstration in the script's header comment: which commit, which
bug, what the failure output was.

E6 is the hardest to make precise and should be attempted last; if it cannot be
made to work without false positives, record that and drop it rather than
shipping a check people learn to bypass — the reasoning `nightly.yml` already
applies to the corpus test.

---

# Execution notes

**Parallelism.** A, B, C and E touch disjoint files and can run on separate
branches. D is independent but needs an install. The only shared gate is smoke,
which must not run concurrently with a build or with another smoke — see
CLAUDE.md's measurement rules, violated once on 2026-10-26 by rebuilding during
a run in flight.

**Corpus runs needed.** Four, total: C1 (ablation), A5 (certification on), and
one baseline before each. Everything else validates in seconds or minutes. The
plan is deliberately shaped so that the expensive evidence is gathered four
times rather than per phase.

**Expected score impact.** A5 lowers it, honestly. C is neutral by
construction. B and E are neutral. #48, closed separately, lowers it again.
Any number quoted after this plan is smaller and means more; quote both and
say why.
