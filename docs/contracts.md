# Contract semantics for ajave

Status: design, 2026-10-25. Task #39.

The thesis: **ajave already has a working contract system, for one domain, and
the right move is to generalise it rather than invent a second one.**

`ajave_models::contract_of` describes external methods. It works — it is the
only part of the tree where a claim about an interface is stated once,
mechanically checked, and cannot silently rot. Everything else engines say to
each other is stated in prose comments, and every defect found in the last week
was a contract that lived only in a comment or nowhere at all.

## Why `contract_of` works, in five properties

These are the properties to copy. Nothing else about it matters.

1. **Totality.** `contract_for` returns `Contract::OPAQUE` for anything unknown.
   There is no `Option`, because "specified to throw" and "we never said" are
   different facts and conflating them is what let the answers spread out.
2. **A refinement order.** `at_least_as_conservative_as` makes two contracts
   comparable: more preconditions and a wider effect is more conservative, and
   only movement *up* that order is safe.
3. **A perturbation harness.** `tools/contract_monotonicity.py` weakens one
   contract to `OPAQUE` and requires that verdicts only weaken to UNKNOWN. A
   verdict that *changes* instead means a consumer is not monotone.
4. **Required evidence, in two independent forms.** A Rust test asserting the
   predicate, and a probe running the real signature on a real JVM with
   adversarial arguments.
5. **Keyed on full identity.** `(class, name, desc)`, because
   `Integer.valueOf(int)` is total and `Integer.valueOf(String)` throws.

## What an internal contract must state

Each field below exists because a specific defect would have been impossible
with it. The first three exist today; the last four do not.

| Field | States | The defect it prevents |
|---|---|---|
| `direction` | what a consumer may **conclude** | exists, enforced at publish |
| `approximations` | what the producer did **not model** | exists, declared |
| `producers` / `consumers` | who may write it, who reads it | **#37** — `Precision` has a consumer declaring interest and zero producers |
| `scope` | over **what** the claim holds: the whole program, one method, one program point, one execution | the `ranges` lemma asserted about a term the variable no longer denoted. Producer and consumer disagreed about *when* a `VarId` means what |
| `units` | what a number **measures** | `Bounded { k }` — producer meant a path-length bound, consumer read it as an iteration count |
| `publishable_when` | the producer's own **precondition** for saying it at all | `$$coll_size` had a reader and an incrementer and no initialiser; AI bounds are sound only from a *converged* fixpoint |
| `purpose` | whether the artifact is meant to **change a verdict** or only to **explain one** | measured today: four options all scored identically to baseline. For two of them that is correct, for two it is failure, and a score diff cannot tell them apart |

The last row is the one this session produced by accident and it is the most
useful. See "Inert by design versus inert by defect" below.

## Four mechanical checks

### 1. Every declared interest has a producer — static

`Interest` names artifact kinds an engine wants to be woken for. A bit naming a
kind nothing produces is a dependency on a message nobody sends. Walk the
`Artifact::` constructor sites in the workspace, intersect with every
`interest()` return, fail on a bit with no producer.

Catches #37 for free. Cheap enough to run in CI as a unit test.

### 2. Every artifact kind has a producer *and* a consumer — static

Adding a variant with neither is a comment with a type. `Invariant`,
`Precision`, `Trace` and `Residual` sat unused for months precisely because
nothing had to.

A kind deliberately parked (`Query`/`Lemma` were, behind a flag) declares that
rather than being silently absent: `purpose: Parked { why }`.

### 3. Artifact monotonicity — dynamic, and the important one

This generalises `contract_monotonicity.py` from library contracts to internal
artifacts, and it is the check that unifies every defect in this document.

For each artifact kind, perturb its producer to publish the **weakest form the
contract permits** — a `Bounds` of top, a `Status` of Open, a `Residual`
covering nothing — and re-run the corpus. Three outcomes, three meanings:

| Outcome | Meaning |
|---|---|
| verdicts **weaken** (anything → UNKNOWN) | correct: the artifact was load-bearing and the consumer is monotone |
| verdicts are **unchanged** | the artifact is **inert**. Either a defect, or `purpose` says it is a diagnostic |
| verdicts **strengthen or flip** | the consumer concluded more than the contract permits. The −16 direction |

The middle row is the efficacy test from the architecture review, mechanised.
Every live-but-vacuous defect this session found — the lemma on a dead term,
`$$coll_size` with no writer, `Bounded` guarded only by nesting, `Precision`
with no producer — is a program where perturbing the artifact changes nothing.
**One harness detects all four, and would have detected them without anyone
suspecting them**, which is the limit the review explicitly flagged about
hand-written efficacy tests.

### 4. Scope coherence — static

A `VarId` indexes one `Body`; an `ObligationId` likewise. An artifact whose
`scope` is one method, consumed where the method is not fixed, is the
id-collision class that cost 32 points once. Any collection keyed by
`ObligationId` or `BlockId` alone that outlives one `Body` is a scope violation
and is findable by inspection of the key type.

## Inert by design versus inert by defect

Measured 2026-10-25, each option alone against baseline, full corpus:

| | valid-assert | no-runtime-exception | purpose | verdict |
|---|---|---|---|---|
| baseline | 871 | 1184 | — | — |
| A — AI answers `Bounds` | 871 | 1184 | convert tasks | **falsified** |
| B — refutation artifact | 871 | 1184 | explain | **confirmed** |
| C — residual | 871 | **1182** | explain | confirmed, and it costs 2 |
| D — nullness queries | 871 | **1182** | convert tasks | **falsified, and it costs 2** |

Valid-assert is identical to the digit across all five runs. On
no-runtime-exception, C and D each lose two points — one task — which is the
cost of the extra work they do, and neither buys anything back.

Four mechanisms, near-identical scores, and **the right reaction differs by
mechanism**:

* **B and C are diagnostics.** They publish an explanation of why an obligation
  is open. Changing no verdict is what they are *for*; a verdict change would
  mean they had overstepped. Inertness confirms them.
* **A and D are supposed to convert tasks.** Inertness falsifies both, exactly
  as the pre-check criteria written before the run said it would. D is worse
  than inert: it costs a task.

Nothing in a score diff distinguishes those two cases. A `purpose` field does,
and it is the cheapest field in the table to add.

The asymmetry is worth stating plainly, because it is the reason this matters.
A diagnostic that changes no verdict and a converter that changes no verdict
produce **the same row in a results table**, and they need opposite responses:
keep the first, delete the second. Four runs of a 1,784-pair corpus, roughly
three hours of machine time, cannot tell them apart. One declared field can.

## Where the declarations live

In Rust, beside the type, so they are checkable rather than documentation:

```rust
impl Artifact {
    /// What a consumer may conclude, and under what conditions it was said.
    pub const fn contract(kind: ArtifactKind) -> ArtifactContract { … }
}
```

A `const fn` over an enum rather than a registry, for the same reason
`contract_for` is total: a kind added without a contract must fail to compile,
not default to permissive.

## What this is not

Not a proof system, and not a specification language for the programs under
analysis. It is a contract between *parts of ajave*, and the thing it buys is
that a defect in the seams becomes a test failure rather than a quiet loss of
score. Every such defect this session was found by hand, mostly by accident, and
four of them had been live for months.

---

# Part II: the seams, surveyed

Added 2026-10-26. Part I above treats *one* interface — what an engine puts on
the blackboard. A verifier sits behind seven, and surveying them changes which
of Part I's four checks is worth building first.

Enforcement is scored in four tiers:

* **checked** — a violation fails a test or a harness
* **typed** — the compiler rejects some violations, nothing checks meaning
* **prose** — stated in a doc comment, nothing checks it
* **absent** — not stated

## The census

| Seam | Interface | Contract | Enforcement |
|---|---|---|---|
| engine → models | `contract_of` | total, refinement order, full-signature keys | **checked** — `contract_monotonicity.py`, `validate_jdk_allowlist.py`, Rust tests |
| engine → orchestrator | `Progress`, `Interest`, `Budget` | `Suspended` must raise a bounded parameter; `Blocked` re-entered only on a matching publish | **checked** — 13 tests, incl. `an_engine_that_always_suspends_terminates_without_a_deadline` |
| engine → blackboard: *direction* | `publish_with` | Over may discharge, Under may violate, nobody may discharge in a threaded program | **checked** — rejected at publish, 16 tests |
| engine → blackboard: *approximations* | `publish_with` | producer declares what it did not model faithfully | **typed** — see "The dishonest default" |
| engine → blackboard: *meaning* | doc comments | scope, units, publishable-when, purpose | **prose** — this is Part I |
| engine → certifier | `CertResult` | Confirmed / Refuted / Inconclusive, and what may rest on each | **prose** |
| engine → solver | `Solver` | push/pop pairing; `Unknown` concludes nothing | **prose** — a `CLAUDE.md` rule and one helper |
| engine → CPA | `Lattice`, `Cpa` | `leq` a partial order, `join` an upper bound, widening terminating, `transfer` sound | **prose** — and see "The untested substrate" |
| frontend → IR | `Diverge`, obligation seeding, `guarded` | an unmodelled instruction costs completeness, not soundness | **prose** — tested only end-to-end, via `validate_own_benchmarks.py` |

The top three rows are in good shape. The survey's value is that the two worst
rows are **not** the ones Part I was written about.

## The dishonest default

`Approximations` is the mechanism that hands an obligation back to a more
faithful engine: `open_for(models_faithfully)` returns obligations closed under
an approximation the caller does not make. Under-declaring means the better
engine never sees the obligation again. That asymmetry is why the rule is *when
in doubt, declare*.

The API inverts it. Measured 2026-10-26:

* **19** publish sites across the engines; **14** call `publish()`, which
  hardcodes `Approximations::EXACT`. Five call `publish_with`.
* **9** sites name an approximation flag at all.
* `open_for` has exactly **one** non-test consumer: `smt-bmc`, three sites.

So silence declares perfect faithfulness, and silence is the common case. This
is the `Option`-versus-total mistake that `contract_for` exists to fix,
reproduced one layer up: the default answer is the *strongest* claim rather than
the most conservative one.

The concrete suspect: `ai.rs` publishes `Status::Discharged` through
`publish()`, so `EXACT`, while `interval.rs` carries 80 lines of float-interval
handling and names `Approximations` nowhere. If outward-rounded float intervals
are faithful then the declaration is right — but nobody has ever established
that, and if it is wrong the BMC's FPA pass is silently never offered those
obligations. That pass exists precisely to reconsider them (#27).

Two fixes, independent:

1. **Invert the default.** `publish()` declares the widest plausible set for the
   producer, and an engine that wants `EXACT` says so. Over-declaring costs time
   and is measurable; under-declaring loses answers silently.
2. **Check honesty mechanically.** For each published `Discharged`, intersect
   the IR constructs reachable from the obligation with the flags declared. A
   float op in the body under an `EXACT` declaration is a candidate defect. This
   is static, cheap, and needs no corpus run.

## The untested substrate

`Cpa` is the shared fixpoint for the interval AI and for CEGAR's predicate
domain — the substrate under the portfolio's only two over-approximating
state-space engines.

| File | Lines | Tests |
|---|---|---|
| `ajave-core/src/cpa.rs` | 227 | **0** |
| `ajave-engines/src/interval.rs` | 2131 | **0** |
| `ajave-engines/src/predicate.rs` | 495 | **0** |

Two `Lattice` impls, no law checks of any kind. `stop_sep`'s correctness rests
entirely on those laws, and the comment at `cpa.rs:57` records what happens when
a subtlety there goes unnoticed: a variable absent from a state's map reads as
Top, the first (empty, therefore Top-everywhere) state subsumed states at
unrelated program points, exploration was truncated before the obligation, and
`assert2` became **a false TRUE**.

`CLAUDE.md` requires that a comment stating a soundness argument have a test
named after it. For the substrate carrying the most −16-exposed engines in the
tree, that requirement is unmet — and this is the cheapest gap in the census to
close, because lattice laws are property tests over generated intervals, not
benchmark canaries. They generalise in exactly the way Part I asks for, and they
need no corpus time at all.

## What the survey changes

Part I ranked artifact monotonicity as the important check. On the evidence
here the order is:

1. ~~**Lattice and widening laws**~~ — **done 2026-10-26.** The CPA substrate
   is split into `AbstractDomain` + `MergePolicy`, the laws ship as
   `fixpoint::laws` so a later domain inherits them, and the merge contract is
   `debug_assert`ed at the call site. 30 tests where there were none; see
   `docs/plans/cpa-to-domain-and-policy.md`.
2. **Honest-approximation audit** — static, and it settles whether the single
   consumer of `open_for` is being starved.
3. **Every asker has a consumer** (#40) and **every interest has a producer**
   (#37) — both static, both would have caught a defect committed this month.
4. **Artifact monotonicity** — the most general check, and the only one that
   needs corpus runs. Worth building, worth building last.

### What the first one actually found

Not a broken law. The substrate's *configuration surface* was the defect:
`stop` and `prec` were never overridden by any of the three implementors, and
`prec` — documented as "the hook CEGAR lives in" — did nothing, while CEGAR
refined from outside the loop all along. None of the three configurations the
module header advertised was what any implementor did.

That is worth recording because it is a **different shape** from the five
live-but-vacuous defects that motivated Part I. Those were artifacts nobody
consumed. This was a *parameter nobody varied* — the same vacuity one level
down, in a trait rather than a message. The check that catches it is the same
census: enumerate the implementors, intersect with what the interface offers,
and fail on a configuration point with no variation.

So the mechanical check list gains a fifth entry, and it is cheap:

### 5. Every configuration point is varied — static

For each trait with defaulted methods, count overrides across the workspace. A
defaulted method no implementor overrides is not a configuration point; it is a
decision wearing a parameter's clothes, and its doc comment is unverified by
construction. Delete it or document it as fixed.
