# Four options for getting more out of the cooperating engines

Implementation plans. Proposal and ranking: the "More From Cooperating Engines"
artifact. Status: A implemented, B implemented in its in-loop form, C and D as
noted below.

Each lands behind its own flag, defaulting **off**, so one build benchmarks all
four individually. That is the opposite of the three-levers experiment, where
all were on by default because they were expected to interact; these four are
independent, so individual measurement is the cheaper design.

```
AJAVE_AI_ANSWERS=1       # A — interval-ai answers Bounds queries
AJAVE_REFUTE_ARTIFACT=1  # B — an unreplayable witness becomes a published fact
AJAVE_RESIDUAL=1         # C — the BMC publishes what it did not cover
AJAVE_NULL_QUERIES=1     # D — nullness as a question kind
```

---

## A — interval-ai answers `Bounds` queries

**The gap.** `Want::Bounds` asks the range of a term. `interval-ai` is an
interval abstract interpreter that discharges on 119 of 172 sampled tasks and
has never answered a question. `ranges` answers `Bounds` from the Javadoc, so it
can only speak about library calls with a published contract — never about a
loop counter in the program under analysis, which is what the askers need.

**Producer.** In `ai.rs::step`, after the fixpoint:

1. Read `bb.unanswered()`, keep `want == Want::Bounds`.
2. For each, the query's `at.method` and `about` must name a `VarId` in a method
   this run analysed, at a block the run reached.
3. Join the intervals across reached states at that `(block, var)` — the same
   join `publish_interval_hints` already performs, extracted so both use it.
4. Publish `Lemma { answer: Answer::Bounds { lo, hi } }` when the interval is
   narrower than top. A top interval is published as `Answer::Unknown`, which is
   worth saying: it stops the scheduler re-asking.

**Consumers already exist and need no change.** `smt-bmc` consumes
`Answer::Bounds` via `known_bounds` and applies it with `assume_known_bound`;
`Interest::LEMMA` re-enters it when the answer lands. `cegar` posts queries as
of the three-levers work.

**Two conditions carried over from the existing hint channel, neither relaxable.**

* **Only a complete fixpoint may answer.** A truncated `reached` set
  *under*-approximates reachable states, so a join over it can yield an interval
  that is too narrow — unsound, and the wrong-TRUE direction. `ai.rs` already
  gates hints on `complete` and that gate is load-bearing.
* **Only `Over`.** `Answer::Bounds` is universal; the blackboard enforces the
  direction at publish.

**`Interest` must gain `QUERY`.** Otherwise a question posted after the AI's
only step never wakes it. This is the mechanism that #37 shows is easy to get
wrong: a declared interest in a kind nobody produces, or a missing interest in
the kind that matters.

**Falsified if** the complete-fixpoint gate means it can almost never answer.
The pre-check is free here because the implementation emits it: a log line
counting queries seen, queries answerable, and queries declined for
incompleteness.

---

## B — an unreplayable witness becomes a published fact

**The gap.** 76 valid-assert witnesses per run are refuted by JVM replay; 56 of
those carry an all-zero nondet sequence. The information is discarded.

**The architectural problem, stated plainly.** JVM replay happens in `main.rs`
*after* `orchestrator.run()` returns, so a refutation cannot reach the engines
during the loop. Feeding post-replay refutations back needs either replay inside
the loop or a second orchestrator pass — both larger than this experiment.

**What is implementable now, and is genuinely in-loop.** The BMC already detects
a witness that *cannot* replay before any JVM runs: `unreplayable` is
`path_tainted && witness.nondet_sequence.is_empty()` — a violation with no input
to blame, derived from a havoced value. It withholds the violation and says
nothing else.

That self-refutation becomes an artifact. The obligation is left open, as now,
plus a published record that the *reason* it is open is a tainted path with no
witness — which names the taint source as the thing to fix.

**Consumer.** `Blackboard::contested()` already pairs an Over proof with an Under
flag and nothing reads it. The honest first consumer is the orchestrator's
end-of-run report, which turns the 56-task population into a named, per-task
diagnosis rather than a corpus-wide statistic.

**Explicitly not claimed.** A refutation says the *witness* was wrong, never that
the obligation is safe. An engine treating it as a discharge would produce wrong
TRUEs at scale. The artifact is `Under`-flavoured information about one
execution.

**Falsified if** the refutations cluster on obligations a different input really
does violate, so nothing downstream can use them. The all-zero figure is the
warning: a witness with no inputs may carry no usable predicate.

---

## C — `Residual`: publish what was not covered

**The gap.** `Artifact::Residual(Condition)` has zero producers and zero
consumers. `ExploreCtx::cut_points` already records exactly where exploration
stopped, as `(MethodKey, BlockId)` pairs, and `obligations_at_risk` already
turns that into the affected obligation set.

**Producer** is therefore nearly free: publish `Condition { covered, note }`
where `covered` is the complement of the cut set.

**The consumer is the whole problem, and this plan does not pretend otherwise.**
No engine currently knows how to analyse "this program restricted to these
paths". CHC would need clause generation scoped to a block subset; k-induction
would need a base case starting from a residual state. Building a producer with
a consumer that merely *logs* the artifact would be precisely the live-but-inert
defect this session documented four times — the rule in `CLAUDE.md` is that an
artifact kind needs a real consumer before its producer is written.

**So C ships as the producer plus a diagnostic consumer only, flagged, and is
not claimed as a cooperation win.** Its value in this round is measuring how
often a residual is non-trivial and how large it is — which is the data needed
to decide whether a real consumer is worth building. Conditional model checking
(Beyer et al. 2012) is the published design to follow if it is.

**Falsified if** residuals are nearly always the whole program, in which case
there is nothing useful to hand on.

---

## D — nullness as a question kind

**The gap.** `Want` has `Bounds`, `Valid`, `Satisfiable` — all about values.
No-runtime-exception is 1,184 of the 2,056 total score and its content is
nullness, which cannot be asked. So engines route around it: `is_nonnull_static`
is a hardcoded list in `interval.rs`, constructor-parameter nullness is a lifter
special case, `eval_nullness` falls back to a program-level check.

**Implementation.**

1. `Want::NonNull` and `Answer::NonNull`/`MaybeNull`. `NonNull` is universal, so
   `Answer::is_universal` must return true for it — the publish rule turns on
   exactly that.
2. Asker: `smt-bmc`, where a havoced call returns a reference it must assume may
   be null.
3. Answerers, in order of safety: the `Contract` database, which already records
   `Precondition::NonNull` positions and non-null returns; then allocation facts
   (JLS 15.9.4 — `new` is never null, a fact no engine publishes); then the AI's
   nullness lattice.

**The soundness bar is the highest of the four and is already written down.** A
wrong "non-null" discharges a NullDeref that can really fire: −16. `CLAUDE.md`
records the specific trap — `System.out` looks like a non-null `static final` and
is mutable through `System.setOut(null)`, so it does not qualify. An
`Answer::NonNull` needs the JDK-allowlist discipline: justified from the
contract, keyed on the full signature, validated against a real JVM with
adversarial inputs.

**Falsified if** the answerable facts are exactly the ones already special-cased,
making the general mechanism pure cost.

---

## Measurement protocol

One build, each flag measured alone, both properties, 60s, idle-gated:

| run | flags |
|---|---|
| baseline | none |
| A | `AJAVE_AI_ANSWERS=1` |
| B | `AJAVE_REFUTE_ARTIFACT=1` |
| C | `AJAVE_RESIDUAL=1` |
| D | `AJAVE_NULL_QUERIES=1` |

A default-off flag cannot regress the default build, so the smoke gate protects
the baseline and each flag is judged only against it.

Stop rules as ever: any wrong answer that is not the `ReverseInterpolator`
mislabel reverts that option; an option inert on both properties is filed
`status:explored` and removed rather than left behind a flag.

---

# Heap options (2026-10-27), from `heap-full-implementation.md`

Recorded here rather than in `CLAUDE.md`, which says not to restate a flag's
default there because that is the claim that rots.

| flag | default | what it does | measured |
|---|---|---|---|
| `AJAVE_SITE_FIELDS` | **on** (`=0` ablates) | B2/B3: site-indexed field cells and array element intervals in `interval` | smoke neutral; see below |
| `AJAVE_CHC_HEAP_SUMMARY` | **off** (`=1` enables) | C1: field footprint threaded through CHC summary relations | smoke **neutral**, 171 vs 171, 0 WRONG |
| `AJAVE_CHC_QGEN` | **on** (`=0` ablates) | D1: `fp.spacer.q3.use_qgen` + `fp.spacer.ground_pobs=false` | smoke **173 vs 171**, 134 correct vs 133, 0 WRONG either way, 319s vs 320s |

## What each is for, and what the measurement does and does not say

**B2/B3** refine the flat field abstraction, which keys one cell per field with
the receiver ignored and is exact only for a class with a single allocation
site. Site cells are a *refinement*: `flat(f)` meet `cell(s, f)`, with a write
through an unknown receiver marking the field escaped so every read falls back
to the flat cell. `AJAVE_SITE_FIELDS=0` restores the pre-B2 behaviour exactly,
and was used to establish that the three tasks lost to #101 are **not**
attributable to this work — identical either way.

**C1** is neutral on smoke and demonstrably capable with CHC isolated:
`engine-chc/FieldWrittenInACalleeIsVisibleToTheCaller` and
`ACalleeThatWritesNothingInvalidatesNothing` are both UNKNOWN without it and
TRUE with it. Neutral-on-smoke is a weak claim — 156 tasks against the corpus's
1784 — and the arity risk it is restricted against (`MAX_SUMMARY_FIELDS`) is
precisely the risk a small set cannot see. It stays off until a corpus run.

**D1** required the array-store fix in 2d51c22 before it did anything at all.
Before that fix Spacer reported the error *reachable* on the array-fill shape,
and quantified generalisation cannot help when the abstraction genuinely admits
a counterexample. After it,
`heap/EveryElementNonNullAfterAFillLoop` is UNKNOWN with the flag off and TRUE
with it on, in CHC-only and full-portfolio alike. That benchmark is now the
smoke canary that prices the flag — the earlier three-arm run showed qgen
neutral only because its single beneficiary was not in the set, which is worth
recording as a way to measure a flag and learn nothing.

Priced with the canary present: **173 against 171, 134 correct against 133, 0
wrong either way, 319s against 320s and the same timeout count.** The expected
cost was timeouts, since a quantified search is a different and usually slower
search, and on this set there is none. So it is **on by default**.

Two caveats belong next to that number. It is 157 tasks, and the gain is
exactly the one task that needs a quantified array invariant — nothing else
moved, which is as consistent with "no other task in this set needs it" as with
"it is free". And it does nothing at all without the array-store fix it shipped
beside, so the flag's value is not separable from that fix on any set where
both are present.
