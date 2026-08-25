# Milestones and issues

Grounded in what's actually in the repo today, not the original estimate —
see `docs/strategies/README.md` for current strategy status. Frontend work
originally budgeted for Aug–Nov 2026 is substantially done already (full
opcode coverage, exception tables, arrays, objects, two working engines, JVM
replay certification), which compresses M0–M1 below and buys room for a
stretch goal before the first submission deadline.

Every issue line is `- [ ] Title \`labels\``, ready to paste into
`gh issue create` or the script in `scripts/create-milestones.py`, which
does that automatically from this file's structure. Label taxonomy is
defined in `.github/labels.yml`; see `docs/sdlc.md` for the family
definitions if a label here is unfamiliar.

**Calendar anchor:** SV-COMP benchmark contributions are due ~September,
tool archive submission ~late November/December, results the following
April. Today is 2026-07-29. First realistic submission is **SV-COMP 2027**
(results April 2027); the competitive push targets **SV-COMP 2028**.

---

## M0 — Competition plumbing & Java 8 validation

**Target: 2026-08-15** (2–3 weeks)

**Why first, regardless of verifier power:** none of the engine work below
scores a single point without a working BenchExec tool-info module, an
fm-tools registration, and a witness the validator track can check. This is
pure infrastructure, but it's on the critical path for *every* later
milestone, and it's the cheapest thing to get wrong silently (a tool-info
module bug means every task times out or errors, indistinguishable from the
verifier being bad). Java 8 validation lands here too: getting bytecode
version assumptions wrong is exactly the kind of thing that passes locally
and fails on the actual competition corpus.

**Exit criteria:** `ajave` can be invoked exactly as BenchExec would invoke
it, against a real (if small) slice of `sv-benchmarks`, and produce correct
verdicts under a Java 8 toolchain, in CI, unattended.

- [ ] Write the BenchExec tool-info Python module (`ajave.py`) `area:benchexec` `priority:p1-blocker`
- [ ] Register `ajave` in `fm-tools` (metadata, archive DOI placeholder, jury rep) `area:benchexec`
- [ ] `scripts/check-java8.sh`: validate classfile major version 52 end-to-end `area:cli` `java8-compat` — **done**
- [ ] `.github/workflows/java8.yml`: CI signal separate from general build health `type:ci` `java8-compat` — **done**
- [ ] `.github/workflows/corpus.yml`: scheduled soundness regression against `jbmc-regression` `type:ci` `priority:p0-soundness` — **done**
- [ ] Package `ajave` as a competition archive (static binary or vendored toolchain, per fm-tools archive format) `area:benchexec`
- [ ] Document the BenchExec invocation contract (exit codes, stdout format, `--trace`/`--ir` are debug-only and must not appear in competition mode) `type:docs` `area:cli`
- [ ] Dry-run against a 50-task local BenchExec invocation, compare wall-clock and memory against the 15s/2GB-ish per-task competition limits `type:test`

---

## M1 — Frontend hardening & real heap modelling

**Target: 2026-09-15** (4–5 weeks — compressed from the original ~35-day
estimate since most of it landed already)

**Status of what's already done:** full opcode coverage, exception-table
routing, arrays, objects, `LineNumberTable`, class hierarchy/`is_subtype`,
standard-library modelling table. What's left is the part that actually
bit during this session: the concrete engine has **no heap content
tracking**, which doesn't just miss bugs (acceptable Under-approximation
incompleteness) but can steer branch decisions down the wrong path via the
`Unknown -> false` default (see `docs/strategies/concrete.md`'s
incompleteness section, and the postmortem in `docs/sdlc.md`).

**Exit criteria:** the concrete engine and the interval domain both track
concrete/abstract array and field contents for the common case (fixed-size
arrays, simple object graphs), and the `Unknown -> false` branch bias is
gone for anything the heap model actually covers.

- [ ] Design doc: heap model shape (flat map vs. field-sensitive graph) before any code — this is core-crate-adjacent, treat like a new strategy `needs-design-doc` `area:core`
- [ ] Concrete engine: track array contents (fixed-size, no aliasing needed for the common case) `area:engines` `tier:2-falsify` `direction:under`
- [ ] Concrete engine: track object field contents for `New`-allocated objects `area:engines` `tier:2-falsify` `direction:under`
- [ ] Interval domain: extend `IState` with a heap component (product with a simple points-to-lite map) `area:engines` `tier:1-ai` `direction:over`
- [ ] `invokedynamic` support (lambdas, Java 9+ string concat) — only 4/176 tasks in `jbmc-regression` need this, so low priority but a real gap `area:frontend` `priority:p3-later`
- [ ] Interprocedural call resolution: wire `Program::devirtualise` into an actual multi-method lift instead of diverging on any live call `area:frontend` `priority:p2-normal`
- [ ] Regression: `scripts/run-corpus.sh` correct-count should rise (was 40/176 before this milestone) with zero new wrong verdicts `type:test`

---

## M2 — Witness I/O

**Target: 2026-10-15** (3–4 weeks)

**Why this is more urgent than it looks:** `ajave` currently certifies its
own `FALSE` results by replaying them internally (`JvmReplay`) and never
writes an actual witness file. That's necessary but not sufficient —
SV-COMP's scoring depends on an *external* witness validator checking a
witness the tool emits to disk. Right now there is nothing to check. An
unconfirmed result scores a fraction of, or none of, the points a confirmed
one does; this milestone is the difference between "correct" and "scored".

**Exit criteria:** every `FALSE` produces a violation witness, every `TRUE`
produces a correctness witness, both in a format `witnesslint`/the
competition's validator track accepts, and both are exercised in CI against
an actual validator rather than just schema-checked.

- [ ] Violation witness emission (format 2.0/GraphML, nondet sequence -> witness automaton) `area:witness` `direction:exact`
- [ ] Correctness witness emission for `Discharged` obligations (the interval invariant, in the format's invariant annotation) `area:witness` `direction:exact`
- [ ] Wire witness output path into the BenchExec tool-info module from M0 `area:benchexec` `area:witness`
- [ ] CI job: run an actual witness validator (not just our own `JvmReplay`) against emitted witnesses `type:ci` `area:witness`
- [ ] Update `docs/strategies/concrete.md` / `interval.md`: witness emission is part of "how it's certified" now, not just internal replay `type:docs`

---

## M3 — SV-COMP 2027 submission

**Target: 2026-12-01** (archive deadline)

**Goal:** a correct, honest entry. Not competitive on TRUE yet — that's M4
onward — but never wrong, and every result validated. Beating JLiSA (third
place, 2026) on the strength of the exception-property coverage already
built would be a good outcome; landing third is the realistic target.

**Exit criteria:** submitted archive, passes fm-tools CI validation, appears
in the 2027 results table with zero incorrect results.

- [ ] Contribute new benchmarks to `sv-benchmarks` if any gaps found during M0–M2 testing (this is worth double-checking: an under-represented task shape is free score for everyone including us) `area:benchexec` `priority:p3-later`
- [ ] Final archive build + fm-tools metadata freeze `area:benchexec` `priority:p1-blocker`
- [ ] Post-results retrospective: where did `UNKNOWN` cost the most points? Feeds directly into M4/M5 prioritisation `type:docs`

---

## M4 — k-induction + invariant injection

**Target: 2027-04-01** (the "real work year" starts here)

**Why this is next:** highest-leverage combination identified in
`docs/architecture.md` §6 (combination A) and, as of M0–M3, still not done
by any Java-track tool. The interval domain already produces invariants
(`ProofKind::Invariant`); this milestone is what makes k-induction's step
case consume them instead of stalling on any property that isn't
k-inductive for a small k on its own.

**Exit criteria:** `docs/strategies/kinduction.md` exists (written before
the code, per the strategy-doc workflow), a working `Engine` is registered,
and the corpus regression shows new `TRUE`s on tasks the interval domain
alone couldn't close (unbounded loops with an inductive invariant).

- [ ] `docs/strategies/kinduction.md`: direction, soundness argument, what it consumes from the blackboard `needs-design-doc` `area:engines`
- [ ] Base case: BMC to depth k (real solver-backed this time, not the enumerate-don't-solve concrete engine) `area:engines` `tier:3-kinduction` `direction:under`
- [ ] Step case: k consecutive states assumed, prove k+1, strengthened by interval invariants pulled from the blackboard `area:engines` `tier:3-kinduction` `direction:over`
- [ ] `InductiveCheck` certifier: currently stubbed (`CertResult::Inconclusive` unconditionally) — this milestone is what makes it real `area:core` `direction:exact`
- [ ] SMT backend behind a trait (`docs/architecture.md`'s "keep the solver behind a trait so you can swap" plan) — Bitwuzla first `area:core` `type:feature`
- [ ] Regression: unbounded-loop tasks that were `UNKNOWN` move to correct `TRUE` `type:test`

---

## M5 — Predicate abstraction + CEGAR

**Target: 2027-08-01**

**Why this order:** consumes the concrete engine's `AbstractTrace` artifacts
(already a first-class blackboard type — `core::artifact::AbstractTrace` —
just nothing publishes to it yet). Combination B in the architecture doc.
Prioritised after k-induction because it's more implementation effort for a
narrower class of properties.

- [ ] `docs/strategies/cegar.md` `needs-design-doc` `area:engines`
- [ ] Concrete/BMC engines publish `AbstractTrace` on an infeasible path instead of discarding it `area:engines` `tier:2-falsify`
- [ ] Craig interpolation over the infeasible trace -> predicates `area:engines` `tier:4-cegar` `direction:over`
- [ ] Predicate-abstraction `Cpa` impl, precision refined via `Cpa::prec` `area:core` `area:engines` `tier:4-cegar` `direction:over`
- [ ] Regression + comparative benchmark against Ultimate Automizer's public results on shared task shapes `type:test`

---

## M6 — CHC escape hatch

**Target: 2027-11-01**

- [ ] `docs/strategies/chc.md` `needs-design-doc` `area:engines`
- [ ] IR -> Horn clause encoding for a single obligation `area:engines` `tier:5-chc` `direction:over`
- [ ] External solver integration (Golem or Eldarica), behind the same solver trait as M4 `area:core` `type:feature`
- [ ] Regression: tasks neither AI nor k-induction close, that CHC does `type:test`

---

## M7 — SV-COMP 2028: the competitive push

**Target: 2028-04-01 (results)**

- [ ] Portfolio scheduling tuning: budget allocation across tiers per `Orchestrator` phase, informed by two full seasons of corpus data `area:core` `type:feature`
- [ ] Performance pass: profile against the full corpus, not just correctness — competition has hard per-task time/memory limits `type:feature` `priority:p1-blocker`
- [ ] Conditional model checking (`Artifact::Residual`, combination C) if time allows — the least-exploited idea in the competition and still unimplemented here `area:core` `priority:p3-later`
- [ ] Final push: aim for outright win on `Java.Overall`, or a clear, documented second place with a concrete path to first `type:docs`

---

## Cross-cutting, not tied to one milestone

These apply throughout and get their own recurring issues rather than a
single checkbox:

- [ ] Every corpus regression failure opens a `priority:p0-soundness` issue automatically (`.github/workflows/corpus.yml`) — **done**
- [ ] Every new `Engine`/`Cpa` gets a `docs/strategies/*.md` before merge, enforced by CI (`scripts/check-strategy-docs.sh`) — **done**
- [ ] Every new crate dependency edge is checked against `docs/crates.md` (`scripts/check-boundaries.sh`) — **done**
- [ ] Java 8 validation re-runs on any change touching the frontend or CLI (`.github/workflows/java8.yml`) — **done**
