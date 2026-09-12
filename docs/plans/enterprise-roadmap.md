# From SV-COMP verifier to something an enterprise can use

Status: proposal. Written 2026-09-10, grounded in measurements taken that day.

The premise is that these are not competing goals. Every change below is
*additive to the path SV-COMP already exercises*, and the two phases with the
largest expected enterprise payoff are also the two that attack the measured
causes of our corpus timeouts. Where a phase genuinely trades score for
generality, it says so and carries a stop rule.

## The governing rule

**Summaries and specs replace *havocs*, never inlining.**

When the BMC cannot inline — depth exceeded, no body, virtual call unresolved —
today's fallback is a havoc, which taints the path, and taint is a whole-run
discharge gate. Every task that inlines today must still inline; only the paths
that are already losing get new machinery.

This is the same construction that made the round loop measurable: round 0
scheduled exactly as before, deepening only on entry 2+. It is what lets a phase
be *predicted to measure as zero or better*, which is the only way to tell a
regression from noise. `CLAUDE.md` records the counter-example: loosening
`all_calls_resolved` looked like +22 on no-runtime-exception and was 9 wrong
TRUEs on valid-assert.

## Invariants that hold at every phase

Non-negotiable, checked before a phase is called done:

1. **Zero wrong answers.** A single wrong TRUE stops the phase and reverts it.
   The corpus currently carries one wrong verdict and it is a benchmark mislabel.
2. **Both properties, idle, reproduced.** Valid-assert and no-runtime-exception
   consume different obligation kinds; a guard sound for one can be vacuous for
   the other. A number from a loaded machine is not evidence.
3. **The held-out probe set does not regress.** `docs/plans/real-world-probe-set.md`.
   Twelve programs, JVM-confirmed, nothing in them scores — which is what makes
   them the only instrument here immune to corpus overfitting.
4. **Cross-engine harnesses green**: `metamorphic.py`, `engine_ablation.py`, the
   CHC encoder conformance tests.
5. **Every new artifact kind has a named consumer before its producer is
   written.** Four artifact kinds sat unused for months for want of this rule.

---

## Phase 0 — repair the instruments (days)

Nothing below is measurable until these land, and all three are already known.

- **Bisect the three stale smoke failures (#35).** `bench.py --set smoke --check`
  currently fails on `AbstractSerializationStreamReader_false`, `SatAckermann01`
  and `SatFibonacci01` against a baseline recorded at `08b1b5b`. The pre-commit
  gate is therefore not trustworthy. Do not re-baseline: that bakes them in.
- **Fix `tools/cleanup.sh`** to catch benchmark runners outside the repo tree. It
  reported "cleaned" while a leaked runner held a task for ten hours and
  contaminated a full valid-assert run.
- **Pin the budget in `just score-all`.** It runs at `bench.py`'s 300s default
  while every recorded score is quoted at 60. "The number to quote" and the
  number the command produces are different numbers.

**Exit:** smoke green, one command reproduces a quotable score.

---

## Phase 1 — per-obligation taint (weeks)

`has_tainted_paths` is a **whole-run boolean** consulted in `can_discharge`. One
unmodelled call therefore poisons every obligation in the program — that is how
a single missing string-array model blocked all 12 securibench tasks.

Convert it to a per-obligation fact, exactly as `all_paths_complete` was
converted via CFG reachability from truncation points (#20). An unmodelled call
should cost the obligations that *depend* on it and nothing else.

Independent of everything below, and the highest ratio of value to risk in this
document. `Completeness::discharge_blocker` exists because "which flag is set"
and "which condition refuses" are different questions.

**Predicted:** positive on both properties. **Stop if:** any wrong answer.

---

## Phase 2 — certified findings (weeks, parallel, zero analysis risk)

Changes no analysis, so it cannot move the score.

Emit **a compiling JUnit test that reproduces the violation**, built from the
witness JVM replay already confirmed. Add SARIF so findings land in normal code
scanning. The pitch becomes "here is a failing test, run it yourself", which no
unsound analyser can offer.

This is the differentiator. Enterprise static analysis gets switched off because
of false positives; replay certification is already refuting 76 valid-assert
witnesses that most tools would have shipped. Today that is a scoring mechanism.
It should be the product.

**Exit:** a violation on any corpus task produces a test that fails on a real
JVM and passes when the bug is fixed.

---

## Phase 3 — summaries replace havocs (months)

The load-bearing change, and the one the governing rule exists for.

- A `Summary { method, pre, post }` artifact carrying its preconditions
  **explicitly**. `objects14` was a wrong TRUE precisely because a check inside a
  callee narrowed a summary's domain into an *unstated* precondition — accidental
  abduction, unsoundly.
- Producer: lazy, only for methods reached and not inlinable.
- Consumer named first: the BMC, at the sites where it currently havocs. CHC's
  `mN_summary(params…, ret)` is a second consumer that already exists.
- Preconditions discharged at every call site, or the obligation stays open.
  `Contract::preconditions_all_seeded()` already encodes this question for
  library methods.
- **Vacuity check.** A precondition strong enough to make the method
  uncallable "verifies" trivially. Refuse to publish a spec whose precondition is
  unsatisfiable — this codebase has been burned by vacuous proofs before.

**Why it should raise the SV-COMP score, not merely preserve it:** inlining is
the measured cost driver. Sampled tasks truncate because `handle_branch_fork`
exhausts `MAX_FORKS` at 500 while `max_depth` is nowhere near. Summaries make
cost linear in methods rather than exponential in call depth.

**Predicted:** non-negative on both. **Stop if:** negative on either after a
reproduced, idle-gated run.

---

## Phase 4 — a derived JDK spec database (months)

The phase that kills the cliff, and the reason library-heavy code is currently
unanalysable.

`contract_of` is hand-written, so coverage is a cliff rather than a slope —
`Integer.equals` on two boxed ints has a specified result and is unmodelled, and
our own `jvm-boxing` benchmarks are unproven because of it. Instead: lift real
JDK bytecode **offline**, run the same sound engines over it, and ship the
resulting summaries as a data file keyed on `(class, name, desc, bytecode-hash)`.

The cost profile is what makes this SV-COMP-viable rather than a distraction. A
warm cache is useless under competition rules, which run every task in a fresh
process — but a *precomputed, shipped* database is a one-time offline cost that
every task benefits from at zero runtime price. It is JBMC's "analyse the JDK
every time" turned into "analyse it once and ship the answer".

Rules carried over unchanged, because a derived spec is exactly as much a
soundness commitment as a typed one:

- Hand-written contracts remain the authority where they exist. They are often
  more precise: they say *when* a method throws, not merely that it might.
- Every derived entry is validated against a real JVM with adversarial inputs,
  the standard `validate_jdk_allowlist.py` already applies.
- Keyed on the full descriptor. `Integer.valueOf(int)` is total;
  `Integer.valueOf(String)` throws.

**Predicted:** positive on both, concentrated in securibench and `argv-tasks`.

---

## Phase 5 — open the world (quarters)

Only now, and only if Phases 3 and 4 measured as predicted.

Bi-abduction: walking a method body, a dereference with nothing known about the
receiver *abduces* the missing precondition into the method's own spec. Specs
derived bottom-up, no entry point required — the technique behind Infer's scale.

Note the fork. Infer uses it as a bug finder and drops the discharge obligation,
which is why it has false positives. The zero-wrong-answer discipline forces the
verification reading: discharge the precondition at each call site, and report
UNKNOWN honestly where you cannot. More work, and it is the whole differentiator.

Scope discipline: value-level abduction first (nullness, ranges over
parameters), then points-to so `x.f` abduces `x ≠ null` — which is open-world NPE
analysis, the most commercially valuable Java property. **Skip full
separation-logic shapes.** Infer's own trajectory moved away from shape analysis
toward a lighter abstract-address domain, because shapes cost enormously and pay
on a narrow class.

What changes for SV-COMP is only the CLI layer: entry-point selection,
obligation seeding scope, output format. A flag, not a fork. Engines, IR,
direction discipline and certification are identical in both modes.

---

## What is deliberately not on this roadmap

**Chasing the SV-COMP score directly.** This session added roughly 136 points and
the most useful thing it produced was twelve programs that score nothing. The
collection fix took a program from unprovable to proved and moved the corpus by
exactly zero. The score is a gate, not a goal.

**Competing with CodeQL on breadth.** Millions of lines with unsound, useful
results is a different product. The bet here is depth and trust: proofs a bounded
checker cannot make, findings certified on a real JVM, and concurrency — 76
benchmarks and a DPOR explorer against an SV-COMP category that does not exist,
which looks like dead weight by the score and is the clearest enterprise
differentiator in the tree.

## Kill criteria

Abandon a phase, and record it as `status:explored` with the measurement, when:

- it produces a wrong answer that is not a benchmark mislabel;
- it is negative on either property after a reproduced, idle-gated run;
- it regresses the held-out probe set;
- its benefit requires a constant fitted by raising it until benchmarks pass.
