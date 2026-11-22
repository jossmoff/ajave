# Roadmap, November 2026: where the points actually are

Written 2026-11-22, after a research pass over the SV-COMP 2026 competition
report, the current Java field, and the invariant-inference literature.

This document exists because the last four capability directions were chosen by
reading our own blocker census, and three of them measured **exactly zero**
(raised unroll cap: 0 of 69 tasks; suppressed refuted witnesses: 0 of 79;
forced FPA: 1 of 8, and −62 corpus-wide). The common cause is now understood and
is recorded in `changes.md`: every bucket in `tools/blocker_census.py` is named
after what *blocks* a verdict, and removing the blocker leaves the obligation
unprovable underneath.

So this roadmap is built the other way round — from **what the competition
scores**, outward to the capabilities that move that number. The single largest
finding is that our headline number is not the number the competition computes,
and the gap is not small.

---

## Part 0 — What the competition actually rewards

Sources: Beyer & Strejček, *Evaluating Software Verifiers for C, Java, and
SV-LIB (Report on SV-COMP 2026)*, TACAS 2026; and the SV-COMP 2026 rules.

### 0.1 The scoring arithmetic, exactly

| Result | Points | Condition |
|---|---|---|
| True correct | **+2** | correctness witness confirmed **or not required** |
| True incorrect | **−32** | wrong proof |
| False correct | **+1** | **violation witness was confirmed** |
| False incorrect | **−16** | false alarm |
| correct-unconfirmed | **0** | agrees with expected result, witness required and not confirmed |

`Java.Overall` in SV-COMP 2026: **1731 tasks, max score 2821**. Those two
numbers determine the shape of the whole problem. With `T` true tasks and `F`
false tasks:

```
2T + F = 2821
 T + F = 1731
→ T = 1090   F = 641
```

So **2180 of the 2821 available points (77%) are in TRUE answers, and 641
(23%) are in FALSE answers.**

### 0.2 Witness requirements for Java — Table 1 of the report

| Base category | Correctness witnesses | Violation witnesses |
|---|---|---|
| `Java.valid-assert.` | **1.0 demo** | **1.0** |
| `Java.no-runtime-exception.` | **– (unsupported)** | **1.0** |

Two consequences, and they point in opposite directions:

1. **Our TRUE answers need no witness at all.** The report: "If there is no
   supported witness format or the only supported witness format is in demo
   mode, the witness generation is not required." `valid-assert` correctness
   witnesses are 1.0 *demo* ("the results of the validation do not play any
   role in the score computation"), and `no-runtime-exception` correctness
   witnesses are unsupported. So every correct TRUE is a clean +2. **All 2180
   TRUE points are collectible with the verifier we already have.**

2. **Our FALSE answers need a confirmed format-1.0 GraphML violation
   witness.** `crates/ajave-core/src/witness.rs` line 1 reads "SV-COMP witness
   format 2.0 emitter." We emit 2.0 YAML only. Every correct FALSE therefore
   scores **0**, not +1. This is issue #127, and it is now confirmed against
   the official report rather than inferred.

### 0.3 The trap that makes a naive fix worse than nothing

From the report's workflow section:

> A witness in format 1.0 is written to file `witness.graphml`. A witness in
> format 2.0 or 2.1 is written to file `witness.yml`. **If a verifier generates
> both files, `witness.graphml` is ignored** in the context of the verification
> track.

and

> If any of the check[s] fail and a witness was required, the verification task
> is seen as **unsolved** by the verifier.

So if we add a GraphML emitter and keep writing `witness.yml`, the GraphML is
ignored, the witness considered is 2.0, 2.0 is not a supported violation format
for Java, the check fails, and the task is **unsolved**. The fix is therefore
"emit 1.0 **and stop emitting 2.0 for Java**", not "also emit 1.0". Getting
this backwards converts a 0 into a 0 while feeling like progress — the exact
shape `docs/measurement-validity.md` is about.

Also worth knowing: **there is no witness linter for Java** ("We skip the last
check in case of Java as there is no witness linter available"), so a
malformed witness is not caught before validation — it just fails to confirm.

### 0.4 Who we are actually competing against

`Java.Overall`, SV-COMP 2026, 1731 tasks, max 2821:

| # | Verifier | Score | Solved | Unconfirmed | False alarms | Wrong proofs |
|---|---|---|---|---|---|---|
| 1 | JBMC | 1561 | 1033 | **315** | 1 | **13** |
| 2 | GDart | 1470 | 920 | 107 | 1 | 1 |
| 3 | JLiSA (new) | 1311 | 617 | 1 | 0 | 0 |
| — | MLB | 1291 | | | | |
| — | Java-Ranger (inactive) | 1059 | | | | |
| — | JayHorn | −2472 | | | | |

Read that table carefully, because it rewrites our priorities:

- **The winner scores 55% of the available maximum.** This is not a saturated
  competition.
- **The winner loses 315 tasks to unconfirmed witnesses** and 13 wrong proofs
  (−416 points). JBMC's unsoundness and its witness problems together cost it
  more than our entire remaining gap to first place.
- **JLiSA took bronze on its first entry with 617 solved tasks, 1 unconfirmed,
  and zero wrong answers** — using nothing but abstract interpretation. Fewer
  than two-thirds of JBMC's solved tasks, 84% of its score. Soundness and
  witness hygiene are worth more than raw coverage.
- **JayHorn scored −2472.** A CHC-based tool, deeply negative. That is what
  unsound discharge does to a score, and it is the strongest available argument
  for our 0-wrong discipline.

### 0.5 What our own score actually is — the decisive arithmetic

Our full-corpus measurement at `0cb403b` is **2170 points over 1785 runs, 1376
correct, 0 wrong**. Those three numbers are enough to decompose it, because the
scheme has only two positive rates and we have no wrong answers:

```
2·Tc + 1·Fc = 2170      (the score)
  Tc +   Fc = 1376      (correct answers)
→ Tc = 794 correct TRUE
  Fc = 582 correct FALSE
```

**582 correct FALSE answers.** Note that the estimate in issue #127 was 581 —
derived independently, by a different route, and it lands within one. That is
about as good a cross-check as this kind of arithmetic gets.

Now apply the competition's actual rules from §0.1–0.2. Every correct TRUE is a
clean +2 because Java correctness witnesses are demo-mode or unsupported. Every
correct FALSE requires a **confirmed format-1.0 violation witness**, and we emit
2.0 only, so every one of them is `correct-unconfirmed` and scores **0**:

| | points |
|---|---|
| What `bench.py` reports | **2170** |
| What the competition would award | **1588** (= 2·794) |
| Uncollectible today | **582 — 26.8% of our reported score** |

And against the field:

| | score | margin over JBMC |
|---|---|---|
| JBMC, SV-COMP 2026 winner | 1561 | — |
| us today, competition-equivalent | **1588** | **+27** |
| us with #127 fixed | **2170** | **+609** |

**Read that margin.** On our own number we look like we would win comfortably.
Under the rules as written we are **27 points ahead of the winner** — inside
the noise of a single timeout swing, on a machine whose timeout count has
moved by 20 points between identical builds. We do not currently have a
defensible lead. We have one *unrealised* lead worth 582 points sitting in a
file-format mismatch.

Caveats, stated because the number is load-bearing: our corpus is 1785 runs
rather than the official 1731 tasks, so the populations are not identical; the
meta-category normalisation of §0.3 is not applied to either figure; and
JBMC's 1561 was measured by the official harness on the official set. So the
**+27** is not a reliable margin. The reliable part is the magnitude: **we are
not being paid for roughly 27% of what we report, and the fix requires no new
verification capability.**

Which brings us to the first item.

---

## Part 1 — Tier 0: points we have already earned and cannot collect

### T0.1 — Emit format-1.0 GraphML violation witnesses (#127)

**This is the highest-value item in this document and it requires no new
verification capability whatsoever.** We already find the violations. We simply
cannot be paid for them.

What is needed:

- A GraphML emitter producing format 1.0 violation witnesses.
- **Suppression of `witness.yml` for Java tasks** (see §0.3). Non-negotiable.
- Assumption syntax matching what the validator parses. Wit4Java extracts
  assumptions of the form `\result = <value>;` and `\result.equals("...")`,
  records one per `Verifier.nondet*` call, mocks those calls with Mockito, and
  runs the real JVM against the `assert`s. Our `witness.rs` already emits
  `\result == {v}` for the 2.0 waypoints — note the **`==` vs `=`** difference,
  and that Wit4Java wants `.equals(...)` for strings rather than
  `\result == "s"`.
- Avoid the known validator failure modes: an empty witness and a witness with
  no counterexample value for a nondet call both return *unknown*; and string
  values containing spaces have been reported to fail Wit4Java's parser.

Why the risk is low: a witness does not change a verdict, so this cannot create
a wrong answer. The failure mode is a witness that does not confirm, which is
precisely our current state.

And there is a strong argument that **the semantic content is already correct
and only the format is wrong.** Look at the unconfirmed column in §0.4: JBMC, a
bounded model checker, has 315 unconfirmed; GDart, a *concolic* executor that
runs a real JVM (SPouT as the executor, JConstraints as the solver backend),
has 107 from a comparable number of solved tasks. Running the program is what
makes a witness confirmable, because the nondet sequence is then observed
rather than inferred. We already do this: `JvmReplay` certifies every violation
on a real JVM before we publish FALSE, and it currently *refuses* 76 of our
witnesses (56 with all-zero values), which is why our false-alarm count is 0.
Every witness that survives `JvmReplay` is, by construction, a concrete nondet
sequence that makes a real JVM reach the violation — which is exactly what
Wit4Java re-checks after mocking `Verifier.nondet*` with Mockito.

So the gap really is formatting plus assumption syntax, not evidence. That is
an unusually cheap 600-ish points.

**On the 2027 question, which decides whether this is worth building at all.**
Two third-party issue trackers claim SV-COMP 2027 will require Java violation
witnesses in YAML (one says "format 2.3+ for Java; GraphML is no longer
listed"), which would make our existing 2.0 emitter nearly correct and this
item nearly worthless. Checked against the authoritative source: the
**SV-COMP 2027 rules page is still a placeholder**, and where it is not, it
says the Input and Output section "remains also the same as in SV-COMP 2026"
and the Scoring Schema "remains also the same as in SV-COMP 2026".

So as of 2026-11-22 the 2026 requirement stands and GraphML 1.0 is what pays.
But the claim is credible enough, and the cost of being wrong high enough, that
the emitter should be built **behind a format selector** keyed on category —
not as a replacement of the 2.0 path. That way a rules change is a
configuration change. Re-check `https://sv-comp.sosy-lab.org/2027/rules.php`
before starting, since it is explicitly due to be expanded, and note that the
`sv-witnesses` schema release in circulation for 2027 is **2.3**, so if the
switch does come our 2.0 emitter needs a version bump too, not just a
re-enable.

**Estimated value: up to our entire correct-FALSE count.** Measure it, do not
guess it: see T0.2.

### T0.2 — Make the internal score model witness confirmation

`tools/bench.py` awards +1 for a correct FALSE with no reference to a witness.
The competition awards +1 only on confirmation. So our headline number
overstates the competition score by *exactly our correct-FALSE count*, and
every comparison we have made against JBMC's 1561 inherits that error.

This is not a scoring nicety. It is the same defect class as the ablation gate
that disabled nothing: the output is indistinguishable from the informative
one, so nothing ever flags it. Until it is fixed we are optimising a number
that does not exist.

Minimum viable version: score a correct FALSE as +1 only when we emitted a
witness in the required format for that category, carrying a concrete value for
every nondet call on the path. Better version: run a real validator. jLiSA's
validator uses JDI `forceEarlyReturn` to inject nondet returns without
rewriting source, which is close to what our own `JvmReplay` already does — and
we already have `--emit-shadow` and `tools/lifter_differential.py`, so a
Wit4Java-shaped self-check is mostly wiring rather than new machinery.

Note the existing asymmetry this exposes: `JvmReplay` already refutes 76 of our
witnesses (56 with all-zero values). Those are violations we do not publish, so
they cost precision rather than correctness — but they are also exactly the
witnesses that would fail Wit4Java. The two checks should share a path.

### T0.3 — Compute the meta-category score the way the competition does

`Java.Overall` is a meta category:

> if a meta category contains k categories of the next level and the i-th
> contained category has the score sᵢ and consists of nᵢ verification tasks,
> then the meta category gets the score (Σ sᵢ/nᵢ) · (Σ nᵢ)/k

So the two Java base categories are **normalised by their own task counts**
before being combined. A sum of raw points across both properties is not the
competition score, and improvements concentrated in the larger category are
worth less than they look. Cheap to implement in `bench.py`, and it changes
which of two candidate improvements is actually bigger.

---

## Part 2 — Tier 1: capability, ranked by evidence

### T1.1 — A nullness domain

**The largest single obligation population.** Of 2675 open obligations,
**1468 are `NullDeref`** — 55%. No current engine carries a dedicated nullness
abstraction; nullness is inferred incidentally by the interval domain
(`is_nonnull_static`) and by the BMC's path conditions.

What it looks like: a per-variable three-point lattice (definitely-null,
definitely-non-null, maybe) with field sensitivity, plus non-null **field
invariants** ("this field is non-null after every constructor"), which is what
real Java code relies on and what no interval domain can express.

Why it ranks first on evidence: it is the biggest population, it is the
property that is now a *full base category* rather than a demo
(`no-runtime-exception` was promoted in SV-COMP 2026, so it is half the
available points), and the abduction probe found usable scalar nullness facts
of exactly the right shape — `(= r q)`, "r aliases a reference already known
non-null", returned in milliseconds once the query was bounded.

Soundness argument: a three-point nullness lattice with a standard transfer
function over `Expr` is a textbook over-approximation; it may discharge, and
`Direction::Over` is the correct tag. The hazard is the one `interval.rs`
already learned — `is_nonnull_static` must stay restricted to `static final`
fields with non-null initialisers, because `System.out` is mutable via
`System.setOut(null)`.

**Do not copy the industrial Java nullness tools.** This needs saying loudly,
because they are the obvious references and their design is illegal for us.
NullAway, Infer's Eradicate and the Checker Framework's Nullness Checker are
all **deliberately unsound**: they default a missing annotation to `@NonNull`
"since that is the most frequent annotation used in practice". NullAway
additionally "unsoundly assumes that arrays do not contain null values" and
unsoundly assumes all methods are pure, and its own paper says its checking is
unsound but "seems to catch most initialization errors in practice". That is a
rational trade for a lint tool whose cost of a false positive is developer
annoyance. For us the cost of an unsound discharge is **−32**, and JayHorn's
−2472 is what that looks like at scale.

So the defaults invert: **unannotated is ⊤ (maybe-null), narrowed only on
evidence** — a dominating null check, a freshly allocated object, a `static
final` non-null initialiser, a constructor that assigns on *every* path. The
precision numbers published for those tools therefore do not transfer, and we
should not plan against them. Closer references for a sound, bytecode-level
treatment: *A Non-Null Annotation Inferencer for Java Bytecode* (arXiv
1007.3183), and the sound direction in *On Leveraging Tests to Infer Nullable
Annotations* (ECOOP 2023), which is careful to "not infer or add `@NonNull` to
a method or field where it may become inconsistent with the runtime behaviour".

Note also the initialization subtlety, which is where field invariants are won
or lost: NullAway considers initialization only from callees that are *always*
invoked, while Eradicate considers initialization in all private/final
constructor callees "even those invoked conditionally, which is less sound". If
we infer "this field is non-null after construction", only the always-invoked
reading is sound.

### T1.2 — Pentagons: intervals plus symbolic strict upper bounds

Logozzo & Fähndrich, *Pentagons: a weakly relational abstract domain for the
efficient validation of array accesses* (SAC 2008 / SCP 2010). The domain
tracks `x ∈ [a,b] ∧ x < y` — strictly weaker than Octagons, dramatically
cheaper. In Clousot it **validated 83% of array accesses in `mscorlib.dll` in
a little over three minutes**.

**Three independent lines of evidence converge on this domain:**

1. **Our own abduction experiments.** The only non-degenerate facts the
   instrument produced on real obligations were `(<= v3 v12)` and, in the
   controlled test, `(<= n len)`. Those are precisely pentagon facts:
   variable-to-variable upper bounds. And the one that matters for
   `ArrayBounds` needs the array length as a *term* — `(select ghost_len r)` —
   not as a variable, which is the single most important design note for the
   implementation and the thing whose absence made the first census run return
   nothing usable.
2. **The domain's origin.** It was built for array-access validation in
   bytecode, which is our dominant provable obligation kind after nullness.
3. **The bronze medalist.** JLiSA combines constant propagation, intervals,
   **upper bounds between variables**, and string abstractions — and scored
   1311 with zero false positives.

Fit: `interval.rs` and the CPA substrate already exist, so this is a new domain
in a known slot rather than a new engine. Two existing hazards apply and both
are already documented: the hint-consumer seam (an absent entry in a sparse map
must read as ⊤, not "no opinion" — `docs/interval-ai-hint-path.md`), and #130's
rule that an artifact crossing a theory boundary must be validated in the
consumer's theory or carry an `Approximations` tag. A LIA-proved pentagon fact
pruning a bitvector search is exactly how #130 produced a wrong TRUE.

Overflow: a pentagon fact `x < y` is not preserved by `x = x + 1` when the
addition wraps. Every published fact must pass the overflow-guarded
preservation query of `docs/proposals/lia-faithfulness.md` §3. This is not
optional and is the whole reason that guard exists.

### T1.3 — String reasoning via the already-linked cvc5

cvc5 is linked statically in-process and, since the `parser` feature was turned
on for the abduction work, we can hand it arbitrary SMT-LIB. cvc5 has a full
string theory.

This matters because of a specific past failure: the **taint engine was
reverted** (2026-08-24) for gaining ~15 securibench FALSE answers while
requiring a hardcoded `"<bad/>"` witness string — benchmark-specific cheating
under our own design rules. A string *solver* removes that objection entirely:
the witness is **derived** by the solver from the program's constraints, which
is exactly what "engines must discover witness values through formal reasoning"
asks for.

Two routes, and they are complementary:

- **Constraint-based (cvc5 strings).** Encode string obligations in the string
  theory, get a model, and the model *is* the witness. Highest value for
  securibench FALSE answers.
- **Abstract domains (prefix, suffix, character inclusion, bricks, string
  graphs, Tarsis).** Tarsis is an automata domain whose alphabet is strings
  rather than characters; the family is from the same group as LiSA, and
  "string abstractions" is one of the four things JLiSA lists. Better for TRUE
  answers on string-manipulating code.

Further support from the field: JDart's SV-COMP 2021 contribution is titled
*Portfolio Solving, Breadth-First Search and **SMT-Lib Strings***, and JLiSA
lists string abstractions as one of its four domains. Both the symbolic and the
abstract-interpretation branches of this competition invested in strings.

Caveat recorded from the taint experiment: the *lifter* changes it needed
(Pure→Call, invokedynamic→Call) caused −55 FALSE regressions from IR bloat and
timeouts. The lesson is that a string capability must not be bought with an IR
change that hurts the BMC — `CLAUDE.md`'s "IR changes must not regress other
engines" rule was written from this.

### T1.4 — Sweep `fp.spacer.global` (global guidance / GSpacer)

Pure measurement, no new code, and the last documented lever in the
CHC-COMP arrays-track configuration that we are not already pulling.

We already set `fp.spacer.q3.use_qgen=true` and
`fp.spacer.ground_pobs=false` together (`chc.rs:3501`, documented as D1, on by
default, measured neutral on smoke and worth one task). The remaining options:

- `fp.spacer.global=true` with sub-options `gg.concretize`, `gg.conjecture`,
  `gg.subsume` (all default true when global is on). GSpacer won the arrays
  category at CHC-COMP 2020.
- `mbqi=false`, which SolCMC sets alongside `use_qgen=true` and
  `ground_pobs=false`.

Two warnings to carry into the measurement, both from upstream issue trackers:
global guidance is **complementary, not better** — one reported 11-clause
system solves in 0.53s without it and times out past 300s with it; and there is
a known null-model segfault in the global-guidance concretizer, worked around
with `fp.spacer.gg.concretize=false`. So this is a per-task configuration
question, not a flag to flip globally, and it must be measured on **both**
properties (`CLAUDE.md`: a guard sound for one can be vacuous for the other).

---

## Part 3 — Tier 2: structural work with a real thesis

### T2.1 — Loop summarisation inside a merged region

The blocker census reports, over the still-truncating tasks, that **`back_edge`
is 50% of all branching refusals** — and the tool's own note says "no published
level addresses this".

That note is literally true and it is the thesis. Java Ranger — the path-merging
extension of Symbolic PathFinder, and the SV-COMP Java winner in 2025 before
going inactive — has three published levels: mode 2 merges multi-path regions
with no method calls and a single exit; mode 3 adds regions that make
summarisable method calls; mode 5 adds return instructions as an extra exit.
**None of them summarises a region containing a loop.** Our own LBE numbers
match: `merged` 34.6%, `exits_method` 15.4% (which Java Ranger's L4/L5 covers),
`back_edge` 50.0% (which nothing does).

Approach: for an affine loop whose trip count is symbolic, compute a closed form
for the induction variables and summarise the region as a single transition with
a trip-count parameter. The literature is candid that this is the open problem —
early summarisation methods "could summarize only loops that update symbolic
variables across iterations in a regular way", and precise summarisation of
multi-path, irregular, or nested loops remains open (LoopSCC, 2025, attacks
multi-branch loops via periodicity and still fails when the oscillation interval
is infinite).

So scope it honestly: **affine, single-nest, side-effect-free-on-arrays loops
first**, which is the shape of the counting loops that dominate our
`ArrayBounds` population. A summary is an over-approximation if the closed form
is guarded by the trip-count relation and the overflow condition; it is unsound
the moment either is assumed rather than asserted.

### T2.2 — A template-library invariant engine, fed by abduction

This is the validated part of the abduction work and it stands on its own
measurements:

| query | answer | cost |
|---|---|---|
| sortedness goal, unguided | `(and (= n 2) …)` — quantifier range shrunk to one index | ~20 s |
| sortedness goal, template in grammar | the sortedness formula, exactly | **20 ms** |
| same, from a library of 8 templates | the sortedness formula | **15 ms** |
| scalar bound, unguided | `(= len n)` — sufficient, too strong | <10 ms |
| scalar bound, grammar | `(<= n len)` | **<10 ms** |

Guided by a template, cvc5 returns
`∀k. 0 ≤ k < n−1 → a[k] ≤ a[k+1]` for an `a[0] ≤ a[1]` goal three orders of
magnitude faster than it returns garbage unguided. **The candidate generator for
an array-content domain is a template library plus grammar-restricted
abduction, not free-form synthesis.**

Stated against itself, as it is in the code: four of those eight templates
entail the goal, so what was measured is cvc5 *selecting* a sufficient template,
most likely in grammar order — not discriminating, and certainly not returning
the **weakest** sufficient fact, which is the one that matters because a
too-strong fact is least likely to survive preservation. So the pipeline is
fixed: abduce a set, run each candidate through initiation and the
overflow-guarded preservation query, keep what survives. No ranking inside the
solver is relied on.

This is architecturally the same shape as Clause2Inv (have a generator propose
atomic clauses, then combine them) and LaM4Inv (use BMC to filter), with the
generator being a solver rather than a language model — which is the right
choice for a competition tool that must run offline and deterministically.

**What this is not:** a license to grow a template library by looking at
benchmark outcomes. A library of standard invariant shapes (monotonicity,
sortedness, boundedness, constancy) checked formally is a domain. A library
grown until specific benchmarks pass is the overfitting `CLAUDE.md` forbids.
The test is the one that file already states: can you say why the change is
correct on programs you have never seen?

### T2.3 — `imc` on cvc5 interpolants

`imc` has been dark on a stale premise: `interpolation.rs:78` says z3 "cannot
interpolate (support was removed upstream)… Install SMTInterpol and set
`AJAVE_SMTINTERPOL_JAR` to enable it." But cvc5 — already linked — exposes
`get-interpolant`, and the in-process script path is now proven by `abduct.rs`.

Mapping: assert `A`, then `(get-interpolant I (not B))`. A third
`InterpolationSolver` variant drops into the existing text-in/text-out
`interpolate(declarations, formula_a, formula_b)` interface.

The honest caveat, carried from the original note: IMC wants an **inductive
sequence** of interpolants and cvc5 gives **binary** ones
(`get-interpolant-next` enumerates alternatives, not a sequence). The sequence
must be constructed by iteration and then **checked**, never assumed. Given
what unbounded `get-abduct-next` did (79 minutes at 100% CPU on the smallest
query in the suite), every interpolant query needs `:tlimit-per` from the first
line of code — `abduct.rs::query_budget_ms` is the pattern.

---

## Part 4 — Tier 3: the corpus is changing under us

### T3.1 — Real-world Java is arriving, and it changes what matters

The Java task count went from **1345 in SV-COMP 2025 to 1731 in 2026**, and the
report names one of the sources: **ARG-V**, a tool "which can pull Java software
projects from GitHub repositories and readily prepare them as benchmark set."

ARG-V's own paper is precise about the scale and is worth reading before
planning around it. It scrapes the first **1,261 repositories** in the
RepoReaper curated GitHub database and generated **68 new benchmarks**, at
~41.7 lines per file against the existing corpus's 42.2 — so the tasks are not
larger, they are *differently shaped*. It builds on PAClab and deliberately
extends scope to **field variables and cross-class interactions**. ARG-V is one
source among several for the +386, not all of it.

The finding that matters: the authors evaluated the new benchmarks against the
four top SV-COMP 2025 Java verifiers — MLB, GDart, Java-Ranger and JBMC — and
report that **performance decreases substantially on the realistic benchmarks**
compared with the existing corpus. Nobody is good at these yet.

That is simultaneously a warning and the clearest opportunity in this document.
The crafted algorithm benchmarks (`InsertionSort-FunSat01` and friends) reward
clever invariant inference — sortedness, loop invariants, quantified array
facts. Realistic Java rewards something else almost entirely: **breadth of JDK
modelling, fields, cross-class flow, strings, exception paths, and not falling
over on code that uses forty library classes.** Field variables and cross-class
interactions are exactly what ARG-V added and exactly where our nullness gap
(T1.1) and `contract_of` breadth live.

Concretely, this means:

- The marginal point is moving from *invariants* to *library models*. Our
  `contract_of` surface and the `is_total_jdk_method` allowlist become the
  highest-leverage code in the tool, and `CLAUDE.md`'s allowlist rules become
  more load-bearing, not less: issue #48 found 22 wrongly-allowlisted methods,
  each a potential −32.
- We should **measure the new tasks separately from the old**. A score that
  improves on crafted algorithms while degrading on real-world code is a score
  moving the wrong way for 2027. `docs/plans/real-world-probe-set.md` already
  exists; it should be aligned with the ARGV-derived population.
- An engine that degrades *gracefully* on large unfamiliar code beats one that
  is brilliant on small code. That is an argument for the abstract-interpretation
  tier (T1.1, T1.2) over the heavy symbolic tier, and it is exactly the profile
  JLiSA scored 1311 with.

### T3.2 — Do not invest in scheduling

Recording this as a deliberate negative, because it is where a plausible
roadmap would go next and the measurement says no. Of 449 unproven tasks, only
**36 are timeouts**. The census's `budget` bucket — the only one a scheduler can
convert — is small, and the `structural` bucket (search stopped with budget in
hand) is explicitly "NOT convertible by scheduling". A portfolio scheduler is
a large build against a 36-task ceiling, most of which is also contention noise.

---

## Part 5 — Parked, with known cost

- **#130**: `invariant_check::check_inductive` has the same unguarded-preservation
  hole that the merged work fixed elsewhere. Known soundness hazard, not yet
  exploited by any engine. Should be closed before any new producer publishes
  invariants — i.e. before T1.2 or T2.2 ship.
- **Baselines**: both `sv-comp.baseline` (at `f09f7ab`) and `smoke.baseline`
  (at `91d963c`, missing four canaries — `--check` reports a 4-task coverage
  mismatch) need re-recording at current HEAD **on an idle machine**. A
  baseline recorded under load is inflated and masks future slowdowns.
- **Unswept constants**: `AJAVE_BMC_DEPTH_SLACK=4` and `AJAVE_LBE_MAX_REGION`.
  `CLAUDE.md` requires re-checking that the score is not sensitive to fitted
  constants; these two have never been swept.
- **#131** (blocked), and three unmerged September branches.
- **Octagons** as a fallback if Pentagons proves too weak: more precise,
  O(n³) in the variable count, and our widest corpus method carries 112
  variables — so only viable with the sparsity-preserving variants. Pentagons
  first, and only revisit if measurement demands it.
- **Prophecy variables** (Prophic3, TACAS 2021) as an alternative route to
  array properties if Spacer's quantified generalisation underperforms: it
  converts quantified array reasoning into quantifier-free reasoning by adding
  prophecy variables. A different encoding, not a flag.
- **Trace abstraction / automata-based verification** (Ultimate Automizer won
  C.Overall with 31472). Powerful and a very large build; noted for
  completeness, not proposed.

---

## Part 6 — Avenues measured and closed

Kept here so they are not re-attempted. Each should also have a GitHub issue
with `type:experiment` and `status:explored`.

| Avenue | Result | Why |
|---|---|---|
| Raise the loop-unroll cap (5/12/30) | **0 of 69** converted, 223s→461s | Nondeterministic trip counts mean no finite unrolling satisfies `all_paths_complete`. Categorical, not a tuning question. |
| Suppress refuted witnesses | **0 of 79** converted | Removing the spurious violation leaves the obligation open-and-unproven. `verdict_excluding()` already recovers TRUE when a refuted violation is the only obstacle. |
| Force FPA everywhere | 1 of 8 in-bucket, **−62 corpus-wide** | A quantified/float search is a different and slower search. |
| Abduction as a per-obligation census | **Structurally cannot work** | The needed fact sits several edges behind the obligation: the operand-stack lowering spreads one Java expression over several blocks, so for `InsertionSort-FunSat01` the guard edge carries assignments and sortedness is four edges back. Bridging that is a fixpoint. The *capability* is validated and reusable (T2.2); the *census* is not. |
| `blocker_census.py` "mislabels refuted-witness tasks" | **No defect; claim retracted** | The tool's ordering comment already argues the case with `BellmanFord-FunSat01` as the disproof, the refuted count travels per row, and the 0-of-79 measurement is the empirical confirmation. `structural` — "an invariant, or a different cap, NOT more time" — is the correct label. |

---

## Part 7 — Recommended order, and why

1. **T0.1 + T0.2 together** — the GraphML emitter and a score that models
   confirmation. They must ship together: the emitter without the scoring fix
   is unmeasurable, and the scoring fix without the emitter just tells us our
   number was wrong. Highest value, lowest risk, no new verification
   capability, and it corrects every comparison we have published.

   To put it in one line: **this is worth 582 points, which is more than every
   other item in this document combined, and it is a serialisation bug.** Our
   defensible margin over the SV-COMP 2026 winner is +27 until it is fixed and
   +609 afterwards. Nothing else on this list should be started first.
2. **T0.3** — meta-category scoring. An afternoon, and it changes which of the
   next two items is bigger.
3. **T1.1 nullness** — largest obligation population (55%), half the available
   points now that `no-runtime-exception` is a full category, and the cheapest
   domain of the three.
4. **T1.4 Spacer sweep** — zero code, runs while something else is being
   written, and it is the one remaining documented lever on the quantified
   array question.
5. **T1.2 Pentagons** — best-evidenced new capability. Close #130 first.
6. **T1.3 strings via cvc5** — unlocks the securibench population without the
   cheating that killed the taint engine.
7. **T2.1 / T2.2 / T2.3** — the structural work, in whichever order the
   measurements from 3–6 justify.

Every one of these is subject to the rules that are already written down and
were learned expensively: run `--set smoke --check` before scoring; `--repeat N`
before quoting; idle machine with `--require-idle`; both properties before
believing any discharge change; a canary for every wrong-answer fix; a minimal
benchmark in `benchmarks/ajave/` for every engine finding, with ground truth
from the JLS/JVMS confirmed on a real JVM; and a soundness argument for every
score improvement, because an improvement without one is a red flag.

And one rule this research pass earned the hard way: **a census wants a
known-answer control.** Five separate defects in the abduction instrument each
read as a plausible result, and only `InsertionSort-FunSat01` — whose needed
fact was known independently — distinguished a finding from a bug.

---

## Part 8 — Novel avenues: things nobody in this field appears to be doing

Everything above is an application of a known technique. This part is the
speculative half, and each item here comes from **our own data** rather than
from a paper — which is why the prior-art checks matter and are recorded.
Ordered by (value × confidence) / cost.

### N1 — Obligation-level scheduling, and the 24% that needs nothing

The abduction census failed as a *shape* census (issue #133), but one of its
measurements is sound regardless of every defect that sank the rest, because it
needs no grammar and no vocabulary: **`already_valid`** simply asks whether the
obligation's goal follows from the preamble with no added hypothesis.

On `InsertionSort-FunSat01`, **10 of 42 obligations (23.8%) came back
`already-valid`** — every incoming edge is safe with no invariant at all.

If that ratio survives corpus-wide, it is the most important number nobody has
measured: **roughly a quarter of our open obligations need nothing from any
invariant domain.** They are provable from the range axioms and ghost facts
alone, and they are open anyway — lost to *routing*, not to capability. No
amount of Pentagons, nullness or array reasoning converts them, which is
precisely the failure mode that made three capability directions measure zero.

**First action, and it is cheap:** run `--abduct-census` corpus-wide and report
*only* the `already-valid` ratio, discarding the shape columns. One SMT query
per obligation, bounded by `AJAVE_ABDUCT_BUDGET_MS`. This is a sound
measurement built from an instrument whose other outputs are not, and saying
which is which is the whole discipline of `docs/measurement-validity.md`.

**Then the avenue itself.** If the losses are routing, the fix is routing.
Every verifier in this competition schedules *whole programs* — a portfolio
picks a configuration per task. Our blackboard is already per-*obligation*:
`open_for(models_faithfully)`, `Completeness::discharge_blocker`, and
`Blackboard::since` exist precisely to let one engine pick up what another put
down, obligation by obligation. Nobody appears to schedule at that granularity.

Prior art to build on rather than reinvent: **conditional model checking**
(Beyer, Henzinger, Keremoglu, Wendler, FSE 2012) has a verifier emit a
*condition* describing what it did not verify, which the next tool continues
from; and **reducer-based conditional verifiers** (Beyer, Jakobs et al., ICSE
2018) turn that condition back into a program. Our `Artifact::Residual` variant
is exactly this idea — and it is one of the kinds `CLAUDE.md` records as having
had **zero producers**. Implementing `Residual` properly *is* conditional model
checking at obligation granularity.

Note this is **not** the scheduler rejected in T3.2. That was a *time* budget
reallocator against a 36-task timeout ceiling. This is about which engine ever
*sees* an obligation, which is a different and much larger population.

### N2 — Unsat-core reuse with renaming, across 2675 obligations

We solve 2675 obligations largely independently, and 1468 of them are
`NullDeref` — overwhelmingly the same few syntactic patterns repeated. Our own
metamorphic harness is built on the fact that obligations across methods
occupy overlapping ids and identical shapes.

Published and recent: **Cache-a-lot** (arXiv 2504.07642, 2025) extends unsat
result reuse by attempting **variable substitutions**, so a core applies to
formulas that differ only by renaming, reporting **up to 74% unsat-core reuse
against a 41% baseline**. And **F\*** records the unsat core for each
discharged obligation and replays it later, "in milliseconds instead of
minutes", falling back to a full solve when replay fails.

Neither is applied at per-obligation granularity in a verifier portfolio. For
us the payoff is not elegance, it is budget: every obligation discharged from a
cached core is budget returned to the obligations that need real work, which is
the same resource the `structural` bucket is starving for.

**Two soundness caveats, both from the sources and both load-bearing:**

- Z3's cores are **not guaranteed minimal**, so reuse must be validated, not
  assumed — replay-or-fallback (F\*'s design) is the sound shape.
- **Quantifier triggers do not appear in Z3's unsat core.** We turn on
  `fp.spacer.q3.use_qgen` by default (D1), so any core taken from a quantified
  Spacer proof is missing the instantiations that made it work. Reusing such a
  core elsewhere would be unsound. Cores must be tagged with whether
  quantifiers participated, and quantified cores excluded from reuse — or the
  reuse restricted to the quantifier-free LIA queries, where it is safe.

### N3 — Contract mining by adversarial probing, as a *soundness oracle*

Our largest looming bottleneck is library breadth (T3.1: the new corpus is real
GitHub Java, exercising fields and cross-class interactions). Our largest
historical soundness incident is the same surface: **issue #48 found 22
wrongly-allowlisted methods**, accumulated because "the list was grown until
the benchmark corpus passed".

The literature confirms this is unsolved rather than solved: the JDK's
specifications are "largely implicit in its documentation, written in natural
language", and automatic specification mining "has been hard to use and often
requires significant user involvement". Existing work either verifies
hand-written JML contracts (KeY on OpenJDK) or mines contracts from execution
traces for other domains. Nobody auto-derives a *verifier's* library allowlist.

**We already own the hard half.** `tools/validate_jdk_allowlist.py` establishes
ground truth "by running the signature on a real JVM with adversarial arguments
(empty receivers, out-of-range indices, nulls, overflow boundaries)". That is
the oracle. What is missing is the generator: enumerate the JDK surface the
corpus actually touches, probe every signature, and derive `Contract`s instead
of writing them.

**The key asymmetry, which is what makes this safe and is easy to get wrong:**

> A probe that finds a throwing input **proves** the method is partial.
> A probe that finds none **proves nothing at all.**

So probing is a **refutation** instrument. It can automatically and
continuously *remove* wrong allowlist entries — which is exactly what #48
needed and what no current gate provides — and it can never justify adding one.
That direction is also the sound one: omission costs precision, a wrong entry
costs correctness.

Concretely: a CI job that probes every allowlist entry on every JDK version we
support and fails on any entry it can make throw. Today the allowlist is
checked by two hand-maintained lists that must be kept in sync with each other.

### N4 — An LLM as the *documentation reader*, with the JVM as falsifier

This is the one place a language model belongs in this project, and it is not
where the literature puts it.

The invariant-synthesis papers (Clause2Inv, LaM4Inv, LORIS) use LLMs to propose
*invariants*. For a competition tool that is a poor fit: it must run offline and
deterministically, and a solver-based generator already works (T2.2).

But N3 leaves a real gap: probing can refute an allowlist entry and never
justify one, and `CLAUDE.md` rule 5 says justification must come from "the
Javadoc/JLS guarantee … for *any* input" — i.e. from **natural-language
documentation**. Reading natural-language specifications and proposing a formal
contract is the task LLMs are actually good at, and it is the task that
currently consumes human attention one signature at a time.

The division of labour is sound because the roles are right:

- **Generator:** proposes a `Contract` for `(class, name, desc)` from the
  Javadoc, citing the sentence it relied on.
- **Falsifier:** the existing adversarial JVM probe tries to break it. Anything
  it breaks is discarded automatically.
- **Admission:** human or CI review of what survives, with the cited sentence
  attached.
- **Runtime:** nothing. Contracts are baked in; the competition binary makes no
  network call and is bit-for-bit reproducible.

This is sound-by-construction in the only sense that matters here: no proposal
enters without surviving a real-JVM falsification attempt, and the thing being
automated is *reading documentation*, not *proving theorems*. It is also the
highest-leverage response to T3.1, because library breadth is a specification
problem rather than a reasoning problem.

Guardrail: this generates **specifications**, never witnesses or invariants. A
model-proposed witness value would be the hardcoded-constant cheating that got
the taint engine reverted. The boundary is firm.

### N5 — The real JVM as the refinement oracle (DASH/SYNERGY, re-pointed)

`JvmReplay` currently **refutes 76 of our witnesses** (56 of them all-zero).
Today that information is used once — to suppress a FALSE verdict — and then
discarded. It is thrown-away refutation evidence about path feasibility.

SYNERGY/DASH/YOGI use *test generation* to choose the frontier of an abstract
counterexample and decide how to refine. The novel substitution for our setting
is that our oracle is **the actual language runtime**, not a generated test: a
refuted witness is a proof that a specific path is infeasible *under real JVM
semantics*, including every corner where our model and the JVM differ — which
is exactly where an invented test oracle would be wrong too.

So: feed refutations back as blocking lemmas. The blackboard already has the
artifact kind (`Lemma`), the direction discipline for it (`RefutedBy` is
`Under`/`Exact`), and `Blackboard::contested()` to report engines that disagree.
The 56 all-zero refutations in particular suggest the concrete engine's
single all-zero probe is generating a systematically infeasible path that
nothing learns from.

### N6 — What this part is not

Surveyed and deliberately not proposed, with reasons, so the list is closed:

- **Neural/learned obligation triage.** Non-deterministic, unexplainable, and
  it would be fitted to the corpus we score on — the overfitting `CLAUDE.md`
  forbids, in its purest form.
- **Probabilistic or quantitative verification.** The properties are safety;
  there is nothing to be quantitative about.
- **Cross-task caching of verified summaries.** Real projects share libraries,
  so caching across tasks is tempting — but SV-COMP runs each task
  independently and in isolation, so it is both against the spirit and
  unavailable in the harness. Cross-*class* summaries within one task (T3.1)
  are the legitimate version.
- **Trace abstraction / automata-based verification.** Legitimate and powerful
  (UAutomizer won C.Overall with 31472), but a from-scratch build of a third
  proof paradigm. Noted in Part 5, not proposed.
- **Termination and no-deadlock engines.** Not Java properties in SV-COMP 2026
  — the only two are `valid-assert` and `no-runtime-exception`. Our concurrency
  engine should therefore serve those two on threaded programs and no more.

---

## Part 9 — Avenues in the competition's structure, not in the code

Three of these are new; two are checked-and-unavailable, recorded so they are
not re-proposed.

### S1 — Upstream the benchmark label we believe is wrong

We hold a position that one SV-COMP task is **mislabelled**: our FALSE on
`ReverseInterpolator` is right and the benchmark's expected TRUE is wrong,
which costs us **−32** every run. Separately, our `valid-assert` score is
**+33 against stock sv-benchmarks** because of a local correction, which means
every external comparison we publish has to subtract it first.

Both facts point the same way: **fix it upstream.** Java tasks enter the corpus
through pull requests to `sv-benchmarks`, and the competition explicitly
accommodates this kind of dispute — the report notes that for voted expected
results, "tool developers can inspect the results and convince the community
that a voted expected result is in fact wrong", after which the task is
removed.

This is the cheapest legitimate points on the entire list after #127: a −32
becomes a +2 (a 34-point swing on one task), our local correction stops being a
divergence from the official corpus, and every comparison we make becomes
honest without an asterisk. It costs a well-argued pull request with a JLS/JVMS
citation and a real-JVM demonstration — both of which `CLAUDE.md` already
requires us to have produced before believing our own verdict.

Do this early. Corpus changes have a deadline ("all Java verification tasks
used in the competition must be part of the SV-COMP benchmark collection prior
to the benchmark contribution deadline"), so it is time-boxed in a way code is
not.

### S2 — Contribute benchmarks, deliberately

The corpus is grown by contribution (T3.1: ARG-V added 68 tasks from 1,261
scraped repositories). We have `benchmarks/ajave/` — a suite of minimal
programs, each with ground truth argued from the JLS/JVMS and confirmed on a
real JVM, built under a mandatory rule that every engine finding gets one.
`benchmarks/ajave/jvm-floats/NaNComparisonIsAlwaysFalse` is three lines with a
derivation from IEEE-754 and the `dcmpg` bytecode.

That is a higher evidentiary standard than "scraped from GitHub and checked by
four verifiers". Several of them are exactly the kind of capability-boundary
task the corpus is short of.

The honest tension, and it must be stated: contributing tasks we are good at is
self-serving, and tasks that pin *our* capability boundary are not obviously
general. The defensible subset is the ones encoding **JVM semantics** rather
than our architecture — the float and string semantics cases, where ground
truth comes from the specification and any verifier should agree. Those are a
contribution; a task shaped around our blackboard is not.

### S3 — SV-LIB: wide open, and a demo category

SV-COMP 2026 introduced **SV-LIB**, with **254 verification tasks**, evaluated
against **3 verifiers and 1 validator**. The best score was ~165 of a maximum
391 (42%). By comparison, Java has 11 verifiers and C has 61.

The format's pitch is directly relevant to us: "one of the key features of the
format is **clear formal semantics, painfully missing for languages like C and
Java**". Most of our hard-won engineering is JVM-semantics modelling —
`contract_of`, the allowlist, float bit patterns, exception tables — and a
format with defined semantics removes that entire cost class.

But: it is a **demo** category, so it earns no medals and does not affect the
standings, and retargeting a frontend is a real build. So this is a **watch
item, not a proposal**: if SV-LIB is promoted to a regular category (as
`no-runtime-exception` just was, from demo to base), it becomes the least
contested scoring surface in the competition, and the decision should be
revisited immediately rather than from scratch.

### S4 — Checked and unavailable: there is no Java validation track

This looked like the best idea in this section until I read the rules. Java has
only **3 validators** against C's 16, one of them (JCWIT) inactive, and we
already own a working Java violation-witness replayer — `JvmReplay` currently
*refutes* 76 of our own witnesses, so it already discriminates. Entering as a
validator looked like medals in a nearly-empty category.

It is not available. The validation track's tasks are "the handcrafted
validation tasks in **C.ValidationCrafted** and all validation tasks generated
by verifiers on the verification tasks in **C.Overall**". Java witnesses are
validated in order to score the *verification* track; there is no Java
validation category to compete in, and the medal tables (Tables 14–16) list
only C meta categories.

What survives from the idea: building a GraphML **reader** so we can validate
our own witnesses end-to-end is still worth it, because it is the honest
version of T0.2 and it de-risks the writer in T0.1. Just not for points of its
own.

### S5 — Checked and unavailable: no cross-task caching

Noted in Part 8 N6 and repeated here because it is a structural rather than a
technical limit: each tool execution is independent, so nothing learned on one
task may be carried to the next. Verified in the resource rules — each verifier
run is separately limited to 15 GB and 15 minutes of CPU on 4 processing units.

---

## References

**Competition**
- Beyer, Strejček. *Evaluating Software Verifiers for C, Java, and SV-LIB
  (Report on SV-COMP 2026)*. TACAS 2026.
- Beyer. *Improvements in Software Verification and Witness Validation:
  SV-COMP 2025*. TACAS 2025.
- SV-COMP 2026 rules: https://sv-comp.sosy-lab.org/2026/rules.php

**Witnesses**
- Ayaziová, Beyer, Lingsch-Rosenfeld, Spiessl, Strejček. *Software Verification
  Witnesses 2.0*. SPIN 2024.
- Wu, Schrammel, Cordeiro. *Wit4Java: A Violation-Witness Validator for Java
  Verifiers*. TACAS 2022.
- jLiSA witness validator: https://github.com/lisa-analyzer/jlisa-witness-validator
- GraphML format reference: https://github.com/sosy-lab/sv-witnesses

**The Java field**
- JLiSA: *The Java Frontend of the Library for Static Analysis*
  (competition contribution), SV-COMP 2026.
- Sharma et al. *Java Ranger: statically summarizing regions for efficient
  symbolic execution of Java*. ESEC/FSE 2020. And the SV-COMP 2020 and 2023
  competition contributions.
- JBMC, GDart/JDart: see the SV-COMP 2026 report's tool table.

**Benchmarks and the corpus**
- *Demonstrating ARG-V's Generation of Realistic Java Benchmarks for SV-COMP*.
  arXiv 2602.04786 / Springer 10.1007/978-3-032-22749-2_14.
- Mues, Howar et al. *GDart: An Ensemble of Tools for Dynamic Symbolic
  Execution on the JVM* (competition contribution); *SPouT: Symbolic Path
  Recording during Testing*; *JDart: Portfolio Solving, Breadth-First Search
  and SMT-Lib Strings* (SV-COMP 2021).

**Nullness**
- Banerjee, Clapp, Sridharan. *NullAway: Practical Type-Based Null Safety for
  Java*. ESEC/FSE 2019. (Explicitly unsound by design — see T1.1.)
- Estep et al. *Gradual Program Analysis for Null Pointers*. ECOOP 2021.
- Dietrich et al. *On Leveraging Tests to Infer Nullable Annotations*.
  ECOOP 2023.
- *A Non-Null Annotation Inferencer for Java Bytecode*. arXiv 1007.3183.

**Abstract domains**
- Logozzo, Fähndrich. *Pentagons: a weakly relational abstract domain for the
  efficient validation of array accesses*. SAC 2008 / SCP 2010.
- Cousot, Cousot, Logozzo. *A parametric segmentation functor for fully
  automatic and scalable array content analysis* (FunArray). POPL 2011.
- Costantini, Ferrara, Cortesi. *Static analysis of string values*. ICFEM 2011.
- Negrini, Arceri, Ferrara, Cortesi. *Twinning automata and regular expressions
  for string static analysis* (Tarsis). VMCAI 2021; journal version JSEP 2024.

**Invariants and interpolation**
- Gurfinkel, Shoham, Vizel. *Quantifiers on Demand* (QUIC3). ATVA 2018 /
  arXiv 2106.00664.
- Mann, Irfan, Griggio, Padon, Barrett. *Counterexample-Guided Prophecy for
  Model Checking Modulo the Theory of Arrays*. TACAS 2021.
- Fedyukovich, Prabhu, Madhukar, Gupta. *Quantified Invariants via
  Syntax-Guided Synthesis* (FreqHorn). CAV 2019.
- Flanagan, Leino. *Houdini, an Annotation Assistant for ESC/Java*. FME 2001.
- Ezudheen et al. *Horn-ICE learning for synthesizing invariants and contracts*.
  OOPSLA 2018.
- Dillig, Dillig, Aiken. *Automated error diagnosis using abductive inference*.
  PLDI 2012. And *Explain*: CAV 2013; loop invariants: OOPSLA 2013.
- Reynolds, Barbosa, Larraz, Tinelli. *Scalable algorithms for abduction via
  enumerative syntax-guided synthesis*. IJCAR 2020.
- Z3 Spacer parameters: https://microsoft.github.io/z3guide/programming/Parameters/
  and `src/muz/base/fp_params.pyg`.

**LLM-assisted invariant synthesis** (noted, not proposed for a competition tool)
- *Loop Invariant Generation: A Hybrid Framework of Reasoning-optimised LLMs
  and SMT Solvers*. arXiv 2508.00419.
- LORIS: *Guiding LLM-based Loop Invariant Synthesis via Feedback on Local
  Reasoning Errors*. arXiv 2605.17914.
- Clause2Inv (ISSTA 2025); LaM4Inv (BMC-filtered LLM candidates).

**Novel avenues (Part 8)**
- Beyer, Henzinger, Keremoglu, Wendler. *Conditional model checking: a
  technique to pass information between verifiers*. FSE 2012.
- Beyer, Jakobs, Lemberger, Wehrheim. *Reducer-based construction of
  conditional verifiers*. ICSE 2018.
- *Cache-a-lot: Pushing the Limits of Unsatisfiable Core Reuse in SMT-Based
  Program Analysis*. arXiv 2504.07642, 2025.
- F\* unsat-core hints: replaying proofs "in milliseconds instead of minutes".
- Lee, Jin, Meredith, Roşu. *Towards Categorizing and Formalizing the JDK API*.
  Tech report, UIUC 2012.
- *Experience Report on Formally Verifying Parts of OpenJDK's API with KeY*.
  arXiv 1811.10818.
- Beckert et al. / Godefroid et al. on SYNERGY, DASH and YOGI — test-driven
  abstraction refinement at the frontier.

**Internal**
- `docs/measurement-validity.md` — the theory of a gate that measures nothing.
- `docs/proposals/lia-faithfulness.md` §3 — the overflow-guarded preservation
  query.
- `docs/proposals/research-what-is-unexplored.md` — the four measured nulls.
- `docs/interval-ai-hint-path.md` — the hint-consumer seam.
- `changes.md`, 2026-11-22 entries.
