# Roadmap, November 2026: where the points actually are

Written 2026-11-22, after a research pass over the SV-COMP 2026 competition
report, the current Java field, and the invariant-inference literature.

## Executive summary

**If you read one thing: we are not being paid for 26.8% of our reported score,
and the fix is a file format.**

Six numbers, each derived below rather than asserted:

| | |
|---|---|
| Our reported score (`0cb403b`, 1785 runs, 0 wrong) | **2170** |
| What SV-COMP's rules would actually award | **1588** |
| JBMC, the SV-COMP 2026 Java winner | **1561** |
| So our defensible margin today | **+27** |
| Our margin with the witness format fixed | **+609** |
| Remaining capability headroom: TRUE vs FALSE | **592 pts vs 59 pts** |

The mechanism: Java **TRUE** answers need no witness (correctness witnesses are
demo-mode or unsupported), so all 794 of ours score a clean +2. Java **FALSE**
answers need a *confirmed* format-**1.0 GraphML** violation witness, and
`witness.rs` is a format-2.0 YAML emitter — so all **582** of our correct FALSE
answers score **0**. That is issue #127, now confirmed against the official
rules rather than inferred, and it is worth more than every other item in this
document combined.

Two traps in the obvious fix, both from the official report: emitting GraphML
*alongside* `witness.yml` makes the task **unsolved** rather than fixed
("if a verifier generates both files, `witness.graphml` is ignored"), and
`bench.py` awards FALSE points with no reference to a witness, so the fix is
unmeasurable until the scorer models confirmation.

**Then, for capability: build nullness.** Four independent lines of evidence
converge on it — it is 1468 of 2675 open obligations (55%); `no-runtime-exception`
is 95% TRUE-labelled with 1462 of its 1502 points in TRUE answers, and a
`NullDeref` obligation is exactly what blocks those; an NRE point is worth
**1.31×** a `valid-assert` point under the meta-category formula; and the one
usable signal the abduction instrument produced on real obligations was a
nullness aliasing fact. Then Pentagons (`x ∈ [a,b] ∧ x < y`), on three
independent lines of its own.

**What not to build**, with the arithmetic recorded: a scheduler (36-task
ceiling), an incorrectness-logic/bi-abduction engine (the most exciting thing
here, capped at 59 points until a real-world split measurement says otherwise),
a Java validation-track entry (the track is C-only), and cross-task caching
(structurally impossible). Four further candidates — the boxed-primitive long
tail, transcendental bounds, Spacer's quantified generalisation, and
collections — were measured and are **already done**.

**The competition is not saturated.** The winner scores 55% of the maximum
while losing 315 tasks to unconfirmed witnesses and carrying 13 wrong proofs;
JayHorn scored **−2472**. Soundness and witness hygiene outweigh coverage, which
is the profile we already have.

---

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

### 0.5b The two properties are mirror images, and nobody has acted on it

Counted from our corpus's own `.yml` labels (1785 task-property pairs):

| property | TRUE | FALSE | tasks | max pts | **pts in TRUE** | **pts in FALSE** |
|---|---|---|---|---|---|---|
| `valid-assert` | 312 | 701 | 1013 | 1325 | 624 | **701** |
| `no-runtime-exception` | 731 | 40 | 771 | 1502 | **1462** | 40 |

First, a sanity check that validates everything else in this document: our
corpus totals **1043 TRUE, 742 FALSE, max score 2828**, against the official
**1090 / 641 / 2821**. Different populations, near-identical aggregate — so our
corpus is a good proxy and the arithmetic in §0.5–0.6 transfers.

Now the structure, which is the finding. **`valid-assert` is 69% FALSE tasks.
`no-runtime-exception` is 95% TRUE tasks.** They are near mirror images, and
almost everything follows from that:

- **The witness fix (#127) is overwhelmingly a `valid-assert` story.** 701 of
  the 742 FALSE labels live there. T0.1 is not a general improvement; it is
  almost entirely one category.
- **The TRUE capability headroom is overwhelmingly a `no-runtime-exception`
  story.** 1462 of its 1502 available points are TRUE answers. Every invariant
  domain we build is, in practice, an NRE play.
- **And `NullDeref` is 1468 of 2675 open obligations.** A `NullDeref`
  obligation is precisely what stands between us and an NRE TRUE.

Those three facts compose into the clearest statement available about where
this tool's remaining value sits:

> **The largest single point concentration in the corpus is
> `no-runtime-exception` TRUE answers — 1462 points — and the dominant blocker
> on them is nullness, 55% of all open obligations.**

That is T1.1, reached independently of the abduction work, the literature, and
the competitor analysis. It is the one recommendation in this document that
four separate lines of evidence agree on.

**One more consequence, and it upgrades T0.3.** The meta-category formula
normalises each base category by its own task count before combining, and the
two categories are *different sizes* (1013 against 771). Differentiating
`(s₁/n₁ + s₂/n₂)·(n₁+n₂)/2`:

| a point gained in | marginal value in `Java.Overall` |
|---|---|
| `valid-assert` | 0.881 |
| `no-runtime-exception` | **1.157** |

**A point in `no-runtime-exception` is worth 1.31× a point in `valid-assert`.**
I earlier guessed this normalisation would be near-neutral. It is not — it is a
31% weighting difference, it points the same way as everything else in this
section, and we are currently blind to it because `bench.py` sums raw points.
T0.3 is therefore not bookkeeping; it is the difference between ranking two
candidate improvements correctly and incorrectly.

*(Corpus hygiene note found while counting: one task declares `no-deadlock`,
which is not a Java property in SV-COMP 2026 — the only two are `valid-assert`
and `no-runtime-exception`. It scores nothing and should be excluded from
scoring runs.)*

### 0.5c The corpus is not one population — and the real-world tasks are already here

Task counts by family in `benchmarks/sv-comp`:

| family | tasks | what it is |
|---|---|---|
| `autostub` | **244** | JDK API coverage — one TRUE and one FALSE per library method |
| `jbmc-regression` | 177 | JBMC's own regression suite |
| `securibench` | 113 | string/taint security benchmarks |
| `jpf-regression` | 104 | Java PathFinder's suite |
| `float-nonlinear-calculation` | 87 | transcendentals (`Math.sin` and friends) |
| **`argv-tasks`** | **70** | **the ARG-V real-world GitHub population** |
| `MinePump` | 64 | a product-line family |
| `java-ranger-regression` | 41 | |
| `algorithms` | 40 | the crafted sorting/graph tasks |
| `float_unboundedloop` | 30 | |
| `jayhorn-recursive` | 23 | |
| `jdart-regression` | 16 | |
| `objects`, `juliet-java`, `rtems-lock-model` | 24 | |

Two things fall out of this that change the reading of everything above.

**First: `autostub` is the single largest family at 244 tasks, and it confirms
the "exactly twice" pattern from Part 10.** It is a generated JDK-API coverage
suite — which is why `contract_of` has 277 method names, and why the
boxed-primitive long tail is already modelled. A seventh of the corpus is
library-model coverage, and we have already taken it.

**Second: the ARG-V real-world tasks are already in our corpus**, as
`argv-tasks` — 70 tasks, **104 task-property pairs, max score 171**. So the
split measurement T3.1 asks for is not future work; it can be computed from any
full run we have already done. That is the cheapest unexploited measurement
available, and it is the one that decides whether §0.7's
incorrectness-logic/bi-abduction avenue is capped at 59 points or is the main
event.

Their label distribution is also structurally different from the rest:

| | TRUE | FALSE |
|---|---|---|
| `argv-tasks` `valid-assert` | 26 | 25 |
| `argv-tasks` `no-runtime-exception` | 41 | 12 |
| **corpus-wide** `valid-assert` | 312 | **701** |

**The real-world tasks are label-balanced where the corpus overall is 69%
FALSE on `valid-assert`.** So on realistic code, `valid-assert` TRUE answers
matter far more than the corpus-wide figure suggests — which points the same
way as §0.6 and §0.5b, and makes the invariant work *more* valuable for the
corpus we are heading toward, not less.

### 0.6 Where the remaining headroom is, and it is not where the interesting work is

Combining §0.2's decomposition of the official maximum (T = 1090 true tasks,
F = 641 false tasks) with §0.5's decomposition of our own score (794 correct
TRUE, 582 correct FALSE):

| | we get | available | headroom | **points left** |
|---|---|---|---|---|
| TRUE (+2 each) | 794 | 1090 | 296 tasks | **592** |
| FALSE (+1 each) | 582 | 641 | 59 tasks | **59** |

**Our FALSE coverage is already 91%. Our TRUE coverage is 73%.** So there is
**ten times more score available on the TRUE side** — 592 points against 59.

This single table should govern every capability decision below, and it has
three consequences that are not obvious:

1. **Capability work belongs on the TRUE side.** Proving programs correct —
   nullness, Pentagons, array invariants, CHC configuration — is where the
   points are. Bug-finding is nearly exhausted on this corpus.
2. **The two large prizes are the same size and wildly different in cost.**
   The witness gap is 582 points and is a serialisation bug. The entire
   remaining TRUE capability headroom is 592 points and is years of research.
   That is not a close call about what to do first.
3. **Anything that improves FALSE-finding is capped at 59 points** on the
   current corpus, however elegant. Which brings us to the most interesting
   thing in this document, and why it is not ranked first.

### 0.7 Incorrectness logic and bi-abduction — the find, and its honest demotion

The most compelling technique I found in this research pass is the
**incorrectness logic** line: IL as the formal dual of Hoare logic for *proving
bugs exist* (O'Hearn), **Incorrectness Separation Logic** marrying it to the
frame rule (CAV 2020), and **bi-abduction** (Calcagno, Distefano, O'Hearn,
Yang, POPL 2009) ported to the under-approximate setting to give compositional,
per-method specification inference — the basis of Infer-Pulse and Pulse-X.
Reported fix rates: Pulse-X 61% against Infer's 23–59%, and Pulse at Facebook
82%. A 2025 paper extends the line to object-oriented programs.

Why it looks tailor-made for us:

- **It is literally abduction**, and after this week we have abduction
  in-process via cvc5. `abduct.rs` is the primitive bi-abduction is built on.
- **It is compositional.** Per-method specs with a frame rule, so it never
  unrolls a whole program — which is exactly the wall our BMC hits
  (`back_edge` 50% of branching refusals, the whole `structural` bucket).
- **It cannot cause a wrong TRUE.** IL is under-approximate, so its results
  are `Direction::Under`: may violate, may not discharge. Our blackboard
  already enforces that at publish, and `JvmReplay` already certifies every
  violation on a real JVM before we answer FALSE.
- **It is Infer's technology, and Infer runs on millions of lines of real
  Java** — the exact population T3.1 says is arriving.

And yet: **it is a FALSE-finder, and §0.6 caps FALSE-finding at 59 points.**
Three to six months of work on a separation-logic engine, for at most 59
points, while a GraphML emitter is worth 582 and a nullness domain is worth a
share of 592. So it is **not proposed for the current corpus**, and recording
that is the whole point of doing the arithmetic before the design.

The condition under which it becomes a top item is specific and worth watching
for: our 91% FALSE coverage is measured on *today's* corpus, which is mostly
crafted algorithms. ARG-V's own finding is that all four top 2025 verifiers
"decrease substantially" on realistic code. If a split measurement (T3.1) shows
our FALSE coverage on the real-world population is far below 91%, then the 59
is wrong, the headroom is real, and this becomes the right answer — because
compositional under-approximate reasoning is the published technique for
bug-finding at that scale, and nothing else on this list is.

Also worth keeping from that literature regardless of whether we build the
engine: Pulse deliberately **does not support inductive predicates** (list
segments and such) and uses a simplified bi-abduction over pure assertions
instead. That is a strong hint about where the cost/benefit knee sits for any
heap reasoning we add.

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

**Upgraded by §0.5b: this is worth 31%, not nothing.** Our two categories are
different sizes (1013 and 771 task-property pairs), so a point in
`no-runtime-exception` is worth **1.31×** a point in `valid-assert` in the
meta score. Summing raw points makes us blind to that.

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

### T1.5 — The Astrée precision recipe: thresholds, array expansion, partitioning

Astrée is the most successful industrial abstract interpreter, and its authors
published the list of what actually buys precision. Theirs reads: "expansion of
small arrays, widening with several thresholds, loop unrolling, trace
partitioning, **relations between loop counters and other variables**".

That last item is T1.2 again, arrived at from a third direction. Three of the
others we do not do at all, and each is cheap, standard, and lands on the TRUE
side of §0.6.

**(a) Widening with thresholds.** Astrée's interval domain "by default applies
simple preset widening thresholds (enriched with dynamically computed ones)" —
on widening, a variable jumps to the *least threshold above* its current value
rather than straight to ∞. Candidate thresholds come from the program text:
array lengths, loop bounds, integer literals, `Integer.MAX_VALUE`.

This matters to us for a reason beyond precision. `CLAUDE.md` names
`widen_delay` among the constants "chosen by raising them until specific
benchmarks passed", i.e. a standing overfitting liability by our own rules.
Threshold widening **replaces a fitted constant with a mechanism derived from
the program under analysis** — it generalises to programs we have never seen,
which is exactly the test that file sets. A cheap precision win that also
retires a known liability is a rare combination.

**(b) Expansion of small arrays.** For an array whose length is a known small
constant, treat each element as its own variable. The entire quantified-array
problem — the one that sank the abduction census and motivates FunArray and
QUIC3 — **does not arise** for that subset: intervals alone then prove
element-wise facts exactly.

This will not help `InsertionSort-FunSat01`, whose array is `new int[N]` for
nondeterministic `N`. I said the measurement to do first was how many corpus
arrays have a constant length, so I did it — a regex over the 1498 Java sources
in `benchmarks/sv-comp`:

| | count | share |
|---|---|---|
| array allocations found | 196 | — |
| constant length | 53 | 27.0% |
| **constant and length ≤ 8** | **38** | **19.4%** |
| constant, length 9–32 | 13 | 6.6% |
| non-constant length | 143 | 73.0% |

Most common constant lengths: 1 (×10), 10 (×10), 3 (×8), 2 (×7), 4 (×6).

**So expansion applies to 38 of 196 allocation sites.** Two readings, and both
belong in the decision:

- *Pessimistic:* 196 array allocations across 1498 files is not many. Arrays
  are rarer in this corpus than the volume of array-invariant literature
  implies, and expansion touches a fifth of those.
- *Optimistic:* sites are not obligations. 900 of 2675 open obligations are
  `ArrayBounds`, so arrays are obligation-*dense* — a single site inside a loop
  generates many checks. If the 19% of sites carries ~19% of those
  obligations, expansion is in range of ~170 obligations, which is not trivial.

The honest conclusion is that this is **cheap and low-ceiling**, so it goes
after (a) rather than before it, and it is a candidate to drop entirely if (a)
and T1.2 together already discharge the small-constant-array population —
which they plausibly do, since intervals handle `a[0]` and `a[1]` on a length-2
array without any expansion at all.

The broader calibration is worth stating because it cuts against the direction
this project has been drifting in: **the quantified-array thread — FunArray,
QUIC3, the abduction census, sortedness templates — targets a population of a
few hundred obligations, while `NullDeref` is 1468 of 2675.** The array work is
intellectually the most interesting thing here and it is not where the mass is.

**(c) Trace partitioning.** Rival and Mauborgne's domain (ESOP 2005, TOPLAS
2007) abstracts over a *partition* of traces rather than the set of all traces,
recovering disjunctive precision where a plain join destroys it, then merging
partitions once they stop paying. The reported effect is stark — ten abstract
states where partitioned against two where merged — and the design point is
that "partitions are merged soon enough that the widening operator does not
need to collapse them".

We already own the dual knob: large-block encoding *merges* regions, and the
LBE census says `merged` 34.6%. Partitioning is the decision not to merge, kept
locally. Astrée inserts partitioning directives **automatically after a
preliminary analysis**, which is the design to copy — a two-pass scheme, not a
hand-tuned directive list, because a hand-tuned list is overfitting with extra
steps. Mopsa now supports bounded trace partitioning too, so there is a second
implementation to learn from.

Order within this item: **(a) then (b) then (c)**. Threshold widening is the
cheapest and retires a liability; array expansion needs one frontend
measurement before it is worth building; trace partitioning is the largest and
should wait until Pentagons exists, since partitioning a weak domain buys less
than partitioning a relational one.

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

### T3.1b — Two architectures for the library problem, and why ours is right

Since library breadth is the bottleneck T3.1 identifies, it is worth knowing
how the tool that beat us solves it — because the answer is "completely
differently", and the comparison clarifies what we should and should not copy.

**JBMC writes executable models.** It ships a **Java Operational Model**
(`core-models.jar`), hand-written Java derived from OpenJDK 8 and simplified
for verification: performance optimisations stripped "such as in container
implementations", `assume` statements and CPROVER built-ins standing in for
arrays and strings, described as "exact but verification-friendly". It covers
the common `java.lang` classes and a few `java.util` ones. Loading the real JDK
is explicitly rejected as producing a model "far too large". An unmodelled call
gets a warning and a nondeterministic return — the same default as our
`Contract::OPAQUE`.

**We write declarative contracts.** `ajave_models::contract_of` states
preconditions and effects per `(class, name, desc)`, with
`Contract::at_least_as_conservative_as` giving the refinement order and
`tools/contract_monotonicity.py` checking consumers respect it.

The trade is real and runs in both directions:

| | executable models (JBMC) | declarative contracts (ours) |
|---|---|---|
| consistency with the verifier's own semantics | automatic — it is just Java, lifted identically | must be argued per entry |
| cost of a wrong entry | a modelling bug, found like any other | a **wrong TRUE, −32** (issue #48: 22 of them) |
| cost per method | high — write and maintain real code | low — one table row |
| effect on the BMC | every call inlines code; this is the "far too large" problem in miniature | none |
| usable by an abstract domain | no — a domain would have to analyse the model | **yes** — a contract *is* a transfer function |
| JDK version coupling | tight (their jar breaks on JDK 22+) | loose |

The last two rows are why our architecture is the right one *for us*: §0.6 says
our headroom is on the TRUE side, §0.5b says that means
`no-runtime-exception` TRUE answers, and the engines that produce those are
abstract domains, which consume contracts directly and cannot consume
executable models at all. JBMC is a bounded model checker, so inlining real
code is natural for it and ruinous for an interval domain.

So: keep contracts, and fix the thing contracts are bad at — **validation per
entry**, which is exactly N3.

**One licence constraint, recorded because it is easy to get wrong.**
`diffblue/java-models-library` is open source under **GPL2 with a classpath
exception**; ajave is **MIT**. The classpath exception exists so that programs
*linking* the models are not infected — it does not make the source a safe
basis for deriving our own. So:

- **Do not derive contract text from reading it.** That is a derivative-work
  question we should not have, and `CLAUDE.md` rule 5 already names the correct
  source of truth: "does the Javadoc/JLS guarantee this cannot throw for *any*
  input".
- **Its class list is a different matter.** Which signatures a serious Java
  verifier found worth modelling is a fact about priorities, not an expression,
  and using it to order our own work is defensible. Even so, prefer deriving
  that list from **our own corpus**: measure which unmodelled signatures
  actually block obligations, which is both licence-clean and better targeted.

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

Two numbers decide this ordering and both are derived above rather than
asserted: **582 points are uncollectible today for a file-format reason**
(§0.5), and **the remaining capability headroom is 592 points in TRUE against
59 in FALSE** (§0.6). So: fix the serialisation first, then spend every
capability hour on proving programs correct.

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
3. **T1.1 nullness** — largest obligation population (1468 of 2675, 55%), and
   it lands squarely on the TRUE side of §0.6: a `NullDeref` obligation is what
   stands between us and a `no-runtime-exception` **TRUE**, which is now a full
   base category rather than a demo. Cheapest of the three domains, biggest
   population, right side of the ledger. Carry the soundness inversion from
   T1.1: unannotated is maybe-null, narrowed only on evidence — the opposite of
   every industrial Java nullness tool.
4. **T1.4 Spacer sweep** — zero code, runs while something else is being
   written, and it is the one remaining documented lever on the quantified
   array question.
5. **T1.2 Pentagons** — best-evidenced new capability. Close #130 first.
6. **T1.3 strings via cvc5** — unlocks the securibench population without the
   cheating that killed the taint engine.
7. **N1's cheap half, at any time** — the corpus-wide `already-valid` ratio.
   One bounded SMT query per obligation, and if InsertionSort's 23.8% holds it
   says a quarter of our open obligations need no invariant at all and are lost
   to routing. That number changes the value of items 3, 5 and 7, so it is
   worth having early even though the instrument that produces it failed at its
   original job.
8. **T2.1 / T2.2 / T2.3** — the structural work, in whichever order the
   measurements from 3–7 justify.
9. **S1 upstream the mislabelled benchmark** — a 34-point swing on one task and
   it removes the asterisk from every external comparison. Placed last only
   because it is someone else's merge queue, not ours; start the conversation
   early because it is deadline-bound.

Deliberately **not** on this list, with the arithmetic recorded above:
a scheduler (T3.2, 36-task ceiling), an incorrectness-logic/bi-abduction engine
(§0.7, capped at 59 points until the real-world split says otherwise), a Java
validation-track entry (S4, the track is C-only), and cross-task caching
(S5, structurally impossible).

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

## Part 10 — Measured as already addressed

Four opportunities that looked promising when derived from the corpus and turn
out to be done. Recorded because negative information prevents re-work, and
because what survives this filter is a much sharper claim than what went in.

**The long tail of boxed-primitive statics.** Counting JDK calls across the
1498 corpus sources shows a striking pattern: dozens of methods appearing
**exactly twice** — `Integer.bitCount`, `Long.rotateLeft`,
`Integer.numberOfLeadingZeros`, `Short.reverseBytes`, `Character.isMirrored`,
`Character.getDirectionality`, and ~100 more. Appearing exactly twice is the
signature of a systematically generated family (one TRUE and one FALSE task per
method), which would make each a cheap two-task win, and almost all of them are
pure total functions that cannot throw — i.e. free `no-runtime-exception`
TRUEs, the exact side §0.6 says the headroom is on.

**Already done.** `contract_of` knows **277 distinct method names**, and all ten
sampled at random from that tail are modelled in two to four places each. This
is a large part of why our NRE position is strong.

**Sound over-approximation of transcendentals.** `Math.sin` appears 180 times
in the corpus, `cos` 98, `pow` 89, `sqrt` 52, `log` 43 — 462 occurrences in the
top five alone, and the largest identifiable JDK population by far. Our `nra`
engine is `Direction::Under` (falsification), so it finds FALSE and cannot prove
TRUE; proving TRUE needs sound *bounds*.

**Already done.** `math_interval.rs` provides exactly that —
"Sound interval abstractions for `java.lang.Math`", `eval(target, args) ->
Option<Range>`, consumed by `interval.rs`. Its module doc makes the same
argument from the same evidence I reconstructed independently, down to citing
JLiSA's bronze medal, and gives the worked `coral3` example where
`sin ⊆ [0, 0.708)` and `cos ⊆ (0.707, 1]` on `[0, π/4)` settle the assertion
with no solving at all.

**Quantified generalisation in Spacer.** `fp.spacer.q3.use_qgen=true` with
`fp.spacer.ground_pobs=false` — on by default at `chc.rs:3501`, documented as
D1, measured neutral on smoke and worth one task. Only `fp.spacer.global`
remains unpulled (T1.4).

**Collections.** They barely appear: `Arrays.copyOfRange` ×6, `Arrays.asList`
×5, `Collections.enumeration` ×4, `Collections.sort` ×3, `Collections.singleton`
×3. Against 462 transcendental calls. Collection modelling is not a current
bottleneck, which is worth knowing because it is where intuition about "real
Java" sends you first.

### What this filter leaves

Library and model breadth is **not** the bottleneck on the *current* corpus.
That makes two things sharper:

1. **T3.1's argument is about the future corpus, not this one.** The claim is
   not "we model the JDK badly" — we model this corpus's JDK usage well. It is
   that ARG-V-style real code will use a different and wider surface, and the
   evidence for that is ARG-V's own finding that all four top 2025 verifiers
   degrade substantially on it. So the action is the **split measurement**, not
   a modelling sprint.
2. **The two real items stand almost alone.** After this filter the list is
   short: **582 points in a witness format** (T0.1, a serialisation bug) and
   **nullness, 1468 of 2675 open obligations** on the side of the ledger where
   1462 points sit (T1.1). Everything else in this document is smaller, slower,
   or conditional on a measurement not yet taken.

That is a more useful roadmap than one which lists twenty plausible things, and
it is only this short because the easy candidates were measured rather than
assumed.

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

## Part 11 — The participation checklist, which is not optional and is dated

Everything above assumes we can enter. The report spells out what entry
requires, and none of it is code:

For each verifier, the participating team creates:

1. **a tool archive on Zenodo**, from which the tool is downloaded;
2. **a `<tool>.yml`** in the **Formal-Methods Tools** repository, with basic
   information, the name of its **jury representative**, and the Zenodo archive
   identifier;
3. **a tool-info module** in the **BenchExec** repository, specifying the
   interface for running the tool and interpreting its result;
4. **a merge request** to `category-structure.yml` in the **Benchmark
   Definitions** repository, declaring the categories the tool participates in.

Several of these are gated on other people's review cycles, and two have hard
deadlines: benchmark contributions must be merged "prior to the benchmark
contribution deadline" (which bounds S1 and S2), and a jury representative is a
*person*, not a file.

Three consequences worth planning around:

- **The tool-info module decides how our output is read.** It is where "the
  last line of stdout is the verdict" is formalised, and it is also where the
  witness-file convention lands — so T0.1's format selector and the tool-info
  module are the same conversation. A tool-info module that advertises the
  wrong witness format would reproduce #127 from the outside.
- **Resource limits are fixed and should be what we measure against.** Each
  verifier run is limited to **15 GB of memory and 15 minutes of cumulative CPU
  time on 4 processing units**. Our `--timeout` and worker counts should mirror
  that, or our timeout counts predict nothing. (Validator runs get 2 processing
  units and 7 GB, which is why S4's non-availability costs us nothing.)
- **Inactive status is visible and consequential.** Tools without active team
  support are marked `∅` in the results tables, keep legacy witness-format
  support that active tools lose, and are excluded from some prize categories.
  Java-Ranger — the 2025 winner — is marked inactive in 2026. Being present and
  active is itself worth something.

None of this is interesting, and all of it is on the critical path. It should be
started before the capability work, not after, because it is latency rather
than effort: a merge request to someone else's repository takes as long as it
takes.

---

## Appendix — how to re-derive every number here

`CLAUDE.md` holds that a number produced without stated conditions is not
evidence. That applies to this document, so here is how to check it. Several
claims below are load-bearing for the whole ranking; if one is wrong, the
ranking changes.

**Official competition figures** — Beyer & Strejček, TACAS 2026. Extract the
text and read Table 1 (witness formats per base category), Table 2 (verification
scoring), Table 3 (validation scoring), Table 12 (all Java verifiers) and
Table 13 (medalists):

```sh
pdftotext 2026-TACAS.Evaluating_Software_Verifiers_for_C_Java_and_SV-LIB.pdf out.txt
grep -n -i java out.txt
```

The three claims to check first, because everything rests on them:
1. `Java.valid-assert.` correctness witnesses are **1.0 demo**;
   `Java.no-runtime-exception.` correctness witnesses are **–**. (Table 1.)
2. "If there is no supported witness format or the only supported witness
   format is in demo mode, the witness generation is **not required**."
3. Violation witnesses for both Java categories are **1.0**, not demo, and
   False-correct is "+1 … the violation witness **was confirmed**".

(1)+(2) give "every TRUE is a free +2"; (3) gives "every FALSE needs GraphML".
If any of the three is misread, §0.5's 582 is wrong.

**The official max decomposition** (T = 1090, F = 641): solve `2T + F = 2821`
and `T + F = 1731` from Table 12's header ("1731 tasks, max. score 2821").

**Our score decomposition** (794 TRUE, 582 FALSE): solve `2Tc + Fc = 2170` and
`Tc + Fc = 1376` from the full-corpus run. Valid **only because we have zero
wrong answers** — any `−32` or `−16` term breaks the system, so re-derive it
from the run's own counts rather than reusing these numbers after a regression.

**Our corpus's label distribution** (1043 TRUE / 742 FALSE / max 2828, and the
per-property split):

```sh
python3 - <<'EOF'
import pathlib, re, collections
c = collections.Counter()
for y in pathlib.Path("benchmarks/sv-comp").rglob("*.yml"):
    for m in re.finditer(r"property_file:\s*(\S+)[\s\S]*?expected_verdict:\s*(\w+)",
                         y.read_text(errors="ignore")):
        c[(m.group(1).split('/')[-1].replace('.prp',''), m.group(2))] += 1
for k in sorted(c): print(k, c[k])
EOF
```

**The 1.31× meta-category weighting**: with `n₁ = 1013` (valid-assert) and
`n₂ = 771` (NRE) from the above, differentiate
`(s₁/n₁ + s₂/n₂)·(n₁+n₂)/2` — the marginal values are `(n₁+n₂)/(2n₁) = 0.881`
and `(n₁+n₂)/(2n₂) = 1.157`. **This one is sensitive to the category sizes**,
which are our corpus's rather than the official ones, so recompute it from the
official per-category task counts before relying on the exact figure. The
*direction* (NRE worth more) holds for any `n₂ < n₁`.

**Array allocation counts** (196 total, 53 constant, 38 of length ≤ 8): the
regex over `benchmarks/sv-comp/**/*.java` in T1.5(b). Counts *source
allocations*, not obligations, and that distinction is the whole argument in
that section — do not quote it as an obligation count.

**JDK call distribution** (`Math.sin` ×180 etc.): the `([A-Z]\w+)\.(\w+)\(`
scan in Part 10. Crude — it cannot distinguish a user class named `Matrix` from
a JDK one, so it is filtered against a hand-written list of JDK class names and
will miss instance calls through variables. Good enough for ranking
populations, not for coverage claims.

**Contract coverage** (277 method names): `grep -roh '"[a-z][A-Za-z0-9_]*"'`
over `crates/ajave-models/src/*.rs`, deduplicated. An **over**-estimate — it
counts every lowercase string literal, not only method names — so treat it as
"the same order of magnitude as the corpus's JDK surface", which is all the
argument needs.

**Obligation populations** (1468 `NullDeref` and 900 `ArrayBounds` of 2675):
from earlier blocker-census runs, not re-measured here. **Re-measure before
committing to T1.1** — it is the single number the top capability
recommendation rests on, and `tools/blocker_census.py` reports obligation
counts from the orchestrator's own open-set.

**Anything from a run**: on an idle machine, `--require-idle`, after
`tools/cleanup.sh`, with `--repeat N` before quoting, and `--set smoke --check`
green first. The Apple indexing daemons (`mds_stores`, `mediaanalysisd`) hold
this machine near load 3 for long stretches and have twice blocked a baseline
re-record; that is a real constraint on when measurements can be taken, not an
excuse to take them anyway.

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

**The library problem**
- Cordeiro, Kroening, Schrammel et al. *JBMC: A Bounded Model Checking Tool for
  Java Bytecode*. arXiv 2302.02381; TACAS 2019 competition contribution.
- `diffblue/java-models-library` — the Java Operational Model, OpenJDK 8 based,
  GPL2 with classpath exception. **Read the licence note in T3.1b before using.**

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
- Rival, Mauborgne. *Trace partitioning in abstract interpretation based static
  analyzers*. ESOP 2005; *The Trace Partitioning Abstract Domain*. TOPLAS 2007.
- Cousot, Cousot, Feret, Miné, Rival et al. *Why does Astrée scale up?*
  FMSD 2010; *The Astrée Static Analyzer*. ESOP 2005.
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

**Incorrectness logic and bi-abduction (§0.7)**
- O'Hearn. *Incorrectness Logic*. POPL 2020.
- Raad, Berdine, Dang, Dreyer, O'Hearn, Villard. *Local Reasoning about the
  Presence of Bugs: Incorrectness Separation Logic*. CAV 2020.
- Calcagno, Distefano, O'Hearn, Yang. *Compositional Shape Analysis by Means of
  Bi-Abduction*. POPL 2009.
- Le, Raad, Villard, Berdine, Distefano, O'Hearn. *Finding Real Bugs in Big
  Programs with Incorrectness Logic*. OOPSLA 2022 (Pulse-X).
- *Inferring Incorrectness Specifications for Object-Oriented Programs*,
  2025.

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
