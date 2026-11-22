# Why a differential gate can pass without measuring anything

Written 2026-11-22, after a session in which three of the author's own
measurements were inert, one correct explanation was retracted on the strength
of one of them, and a defect worth +10 points was found by reading a function
rather than by any of the four gates that are supposed to find defects.

`CLAUDE.md` already says how to make a *score* trustworthy: idle machine,
snapshotted binary, `--repeat`, provenance on the baseline. This document is
about the other half — the gates that carry no expected-verdict label
(`engine_ablation.py`, `metamorphic.py`, and any future differential harness).
Those are stronger oracles precisely because they need no labels, and they fail
in a way a score cannot: **they can pass while measuring nothing at all**, and
the passing output is byte-identical to the informative result.

## 1. The shape of a differential experiment

A differential gate applies an intervention `I` to the system `S` and compares
an observation before and after:

```
verdict(S)  vs  verdict(I(S))
```

and concludes from the difference. Ablation takes `I` = "remove engine `e`";
metamorphic testing takes `I` = "apply a meaning-preserving edit". The
conclusion drawn is of the form "no difference, therefore no defect of this
kind".

That inference has two preconditions, and neither is observable in the output:

1. **The intervention was applied**: `I(S) ≠ S`.
2. **The observation is sensitive to it**: `verdict` can distinguish the two.

If either fails, `verdict(I(S)) = verdict(S)` *necessarily*, for every program,
forever. The gate reports a pass. The pass is a tautology.

This is the whole fault. An experiment whose intervention is the identity is
not a weak experiment — it is **not an experiment**, and it is indistinguishable
on paper from a strong one that found nothing.

## 2. This is vacuity, and the remedy is a witness

The model-checking literature named this. A property passes **vacuously** when
some part of it is irrelevant to its truth — canonically antecedent failure,
where `G(req → F ack)` passes on a model in which `req` never holds. Beer,
Ben-David, Eisner and Rodeh gave the first efficient detection algorithm, for a
subset of ACTL, by model-checking a *witness formula* obtained by replacing a
subformula with `true` or `false`: if the property still passes, the subformula
never mattered. Kupferman and Vardi generalised this to more expressive
specifications and framed the output as an **interesting witness** — a
computation that satisfies the formula *and contains a request*.

The mapping onto an ablation is exact:

| model checking | ablation gate |
|---|---|
| `G(req → F ack)` | "no verdict flips without engine `e`" |
| `req` never holds | no engine in the portfolio has id `e` |
| passes vacuously | "PASS — no verdict flipped" |
| interesting witness | a run in which the portfolio actually shrank |

So the remedy is the one the literature already prescribes: **a passing
differential gate must produce a witness that the interesting case occurred.**
Not a request that it occur — evidence that it did.

The same problem is standard elsewhere under other names. Mutation testing
excludes mutants that fail to compile and struggles with *equivalent mutants*,
semantically identical to the original and therefore unkillable, which inflate
or deflate a score while carrying no information; Budd and Angluin tied the
question of what test data can demonstrate directly to deciding program
equivalence. Fault-injection and chaos practice insists on confirming that the
fault was injected before interpreting the system's survival. Each discipline
arrives at the same rule from its own direction.

## 3. What this cost here, concretely

`AJAVE_DISABLE=<id>` removed engines by id and **silently ignored any name that
matched nothing**. `AJAVE_DISABLE=zzz` ran the complete portfolio and printed
nothing at all.

Three consequences, all measured on 2026-11-22:

- Three hand-run ablations named `smt-bmc`, `kinduction` and `ai` against a
  portfolio that spells them `smt-bmc-fpa`, `k-induction` and `interval-ai`.
  Each returned the full-portfolio verdict and was read as "this engine is not
  needed". On the strength of one, a correct explanation of a score change was
  retracted and replaced with a guess.
- `tools/engine_ablation.py` listed eleven ids, of which `imc` (absent without
  `AJAVE_SMTINTERPOL_JAR`) and `cegar` (absent unless `cegar.available()`) are
  routinely not in the portfolio. Two of eleven rows were inert.
- The BMC is constructed **twice** — a cheap integer pass and a second
  floating-point pass whose `Engine::id` returns `smt-bmc-fpa` so attribution
  shows which decided what. The harness named only `smt-bmc`. On the
  MergeSortIterative tasks the surviving FPA pass discharges 12 of the 27
  obligations in `merge`, so "removing the BMC flips nothing" had never once
  been measured against a portfolio without the BMC.

The fix is in two halves, because the first half alone was also inert: the
binary now warns on stderr, naming the unmatched ids and listing the ids present
in the run; and the harness, whose `verdict()` read only stdout while
`run_guarded` captured both, now reads that warning and reports which rows
disabled nothing beside its totals. A warning rather than a refusal, because an
absent engine is legitimate — `imc` really is unavailable on a clean checkout.

Corrected, the gate is twelve real ablations rather than nine: 378 runs, 4
answers lost, 0 verdicts flipped, with `cegar` and `imc` now named as inert.
The conclusion survived. It had simply never been tested.

## 4. The second theory: a sound precision loss is invisible to every
correctness oracle

The +10 came from one commit (`f26ed94`, closing #105) and it is worth stating
why nothing caught the defect for its whole lifetime.

`Blackboard::interval_hints_for_method` reads certificates `interval-ai`
publishes and hands the BMC per-variable bounds. Model it as a partial
interpretation `γ` from syntax to an interval lattice. For a conjunctive formula
`φ = ⋀ᵢ φᵢ`, the correct reading is conjunct-wise and then met:

```
γ*(⋀ᵢ φᵢ)  =  ⨅ᵢ γ(φᵢ)        with γ(unparseable) = ⊤
```

The old code did not do that. It pattern-matched **the whole formula** against
the single shape `And(lo ≤ v, v ≤ hi)` and `continue`d otherwise — so for any
state narrowing two or more variables, which parses as `And(And(..),..)`, it
returned `⊤`: no hints whatsoever, not even for the variables it could read.

Now observe why this is undetectable. `⊤` is the identity for `⊓`, so the
consumer's assumed facts are always a *subset* of the true facts. Fewer assumed
facts prune fewer paths. Fewer pruned paths can only lose proofs, never
manufacture one. The defect is therefore **soundness-preserving**, and
consequently:

- every soundness test passes — nothing unsound is ever derived;
- every ablation passes — removing an engine still only removes evidence;
- metamorphic testing passes — the loss is deterministic and preserved under
  meaning-preserving edits;
- the corpus labels pass — the result is UNKNOWN, which is never WRONG.

`UNKNOWN` is the absorbing state of all four oracles. The *only* observable of
a sound precision loss is the score, which makes score noise the detection
floor: at the ±15–30 points this repository has documented, a defect worth +10
sits underneath it indefinitely. And indeed it was not found by measurement at
all — `docs/interval-ai-hint-path.md` recorded it in prose as #105, "publishes
a multi-variable conjunction that the only reader structurally cannot parse",
from reading the two functions side by side.

Two rules follow, and they are cheap:

1. **A reader of a conjunctive artifact must be a homomorphism from syntactic
   `∧` to lattice `⊓`, with unparsed leaves mapped to `⊤`.** Never match the
   conjunction as a whole; an unreadable conjunct must cost only itself. This is
   now pinned by `an_uninterpretable_conjunct_does_not_hide_the_bounds_beside_it`.
2. **A partial interpretation must count what it declined.** A reader that
   drops input silently is indistinguishable from a producer that published
   nothing, and the two have entirely different fixes. One counter, logged, in
   the consumer.

The first rule generalises past this reader: it is the structural reason a
producer and a consumer can agree on a *type* and disagree on a *language*,
which is the fault `CLAUDE.md` lists first among faults between engines.

## 5. The rules, collected

For any gate that compares a system against an intervened version of itself:

1. **Assert the intervention, do not request it.** The system reports what it
   did; the harness checks that against what it asked for; a mismatch is
   reported next to the result, in the same output a human reads.
2. **An inert row is not a negative result.** Say which rows were inert.
   Silence about them is indistinguishable from evidence.
3. **Name interventions from the system's own vocabulary.** These ids come from
   `Engine::id` at runtime, not from module names or from memory. Anything
   conditionally constructed will drift.
4. **Prefer varying one property of a real program over a fixture whose
   behaviour you predicted** — carried over from
   `docs/interval-ai-hint-path.md`, where it was learned the same way.
5. **A soundness-preserving defect will pass every correctness oracle.** If a
   mechanism is believed to help and the score does not move, the live
   hypotheses are "it never ran", "its output was discarded" and "the gain is
   under the noise floor" — before any hypothesis about the mechanism itself.

## References

- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh. *Efficient Detection
  of Vacuity in ACTL Formulas.* CAV 1997, LNCS 1254, 279–290. Journal version:
  *Efficient Detection of Vacuity in Temporal Model Checking*, Formal Methods
  in System Design 18(2):141–163, 2001.
- Orna Kupferman, Moshe Y. Vardi. *Vacuity Detection in Temporal Model
  Checking.* STTT 4(2):224–233, 2003; earlier at CHARME 1999, LNCS 1703, 82–96.
- Timothy A. Budd, Dana Angluin. *Two Notions of Correctness and Their Relation
  to Testing.* Acta Informatica 18(1):31–45, 1982.
- `docs/interval-ai-hint-path.md` — the hint path itself, and the three pieces
  of work that died on it.
- `CLAUDE.md`, "Measurement Discipline" and "Faults Between Engines".
