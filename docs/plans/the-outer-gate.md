# The outer discharge gate, and the 135 tasks behind it

**Status:** plan, not implemented. Written 2026-10-30 against `main` at `fdd9b6e`
(corpus 2058).

## The measurement

`tools/blocker_census.py` over the 409 **declined** task-property pairs — the
unproven population with known timeouts and the one SV-COMP mislabel held out.
Five chunks, `--jobs 6 --timeout 300`.

| why not | tasks | % | expects TRUE | expects FALSE | ceiling |
|---|---|---|---|---|---|
| **budget** (`all_paths_complete`) | 135 | 33% | 98 | 37 | +233 |
| **float-escalation** (`float_arith_approximated`) | 76 | 19% | 48 | 28 | +124 |
| refuted (`violated` stands) | 61 | 15% | 25 | 36 | +86 |
| no-candidate (nothing published) | 60 | 15% | 53 | 7 | +113 |
| theory (`skipped_obligation`, `has_tainted_paths`) | 44 | 11% | 26 | 18 | +70 |
| model (havoc / unresolved) | 31 | 8% | 19 | 12 | +50 |
| refuted-witness | 1 | 0% | 1 | 0 | +2 |

Ceilings are arithmetic, not forecasts: they assume every task in a bucket
converts, which none will.

### Two corrections this census went through, both worth keeping

**`refuted-witness` was an artefact of bucket precedence.** The first run put it
first in `classify()` on the reasoning that "the witness is the proximate reason
this task scores nothing", and reported it at **211 of 409 (52%)** with a claimed
+228 recoverable. Both figures were withdrawn. `BellmanFord-FunSat01` disproved
the premise: it carries a refuted witness *and* `BLOCKER all_paths_complete`,
with `discharged=0` from every engine. Remove the spurious violation and the
obligation is merely open-and-unproven — UNKNOWN either way.

That is not speculation about the architecture, it is what the architecture
guarantees. `open_or_unconfirmed()` offers violated obligations to
over-approximating engines, precisely so "whichever engine published first"
cannot win outright. `verdict_excluding()` recovers TRUE when a refuted
violation is the only obstacle, and refuses to when the obligation has no
independent proof. Both were built for this case and both work. Corrected
bucket count: **1**. The 358 refuted witnesses are real and now travel as an
annotation column, never as a cause.

**`float_arith_approximated` was hiding in "unclassified".** 76 tasks, 19%,
behind the word *other*. It now has its own bucket because the work it responds
to is unlike every other row: the theory exists and is implemented, and what is
missing is the FPA escalation pass reaching the obligation. Coverage, not
capability. See gh #48 and task #27.

## The mechanism behind the 135

`smt_bmc/mod.rs`, the discharge loop:

```rust
let at_risk = if ctx.completeness.all_paths_complete {
    HashSet::new()
} else {
    obligations_at_risk(prog, &ctx.cut_points)
};
...
// Safety net: if a cut was recorded but produced no at-risk set,
// something is unaccounted for and the old global behaviour stands.
let cuts_accounted = ctx.completeness.all_paths_complete || !at_risk.is_empty();
if cuts_accounted { /* per-obligation discharge */ }
else { /* refuse every obligation in the run */ }
```

Task #20 already made the completeness test per-obligation. The outer gate
bypasses that work in one specific case: **a cut was recorded and `at_risk` came
back empty.** Then nothing is discharged, whatever it was.

`obligations_at_risk` does forward reachability from each cut point (normal and
exceptional successors), collects `Stmt::Check` obligations in reachable blocks,
and transitively taints the *callees* of reachable call sites. Callers are
covered separately: `mark_incomplete` records the cut block **and every frame
above it**, because a cut inside a callee means the caller never returned.

### Empty `at_risk` has two causes and the code cannot tell them apart

1. **A cut was dropped.** `prog.body(mk)` returns `None` and the loop
   `continue`s. The cut is silently discarded, nothing is marked, and refusing
   everything is the *correct* response.
2. **The cut endangers nothing.** Every cut resolved, and no cut reaches an
   obligation or a call. Refusing everything is pure loss.

Instrument the refusal; do not infer which it is. This is the same shape as
C1, where adding refusal logging produced gh #111 within minutes.

## The soundness problem that must be solved first

**`at_risk` is not complete today, so "empty ⇒ nothing at risk" is unsound.**

`obligations_at_risk` follows only the **static** target of
`Rvalue::Call { target, is_virtual }`. Nothing in the workspace enumerates
overrides — `is_virtual` is recorded by the lifter and never consulted here.
So a cut-reachable *virtual* call whose runtime target is an override is
followed to the wrong body, and obligations in the override are omitted from
`at_risk`.

That means the safety net is doing real work rather than merely being
over-conservative, and loosening it without fixing this would be a wrong-TRUE
generator of exactly the kind this project has produced twice (#101, #106).

## Plan

### Phase 0 — make `at_risk` sound for virtual dispatch

Taint every method that overrides the static target of a reachable virtual
call, not just the static target. The class hierarchy is already available
(`Program::is_subtype`); what is missing is the reverse query, "every method
with this `(name, desc)` on a subtype of this class".

- New helper on `Program`, with the reverse-lookup built once per program
  rather than per cut.
- Test named after the argument:
  `a_cut_reaching_a_virtual_call_puts_every_override_at_risk`.
- This change can only **enlarge** `at_risk`, so it is monotone in the safe
  direction and cannot create a wrong TRUE on its own. Measure it alone first:
  it may *reduce* the score by making more obligations at-risk, and that cost
  is the honest price of the gate below being trustworthy.

### Phase 1 — instrument the refusal, change nothing

Replace the single `cuts_accounted` boolean with a reason:

```rust
enum CutAccounting {
    Complete,                 // all_paths_complete, no cuts
    Accounted(HashSet<..>),   // cuts resolved, at_risk non-empty
    Harmless,                 // every cut resolved, reaches no obligation
    Dropped { methods: Vec<MethodKey> },  // a cut had no body
}
```

Log `Harmless` and `Dropped` distinctly. Run the 135-task budget set and report
the split. **Expected outcome unknown — that is the point.** If `Dropped`
dominates, Phase 2 is worthless and the real bug is wherever those bodyless cut
points come from.

### Phase 2 — discharge under `Harmless`, if Phase 1 justifies it

Soundness argument, to be written into the code beside the gate and defended by
a test named after it:

> Every cut point resolved to a body. From each, forward reachability over
> normal and exceptional successors reaches no `Stmt::Check`, and no call site
> whose static target or any override holds one. `mark_incomplete` records
> every caller frame above a cut, so a truncation inside a callee is itself a
> cut point in the caller. Therefore no open obligation lies on a path the
> truncation hid, and discharging them is exactly as sound as discharging under
> `all_paths_complete`.

Premises to verify rather than assume, each its own test:
- (a) every cut point resolved — Phase 1 establishes this at runtime
- (b) reachability is a superset of execution — covers exceptional edges and
  overrides after Phase 0
- (c) caller frames are recorded — `mark_incomplete` does this; needs a test
  that fails if it stops

### Phase 3 — float-escalation, separately

76 tasks, and the cheapest row on the table because the theory is implemented.
The BV pass correctly refuses; the FPA pass must reach the obligation. Overlaps
task #27 and gh #48. Scoped separately so it cannot be confused with the gate
work during measurement.

## Measurement protocol

The buckets give a ready-made before/after population, which is the thing that
has been missing from previous attempts at this area.

- `budget` target set: the 135 pairs, written out by the census.
- Each phase measured **alone**, on an idle machine, against that set — never
  two phases in one run, because an inert change and a harmful one cancel.
- Smoke `--check`, `--repeat 3`, `engine_ablation.py` and `metamorphic.py`
  before any corpus claim. Phase 0 enlarges `at_risk`, so the ablation and
  determinism gates are the ones that matter.
- A score improvement with no soundness argument is a red flag, and Phase 2 is
  the phase where that applies.

## Docs to change

| file | change |
|---|---|
| `CLAUDE.md` | the "Faults Between Engines" section lists whole-run flags as a known hazard; add the outer gate as the measured instance, with the 33% figure |
| `docs/plans/cooperation-options.md` | no flag is proposed here; note that if Phase 2 lands behind one, the table gains a row |
| `changes.md` | one entry per phase, with the measurement, not one entry at the end |
| this file | kept as the record of what was planned versus what happened |

## What would falsify this plan

- Phase 1 shows `Dropped` dominates → Phase 2 is dead, and the work is finding
  why cut points have no body.
- Phase 0 costs more than Phase 2 gains → the gate is correctly conservative
  and the 135 are a genuine budget problem, which makes this a scheduling
  question and not a gate question.
- The 135 turn out to be dominated by tasks whose obligations are *also*
  blocked for another reason, exactly as `refuted-witness` was. The census
  reports one dominant blocker per task; a second blocker behind it would not
  show. **Check this before Phase 0** by re-running a sample of the 135 with
  the gate forced open and seeing whether anything discharges at all.
