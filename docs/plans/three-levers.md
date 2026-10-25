# Three levers on the engines that discharge nothing

Status: experiment plan, 2026-10-25.

Four of twelve engines discharge zero obligations across a 172-task sample;
two discharge nearly everything. The hypothesis is that this is **not a
capability gap** — it is three scoping decisions, each of which makes an engine
refuse work it could already do.

| engine | tasks discharged on | obligations |
|---|---|---|
| interval-ai | 119 / 172 | 4,646 |
| smt-bmc | 30 | 2,512 |
| chc | 4 | 48 |
| k-induction | 1 | 28 |
| imc, cegar, presolve, smt-bmc-fpa | 0 | 0 |

## Why all three at once, and how attribution survives it

Running them as three sequential experiments costs three full measurement
cycles (~40 min each, both properties, idle-gated) and the levers interact:
L1 widens which bodies an engine accepts, L3 widens which methods, and L2
changes what happens when either still refuses. Measured separately, each would
be evaluated against a portfolio the other two have not yet widened.

So: **implement all three, gate each behind its own environment variable,
default all three ON, and measure the combination plus three single-lever
ablations from one build.** That is exactly the shape `AJAVE_RESUME=0` took,
which is how the resumption work got a defensible +5 rather than an arguable
one. One build, five runs, full attribution.

```
AJAVE_SCOPE_OBLIGATION=0   # L1 off
AJAVE_ASK_ON_DECLINE=0     # L2 off
AJAVE_SCOPE_ALL_METHODS=0  # L3 off
```

## L1 — decline per obligation, not per body

**Scoped to CHC only, and the reason matters.**

Two engines look like they have the same guard and do not:

* `chc.rs:451` refuses any body where `body_uses_heap_ops` holds. That is a
  **capability** guard. CHC havocs what it cannot model, and its own tests state
  why that is sound for an over-approximating engine: an unconstrained value
  contains the real one, so a proof over it holds of the program. Widening what
  CHC attempts is therefore a precision question.
* `cegar.rs:102` refuses the whole program when `body_uses_havoced_ops` holds.
  That is a **soundness** guard. Its comment is explicit: unconstrained abstract
  values collapse the predicate domain to top, "which makes the safety check
  trivially succeed, producing unsound TRUE verdicts". CEGAR's abstract
  interpretation loses safety-critical information where an SMT UNSAT check
  would stay conservative.

So CEGAR's guard is **not** touched by L1. The architecture review already said
so — "that guard carries a real soundness argument, so it is not a cheap unlock"
— and the first draft of this plan proposed unlocking it anyway. Writing the
rule down does not make one follow it; this is the second time this week that
has been demonstrated on the author.

CEGAR still gets L2 and L3, neither of which weakens a guard.

Previously measured: CEGAR skips **109 of 121 tasks** on that guard, so the
single largest refusal in the portfolio stays in place. If it is ever to be
opened, the prerequisite is understanding the collapse mechanism and a test that
fails when the abstraction goes to top — not a reachability filter.

But obligations are individual. One havoc in a 60-obligation method kills all 60,
including the 59 whose paths never reach it.

The test is CFG reachability from the offending statement to the obligation's
`Check` — the same question `obligations_at_risk` in `smt_bmc/mod.rs` already
answers for truncation points, so the shape is established and tested. An
obligation the feature cannot reach is one the engine may attempt.

**Soundness.** The direction is the dangerous one: this lets an over-approximating
engine attempt more obligations, and a discharge is a claim about every
execution. So the reachability must be *over*-approximate — if in doubt, the
obligation is excluded. Block granularity, forward reachability, every
successor including exceptional edges.

Deliberately not full backward slicing. Slicing is the stronger version and
`ajave-opt` (`dce`, `copy_prop`, `compact`, already wired behind
`level_from_env`) is the machinery for it, but it rewrites the body, which
changes `VarId`s and therefore every obligation and invariant keyed by them.
Reachability answers the same question for this experiment without touching the
IR.

## L2 — a decline becomes a question

91 early returns refuse work; most say nothing. When CEGAR meets a havoc it
returns `Blocked`. It should `ask`: *what is the range of `v7`?*

The machinery is built and on by default as of this week — `Query`/`Lemma`,
`Interest::LEMMA`, and a scheduler that re-enters an engine exactly when its
answer arrives. The producer side exists in the BMC only. This generalises it:
an engine that cannot proceed publishes the question that would unblock it, and
`ranges` or any later answerer can respond.

This makes every alternative engine *also* a resource **without changing its
analysis** — only its failure mode. That is the whole appeal.

Scope for this experiment: the havoc and unresolved-call declines in `cegar`
and `chc`, which are the two measured as refusing most.

## L3 — analyse methods other than the entry

`cegar.rs` filters `oref.method == *entry`. An obligation in a helper method is
invisible to it — not declined, never considered. `chc`'s single-method
encoder is chosen per body and reached only for the entry.

So an engine's reach is bounded by one method, in a corpus where the BMC
routinely inlines four deep. Lift the loop over methods, analysing each body
that has open obligations.

**Soundness.** A per-method proof is a proof about that method under
*unconstrained parameters* — strictly more conservative than one under the
caller's actual arguments, so a discharge remains sound. The risk is the
opposite: it will often fail, costing time. Hence the gate and the ablation.

## Measurement protocol

Non-negotiable, from `CLAUDE.md`:

1. `cargo test`, `clippy`, `fmt` clean. `metamorphic.py` and `engine_ablation.py`
   on the smoke set.
2. Smoke must not regress — noting the gate is currently stale on three tasks
   (#35), so compare against the same three failures and no more.
3. **Both properties, full corpus, 60s, idle-gated, nothing else running.**
   Loosening what an Over engine may attempt is the wrong-TRUE direction:
   loosening `all_calls_resolved` once read as +22 on NRE and was nine wrong
   TRUEs on valid-assert.
4. Held-out probe set must not regress (8/12 on valid-assert today).
5. Five runs from one snapshot: all-on, then each lever off alone.

## Stop rules

- **Any wrong answer that is not the `ReverseInterpolator` mislabel: revert the
  lever that caused it.** This is the direction where a mistake is −16.
- A lever that is negative or inert on both properties is filed
  `status:explored` with its number and removed, not left behind a flag.
- A lever whose gain depends on a constant fitted to the corpus is not a result.

## Expected outcome, recorded before measuring

L1 positive and largest — it attacks a guard measured to refuse 109 of 121
tasks. L3 positive but smaller, and the most likely to cost time. L2 near-zero
on the corpus and valuable anyway, on the same reasoning that put `AJAVE_ASK`
on by default at exactly neutral: the corpus has few unmodelled-call tasks and
real code is full of them.

If L1 is not positive, the hypothesis that these engines are scope-limited
rather than capability-limited is wrong, and the whole framing needs rethinking.
