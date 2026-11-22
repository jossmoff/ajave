# houdini_engine

**Direction:** Over
**Tier:** 1 (invariant synthesis, alongside the interval domain)
**Status:** working, **off by default** (`AJAVE_HOUDINI=1`), publishes without
concluding
**Source:** `ajave-engines/src/houdini_engine.rs` (the engine) and
`ajave-engines/src/houdini.rs` (the elimination algorithm)

Owed since `91d963c` registered the engine, which `scripts/check-strategy-docs.sh`
caught on PR #132 — the rule is that this file lands *before* registration, and
it did not.

## What it proves or finds

Houdini (Flanagan & Leino, FME 2001). Given a finite pool of candidate
predicates per block, it starts from their conjunction and repeatedly deletes
any candidate that is not preserved, until nothing more can be deleted. What
survives is the **greatest inductive map** expressible as a conjunction of pool
members — unique, independent of elimination order, and reached in at most one
pass per candidate.

The pool comes from `Blackboard::candidate_conjuncts`: every distinct conjunct
any engine has already claimed about the method. So this engine is parasitic by
design — it has no abstract domain of its own and proposes nothing the portfolio
did not already say somewhere.

It publishes `Artifact::InvariantMap`. It does **not** discharge anything.

## What it assumes / where it's unsound if the assumption breaks

Two queries carry the whole argument, both in `LiaEncoding`:

- **initiation**: `¬M(entry)` is UNSAT.
- **preservation**: for every edge `b → c`,
  `M(b) ∧ (T_{b→c} ∨ ovf_b) ∧ ¬M(c)′` is UNSAT.

The `ovf_b` disjunct is the part that is easy to get wrong and was wrong before
`712b670`. Preservation is checked in linear integer arithmetic, where integers
are unbounded, so `0 ≤ sum` is preserved by `sum = sum + 2` in LIA and false on
a JVM once the addition wraps. Treating overflow as an extra transition with an
unconstrained post-state — "an exceptional edge in disguise" — restores
soundness without demanding that invariants exclude overflow. The theorem and
its proof are in `docs/proposals/lia-faithfulness.md` §3.

Range axioms are asserted of the **pre-state only**. Asserting `range(x′)`
beside `x′ = x + 1` silently removes the overflowing transition from the model
instead of describing it, which makes every `ovf` unsatisfiable and every test
of the guard pass for the wrong reason. Pinned by
`range_axioms_are_asserted_of_the_pre_state_only`.

Published with `Approximations::INT_WRAPPING`, because the map means "inductive
in the arithmetic the LIA encoder models", not "true at this block".

**The map must not reach `interval_hints_for_method`.** It did, in `91d963c`,
and produced ajave's own wrong TRUE (#130): the BMC reasons in bitvectors and
uses a hint to *prune*, so a hint sound only in unbounded arithmetic deleted a
throwing path and `all_paths_complete` still held. `interval-ai`'s own bounds
were safe in that channel only because that domain models wrapping — so the
channel broke when a second producer joined it. See `docs/contracts.md` §2.

## Known incompleteness (things it will correctly say UNKNOWN about)

**It finds conjunctions and nothing else**, which is the binding constraint
rather than a detail. A counting loop needs `x < n` to know its increment cannot
overflow, and no conjunction of unary bounds over `x` and `n` separately says
that. Filed as #131, with
`benchmarks/ajave/engine-ai/ALowerBoundSurvivesOnlyIfTheIncrementIsBounded` as
the minimal case.

Measured, one build, 69 loop-heavy unproven pairs:

| | correct | unproven | WRONG | score |
|---|---|---|---|---|
| `AJAVE_HOUDINI=0` | 5 | 64 | 0 | 10 |
| `AJAVE_HOUDINI=1` | 5 | 64 | 0 | 10 |

Identical. Not "a small gain lost in noise" — the same tasks, the same
verdicts. Since the plumbing demonstrably runs, the honest reading is that the
hypothesis class is what fails, which is what makes the ICE line of work
(implication counterexamples, Horn-ICE for the multi-block case this map
already is) the natural successor rather than more candidates.

Also absent: nothing promotes a map to `InvStatus::Inductive` outside
`AJAVE_CERTIFY_TRUE`, and an unrenderable candidate is dropped rather than
approximated (`an_unrenderable_candidate_is_dropped_from_the_pool`).

## How it's certified (which `Certifier` checks its output, if any)

`invariant_check::check_map_inductive`, which re-runs initiation and
preservation through the same `LiaEncoding` query builders — deliberately the
same ones, so a fix to the relation cannot land on one side only. Gated behind
`AJAVE_CERTIFY_TRUE=1`.

`#130` records the part not yet fixed: `invariant_check::check_inductive` has
the identical unguarded-preservation hole for *point* invariants, latent only
because that gate is off.

Because the engine publishes and does not conclude, `Artifact::InvariantMap` is
currently **a producer with no consumer** — a state `CLAUDE.md` permits only
when it is declared, which `docs/contracts.md` §2 does.
