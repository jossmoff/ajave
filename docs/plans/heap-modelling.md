# Heap modelling: full plan and feasibility

Written 2026-09-01, after attempting the CHC version and reverting it. Every
claim below is measured; the commands are in the session and the findings are
mirrored on #60.

## Feasibility verdict

**Not as "give CHC a heap theory". That framing is wrong, and doing it now would
ship unsound answers.**

But the underlying goal is feasible, because of one fact that reframes the whole
problem:

> **The heap is already modelled, soundly, in the BMC.** Object fields and array
> elements are SMT arrays over bitvectors (`array_select_lookup`,
> `array_store_update`, `type_array`). Java's 32-bit arithmetic is modelled
> exactly.

So the gap is not *heap modelling*. It is **unbounded proof over a heap that is
already modelled**. That is a different, smaller problem with a different host.

## Why CHC is the wrong host

Four blockers, each independently fatal, found by building it:

**1. CHC's arithmetic is unsound for Java, and only gating hides it.**
The encoding is LIA — mathematical integers. `jayhorn-recursive/UnsatAddition02`
computes `m+n` recursively and asserts unreachability of `m>=100 && n>=100 &&
result<200`. Over the integers that is genuinely impossible and CHC proves it.
Over 32-bit ints `m+n` overflows negative and the assertion fires — the expected
verdict is FALSE.

CHC *discharges* it. The only reason no wrong answer is emitted today is that
`bb.open()` removes the obligation once the BMC publishes its candidate.
Switching to `open_or_unconfirmed` — which any heap work needs, see (2) —
**produces the wrong TRUE immediately**. Verified in isolation, with no heap
changes present.

The file's own comment acknowledges this ("for programs where overflow is the
bug, BMC will find the violation"), but that mitigation is a scheduling
accident, not a soundness argument.

**2. CHC never sees these obligations anyway.** It takes `bb.open()`, and an
unconfirmed violation candidate removes the obligation from that set. Every
array-heavy task already has one, so CHC reaches them with nothing to do — which
is why heap work on it appears to have no effect.

**3. CHC is assertion-only and entry-only.** It filters to
`ObligationKind::Assertion` in the entry method. `algorithms` has 27 unproven
under no-runtime-exception, and CHC cannot touch any of them, nor assertions in
callees. The "+97 ceiling" on #60 assumes otherwise.

**4. Void methods have no summary relation.** `void sort(int[] a)` therefore
threads no heap, and the encoding believes the array is untouched. This produced
five wrong TRUEs; the `BellmanFord-MemUnsat01` and `InsertionSort-MemUnsat01`
canaries caught them.

And beyond correctness: even with the encoding apparently right, Spacer produced
a 350KB query for BellmanFord and did not finish in three minutes.

## What *does* work

Probed before building, and worth keeping:

- Nested heap is the right shape: `H : (Array Int (Array Int Int))` for
  elements, `L : (Array Int Int)` for lengths.
- **Quantified array invariants need `fp.spacer.q3.use_qgen=true`.** On a
  minimal `forall k < i. a[k] == 0` loop the default configuration times out at
  60s; with the flag it proves in under a second.
- The probe discriminates: safe → `sat`, unsafe → `unsat`.

## Why k-induction is the right host, and what blocks it

It reuses a sound encoding instead of replacing an unsound one. Two blockers,
both concrete:

**A. Its encoder has no heap.** `smt_encode` maps `ArrayLoad`, `ArrayLength`,
`NewArray`, `GetField` and `GetStatic` to `fresh("havoc")`, and *ignores*
`ArrayStore`, `PutField` and `PutStatic` entirely. That is sound — an
unconstrained read over-approximates — but it cannot prove anything about a
heap, because every write is dropped.

**B. Its base case is starved.** The BMC publishes `Status::Bounded` only when
there are **no violations at all** in the whole run, and only for entry-method
obligations. Measured: **0 of 20** `algorithms` tasks get a `Bounded` artifact,
so k-induction never runs on any of them. This is the answer to the original
question of why k-induction contributes nothing.

## The plan

Ordered so each step is independently measurable, and so nothing depends on a
later step to be sound.

### Phase 1 — Unstarve the base case (no heap work at all)
Relax `Bounded` publishing from "no violations anywhere" to "this obligation had
no violation". The current rule is far stronger than its own comment justifies:
one unrelated candidate elsewhere in the program suppresses the bounded status
of every obligation.

*Measure alone.* This may move tasks with no heap involvement, and it tells us
whether k-induction is worth feeding before building it a heap.

### Phase 2 — Give `smt_encode` the BMC's heap
Port the array/field encoding from `smt_bmc/encode.rs`: fields and array
elements as SMT arrays over bitvectors, a length map, allocation identity from
`New`/`NewArray`. This is a port, not a design — the semantics is already
settled and already sound.

*Acceptance:* `benchmarks/ajave/heap/ArrayInvariantHoldsForAllElements` proves,
and its `Violated` twin still reports FALSE.

### Phase 3 — Induction over the heap
The step case must relate heap states across iterations. Start with the
quantifier-free fragment (a specific element), then add the quantified
invariant, passing Spacer-equivalent options to whichever solver backs it.

*Risk, stated plainly:* this is where it may not converge, exactly as Spacer did
not on BellmanFord. Budget it, bound the solver, and be prepared to conclude the
category is out of reach.

### Phase 4 — Only then reconsider CHC
If CHC is ever to help it needs, in order: BV arithmetic instead of LIA (1),
summary relations for void methods (4), and widening beyond
assertion-only/entry-only (3). Each is a project. Do not start any of them for
the heap's sake — do them if inter-procedural summaries are wanted for their own
reasons.

## What was kept from the attempt

A wall-clock bound on the Spacer call, which had none. Nothing exposed that
while the heap guard held, because CHC never saw a program hard enough to hang
on. Any future encoding work makes it reachable immediately.

## The honest expectation

`algorithms` is 22 unproven + 7 timeout on valid-assert and 27 + 7 on
no-runtime-exception. Phase 1 may claim a few tasks cheaply. Phases 2–3 are the
real work and their payoff is genuinely uncertain: the loop invariants these
tasks need are the hard case for every technique, and one solver has already
declined to find them. Treat the phase-1 measurement as the go/no-go.
