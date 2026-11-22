# How `interval-ai` publishes, and why three pieces of work died on it

Written 2026-10-28 after B2, B3 and #103 were each built on a guess about this
path and each failed. Four separate theories were formed for the resulting null
results; one was right and was abandoned because a hand-built test fixture
appeared to contradict it. This document exists so the next person reads rather
than guesses.

## The path, in order

`AiEngine::init` (`ai.rs`) runs before any engine's `step`.

1. **Whole-program analyses**: `analyze_constructor_fields`,
   `analyze_return_nullness`, `stable_stream_statics`, `analyze_field_precision`.
   These always run and feed `IntervalCpa`.

2. **Early returns**, each logged at INFO as `interval-ai: declining — …`:
   no entry method; entry has no body; entry not fully lifted (any
   `Terminator::Diverge`); entry uses `long`.

3. **Float loops take a different route.** If the entry uses float types *and*
   has loops, `init` runs `explore` with `WidenAtLoopHeaders` (cap 2000) and —
   on success — calls `discharge_obligations`. It **publishes no hints** and
   returns. This path exists to beat the BMC to float-loop obligations.

4. **Everything else**: `explore(&cpa, &Sep, prog, &start, (), 1000)`, then

   ```rust
   if complete {
       self.publish_interval_hints(entry, &reached, bb, body);
   }
   ```

## The two facts that matter

### `Sep` means no widening, so an unbounded loop never converges

Step 4 explores with `&Sep` — pure path sensitivity. A loop whose trip count is
not statically known enumerates states until `max_states = 1000`, returns
`complete = false`, and **nothing is published at all**, however precise the
intervals were.

Measured, three programs differing only in their loop:

| program | hints the BMC applies |
|---|---|
| bounded loop (`for i in 0..3`) | **83** |
| unbounded loop (`for i in 0..n`, `n` nondet) | **0** |
| no loop | 32 |

The gate is **correct and must stay**. An incomplete exploration has not visited
every reachable state, so a per-point interval derived from it may not hold on
an unvisited path — and `smt-bmc` asserts a hint as a *fact*. Publishing from an
incomplete run would be unsound.

Note the asymmetry with step 3: the *harder* case (float loops) widens and
converges; the general case does not widen and does not.

### Hints are per **block entry**, so a single-block body publishes nothing

`join_block_intervals` skips any state whose `location().index != 0`. Only
block-entry states contribute. A body with one block has exactly one such state
— the method entry, where nothing is known yet — so it publishes nothing even
though it converges trivially.

This is what made a hand-built single-block fixture look like a counterexample
to the gate above. It was not; it was testing something else.

## What this means for work that depends on hints

The AI's precision reaches a consumer only when the exploration converges, and
it converges only when the BMC could usually have unrolled the program anyway.
**The AI is precise where the BMC is already sufficient, and silent where the
BMC is stuck.** That is the structural reason three separate pieces of work
measured exactly zero:

- **B2** (site-indexed field cells) and **B3** (array element intervals) — see
  #104. Both now resolve correctly, and neither can reach a consumer on a
  loop-bearing program.
- **#103** (disjunctive hints) — attempted and reverted. Blocked identically.

## Where the leverage actually is

Two candidates, both different work from refining the abstract domain:

1. **Make step 4 converge.** `WidenAtLoopHeaders` already exists and is already
   used by step 3. Using it (or a widening policy) for the hint exploration
   would make `complete` true far more often. The cost is precision at loop
   headers and the risk is timeouts; it is a measurement, not an argument.
2. **Publish something sound from an incomplete run.** Facts about *visited*
   points only, which needs an argument about what "visited" guarantees when the
   search was truncated. Harder, and worth less than (1) until (1) is measured.

Also outstanding and independent: #105, where `interval_state_as_formula`
publishes a multi-variable conjunction that the only reader structurally cannot
parse.

### Update, 2026-11-22: #105 was worth +10 points

Fixed in `f26ed94` and measured afterwards, which is the only reason the size is
known. Five `no-runtime-exception` tasks — `InsertionSort-MemUnsat01` and four
`MergeSortIterative` variants — are UNKNOWN at main (`21ec85c`) and TRUE at
`f26ed94`, at +2 each. They were the whole of a score delta that had been
credited to four later commits and a different branch.

The reader required the formula to be *exactly* `And(lo <= v, v <= hi)`, so any
state narrowing two or more variables parses as `And(And(..),..)` and was
dropped whole — no hints at all, not even for the variables it could read. With
the portfolio cut to `interval-ai` alone on both builds, the engine proves the
*identical* obligations either way (15/27 in `merge`, 7/9 in `main`, 4/4 in
`iterativeMergesort`); what changes is who closes the other twelve:

```
main 21ec85c:   Main.merge#18 -> Open
f26ed94:        Main.merge#18 -> Discharged { by: smt-bmc-fpa, proof: Exhaustive }
```

So this document's prediction was right and understated: the leverage was not
only in making step 4 converge, it was in the reader that discarded what step 4
already published. Note which engine consumes it — `smt-bmc-fpa`, the second
BMC pass, not `smt-bmc`. An ablation naming `smt-bmc` does not remove it, which
is a separate defect recorded in [`measurement-validity.md`](measurement-validity.md).

Why nothing caught it for its whole lifetime: dropping an unparsed conjunct
yields `Top`, which is sound, so the defect is a *pure* precision loss and
`UNKNOWN` is the absorbing state of every oracle this repository has. See
[`measurement-validity.md`](measurement-validity.md) §4 for the argument and the
two rules that follow.

## The methodological note

Of four theories formed about this path, three were wrong and one was discarded
on bad evidence. The fixtures that misled were hand-built bodies whose behaviour
was assumed rather than checked. The measurement that settled it took one
minute: three real programs differing in exactly one property, counting an
observable the engine already logs.

Prefer varying one property of a real program over constructing a fixture whose
behaviour you have predicted.
