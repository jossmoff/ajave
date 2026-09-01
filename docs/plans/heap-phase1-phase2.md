# Heap work: detailed plans for phases 1 and 2

Companion to `docs/plans/heap-modelling.md`, which explains why k-induction is
the host and why CHC is not. This is the implementation detail for the first two
phases. Phase 1 involves no heap at all and is the go/no-go for phase 2.

---

# Phase 1 — Unstarve the base case

## The problem, exactly

`smt_bmc/mod.rs` publishes `Status::Bounded { k }` — "no violation of this
obligation within k steps" — inside:

```rust
if !ctx.exhausted && ctx.budget_left() {
    if ctx.completeness.all_paths_complete {
        ... per-obligation discharge ...
    } else if violations_empty {          // <-- global gate
        for oref in bb.open() { ... publish Bounded ... }
    }
}
```

`violations_empty` is a **program-wide** gate: one candidate violation anywhere
suppresses the bounded status of *every* obligation. Measured, no `algorithms`
task under valid-assert produces a `Bounded` artifact — **0 of 20** — so
k-induction never runs on any of them. That is the concrete reason it
contributes nothing, independent of heaps.

## Why this is clearly wrong

The discharge branch immediately above it was already migrated away from exactly
this gate, and says so:

> Per-obligation discharge: an obligation can be discharged if the exploration
> was complete enough AND *this specific obligation* has no violation and was
> not skipped. This is strictly more powerful than the old `violations_empty`
> global gate — a violation on obligation A no longer prevents discharging
> obligation B.

`Bounded` was simply never migrated with it.

## The change

Replace the global gate with the same per-obligation test the discharge branch
uses:

```rust
} else {
    for oref in bb.open() {
        if &oref.method == entry
            && !ctx.skipped_obligations.contains(&oref.id)
            && !violated_oids.contains(&oref.id)        // <-- per obligation
        {
            ... publish Bounded ...
        }
    }
}
```

## Soundness argument

`Bounded { k }` asserts only "no violation of *this* obligation within k steps".
The BMC already computes `violated_oids` per obligation, so the test is exact
rather than approximate. A violation of obligation A says nothing about
obligation B, which is precisely the reasoning already accepted for discharge.

`skipped_obligations` must stay in the test, and for a reason worth restating:
those are obligations whose violation was *suppressed because the path was
tainted*. The solver did find a satisfying assignment for the error path, so
their bounded status would be a claim we know to be false.

## Deliberately NOT in this phase

**Do not switch `bb.open()` to `bb.open_or_unconfirmed()` here.** The discharge
branch does, but for `Bounded` it would feed k-induction obligations that carry
an unconfirmed violation, and a proof from an engine with a latent soundness bug
would then override a real candidate. That is exactly how CHC's LIA/32-bit bug
turns into a wrong TRUE (see `heap-modelling.md`). Widen one thing at a time.

## How to measure

1. `--set smoke` and `--set ajave` — must stay 0 wrong.
2. Count `Bounded` artifacts before/after on 20 `algorithms` valid-assert tasks;
   the metric for this phase is "does k-induction get a base case at all".
3. **Both** properties on the full corpus. Anything that lets a new engine
   discharge must be measured on valid-assert *and* no-runtime-exception; the
   canaries that catch these live on valid-assert.

## Acceptance

- `Bounded` published for at least some `algorithms` obligations.
- k-induction is observed attempting a step case where it previously did not.
- Zero wrong answers on both properties.

## Expected outcome, honestly

Probably few or no new correct answers *by itself*: k-induction's encoder havocs
every heap read, so the tasks it now reaches will mostly fail their step case.
The value is that it makes phase 2 testable. **If phase 1 shows k-induction
still cannot attempt anything useful, stop — phase 2 has no consumer.**

---

# Phase 2 — Give `smt_encode` the BMC's heap

## What is missing

`smt_encode.rs` is k-induction's encoder and has no heap:

| Construct | Current treatment |
|---|---|
| `ArrayLoad`, `ArrayLength`, `NewArray`, `InstanceOf` | `fresh("havoc", 32)` |
| `GetField`, `GetStatic` | `fresh("havoc", field_width)` |
| `ArrayStore`, `PutField`, `PutStatic` | **ignored** (`=> {}`) |

This is sound — an unconstrained read over-approximates every value — but it can
prove nothing about a heap, because every write is discarded. Any obligation
whose truth depends on a stored value has a trivially satisfiable violation
term, so `try_step_case` returns "not proved" for all of them.

## What to port

From `smt_bmc/encode.rs`, whose model is already sound and already models Java's
32-bit arithmetic exactly:

1. **Field arrays.** One SMT array per resolved field key, `ref -> value`
   (`get_field_array`, `field_key_resolved`). Burstall–Bornat field splitting:
   distinct fields cannot alias, for free.
2. **Array elements.** `array_select_lookup` / `array_store_update`.
3. **A length map**, `ref -> length`, so `ArrayLength` and bounds obligations are
   expressible without reading an element.
4. **Allocation identity.** `New` / `NewArray` yield fresh references, distinct
   from every other live one. Without this two arrays may alias and a write can
   be erased.

## The one real design difference

This is a port, but not a transcription, and this is why:

- `smt_bmc` explores **one path at a time**, so it holds a single mutable heap
  and updates it as it goes.
- `smt_encode` encodes **the whole body as one formula**, joining reaching
  definitions at merge points with `ite(path_cond, v_then, v_else)`.

So the heap must become an SSA value like any other, merged at joins with the
same `ite`. SMT arrays are first-class terms, so `ite` over two array terms is
well-formed and needs no new machinery — but the merge must actually be written,
and it is the part `smt_bmc`'s code does not contain.

Two consequences:

- Heap terms must carry the `frame` prefix `encode_body` already threads, so
  k-induction can hold several frames in one solver context.
- The heap at body entry is a **fresh unconstrained array**, which is exactly
  right for an inductive step: assume nothing about the incoming heap.

## Order of work

1. Field arrays only (no arrays-as-in-`int[]`), with join merging. Smallest
   change that makes any heap obligation provable.
2. Array elements plus the length map.
3. Allocation identity and disequality.
4. `PutStatic` / `GetStatic` on the same mechanism.

## Acceptance

- `benchmarks/ajave/heap/ArrayInvariantHoldsForAllElements` proves.
- Its twin `ArrayInvariantViolated` still reports FALSE. **Both** matter: an
  encoding that says TRUE for anything containing an array passes the first and
  fails the second.
- The `BellmanFord-MemUnsat01` and `InsertionSort-MemUnsat01` canaries stay
  correct — they caught the CHC attempt and are the sharpest signal here too.
- Zero wrong answers on both properties.

## Risks

- **Solver cost.** Arrays make queries markedly harder. k-induction has no
  wall-clock bound on its solver either; add one *before* this lands, as was
  done for CHC.
- **Silent over-approximation.** If a write is dropped anywhere in the port, the
  encoding stays sound but proves nothing, and looks like "the technique does
  not work" rather than a bug. Add a debug assertion that every `ArrayStore` and
  `PutField` produced a new heap term.
- **Phase 3 may still not converge.** The port makes heap properties
  *expressible*; finding the loop invariant is a separate problem, and Spacer
  already declined on BellmanFord. Do not treat phase 2 landing as evidence that
  phase 3 will.
