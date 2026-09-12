# Predictions, written before running anything

Every probe asserts something a Java programmer would call obvious, and every
one is TRUE by construction. So a failure is a precision result, not a bug.

Grounded in what the repo already records as weak: #95 (heap contents — statics,
instance fields, array cells), #96 (the failed array-element nullness attempt),
#28 (string terms lost through arrays), #18 (CHC declines any body touching
arrays or the heap), and `body_uses_heap_ops` in chc.rs.

The prediction is a split: **control flow is handled, state is not.** Anything
resting on the *contents* of a heap object, a collection or an array should
fail, and anything resting only on which branch runs should pass.

| probe | predicted | why |
|---|---|---|
| InheritedOverride | pass | devirtualisation, no state |
| TryFinallyRunsOnce | pass | a static int, exception edges already modelled |
| EnumSwitch | fail | enum constants are statics initialised in `<clinit>`, which is deliberately not seeded |
| VarargsSum | fail | synthesises an array and reads its elements back |
| InterfaceDispatch | fail | two allocations, a field read per implementation |
| StringBuilderLoop | pass | StringBuilder length is explicitly modelled |
| BoxedEquality | fail | `Integer.valueOf` then `equals` on the boxed contents |
| ArrayListSum | fail | collection contents; `get` is a partial function and not allowlisted |
| HashMapGetAfterPut | fail | map contents plus an unboxing NPE obligation |
| IteratorVisitsEveryElement | fail | `Arrays.asList` then iteration — collection contents |
| StringSplitLength | fail | `split` returns a String[]; #28 is exactly this |
| NullFieldAfterConstructor | pass | constructor parameter nullness was fixed and is in the NRE canaries |

Predicted: 4 pass, 8 fail.

If markedly more pass than that, my model of the engine is wrong in an
optimistic direction and the weak-spot issues need re-reading. If markedly
fewer, the gap is wider than the issues suggest.

---

## Results

Run 2026-09-10, both properties, 60s budget. Ground truth for all twelve
confirmed on a real JVM with `-ea` before ajave saw them.

**7 pass, 5 fail on valid-assert. The prediction was 9/12 correct, and the three
misses were all pessimistic** — `EnumSwitch`, `VarargsSum` and
`HashMapGetAfterPut` proved when I expected them to fail. Being wrong in that
direction is worth recording: the weak-spot issues describe the engine as
narrower than it is.

| probe | VA | NRE | predicted |
|---|---|---|---|
| EnumSwitch | TRUE | UNKNOWN | fail — wrong |
| VarargsSum | TRUE | TRUE | fail — wrong |
| HashMapGetAfterPut | TRUE | TRUE | fail — wrong |
| InheritedOverride | TRUE | TRUE | pass |
| TryFinallyRunsOnce | TRUE | TRUE | pass |
| StringBuilderLoop | TRUE | TRUE | pass |
| NullFieldAfterConstructor | TRUE | TRUE | pass |
| ArrayListSum | UNKNOWN | UNKNOWN | fail |
| IteratorVisitsEveryElement | UNKNOWN | UNKNOWN | fail |
| StringSplitLength | UNKNOWN | UNKNOWN | fail |
| BoxedEquality | UNKNOWN | TRUE | fail |
| InterfaceDispatch | UNKNOWN | TRUE | fail |

`HashMapGetAfterPut` proving while `ArrayListSum` does not is the sharpest
result here: a single put/get *is* modelled, and contents read back through a
loop bounded by the collection's own size are not.

### Three distinct blockers, not one

The five failures are not one gap. Each was read from the engine's own refusal
logging rather than guessed:

1. **`BLOCKER all_paths_complete`** (`ArrayListSum`, `IteratorVisitsEveryElement`)
   — `size()` and `hasNext()` are unmodelled, so a loop bounded by a
   collection's own length has no bound at all, unrolls to the cap and
   truncates. `for (int i = 0; i < xs.size(); i++)` is probably the single most
   common shape in real Java that the portfolio cannot see through.

2. **`BLOCKER skipped_obligation`, violation withheld** (`BoxedEquality`) — the
   BMC finds the assertion satisfiable through an unmodelled `Integer.equals`,
   then suppresses its own witness because it has no nondet values to blame and
   could never replay. Suppressing is correct; the obligation is then skipped
   and nothing over-approximating picks it up. This one is a *contract* gap, not
   an engine gap.

3. **`BLOCKER violated`, refuted by replay** (`InterfaceDispatch`) — an
   unresolved interface call makes the assertion trivially falsifiable, so a
   violation is published and JVM replay withdraws it. CHC cannot take over:
   `chc-imprecision: rvalue GetField`. Two independent gaps must close.

### Why these are not corpus benchmarks

Every constant in `CLAUDE.md` was fitted while looking at `sv-benchmarks/`,
which is also what we score on. These twelve were written from the shape of
ordinary Java and nothing else, so they are a held-out set in the sense #47
asks for. The five failures are now in `benchmarks/ajave/real-world/`, added
before any fix, each with its ground truth argued from the JLS and its blocker
named.

---

## After the collection fixes (2026-09-10, one binary, 60s)

`ArrayListSum` moves **UNKNOWN/UNKNOWN → TRUE/TRUE**. Eight of twelve now prove
on valid-assert, against seven before and four predicted.

| probe | VA | NRE |
|---|---|---|
| ArrayListSum | **TRUE** | **TRUE** |
| EnumSwitch | TRUE | UNKNOWN |
| HashMapGetAfterPut | TRUE | TRUE |
| InheritedOverride | TRUE | TRUE |
| NullFieldAfterConstructor | TRUE | TRUE |
| StringBuilderLoop | TRUE | TRUE |
| TryFinallyRunsOnce | TRUE | TRUE |
| VarargsSum | TRUE | TRUE |
| BoxedEquality | UNKNOWN | TRUE |
| InterfaceDispatch | UNKNOWN | TRUE |
| IteratorVisitsEveryElement | UNKNOWN | UNKNOWN |
| StringSplitLength | UNKNOWN | UNKNOWN |

**Corpus: 871 + 1182 = 2053, against 870 + 1183 = 2053 before. Net zero.**

That number is the finding, not a disappointment. A change that takes a program
from unprovable to proved, and moves the score by nothing, is a direct
measurement of how little the corpus resembles the population — which is what
this document was written to test. It also means the case for keeping the change
rests on the held-out set, exactly as it did for defaulting `AJAVE_ASK` on at
neutral. Without a held-out set neither decision is defensible; with one, both
are.

### The three remaining, and what each needs

* `IteratorVisitsEveryElement` — the only one needing real new machinery. `next()`
  has no index to offer, so it wants a per-iterator ghost cursor incremented on
  each call and tied to the same length. Everything else here was wiring.
* `StringSplitLength` — a `String[]` with a length nothing computes (#28).
* `BoxedEquality` — `Integer.equals` on two boxed ints has a specified result and
  is simply unmodelled. Confirmed as a known hole independently: our own
  `jvm-boxing/IntegerCacheIdentity` and `OutsideCacheUseEquals` are unproven too.
* `InterfaceDispatch` — needs two gaps closed at once: devirtualisation over the
  candidate types, and a CHC encoder that does not decline on `GetField` (#18).
