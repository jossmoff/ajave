# BinaryTreeSearch needs field contents, not shape

`docs/plans/heap-full-implementation.md` makes the two `BinaryTreeSearch` tasks
the acceptance test for **E3 · Disjointness**, the top of a three-checkpoint
chain: ghost depth (E1) → reachability (E2) → disjointness (E3). Reading the
programs shows that is the wrong category, and the tasks are reachable without
any of it.

## What the program actually asserts

```java
BinaryTree b = new BinaryTree();
for (int i = 1; i < N; i++) {
  int n = Verifier.nondetInt();
  if (n >= 0) { b.insert(n); }      // only non-negative values enter the tree
}
int v = Verifier.nondetInt();
Verifier.assume(v < 0);
assert (b.search(v) == false);       // "didn't put in any negative numbers"
```

The needed invariant is

```
∀o. select(value_array, o) ≥ 0
```

a quantified claim over a **field array**, maintained across `insert`. Given it,
`search(v)` for `v < 0` has `curr.value != v` and `curr.value > v` at every
node, so it always walks left and returns `false`.

Nothing in that argument mentions acyclicity, reachability or disjointness. The
tree's *shape* is irrelevant to the property — only the values stored in it
matter.

## What it does need, all of which already exists

| requirement | mechanism | state |
|---|---|---|
| field contents as Burstall arrays | A1–A3 | landed |
| quantification over the array index | D1 / `AJAVE_CHC_QGEN` | landed, default on |
| an unbounded loop the BMC cannot unroll (`while (curr != null)`) | CHC summarisation | landed |
| the invariant surviving the call to `insert` | **C1 / `AJAVE_CHC_HEAP_SUMMARY`** | landed, **off by default** |

The fourth is load-bearing. `insert` is a `void` method whose entire purpose is
its heap effect — the shape that had no summary at all before C1, so a call to
it *clobbered* `Node.value` exactly where the invariant is established.

## Measured

| task | expected | default | `AJAVE_CHC_HEAP_SUMMARY=1` |
|---|---|---|---|
| `BinaryTreeSearch-FunSat01` | true | UNKNOWN | **TRUE** |
| `BinaryTreeSearch-FunUnsat01` | false | FALSE | FALSE |
| `BinaryTreeSearch-MemSat01` | true | UNKNOWN | UNKNOWN |
| `BinaryTreeSearch-MemUnsat01` | false | UNKNOWN | UNKNOWN |
| `BinaryTreeSearch-MemUnsat02` | false | UNKNOWN | UNKNOWN |

One gain, no wrong answers. Importantly **no `Unsat` task became TRUE**, which
is the failure mode to watch for in this encoder: a pre/post-collapse bug fixed
on 2026-10-28 had a summary claiming `m_s(params, H, H)` — "this method changes
nothing" — and produced no wrong verdict only because CHC cannot publish FALSE.
A second defect of that family would appear here as a `false` task proved safe.

## Why this was mis-categorised, and the lesson

The plan grouped these tasks by their *data structure* rather than by their
*proof obligation*. A binary tree suggests shape reasoning; the assertion asks
about values. Nothing short of reading the five programs would have caught it —
and the same error had already been made twice in the same plan:

- **Part D's gate** was described as needing a quantified invariant; the real
  blocker was that the CHC encoders never emitted the array `store` at all,
  which a *constant*-bound test exposed in a minute.
- **Part E1's premise** — "acyclicity is `depth` being well-founded" — is false
  for cycles of length ≥ 2, which z3 settles in two lines.

Three premises, three wrong, all cheap to check and none checked before
implementation began. **Read the programs a checkpoint is aimed at before
accepting its category.**

## Consequence for the plan

Part E (E1, E2, E3) is descoped. Its premise is false (#102) *and* its own
acceptance test does not need it. The remaining heap work is finishing and
correcting what exists:

1. flip C1's default, conditional on a category measurement and no new timeouts
2. declare the three heap `Approximations` — no engine declares any today, so
   `open_for` can never return a heap obligation to a more faithful engine
3. decide B2/B3 (#104) — zero measured value, live in the interval hot path
4. fix #105 — `interval_state_as_formula` publishes an unreadable `Invariant`
5. certify a heap proof — the `FunSat01` TRUE rests on an unchecked Spacer `sat`
