# IR reduction: a normalisation and optimisation stage between lifting and the portfolio

Status: **plan**. Nothing implemented. Feature-flagged from the first commit,
default off, until the differential in §6 passes on both properties.

---

## 1. The evidence

Three measurements, taken 2026-09-02.

**The IR is mostly bookkeeping.** Bare copies (`vN = vM`) as a share of all
assignments:

| task | statements | assignments | bare copies |
|---|---|---|---|
| `jayhorn-recursive/SatFibonacci01` | 330 | 144 | 67 (**47%**) |
| `jbmc-regression/array1` | 372 | 165 | 74 (**45%**) |
| `algorithms/BellmanFord-FunSat01` | 642 | 313 | 111 (**35%**) |

These are the JVM operand stack materialised into `VarKind::Stack` temporaries.
`int x = Verifier.nondetInt(); if (x < 0)` lifts to four assignments:

```
v0 = nondet<Int>()
v2 = v0
v1 = v2
v3 = v1
v4 = v3 >= 0
```

**State is wide.** Widest method in each task: BellmanFord **112** variables,
array1 **40**, SatFibonacci01 **22**. Every one becomes an argument of every CHC
block predicate and an entry in every BMC state.

**The solver is not the problem; the encoding is.** On hand-written Fibonacci
clauses, z3-Spacer proves `ret >= n-1` *instantly*. On ours it times out. And
JayHorn's own trace preprocesses **93 clauses over 76 relations down to 14 over
6** before solving. We hand the solver everything.

### What this is not

Honest bound, because the case rests on it. Measured BMC cost drivers:

| task | solver calls | block visits | forks |
|---|---|---|---|
| SatFibonacci01 | 973 | 1580 | 500 |
| BellmanFord-FunSat01 | 460 | 829 | 274 |
| Alarm_prop1 | 455 | 619 | 62 |

**Forks dominate the visit count**, so the BMC's cost is path explosion, not
state width. Its merge cost is roughly `forks × width`, so a 40% narrower state
buys ~40% off merges and nothing off the fork count. That is worthwhile and it
is *not* an order of magnitude. The order-of-magnitude case is CHC and the other
text-SMT engines, where width sets predicate arity directly.

Do not sell this as fixing timeouts. Sell it as: every budget constant in the
system — `MAX_LOOP_UNROLL`, `MAX_CALL_DEPTH`, `MAX_FORKS`, `MAX_BLOCK_VISITS`,
`MAX_ENCODING_COST` — is a proxy for "we cannot afford more", and cheaper IR
buys depth at all of them without touching a fitted constant.

---

## 2. What other tools do

**SeaHorn** splits its LLVM stage in two, and the split is the important part: a
*required* set of transformations needed for correct results even with the
optimiser disabled (SSA construction, internalising functions, lowering
switches), and an *optional* pre-processor whose "only mission is to optimize
the bitcode to make the verification task easier". We should copy that shape
exactly — it is the same distinction as normalisation versus optimisation, and
it is what makes a feature flag meaningful rather than a risk.

**mem2reg alone yields ~81% of the speedup of full `-O1`** on LLVM. The single
highest-value transformation is the one that removes the memory/stack shuffling
a frontend emits — which is precisely our 35–47% of copies.

**CBMC** applies constant propagation, singleton propagation, dead code removal
and a full slicer to its goto-programs, and reports both memory and runtime
gains from field-sensitive constant propagation.

The consistent lesson: frontends emit noise, and every verifier that scales
removes it once, centrally, rather than in each backend.

---

## 3. Where it fits

```
classfile ──lift──►  Body  ──[ normalise ]──►  Body  ──[ optimise ]──►  Body ──► portfolio
                            always on            AJAVE_IR_OPT, off by default
```

A new crate, `ajave-opt`, depending only on `ajave-ir`:

* `ajave-ir` stays data-only, as it is today. A transformation crate must not
  put logic there.
* `ajave-frontend` keeps lifting only. Lifting and optimising are different
  jobs with different failure modes, and today's session found three bugs that
  came from one component quietly doing another's work.
* `ajave-cli` runs the stage after `lift` and before `Orchestrator::new`, so
  every engine sees the same IR and none can opt out — the alternative,
  per-engine optimisation, is how the same bug gets written seven times.

`ajave-opt` exports one entry point:

```rust
pub fn reduce(prog: &mut Program, level: Level) -> Stats;
pub enum Level { Normalise, Optimise }
```

`Stats` records statements and variables removed per pass, so the effect is
measurable per task rather than inferred from wall clock.

---

## 4. The passes

Ordered by measured value over risk. Each is independently testable and
independently disableable.

| # | pass | what it does | risk |
|---|---|---|---|
| P1 | **copy propagation** | rewrite uses of `vN` defined by `vN = vM` to `vM` | low |
| P2 | **dead assignment elimination** | drop assignments whose result is never read | **medium** — see exclusions |
| P3 | **constant folding** | evaluate `2 != 0`, fold branches on constants | low |
| P4 | **variable compaction** | renumber so `body.vars` is dense | **medium** — see invariant 3 |
| P5 | **block merging** | fuse a block with its single predecessor | medium |
| P6 | **unreachable block elimination** | drop blocks with no path from entry | low |

P1+P2+P4 together are the mem2reg analogue and should be built first; P3, P5, P6
only afterwards, and only if measurement justifies them.

### Exclusions for P2, which are the whole safety argument

An assignment may be removed **only** if its value is never read *and* its
rvalue is free of effects. Never removable:

* `Rvalue::Nondet` — the witness is a *sequence* of nondet values replayed on a
  real JVM (`-Dajave.seq=...`). Removing or reordering one changes what the
  witness means, and a witness that does not reproduce is a lost FALSE.
* `Rvalue::Call` — a call has effects even when its result is unused, and may
  throw.
* `Rvalue::New` / `NewArray` — allocation is observable through
  `NegArraySize`, and identity is observable through reference equality.
* Anything reached by a `Stmt::Check` — obligations are the product.

`Stmt::MonitorEnter`/`MonitorExit`, `PutField`, `PutStatic` and `ArrayStore` are
not assignments and are never touched by P2.

---

## 5. Invariants every pass must preserve

These are the contract. A pass that breaks one is a wrong answer, not a
regression, and each has a named test in §6.

1. **Obligations survive with their identity.** Every `Stmt::Check(oid)` must
   remain, `oid` must still index the same `Obligation`, and its `cond` must
   denote the same value. Ids are per-`Body` indices — the collision fixed
   earlier today is exactly what happens when that is treated loosely.
2. **Nondet order is preserved.** See P2 exclusions. This is a *sequence*
   property, so it constrains reordering as well as removal.
3. **Parameter slots keep their meaning.** `find_param_var_indices` maps
   parameters by `VarKind::Local(slot)`, and `Body::is_static` decides whether
   slot 0 is `this`. P4 renumbers `VarId`s and must not disturb which variable
   holds which local slot.
4. **Exceptional edges stay consistent.** P5 merges blocks; two blocks with
   different `exceptional` lists may not be fused, because the handler set is
   part of the semantics.
5. **`bytecode_offset` survives on anything carrying an obligation.** Witnesses
   and source lines are anchored to it.
6. **Monitors are untouched.** The concurrency engine cannot reconstruct a
   critical section that has been optimised away — the lifter already discarded
   these once and had to be fixed.

A `validate(body: &Body) -> Result<(), String>` checker asserts the structural
half of these — every `VarId` in range, every `BlockId` resolvable, every
obligation referenced by exactly one `Check`, entry reachable — and runs after
every pass under `debug_assertions` and in every test. Cheap, and it converts a
pass bug from a wrong verdict into a panic in CI.

---

## 6. Testing

Four layers, weakest to strongest.

**Per-pass unit tests.** Hand-built `Body` values, as in `kinduction.rs`: a
pass's effect asserted directly, plus one test per exclusion in §4 — *a nondet
whose result is unused is not removed*, *a call whose result is unused is not
removed*, *a monitor is not removed*.

**The structural checker.** §5, after every pass, in debug builds.

**A configuration differential — the important one.** `AJAVE_IR_OPT=0` versus
`=1` must produce the *same verdict on every task*. This is exactly the property
`tools/metamorphic.py` already encodes, with the transformation applied to the
IR instead of the source, so it should be a mode of that tool rather than a new
one. Unlike a benchmark it needs no expected-verdict label, so it holds on
programs no benchmark covers, and it is the check that makes the feature flag
meaningful: **optimisation that changes a verdict is a bug in the optimiser,
without exception.**

**Both properties, full corpus.** A discharge-affecting change measured on one
property is not measured; `CLAUDE.md` records what that cost before.

---

## 7. Performance measurement

The claim is that encodings shrink, so measure encodings, not just wall clock:

* CHC encoding bytes per task (already logged: "generated N bytes").
* BMC `solver calls`, `block visits`, `forks` (already logged).
* `Stats` from `reduce`: statements and variables removed per pass.
* Per-task wall clock via the existing baselines, which already flag a task that
  became much slower.

Record the before/after table in `changes.md` per pass. A pass that removes
statements but does not move any of the four numbers above has not earned its
place.

---

## 8. Rollout

1. Land `ajave-opt` with P1, P2, P4, `validate`, unit tests. Flag **off**.
2. Run the configuration differential across the smoke and ajave sets.
3. Measure both properties with the flag on; compare encodings and verdicts.
4. Turn on by default only when the differential is clean and both properties
   are non-negative.
5. Remove the flag once it has survived a full scoring cycle on.

## 9. What would make this not worth doing

Stated in advance so it can be checked rather than argued:

* If the configuration differential shows *any* verdict change that is not a
  timeout, stop and find the bug before proceeding.
* If P1+P2+P4 remove 40% of statements and CHC's encoding bytes fall by less
  than 20%, the noise was not where the cost is, and P3/P5/P6 will not rescue it.
* If the BMC's fork counts are unchanged and its wall clock moves less than 10%,
  the gain is confined to the text-SMT engines — still worth having, but it does
  not justify the "unlocks serious value" framing and the plan should be
  re-scoped to CHC and IMC alone.
