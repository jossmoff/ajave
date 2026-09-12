# The round loop and cursor deltas

Status: design, not implemented. Supersedes nothing; completes the half of the
scheduling work that `8c9d53a` (process deadline) left open.

## 1. What is actually dead

Two mechanisms are described in `engine.rs` and `blackboard.rs` as load-bearing,
and neither runs.

**The round loop.** `main.rs` calls `orchestrator.run(&prog, 16)`. Every engine
opens `step` with

```rust
if self.done { return Progress::Exhausted; }
self.done = true;
```

so round 0 does the work, round 1 collects thirteen immediate `Exhausted`
returns, `all_retired` fires, and rounds 2–15 never happen. There is no path by
which an engine is given a second slice of time.

**Cursor deltas.** `Blackboard::since(cursor)` is documented as the thing that
"makes an engine removable without the others noticing". Its only caller in the
workspace is `main.rs:1017`, `since(0)`, a full dump for `--trace`. No engine
reads a delta. The engines that genuinely consume other engines' output —
`k-induction` reading `Bounded`, `smt-bmc` reading `Lemma`, `chc` reading
`open()` — do it by querying derived indexes on every entry, which works
precisely because there is only ever one entry.

The two are not independent. A cursor delta is meaningless to a one-shot engine:
it reads the whole state once and leaves. **Deltas only become meaningful once
engines resume, and resumption is only affordable once deltas exist to say who
is worth resuming.** They have to land together.

## 2. Two conditions for a round loop to pay

- **(a) Re-entry must be able to produce what the first entry could not.**
  Otherwise a round is pure cost.
- **(b) Not re-entering must be cheap and correct.** Otherwise round *N* spends
  the deadline on engines with nothing new to read.

(a) is the resumption contract, §4. (b) is the cursor, §5.

## 3. `Progress` is the wrong shape

```rust
/// Ran, learned nothing, but could do more with a bigger budget.
Stalled,
```

That comment conflates the two states the scheduler has to tell apart:

- out of **time**, work outstanding — re-enter, no new information required;
- out of **information** — re-entering costs a step and changes nothing.

Today every engine that returns `Stalled` has just set `done = true`, so in
practice `Stalled` always means the second. The rename below is therefore
faithful, not a behaviour change.

```rust
pub enum Progress {
    /// Published something new.
    Advanced,

    /// Stopped on the clock with work outstanding. Re-entering with a fresh
    /// slice makes strictly more progress on the *same* inputs, so the
    /// scheduler re-enters without waiting for anything to change.
    ///
    /// Contract: an engine may return this only if its next entry runs at a
    /// strictly higher setting of a *bounded* precision parameter. That is
    /// what makes the loop terminate when there is no deadline — see §6.
    Suspended,

    /// Ran, learned nothing, and more time alone will not help. Re-enter only
    /// when something in `interest()` has been published.
    Blocked,

    /// Will never publish again. Retired.
    Exhausted,
}
```

`Stalled` → `Blocked` is a mechanical rename at 13 sites. `Suspended` starts
with no producers, which is the point: phases P1–P3 below are meant to measure
as zero.

## 4. Resumption is deepening, not continuation

The obvious reading of "resume" is a suspended continuation: keep the frontier,
pick up mid-path. For `smt-bmc` that means a CPS rewrite of
`explore_block_until` — 19 recursion sites, all mutating a shared `self`, with
solver `push`/`pop` paired across the recursion. `CLAUDE.md` already names
dangling pushes as a bug class; a hand-rolled continuation is the most direct
way to create one. High risk, and not the cheapest way to get the property we
want.

The cheaper mechanism that is equally real: **every resumable engine has exactly
one bounded, monotone precision parameter, and resumption is restart at the next
value.**

| engine | parameter | already exists as |
|---|---|---|
| `smt-bmc` | path-length bound | `self.max_depth` |
| `k-induction` | induction depth | `k` loop bound |
| `imc` | unrolling depth | base-case `k` |
| `interval-ai` | widening delay | `widen_delay` |
| `chc` | Spacer query timeout, shrinking obligation set | solver timeout |

Restarting re-explores the shallow prefix. That is the standard iterative-
deepening overhead, bounded by a constant factor whenever cost grows
geometrically in the parameter — which is the case here — and it needs **no
change to the explorer at all**. The resumable state is one integer.

### The zero-regression rule

The first entry keeps today's parameter value. Deepening happens only on entry
2+, only when there is time left and something still open. Round 0 is therefore
byte-for-byte the run we measure today, and every later round is strictly
additive. That is what makes P4 measurable against the existing baseline without
confounds — a design property, not a hope.

### The trap this must not spring

`smt-bmc` publishes `Status::Bounded { k: self.max_depth }` at `mod.rs:941`. Its
consumer, `kinduction.rs:150`, reasons: *`Bounded` was published, the reachable
code is loop-free, therefore the bounded search covered every path* — and
discharges outright. So `Bounded { k }` is a claim that the search **reached**
depth k.

That claim survives today only by nesting: the publish sits inside
`if !ctx.exhausted && ctx.budget_left()` (`mod.rs:820`), so a wall-clock cut
skips it. Nothing tests this. Deepening moves exactly this code, and if a
time-truncated pass ever publishes `Bounded`, k-induction converts a search that
never happened into a proof: **a wrong TRUE at −16.** §7 pins it with a test
before P4 touches anything.

## 5. The cursor

### Interest

```rust
bitflags! {
    /// What an engine reads from the blackboard.
    pub struct Interest: u8 {
        const STATUS    = 1 << 0;
        const INVARIANT = 1 << 1;
        const PRECISION = 1 << 2;
        const TRACE     = 1 << 3;
        const RESIDUAL  = 1 << 4;
        const QUERY     = 1 << 5;
        const LEMMA     = 1 << 6;
        const ANY       = 0x7f;
    }
}
```

```rust
/// What this engine reads. A `Blocked` engine is re-entered only once an
/// artifact matching this set has been published since its last step.
///
/// Same discipline as `Approximations`: under-declaring silently loses answers,
/// over-declaring only wastes a step. The default is therefore the widest set,
/// and an engine narrows it deliberately.
fn interest(&self) -> Interest { Interest::ANY }
```

Declarations:

- `k-induction`, `imc`, `chc`, `interval-ai` — `STATUS`. A shrinking open set,
  or a new `Bounded`, is the only thing that changes their answer.
- `smt-bmc` — `LEMMA | PRECISION`. Answers to its own queries, and AI interval
  hints.
- `presolve`, `concrete`, `nra`, `concolic`, `float-search`, `concurrency` —
  `Interest::empty()`. They read the program, never the board.

This deletes a hack. `mod.rs:966` currently does `self.may_reenter = false;
self.done = false; return Progress::Stalled;` — a hand-rolled one-shot re-entry
so the BMC can come back for query answers, which fires on the very next round
whether or not anyone has answered. Under this design it becomes `Blocked` with
`Interest::LEMMA`, and the scheduler re-enters it exactly when an answer lands.
The special case becomes the general mechanism, and `may_reenter` goes away.

### Ownership

The **orchestrator** owns cursors, beside `retired`. An engine that forgets to
advance its cursor silently disables its own skip; one that advances twice
silently drops artifacts. Advanced in one place, once per step:

```rust
struct EngineState {
    retired: bool,
    suspended: bool,
    /// Blackboard head at the end of this engine's last step.
    cursor: u64,
    steps: u32,
}
```

New blackboard method — the first real consumer of `since`:

```rust
/// Whether anything matching `interest` was published at or after `cursor`.
pub fn changed_since(&self, cursor: u64, interest: Interest) -> bool
```

While we are here: `since` locates its start with `position()`, a linear scan.
Sequence numbers are monotone, so it should be `partition_point`. Irrelevant at
one call per run; it is about to become rounds × engines.

### The round-0 trap

`Blackboard::seed` inserts statuses directly into the map and publishes nothing
to the log. At round 0 the log is empty, so `changed_since(0, ANY)` is `false`
and the naive rule skips **every engine and answers UNKNOWN on everything**. An
engine with `steps == 0` is always live. Stated here because it is a
five-minute bug that looks like a scheduling subtlety.

## 6. The loop

```
for round in 0..max_rounds:
    if now + MIN_SLICE > deadline - REPORT_RESERVE: break
    live = engines where !retired && (steps == 0 || suspended
                                      || bb.changed_since(cursor, interest))
    if live.is_empty(): break
    for e in live:
        slice = allocate(remaining, live.len())
        if slice < MIN_SLICE: break round
        p = e.step(prog, bb, budget_with(slice))
        cursor = bb.head()
        suspended = (p == Suspended); retired |= (p == Exhausted)
    phase = next_phase(...)
```

### Allocation

Today `engine_share = 0.6` of the remaining time, per step. Over a round of six
that leaves `0.4^6 ≈ 0.4%` — correct when round 0 is the only round, useless
when there are more. Two knobs that say what they mean:

```rust
/// Fraction of the remaining time one round may consume.
round_share: f64,   // 0.7
/// Ceiling on any single engine's slice, as a fraction of remaining.
engine_cap: f64,    // 0.6
```

```rust
let share = engine_cap.min(1.0 - (1.0 - round_share).powf(1.0 / live as f64));
```

- `live = 1` → `min(0.6, 0.7) = 0.6`, exactly today's number.
- `live = 6` → `min(0.6, 0.188) = 0.188`, and a full round consumes 70%.

Time left by an engine that returns early is recycled for free, because
`remaining` is recomputed per step.

Both constants are fitted, which `CLAUDE.md` says to record and re-check. They
are provisional until a sweep over `round_share ∈ {0.5, 0.6, 0.7, 0.8}` ×
`engine_cap ∈ {0.4, 0.6, 0.8}` runs on the smoke set and a held-out slice.
Expose them as `AJAVE_ROUND_SHARE` / `AJAVE_ENGINE_CAP` so the sweep does not
rebuild between points — a rebuild during a scoring run is a hazard `CLAUDE.md`
logs by name.

### The reserve

`orchestrator.deadline` is `now + timeout`, and JVM replay plus witness emission
happen *after* `run` returns. Today the loop usually stops early, so the overrun
is invisible. A loop that resumes will spend the whole budget, and certification
is what turns a FALSE into a point.

```rust
deadline = now + timeout - REPORT_RESERVE;
```

`REPORT_RESERVE` is measured from the replay tail, not guessed. That measurement
is a prerequisite for P4, not a follow-up.

### Termination

Three independent guarantees, each covering a case the others do not:

1. `max_rounds = 16` — backstop.
2. The deadline — the timed case.
3. **The `Suspended` contract.** A strictly increasing, bounded precision
   parameter means an engine returns `Exhausted` after finitely many entries.
   This is the one that matters for runs without `--timeout`, which is how every
   unit test and most `just` recipes invoke the tool. Without it, P4 hangs the
   test suite rather than losing points.

## 7. Tests, named after the invariants they hold

- `a_blocked_engine_is_not_re_entered_until_its_interest_changes`
- `a_suspended_engine_is_re_entered_with_no_new_artifacts`
- `an_engine_that_always_suspends_terminates_without_a_deadline`
- `an_engine_that_has_never_stepped_is_always_live` (§5's round-0 trap)
- `a_round_never_consumes_the_whole_remaining_time`
- `a_lone_engine_is_sliced_exactly_as_before` (pins `live = 1` → 0.6)
- `a_cursor_advances_exactly_once_per_step`
- `bounded_is_not_published_when_the_slice_expired` — **write this first.**
  It holds today by nesting alone and is the −16 in §4.
- `bmc_does_not_deepen_before_a_pass_completes` — deepening is gated on
  `all_paths_complete`; otherwise a time-truncated shallow pass is replaced by a
  more truncated deep one, which is strictly worse.

Known interaction: `tools/engine_ablation.py` removes an engine, which changes
`live.len()`, hence every slice. Ablation verdicts become time-sensitive in a
way they were not. Run it with a generous `--timeout` so a lost answer means
lost evidence rather than a smaller slice.

## 8. Phasing

Each phase ends with `just score-all` on an idle machine. P1–P3 are predicted to
measure as **zero**; that prediction is the test.

| | change | expected |
|---|---|---|
| **P1** | `Progress` taxonomy, `interest()` defaulting to `ANY`, orchestrator cursors, `changed_since`, `partition_point` | 0 — plus round 1's thirteen no-op steps disappear |
| **P2** | `round_share` / `engine_cap` behind env vars, `REPORT_RESERVE` measured | 0; sweep the constants here, while nothing else moves |
| **P3** | per-engine `interest()` declarations; delete `may_reenter` | small positive |
| **P4** | `smt-bmc` deepening — the first `Suspended` producer | where the points are, and where the −16 is |
| **P5** | `k-induction`, `imc`, `chc`, `interval-ai` deepening, one at a time, one measurement each | incremental |

If P1 or P2 does not measure as zero, stop: something in the rename or the
allocator changed behaviour that was not supposed to change.

## 9. Out of scope, deliberately

- **Suspended continuations.** If P4 shows restart overhead dominating, the CPS
  rewrite of `explore_block_until` is the escalation — its own project, with its
  own justification.
- **A per-engine cost model.** Slices stay uniform-with-a-cap. A model fitted to
  task identity is the overfitting `CLAUDE.md` warns about, relocated from the
  engines into the scheduler.
- **Re-enabling `AJAVE_ASK`.** Resumption makes the query loop cheaper — an
  unanswered query is exactly a `Blocked` engine waiting on `Interest::LEMMA` —
  but turning it on is a separate measurement.

---

## 10. As built

Implemented on `feat/resumption`. Five things came out differently, and each was
a measurement rather than a change of mind.

**The resumable parameter is the work scale, not depth.** §4 named `max_depth`
as `smt-bmc`'s parameter on the strength of the textbook algorithm. Sampling the
tasks that actually truncate shows `handle_branch_fork` exhausting `MAX_FORKS`
with `max_depth` nowhere near — `SatAckermann01` cuts at 500 forks and 1414
block visits. Deepening on depth would re-run an identical exploration and stop
in an identical place. The parameter is now a per-instance multiplier on
`MAX_FORKS`/`MAX_SOLVER_CALLS`/`MAX_BLOCK_VISITS`, doubling to a ceiling of 8.

**Round 0 keeps the flat cap.** §6 derived every engine's share from
`round_share`. Measured, that gave thirteen live engines 0.088 of the remainder
apiece where they used to get 0.6 — a different first round, and therefore a
baseline that predicts nothing. The zero-regression rule §4 states for deepening
applies to the allocator for the same reason, so `slice_share` returns
`engine_cap` in round 0 and the geometry starts at round 1.

**`RESUME_HEADROOM` is the guard that makes any of this affordable, and the
design did not anticipate it.** The obvious condition — resume unless the clock
has already expired — was the first thing written and measured 6x to 20x on
individual smoke tasks (`BellmanFord-MemUnsat01` 11s → 72s) for one point. A
pass entered with 40% of a slice left costs at least twice what the first 60%
did, because the bound doubles *and* the restart repeats the prefix; it
truncates, and reports nothing for the whole of it. A deeper pass now starts
only with room to finish: `left >= 2 × spent`.

**Three engines declare no resumable parameter.** §8 listed `k-induction`,
`imc`, `chc` and `interval-ai` for P5. Only two have one. `imc`'s
`MAX_ITERATIONS` bounds a fixpoint that converges or does not, so raising it
spends longer failing. `cegar` refines on counterexamples, not on a bound.
`interval-ai` reaches its fixpoint in milliseconds and is never the engine
holding the clock. `Suspended` is a promise of progress, and an engine that
cannot keep it should not make it — declaring one for symmetry would be exactly
the ceremony this document exists to remove.

**A second lying comment, alongside the one in §4.** `chc::solver_timeout_secs`
documented itself as "a slice of the remaining budget rather than the whole of
it". It was a flat ten seconds, and the engine took `_budget` and dropped it —
which is why a task given a 295-second deadline was still running at 400. The
deadline shipped in `8c9d53a` only ever bound the two engines that read their
budget. It is now derived from the slice, and the CHC engine resumes when Spacer
answers `unknown` inside its bound and there is room for a doubled query.

### Pre-existing: the smoke baseline is stale

`--check` reports three failures — `AbstractSerializationStreamReader_false`,
`SatAckermann01`, `SatFibonacci01`. All three reproduce identically on the
pre-change binary, with identical wall times, so they belong to a commit between
`08b1b5b` (where the baseline was last recorded) and `HEAD`. Re-baselining would
bake them in, which `justfile` warns about at the recipe; they want bisecting
first.
