# Large-block encoding in the BMC

How a branch is encoded, why the choice is the difference between linear and
exponential work, and what had to be true before merging was safe.

Implementation: `crates/ajave-engines/src/smt_bmc/cfg.rs`, consumed by
`explore.rs`'s `join_for_block`. Issue: [#128]. Prior diagnosis: [#124],
[#126].

## The two ways to encode a branch

The explorer already had both. Which one a branch got was decided by
`find_join`, and that decision was the whole problem.

**Forked** (`handle_branch_fork`). Each arm is explored to the end of the
enclosing region, and the two end states are merged afterwards. The remainder
of the method is therefore explored *once per arm*. Two sequential branches
explore the tail four times; twenty-four explore it 16,777,216 times. A
feasibility query is posted per arm, and a fork is charged against
`MAX_FORKS`.

**Merged** (`handle_branch_diamond`). Both arms are explored only as far as the
point where they reconverge, the states are merged with one `ite` per differing
variable, and the continuation is explored **once**. No feasibility query, no
fork charged. Work is linear in the number of branches.

This is the distinction large-block encoding names. Beyer, Cimatti, Griggio,
Keremoglu and Sebastiani introduced it for predicate abstraction and reported
that it "may reduce the number of paths to be explored up to exponentially"
(*Software Model Checking via Large-Block Encoding*, FMCAD 2009). Avgerinos,
Rebert, Cha and Brumley gave the symbolic-execution form as *veritesting*
(ICSE 2014), and Java Ranger is the Java instance — SPF plus statically
summarised regions, with dynamic inlining of method-regions so that Java's
many small dispatched methods can join a multi-path region (Sharma, Hussein,
Whalen, McCamant, Visser, ESEC/FSE 2020). Java Ranger led the SV-COMP Java
track before going inactive, and the same group formalised its semantics in *A
Formal Semantics for Java Symbolic Evaluation using Large-Block Encoding*
(2026).

## What was wrong

`find_join` intersected depth-limited forward-reachable sets and took the
numerically smallest common block. Two defects:

1. The reachability walk was capped at 50 blocks and followed only edges to
   higher block ids, so a join further away simply was not found.
2. It declined — and therefore forked — whenever one arm's target was
   reachable from another arm's target, on the stated grounds that "the
   branches are not independent".

The second is the expensive one, because that condition describes **the
commonest branch shape in Java**. `if (c) { ... }` compiles to `ifeq join`, so
the *else* target of the branch **is** the join block, and the join is
trivially reachable from the then block. Every one-armed `if` forked.

Even when a join was found, the numerically smallest common successor is not
the immediate post-dominator. It happened to coincide often enough in
small bodies that the mechanism went unexamined.

## What replaced it

`CfgInfo::of` computes, once per `Body`:

- **Immediate post-dominators**, as dominators of the reverse CFG rooted at a
  virtual exit, by the iterative algorithm of Cooper, Harvey and Kennedy (*A
  Simple, Fast Dominance Algorithm*, 2001). Every block with no normal
  successor — `Return`, `Throw`, `Halt`, `Diverge` — is a predecessor of the
  virtual exit.
- **Back edges**, by a three-colour DFS from the entry: an edge whose target
  was still on the stack when it was taken.
- **The join for each branching block**, eagerly, because the explorer asks the
  same question once per visit and a loop body is visited many times.

`join_for(b)` answers `Some(j)` only when `j` is `b`'s immediate
post-dominator, `j` is not the virtual exit, and no block in the region from
`b` to `j` is the source of a back edge.

### Exception edges are deliberately excluded

`Block::exceptional` is not in this graph. An implicit throw is explored as a
separate subtree under a saved state and restored afterwards — see
`fork_into_implicit_handler`, whose comment records that "an exception does not
rejoin the path it left". The main path still reaches the post-dominator, so
merging there stays correct. Including those edges would make the virtual exit
the immediate post-dominator of almost every block and merge nothing.

## Soundness

The merge is **exact**, not an approximation in either direction, and that is
why `handle_branch_diamond` posts no feasibility query and sets no completeness
flag.

Each arm is explored under its own branch constraint and yields a map from
variable to term. The merged map sends each variable to `ite(c, t_then,
t_else)`. For any concrete execution, `c` evaluates to a definite value, so the
merged state denotes exactly the state that execution reaches. Nothing is
added and nothing is dropped.

Two preconditions make that argument work, and `join_for` enforces both:

1. **`j` post-dominates `b`.** Otherwise some execution leaves the method
   without passing `j`, its arm is explored to a different program point, and
   merging two states captured at *different* program points yields a state no
   execution has. That is unsound in both directions — it can both invent and
   omit behaviour.
2. **The region is acyclic.** `explore_block_until` stops the first time it
   reaches the sentinel. If the region contained a loop whose exit is `j`, the
   arm would stop after one iteration, silently dropping the states reachable
   after more. Loops therefore remain the explorer's unrolling territory,
   bounded by `MAX_LOOP_UNROLL`.

What happens when an arm is cut short by a budget *before* reaching `j`:
`explore_block_until` calls `mark_incomplete`, which clears
`all_paths_complete`, so `Completeness::can_discharge` refuses and no `Over`
claim can rest on the truncated merge. A violation found after such a merge is
still only a candidate until `JvmReplay` reproduces it. So a truncated diamond
costs a proof, not correctness.

The residual risk is not in the algorithm but in `merge_states_ite`: if it
failed to merge some component of the state — a string term, an array, a field
map — the merged state would be wrong. That path existed before and now fires
far more often, so it is checked by the oracles below rather than by argument.

## The second defect: `max_depth` was a cap on method size

Independent of the join computation, and found while measuring it.

`max_depth` bounds **path length in blocks**. It is not what makes exploration
terminate: iterations are bounded by `MAX_LOOP_UNROLL`, inlining by
`MAX_CALL_DEPTH`, and total work by `MAX_BLOCK_VISITS`, `MAX_SOLVER_CALLS` and
the deadline. A flat bound of 200 therefore bought no termination — it capped
**the size of method the engine could traverse at all**, at 200 blocks of
straight-line code.

`AlarmFunctional.alarmFunctional` is 893 blocks in one Simulink-generated
method. The search was cut after a fraction of it with every other budget
untouched — 59 forks against a cap of 500, 608 block visits against 50,000 —
and no resumption could help, because iterative deepening deliberately never
raises depth. The `scale` doc comment asserted that `MAX_FORKS` binds "long
before `max_depth`", which is false for this family; that is [#126].

`path_length_bound` now takes the larger of the floor and the entry body's own
block count times a slack factor. Bodies under `floor / slack` blocks are
**bit-identical** to before, which is most of the corpus. The slack covers
blocks that are on a path but not in the entry body: inlined callees, and the
extra copies an unrolling contributes.

## Measurements

One build, both properties, idle machine, single invocation per figure.

### Full corpus

| | before (`e83a4a2`) | after | Δ |
|---|---|---|---|
| valid-assert | 911 | **948** | +37 |
| no-runtime-exception | 1184 | **1211** | +27 |
| combined | 2095 | **2159** | **+64** |
| correct | 1337 | 1370 | +33 |
| wrong | 0 | **0** | — |

1785 runs in 4741 s, 29 timeouts, 0 `ERROR` verdicts. The timeouts are 14 in
`jbmc-regression`, 9 in `argv-tasks`, 3 in `securibench`, 3 in `autostub`, and
**none** in `java-ranger-regression` — the large-method category that gained
most did not pay for it in wall clock.

### The Alarm family

Nine tasks, both properties, all expected TRUE, previously all UNKNOWN. The
36-point target diagnosed in [#124].

| | before | after |
|---|---|---|
| score | 0 | **36** |
| correct | 0 of 18 | **18 of 18** |
| wall clock | 526 s | 122 s |

It is both decided and four times faster. The family accounts for 36 of the
+64, so the remaining +28 came from the rest of the corpus: post-dominator
joins help generally, not only on generated code.

### The mechanism, on the minimal benchmark

`benchmarks/ajave/engine-bmc/AChainOfOneArmedIfsMustNotForkPerBranch` — 24
one-armed ifs maintaining `x + y == 24`, a relational property an interval
domain cannot express. valid-assert, same build:

| | forks | solver calls | block visits |
|---|---|---|---|
| `AJAVE_LBE=0` | 500 (the cap) | 980 | 862 |
| `AJAVE_LBE=1` | 2 | 4 | 53 |

The portfolio answers it either way, because there is no loop and CHC's
single-method bitvector encoding proves it in one query. With the other
over-approximating engines removed the capability boundary is exact:

```
AJAVE_DISABLE=chc,imc,cegar,concolic,kinduction AJAVE_LBE=0  -> UNKNOWN
AJAVE_DISABLE=chc,imc,cegar,concolic,kinduction AJAVE_LBE=1  -> TRUE
```

### The FALSE twin, which is the one that could fail

`AChainOfOneArmedIfsMustNotForkPerBranch` cannot distinguish a correct merge
from a merge that silently loses an arm: losing an arm still leaves
`x + y == 24` holding, so the verdict stays TRUE either way.
`AMergedRegionMustNotLoseTheArmThatBreaksTheInvariant` is the same program with
one arm that increments `x` without decrementing `y`, so the lost arm is the
one carrying the violation and the same bug reads as a **wrong TRUE at -32**.
That is the test `CLAUDE.md` asks for under "every engine publishing `Over`
needs a test that would fail if its encoding were unsound".

It also discriminates on the verdict in the full portfolio, which the TRUE twin
does not:

```
AJAVE_LBE=0  -> UNKNOWN    (the fork blowup prevents even finding the violation)
AJAVE_LBE=1  -> FALSE      (found, and reproduced by JvmReplay)
```

### Oracles that do not use an expected verdict

Both are stronger than the corpus here, because merging now fires on most
branches and a latent bug in `merge_states_ite` would show as a flip.

- `bench.py --set smoke --repeat 2` — all verdicts stable. Post-dominator
  computation is deterministic: `HashSet` is used only for membership, and
  every collection a decision reads from is sorted or a `BTree*`.
- `metamorphic.py --set smoke` — **PASS, no verdict changed** across 69
  transformed runs, 2 weakened (answer lost, not flipped).
- `bench.py --set smoke --check` — PASS, 0 WRONG.

## Switches, and what is still fitted

| Variable | Default | What it does |
|---|---|---|
| `AJAVE_LBE` | on | `0` restores the old reachability heuristic, on the same build. This is what makes a controlled comparison possible, and it is why the previous heuristic is kept rather than deleted. |
| `AJAVE_BMC_DEPTH` | 200 | The floor under `path_length_bound`. |
| `AJAVE_BMC_DEPTH_SLACK` | 4 | Blocks of path-length budget per block of the entry body. |
| `AJAVE_LBE_MAX_REGION` | 0 (unbounded) | Caps the blocks in a merged region. |

The slack factor is a **fitted constant** of the kind `CLAUDE.md` warns about,
and its sweep is **not yet done** — it is started and abandoned, so nothing
here rests on it. The population where the value can matter at all is bodies
over `floor / slack` blocks; below that the floor dominates and behaviour is
bit-identical, which is the argument that 4 is low-risk rather than the
evidence that it is right. The sweep belongs on `java-ranger-regression`, the
corpus's large-method population, across slack in {1, 2, 4, 8} with an
`AJAVE_LBE=0` control. Tracked as a follow-up; until it runs, read 4 as
provisional.

`AJAVE_LBE_MAX_REGION` is unbounded by default and that is a deliberate
provisional choice, not a conclusion. Adjustable-block encoding (Beyer,
Keremoglu, Wendler, *Predicate Abstraction with Adjustable-Block Encoding*,
FMCAD 2010) exists precisely because region size trades path enumeration for
formula size, and past some point the solver answers `unknown` where
enumeration would have answered. The corpus run shows no sign of that cost yet
— the score rose and the timeouts did not concentrate in the large-method
category — so the parameter is in place, measured at 0, and should be swept
before anyone relies on the default.

## What this does not do

It merges **branches**, not calls. A call is still inlined, so a deep call
graph still produces one enormous path constraint —
`alarmFunctional` reaches 9858 conjuncts on a single path. Java Ranger's
method-regions are the next step, and the structural answer for real codebases
is a summary per procedure rather than a region per branch: interpolation-based
function summaries (FunFrog, 2012; HiFrog, TACAS 2017) or bi-abduction
(Calcagno, Distefano, O'Hearn, Yang, POPL 2009). Those are tracked separately.

Loops are untouched: a region containing a back edge is declined and the
explorer unrolls as before.

[#124]: https://github.com/jossmoff/ajave/issues/124
[#126]: https://github.com/jossmoff/ajave/issues/126
[#128]: https://github.com/jossmoff/ajave/issues/128
