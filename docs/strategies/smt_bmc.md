# smt_bmc

**Direction:** Under
**Status:** working
**Source:** `ajave-engines/src/smt_bmc.rs`

## What it proves or finds

SMT-backed bounded model checker that encodes paths symbolically and asks a
solver for satisfying assignments. Unlike the concrete engine's fixed candidate
pool, this finds violations reachable within bounded depth for *any* integer/long
inputs. Example: `if (i >= 1000) assert i > 1000` needs exactly `i=1000`, which
the concrete engine's pool doesn't contain but the SMT solver finds immediately.

DFS with push/pop over the non-SSA IR. A branch is handled in one of two ways,
and which one it gets is the difference between linear and exponential work:

- **Merged** (`handle_branch_diamond`) when the branch block has an immediate
  post-dominator reachable without crossing a loop back edge. Both arms are
  explored as far as that join, the states are merged with one `ite` per
  differing variable, and the continuation is explored **once**. No feasibility
  query is posted and no fork is charged.
- **Forked** (`handle_branch_fork`) otherwise. Each arm is explored to the end
  of the enclosing region, so the whole remainder is duplicated, and the two
  end states are merged afterwards.

Choosing the join is `cfg.rs`, which computes real post-dominators. This is
large-block encoding (Beyer, Cimatti, Griggio, Keremoglu, Sebastiani, FMCAD
2009); `AJAVE_LBE=0` restores the previous reachability heuristic, which
declined on every one-armed `if` and therefore forked the commonest branch
shape in Java. The soundness argument, the measurements and the switches are
in [`../large-block-encoding.md`](../large-block-encoding.md).

## What it assumes / where it's unsound if the assumption breaks

> **Stale below this line, beyond the branch encoding.** The two bullets on the
> heap and on exceptional control flow no longer describe the engine, and
> "can only find bugs, never prove safety" is wrong in the way that matters:
> this engine publishes `Over` whenever `Completeness::can_discharge` allows
> it, which is what makes `all_paths_complete` the outer gate on most of the
> corpus. Treat the rest of this section as unreviewed.

Registered as `Under`, but it also discharges: a run that covered every path
publishes `Over`.

- **No heap model.** Fields, arrays, object allocations, and method calls all
  produce fresh unconstrained terms. Sound for Under (any value is a possible
  value), but misses bugs that require specific heap state.
- **No string semantics.** `Nondet(Ty::Str)` produces a fresh unconstrained i32
  (mapped to a string pool index for witness compatibility). String method
  results are unconstrained.
- **Depth-bounded.** Paths longer than `max_depth` block transitions are cut
  off, which also forfeits any proof that depended on the cut subtree. The
  bound is **path length in blocks**, not iterations or effort — termination
  comes from `MAX_LOOP_UNROLL`, `MAX_CALL_DEPTH`, `MAX_BLOCK_VISITS`,
  `MAX_SOLVER_CALLS` and the deadline. A flat bound therefore capped the size
  of method the engine could traverse at all, so it now scales with the entry
  body (`path_length_bound`, `AJAVE_BMC_DEPTH_SLACK`).
- **No exceptional control flow.** Exception routing is not modelled in the
  symbolic exploration. Violations inside try blocks may produce witnesses
  that JvmReplay will reject (which is fine -- they get downgraded).

## Known incompleteness

All the above are completeness gaps, not soundness gaps. The SMT engine will
never claim a bug that doesn't exist -- at worst, JvmReplay will reject a
spurious witness and it gets downgraded to UNKNOWN.

## How it's certified

Same JvmReplay path as the concrete engine. Every `Violated` status is fed to
`core::certify::JvmReplay` before being reported. The nondet_sequence in the
witness comes from `get_value` on the solver model, in the same format the
concrete engine uses.
