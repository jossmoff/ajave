# smt_bmc

**Direction:** Under
**Status:** working
**Source:** `roast-engines/src/smt_bmc.rs`

## What it proves or finds

SMT-backed bounded model checker that encodes paths symbolically and asks a
solver for satisfying assignments. Unlike the concrete engine's fixed candidate
pool, this finds violations reachable within bounded depth for *any* integer/long
inputs. Example: `if (i >= 1000) assert i > 1000` needs exactly `i=1000`, which
the concrete engine's pool doesn't contain but the SMT solver finds immediately.

Single-path DFS with push/pop over the non-SSA IR. Each path through the CFG
gets its own solver context; branches fork the exploration with appropriate
constraints asserted on each side.

## What it assumes / where it's unsound if the assumption breaks

Under-approximating by construction -- can only find bugs, never prove safety.

- **No heap model.** Fields, arrays, object allocations, and method calls all
  produce fresh unconstrained terms. Sound for Under (any value is a possible
  value), but misses bugs that require specific heap state.
- **No string semantics.** `Nondet(Ty::Str)` produces a fresh unconstrained i32
  (mapped to a string pool index for witness compatibility). String method
  results are unconstrained.
- **Depth-bounded.** Paths longer than `max_depth` block transitions are cut
  off. Misses bugs requiring deeper paths.
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
