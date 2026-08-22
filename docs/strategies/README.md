# Strategies

One file per verification strategy. A strategy is a module in
`roast-engines/src/` that implements `Engine` or `Cpa`; shared helpers
(`smt_text`, `body_analysis`, `body_shape`, `math_eval`, `str_eval`,
`smt_encode`, `interpolation`) are not strategies and have no file here.
Coverage is enforced by `scripts/check-strategy-docs.sh` (CI job
`strategy-docs`), which decides what counts by looking for an `impl Engine`
or `impl Cpa`, not by globbing filenames.

## Implemented

| Strategy | Direction | Tier | Status | Doc |
|---|---|---|---|---|
| Presolve | Over | 0 | working | [presolve.md](presolve.md) |
| Interval domain | Over | 1 | working | [interval.md](interval.md) |
| — engine wrapper | Over | 1 | working | [ai.md](ai.md) |
| Concrete falsifier | Under | 2 | working | [concrete.md](concrete.md) |
| BMC + SMT | Under | 2/3 | working | [smt_bmc.md](smt_bmc.md) |
| k-induction | Over | 3 | working | [kinduction.md](kinduction.md) |
| IMC | Over | 3 | working | [imc.md](imc.md) |
| Predicate domain | Over | 4 | working | [predicate.md](predicate.md) |
| Predicate CEGAR | Over | 4 | working | [cegar.md](cegar.md) |
| CHC encoding | Over | 5 | working | [chc.md](chc.md) |
| NRA (transcendental) | Under | 5 | working | [nra.md](nra.md) |

Runtime availability is not the same as being implemented. The SMT-backed
engines register only when a solver binary is found (`SmtLibFactory::from_env`
for BMC and k-induction; an interpolating solver for IMC and CEGAR; `z3` or
`$ROAST_CHC_SOLVER` for CHC). NRA additionally requires the `nra` Cargo
feature, which is on by default but links CVC5 statically — build with
`--no-default-features` to drop it and the C++ toolchain requirement with it.

## Two things that hold across every proving engine

**The havoc guard.** k-induction, IMC, CEGAR and CHC all encode integer
arithmetic and havoc everything else. An UNSAT over an encoding that quietly
dropped the heap would look exactly like a proof, so all four skip any body
where `body_analysis::body_uses_havoced_ops` holds. That single predicate is
the shared soundness assumption of the entire proving half of the portfolio;
it is defined once, in `body_analysis`, and derived from the same walk that
produces `BodyShape` so the two cannot drift apart.

**Certification status.** `docs/architecture.md` describes a design in which
TRUE rests on invariants re-checked by an independent pass. That pass does not
exist yet. Today the only `Certifier` is `JvmReplay`, which handles
violations: every FALSE is replayed on a real JVM against the exact bytecode
that was lifted, and downgraded to UNKNOWN if the expected exception does not
fire. A TRUE, by contrast, rests on the discharging engine's authority plus
the direction discipline enforced by the blackboard. Each engine doc's "How
it's certified" section says which of those two it is; none of the proving
engines is independently certified, and the invariants that would make that
possible (IMC's accumulated `F`, CHC's Horn invariant, k-induction's step
case) are computed and then discarded rather than published.
