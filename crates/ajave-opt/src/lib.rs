//! IR reduction: what the portfolio sees, after the noise is removed.
//!
//! # Why this exists
//!
//! The lifter materialises the JVM operand stack into `VarKind::Stack`
//! temporaries, so **35–47% of every method's assignments are bare copies**
//! (`vN = vM`), and the widest method in `algorithms/BellmanFord-FunSat01`
//! carries 112 variables. Each of those becomes an argument of every CHC block
//! predicate and an entry in every BMC state, and every engine pays for it
//! again in its own encoding.
//!
//! z3-Spacer proves `fib(n) >= n-1` instantly on hand-written clauses and times
//! out on ours; JayHorn's own trace reduces 93 clauses over 76 relations to 14
//! over 6 before solving. The solver is not the problem.
//!
//! # Normalise versus optimise
//!
//! SeaHorn splits its LLVM stage into transformations *required* for correct
//! results and an optional pre-processor whose "only mission is to optimize the
//! bitcode to make the verification task easier". The same split applies here,
//! and it is what makes the feature flag meaningful: [`Level::Normalise`] is
//! always safe to run, [`Level::Optimise`] is the part still earning trust.
//!
//! # Why a separate crate
//!
//! Dead-assignment elimination has to know whether a call is pure, which
//! `ajave_models::contract_of` answers — and `ajave-models` already depends on
//! `ajave-ir`, so a pass module inside the IR crate would be a dependency
//! cycle. Duplicating purity knowledge instead would recreate the "second place
//! that answers a question about external code" that `contract_of` exists to
//! prevent.

use ajave_ir::{Body, Program};
use log::debug;

mod compact;
mod copy_prop;
mod dce;
mod liveness;

#[cfg(test)]
mod tests;

/// How much reduction to apply.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Level {
    /// Nothing at all. The baseline the differential compares against, and the
    /// escape hatch if a pass is ever suspected in the field.
    None,
    /// Structure-preserving rewrites only.
    Normalise,
    /// Everything in `Normalise`, plus passes that remove statements and
    /// variables. Behind `AJAVE_IR_OPT` until the configuration differential
    /// has run clean on both properties.
    Optimise,
}

/// What a reduction removed. Reported so the effect is measurable per task
/// rather than inferred from wall clock: a pass that removes statements without
/// moving encoding size or solver calls has not earned its place.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct Stats {
    pub copies_propagated: usize,
    pub assignments_removed: usize,
    pub vars_removed: usize,
    pub bodies: usize,
}

impl Stats {
    fn merge(&mut self, other: Stats) {
        self.copies_propagated += other.copies_propagated;
        self.assignments_removed += other.assignments_removed;
        self.vars_removed += other.vars_removed;
        self.bodies += other.bodies;
    }
}

/// A single rewrite over one method body.
///
/// Passes are separate types rather than functions so each has its own tests
/// and can be disabled individually while a fault is bisected — which matters
/// because a pass bug is a wrong verdict, not a slow one.
pub(crate) trait Pass {
    fn name(&self) -> &'static str;
    /// Rewrite in place; report what changed. Must leave the body valid.
    fn run(&self, body: &mut Body, stats: &mut Stats) -> bool;
}

/// Cap on driver iterations.
///
/// The passes reach a fixpoint quickly — copy propagation exposes dead
/// assignments, whose removal exposes further copies — but a pass that reported
/// "changed" without changing anything would otherwise spin forever. The cap
/// bounds a bug rather than tuning a result: hitting it is logged, and no
/// corpus body has come close.
const MAX_ROUNDS: usize = 8;

/// Reduce every body in the program.
pub fn reduce(prog: &mut Program, level: Level) -> Stats {
    let mut total = Stats::default();
    let keys: Vec<_> = prog.bodies.keys().cloned().collect();
    for key in keys {
        if let Some(body) = prog.bodies.get_mut(&key) {
            let mut s = reduce_body(body, level);
            s.bodies = 1;
            total.merge(s);
        }
    }
    debug!(
        "ir-opt: {} bodies, {} copies propagated, {} assignments and {} vars removed",
        total.bodies, total.copies_propagated, total.assignments_removed, total.vars_removed
    );
    total
}

/// Reduce one body to a fixpoint.
pub fn reduce_body(body: &mut Body, level: Level) -> Stats {
    let mut stats = Stats::default();
    if level == Level::None {
        return stats;
    }
    let passes: Vec<Box<dyn Pass>> = match level {
        Level::None => unreachable!("handled above"),
        // Copy propagation only rewrites *uses*; it removes nothing, so it
        // cannot lose a statement an engine depends on.
        Level::Normalise => vec![Box::new(copy_prop::CopyPropagation)],
        Level::Optimise => vec![
            Box::new(copy_prop::CopyPropagation),
            Box::new(dce::DeadAssignmentElimination),
        ],
    };

    for round in 0..MAX_ROUNDS {
        let mut changed = false;
        for pass in &passes {
            let before = *body_shape(body);
            changed |= pass.run(body, &mut stats);
            debug_assert!(
                ajave_ir::validate(body).is_ok(),
                "pass {} produced an invalid body: {:?} (was {:?})",
                pass.name(),
                ajave_ir::validate(body),
                before
            );
        }
        if !changed {
            break;
        }
        if round == MAX_ROUNDS - 1 {
            debug!("ir-opt: {} hit the round cap, stopping", body.key);
        }
    }

    // Compaction runs last and once: it renumbers, so running it inside the
    // fixpoint would churn ids for no benefit.
    if level == Level::Optimise && std::env::var("AJAVE_NO_COMPACT").is_err() {
        compact::compact(body, &mut stats);
        debug_assert!(
            ajave_ir::validate(body).is_ok(),
            "compaction produced an invalid body: {:?}",
            ajave_ir::validate(body)
        );
    }
    stats
}

/// Re-exported so `compact` can rewrite operands with the same coverage
/// `copy_prop` uses; two lists that can drift is how a rewrite misses a read.
pub(crate) use copy_prop::rvalue_operands_mut as copy_prop_operands_mut;

/// A cheap shape summary, used only in the debug assertion above so a failure
/// message says what the body looked like going in.
fn body_shape(body: &Body) -> Box<(usize, usize, usize)> {
    Box::new((
        body.blocks.len(),
        body.vars.len(),
        body.blocks.iter().map(|b| b.stmts.len()).sum(),
    ))
}

/// Whether the optimising level is enabled.
///
/// Off by default. `CLAUDE.md` records what a default justified on one property
/// costs on the other, so this stays off until the configuration differential
/// and both full runs are clean.
pub fn level_from_env() -> Level {
    match std::env::var("AJAVE_IR_OPT").as_deref() {
        Ok("1") | Ok("true") | Ok("on") => Level::Optimise,
        Ok("normalise") | Ok("norm") => Level::Normalise,
        // Default off. Copy propagation alone changes two `float-widen`
        // verdicts and DCE changes seven securibench ones -- the transformed
        // IR is verifiably correct in both cases, so the sensitivity is in the
        // engines, and until that is understood neither level is safe to
        // enable by default.
        _ => Level::None,
    }
}
