//! Dead-assignment elimination.
//!
//! Removes `Stmt::Assign` whose result is never read **and** whose rvalue has
//! no effect. The exclusion list below is the entire safety argument, and every
//! entry corresponds to something an engine would silently get wrong.

use crate::{liveness, Pass, Stats};
use ajave_ir::*;

pub(crate) struct DeadAssignmentElimination;

/// May the value this rvalue computes be discarded?
///
/// Not "is it pure" — the question is narrower and answering the wider one is
/// how this goes wrong.
fn removable(rv: &Rvalue) -> bool {
    match rv {
        // A witness is a *sequence* of nondeterministic values replayed on a
        // real JVM (`-Dajave.seq=...`). Removing one shifts every later value,
        // so a witness that used to reproduce stops reproducing — and a witness
        // that does not reproduce is a lost FALSE, not a lost optimisation.
        // This holds even when the value is unread, because position matters.
        Rvalue::Nondet(..) => false,

        // A call can write fields, start threads and throw, none of which is
        // visible in its result. `contract_of` knows which are pure; anything
        // it has not been told about is `Contract::OPAQUE`, and the default
        // must be to keep the call.
        Rvalue::Call { target, .. } => ajave_models::contract_of(
            &target.class,
            &target.name,
            &target.desc,
        )
        .map(|c| c.effect == ajave_models::Effect::Pure)
        .unwrap_or(false),

        // Allocation is observable twice over: `new int[n]` throws
        // NegativeArraySizeException for n < 0, and object identity is
        // observable through reference equality, which is exactly what the
        // heap encoding's allocation addresses rely on.
        Rvalue::New(_) | Rvalue::NewArray { .. } => false,

        // A load can throw — NullPointerException, ArrayIndexOutOfBounds — and
        // the obligation for that is a separate statement, so dropping the load
        // does not drop the obligation. Kept anyway: the value is unread, so
        // removing it saves nothing an engine notices, and reasoning about
        // which loads are safe is precisely the kind of second opinion about
        // heap behaviour that belongs in one place, not here.
        Rvalue::ArrayLoad { .. } | Rvalue::ArrayLength(_)
        | Rvalue::GetField { .. } | Rvalue::GetStatic(_) => false,

        // Pure computation over values already in scope.
        Rvalue::Use(_) | Rvalue::Bin(..) | Rvalue::Neg(_) | Rvalue::Cast(..)
        | Rvalue::Cmp(..) | Rvalue::InstanceOf { .. } | Rvalue::Havoc(..) => true,
    }
}

impl Pass for DeadAssignmentElimination {
    fn name(&self) -> &'static str {
        "dead-assignment-elimination"
    }

    fn run(&self, body: &mut Body, stats: &mut Stats) -> bool {
        let live = liveness::read_vars(body);
        let mut removed = 0usize;
        for b in &mut body.blocks {
            b.stmts.retain(|s| match s {
                Stmt::Assign(dst, rv) => {
                    let keep = live.contains(dst) || !removable(rv);
                    if !keep {
                        removed += 1;
                    }
                    keep
                }
                // Everything else is an effect or an obligation. `Check` in
                // particular is the product: an optimiser that removes one has
                // deleted the question rather than answered it.
                _ => true,
            });
        }
        stats.assignments_removed += removed;
        removed > 0
    }
}
