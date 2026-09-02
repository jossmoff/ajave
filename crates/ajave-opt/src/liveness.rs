//! Which variables a body actually reads.
//!
//! Shared by dead-assignment elimination and compaction so the two cannot
//! disagree about what is live — a pass that missed a read would delete a value
//! something else depends on, which is a wrong verdict rather than a
//! regression.

use ajave_ir::*;
use std::collections::BTreeSet;

/// Every variable read anywhere in the body.
///
/// Deliberately *not* per-program-point. A flow-sensitive liveness would remove
/// more, and would also have to be right about back-edges and exceptional
/// edges; this whole-body version cannot be wrong about control flow because it
/// does not look at it. `smt_encode`'s back-edge bug is the cautionary case:
/// a traversal that is subtly wrong about the CFG produces a silently wrong
/// answer. Start with the version that cannot have that bug, and measure
/// whether the precise one is needed.
pub(crate) fn read_vars(body: &Body) -> BTreeSet<VarId> {
    let mut live = BTreeSet::new();
    let mut note = |op: &Operand, live: &mut BTreeSet<VarId>| {
        if let Operand::Var(v) = op {
            live.insert(*v);
        }
    };

    for b in &body.blocks {
        for s in &b.stmts {
            match s {
                Stmt::Assign(_, rv) => {
                    for op in rvalue_operands(rv) {
                        note(op, &mut live);
                    }
                }
                Stmt::Assume(op) | Stmt::MonitorEnter(op) | Stmt::MonitorExit(op) => {
                    note(op, &mut live)
                }
                Stmt::PutStatic(_, op) => note(op, &mut live),
                Stmt::PutField { obj, val, .. } => {
                    note(obj, &mut live);
                    note(val, &mut live);
                }
                Stmt::ArrayStore { arr, idx, val } => {
                    note(arr, &mut live);
                    note(idx, &mut live);
                    note(val, &mut live);
                }
                // A `Check` reads its obligation's condition, which lives on
                // the obligation rather than in the statement. Missing this is
                // how an optimiser deletes the value an assertion tests.
                Stmt::Check(oid) => {
                    if let Some(ob) = body.obligations.get(oid.0 as usize) {
                        note(&ob.cond, &mut live);
                    }
                }
                Stmt::Nop => {}
            }
        }
        match &b.term {
            Terminator::Branch { cond, .. } => note(cond, &mut live),
            Terminator::Switch { value, .. } => note(value, &mut live),
            Terminator::Return(Some(op)) | Terminator::Throw(op) => note(op, &mut live),
            Terminator::Goto(_) | Terminator::Return(None)
            | Terminator::Halt | Terminator::Diverge(_) => {}
        }
    }

    // Parameters are read by the caller's argument binding, which is not
    // visible in this body. Dropping one would shift every later parameter's
    // slot, and `find_param_var_indices` maps parameters by slot.
    for (i, vi) in body.vars.iter().enumerate() {
        if matches!(vi.kind, VarKind::Local(_)) {
            live.insert(VarId(i as u32));
        }
    }
    live
}
