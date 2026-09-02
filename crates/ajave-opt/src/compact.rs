//! Variable compaction: renumber so `body.vars` holds only what is used.
//!
//! This is the pass the whole exercise is for. Width is what every consumer
//! pays for — it is the arity of every CHC block predicate and the size of
//! every BMC state, and the BMC's merge cost is roughly `forks × width`.

use crate::{liveness, Stats};
use ajave_ir::*;
use std::collections::{BTreeSet, HashMap};

/// Renumber variables, dropping any that are neither read nor written.
///
/// # The invariant that makes this safe
///
/// `find_param_var_indices` maps a method's parameters by `VarKind::Local`
/// slot, and `Body::is_static` decides whether slot 0 holds `this`. A variable
/// carrying a `Local` slot is therefore kept and keeps its `VarInfo`
/// unchanged, whatever its new `VarId` — `liveness::read_vars` already treats
/// every `Local` as read for this reason. Only `Stack` and `Temp` variables can
/// disappear, and those have no slot for anything to refer to.
pub(crate) fn compact(body: &mut Body, stats: &mut Stats) {
    let read = liveness::read_vars(body);

    // Written-to variables must survive even if never read: the assignment is
    // still there (dead-assignment elimination kept it because its rvalue has
    // an effect), and it needs somewhere to put the result.
    let mut used: BTreeSet<VarId> = read;
    for b in &body.blocks {
        for s in &b.stmts {
            if let Stmt::Assign(dst, _) = s {
                used.insert(*dst);
            }
        }
    }

    if used.len() == body.vars.len() {
        return;
    }

    // Ascending order, so the renumbering is a stable order-preserving
    // relabelling rather than whatever a hash map iterated. Reproducibility is
    // not optional here: verdicts once depended on `HashMap` iteration order.
    let mut remap: HashMap<VarId, VarId> = HashMap::with_capacity(used.len());
    let mut vars = Vec::with_capacity(used.len());
    for (new, old) in used.iter().enumerate() {
        remap.insert(*old, VarId(new as u32));
        vars.push(body.vars[old.0 as usize].clone());
    }
    stats.vars_removed += body.vars.len() - vars.len();
    body.vars = vars;

    let map_op = |op: &mut Operand, remap: &HashMap<VarId, VarId>| {
        if let Operand::Var(v) = op {
            if let Some(n) = remap.get(v) {
                *v = *n;
            }
        }
    };

    for ob in &mut body.obligations {
        map_op(&mut ob.cond, &remap);
    }
    for b in &mut body.blocks {
        for s in &mut b.stmts {
            match s {
                Stmt::Assign(dst, rv) => {
                    if let Some(n) = remap.get(dst) {
                        *dst = *n;
                    }
                    for op in crate::copy_prop_operands_mut(rv) {
                        map_op(op, &remap);
                    }
                }
                Stmt::Assume(op) | Stmt::MonitorEnter(op) | Stmt::MonitorExit(op) => {
                    map_op(op, &remap)
                }
                Stmt::PutStatic(_, op) => map_op(op, &remap),
                Stmt::PutField { obj, val, .. } => {
                    map_op(obj, &remap);
                    map_op(val, &remap);
                }
                Stmt::ArrayStore { arr, idx, val } => {
                    map_op(arr, &remap);
                    map_op(idx, &remap);
                    map_op(val, &remap);
                }
                Stmt::Check(_) | Stmt::Nop => {}
            }
        }
        match &mut b.term {
            Terminator::Branch { cond, .. } => map_op(cond, &remap),
            Terminator::Switch { value, .. } => map_op(value, &remap),
            Terminator::Return(Some(op)) | Terminator::Throw(op) => map_op(op, &remap),
            _ => {}
        }
    }
}
