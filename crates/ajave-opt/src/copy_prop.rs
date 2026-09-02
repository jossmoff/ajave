//! Copy propagation: rewrite reads of a copied value to read the original.
//!
//! `v2 = v0; v1 = v2; v3 = v1` becomes `v2 = v0; v1 = v0; v3 = v0`. Nothing is
//! removed — that is dead-assignment elimination's job — so this pass alone
//! cannot lose a statement an engine depends on, which is why it is safe at
//! `Level::Normalise`.

use crate::{Pass, Stats};
use ajave_ir::*;
use std::collections::HashMap;

pub(crate) struct CopyPropagation;

impl Pass for CopyPropagation {
    fn name(&self) -> &'static str {
        "copy-propagation"
    }

    fn run(&self, body: &mut Body, stats: &mut Stats) -> bool {
        let mut changed = false;
        // Kinds copied out so the per-block loop can consult them while holding
        // a mutable borrow of the blocks.
        let body_vars: Vec<VarKind> = body.vars.iter().map(|v| v.kind).collect();
        // Block-local. A copy chain that crosses a block boundary needs to know
        // every predecessor agrees, which is a merge problem -- and merging is
        // where `smt_encode` had its second bug today. Within a block the
        // statements are a straight line and there is nothing to merge, so this
        // version cannot have that bug. Measure before reaching for more.
        for b in &mut body.blocks {
            let mut alias: HashMap<VarId, Operand> = HashMap::new();

            let resolve = |op: &Operand, alias: &HashMap<VarId, Operand>| -> Option<Operand> {
                match op {
                    Operand::Var(v) => alias.get(v).cloned(),
                    Operand::Const(_) => None,
                }
            };

            for s in &mut b.stmts {
                // Rewrite reads first, then record what this statement defines.
                let mut rewrite = |op: &mut Operand, changed: &mut bool, n: &mut usize| {
                    if let Some(to) = resolve(op, &alias) {
                        *op = to;
                        *changed = true;
                        *n += 1;
                    }
                };
                let mut n = 0usize;
                match s {
                    Stmt::Assign(dst, rv) => {
                        for op in rvalue_operands_mut(rv) {
                            rewrite(op, &mut changed, &mut n);
                        }
                        // Defining a variable invalidates anything aliased to
                        // it, and the alias it may itself have had.
                        alias.remove(dst);
                        alias.retain(|_, v| !matches!(v, Operand::Var(x) if x == dst));
                        // `dst = <operand>` makes dst an alias of that operand
                        // -- but only when that does not move reads *off* a
                        // named local and onto a lifter temporary.
                        //
                        // `x = x + dx` lifts to `v6 = v0 + v1; v0 = v6`, so
                        // aliasing v0 to v6 rewrites every later read of `x` to
                        // read the temporary. The two hold the same value, but
                        // the interval AI narrows whichever variable appears in
                        // a comparison, so the refinement from `if (x > 3.0)`
                        // landed on a dead temporary while the loop-carried `x`
                        // stayed widened at [3.0, inf] -- turning two
                        // `float_unboundedloop` proofs into UNKNOWN.
                        //
                        // That fragility is the analysis's, not this pass's: an
                        // analysis whose precision depends on *which* of two
                        // provably equal variables is named will be surprised by
                        // any rewrite. It is filed separately. Meanwhile the
                        // rewrite that provokes it earns nothing -- a local and
                        // a temporary cost the same -- so the pass declines to
                        // make it.
                        if let Rvalue::Use(src) = rv {
                            let dst_is_local =
                                matches!(body_vars.get(dst.0 as usize), Some(VarKind::Local(_)));
                            let src_is_temp = matches!(
                                src,
                                Operand::Var(sv)
                                    if !matches!(
                                        body_vars.get(sv.0 as usize),
                                        Some(VarKind::Local(_))
                                    )
                            );
                            if !(dst_is_local && src_is_temp) {
                                alias.insert(*dst, src.clone());
                            }
                        }
                    }
                    Stmt::Assume(op) | Stmt::MonitorEnter(op) | Stmt::MonitorExit(op) => {
                        rewrite(op, &mut changed, &mut n)
                    }
                    Stmt::PutStatic(_, op) => rewrite(op, &mut changed, &mut n),
                    Stmt::PutField { obj, val, .. } => {
                        rewrite(obj, &mut changed, &mut n);
                        rewrite(val, &mut changed, &mut n);
                    }
                    Stmt::ArrayStore { arr, idx, val } => {
                        rewrite(arr, &mut changed, &mut n);
                        rewrite(idx, &mut changed, &mut n);
                        rewrite(val, &mut changed, &mut n);
                    }
                    // An obligation's condition is rewritten below, outside the
                    // borrow of `body.blocks`.
                    Stmt::Check(_) | Stmt::Nop => {}
                }
                stats.copies_propagated += n;
            }

            let mut n = 0usize;
            match &mut b.term {
                Terminator::Branch { cond, .. } => {
                    if let Some(to) = resolve(cond, &alias) {
                        *cond = to;
                        changed = true;
                        n += 1;
                    }
                }
                Terminator::Switch { value, .. } => {
                    if let Some(to) = resolve(value, &alias) {
                        *value = to;
                        changed = true;
                        n += 1;
                    }
                }
                Terminator::Return(Some(op)) | Terminator::Throw(op) => {
                    if let Some(to) = resolve(op, &alias) {
                        *op = to;
                        changed = true;
                        n += 1;
                    }
                }
                _ => {}
            }
            stats.copies_propagated += n;
        }
        changed
    }
}

/// Mutable counterpart of `ajave_ir::rvalue_operands`.
pub(crate) fn rvalue_operands_mut(rv: &mut Rvalue) -> Vec<&mut Operand> {
    match rv {
        Rvalue::Use(o) | Rvalue::Neg(o) | Rvalue::Cast(_, _, o)
        | Rvalue::ArrayLength(o) | Rvalue::InstanceOf { obj: o, .. }
        | Rvalue::GetField { obj: o, .. } => vec![o],
        Rvalue::Bin(_, a, b) | Rvalue::Cmp(_, a, b) => vec![a, b],
        Rvalue::ArrayLoad { arr, idx } => vec![arr, idx],
        Rvalue::NewArray { len, .. } => vec![len],
        Rvalue::Call { args, .. } => args.iter_mut().collect(),
        Rvalue::Nondet(..) | Rvalue::Havoc(..) | Rvalue::GetStatic(_) | Rvalue::New(_) => vec![],
    }
}
