//! Shared body-analysis utilities used by multiple engines.

use roast_ir::{BinOp, BlockId, Body, Operand, Rvalue, Stmt, Terminator, VarId};
use roast_models;

/// Returns `true` if the body uses operations that are havoced (unmodelled)
/// in the simplified SMT/LIA encoding: field access, instance-of checks,
/// method calls, or explicit havoc. Proving engines skip such bodies to
/// remain sound.
pub fn body_uses_havoced_ops(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rv) => match rv {
                    Rvalue::GetStatic(_)
                    | Rvalue::GetField { .. }
                    | Rvalue::InstanceOf { .. }
                    | Rvalue::Call { .. }
                    | Rvalue::Havoc(_) => return true,
                    _ => {}
                },
                Stmt::PutField { .. } => return true,
                _ => {}
            }
        }
    }
    false
}

/// Returns `true` if the body uses Long or Double typed variables.
/// The interval AI domain uses i32 arithmetic, so its intervals are unsound
/// for bodies that manipulate 64-bit values (comparisons, casts, etc.).
pub fn body_uses_wide_types(body: &Body) -> bool {
    use roast_ir::Ty;
    body.vars.iter().any(|vi| matches!(vi.ty, Ty::Long | Ty::Double))
}

/// Returns `true` if the body calls transcendental Math methods (sin, cos, exp,
/// log, pow, sqrt, etc.) that require a nonlinear real arithmetic solver.
pub fn body_uses_transcendental_math(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if roast_models::is_transcendental_math(&target.class, &target.name) {
                    return true;
                }
            }
        }
    }
    false
}

/// Returns `true` if the body has any back-edges (loops).
pub fn body_has_loops(body: &Body) -> bool {
    for block in &body.blocks {
        let succs = match &block.term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
            Terminator::Switch { cases, default, .. } => {
                let mut v: Vec<BlockId> = cases.iter().map(|(_, t)| *t).collect();
                v.push(*default);
                v
            }
            _ => vec![],
        };
        for s in succs {
            if s.0 <= block.id.0 {
                return true;
            }
        }
    }
    false
}

/// Walk backward through a block's statements to find the most recent
/// assignment of `v` to a binary operation `Rvalue::Bin(op, a, b)`.
pub fn find_defining_bin(body: &Body, block: BlockId, v: VarId) -> Option<(BinOp, &Operand, &Operand)> {
    for s in body.block(block).stmts.iter().rev() {
        if let Stmt::Assign(dv, Rvalue::Bin(op, a, b)) = s {
            if *dv == v {
                return Some((*op, a, b));
            }
        }
    }
    None
}

/// Negate a comparison operator (Eq<->Ne, Lt<->Ge, Le<->Gt).
/// Non-comparison operators are returned unchanged.
pub fn negate_binop(op: BinOp) -> BinOp {
    match op {
        BinOp::Eq => BinOp::Ne,
        BinOp::Ne => BinOp::Eq,
        BinOp::Lt => BinOp::Ge,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Ge => BinOp::Lt,
        other => other,
    }
}
