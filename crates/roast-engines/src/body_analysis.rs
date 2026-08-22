//! Shared body-analysis utilities used by multiple engines.

use roast_ir::{BinOp, BlockId, Body, Operand, Rvalue, Stmt, Terminator, VarId};

/// Returns `true` if the body uses operations that are havoced (unmodelled)
/// in the simplified SMT/LIA encoding: field access, instance-of checks,
/// method calls, or explicit havoc. Proving engines skip such bodies to
/// remain sound.
///
/// Delegates to `body_shape::analyze` rather than walking the body itself.
/// There used to be a second walk here computing this by hand, and the two
/// disagreed about `Rvalue::Call` -- see the module doc on `body_shape` for
/// what that would have cost the first time `suitable_for_proving` acquired a
/// caller.
pub fn body_uses_havoced_ops(body: &Body) -> bool {
    crate::body_shape::analyze(body).uses_havoced_ops()
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
pub fn find_defining_bin(
    body: &Body,
    block: BlockId,
    v: VarId,
) -> Option<(BinOp, &Operand, &Operand)> {
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
