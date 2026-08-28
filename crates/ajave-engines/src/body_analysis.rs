//! Shared body-analysis utilities used by multiple engines.

use ajave_ir::{BinOp, BlockId, Body, Operand, Rvalue, Stmt, Terminator, VarId};
use ajave_models;

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
    use ajave_ir::Ty;
    body.vars.iter().any(|vi| matches!(vi.ty, Ty::Long | Ty::Double))
}

/// Returns `true` if the body uses Float or Double typed variables (but not
/// necessarily Long). Used to route bodies to the widening interval CPA.
pub fn body_uses_float_types(body: &Body) -> bool {
    use ajave_ir::Ty;
    body.vars.iter().any(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
}

/// Returns `true` if the body uses Long typed variables. The i32-based
/// interval domain is unsound for Long arithmetic; these bodies must be
/// skipped entirely by the standard interval analysis.
pub fn body_uses_long_types(body: &Body) -> bool {
    use ajave_ir::Ty;
    body.vars.iter().any(|vi| matches!(vi.ty, Ty::Long))
}

/// Returns `true` if the body calls transcendental Math methods (sin, cos, exp,
/// log, pow, sqrt, etc.) that require a nonlinear real arithmetic solver.
pub fn body_uses_transcendental_math(body: &Body) -> bool {
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if ajave_models::is_transcendental_math(&target.class, &target.name) {
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

/// Does this body call a method whose exceptional behaviour we do not model?
///
/// A library method with no body is either havoced or modelled for its *value*.
/// Neither captures the exceptions it may raise: `"abc".charAt(5)` throws
/// `StringIndexOutOfBoundsException`, but the IR emits no `Check` for it, so no
/// engine can find a violation and the program looks safe by vacuity.
///
/// Any engine that wants to discharge a **no-runtime-exception** obligation has
/// to account for that. The BMC does it via
/// `Completeness::has_potentially_throwing_havoc`; the interval AI has no
/// equivalent notion of a call at all, so it needs this check instead.
///
/// Methods with bodies are excluded: those are analysed directly, and whatever
/// they throw shows up as an obligation in the callee.
pub fn body_has_unmodelled_throwing_call(prog: &ajave_ir::Program, body: &Body) -> bool {
    first_unmodelled_throwing_call(prog, body).is_some()
}

/// The first such call, for diagnostics: knowing *which* signature blocks a
/// proof is what tells us whether the allowlist is too tight or the program
/// genuinely does something we cannot reason about.
pub fn first_unmodelled_throwing_call<'a>(
    prog: &ajave_ir::Program,
    body: &'a Body,
) -> Option<&'a ajave_ir::MethodKey> {
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(_, Rvalue::Call { target, .. }) = stmt {
                if prog.body(target).is_some() {
                    continue; // has a body — analysed on its own terms
                }
                // An interface or abstract method has no body of its own, but
                // the call is still resolvable when every implementation we can
                // see does. `ObjectFactory.createObject()` is declared on an
                // interface and implemented by the benchmark, so treating it as
                // an unanalysable library call blocked those tasks outright.
                let impls = prog.devirtualise(target);
                if !impls.is_empty() && impls.iter().all(|k| prog.body(k).is_some()) {
                    continue;
                }
                // A call only blocks the verdict when we cannot state *why*
                // it might throw. If its contract names conditions over the
                // arguments, the lifter has already seeded them as obligations
                // and the engines either discharge them or leave them open —
                // either way the burden is carried explicitly, and vetoing here
                // as well would double-count it and lose every program that
                // merely *mentions* such a method.
                match ajave_models::contract_of(&target.class, &target.name, &target.desc) {
                    Some(c) if c.preconditions_all_seeded() => continue,
                    Some(_) => return Some(target),
                    None => {
                        if crate::smt_bmc::could_throw_runtime_exception(target) {
                            return Some(target);
                        }
                    }
                }
            }
        }
    }
    None
}
