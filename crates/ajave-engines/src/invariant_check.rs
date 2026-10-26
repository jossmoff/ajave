//! Independent checking of invariant-backed TRUE claims.
//!
//! Workstream A2 of `docs/plans/codebase-health.md`.
//!
//! `certify.rs` states the project's trust rule: "no artifact reaches the
//! reporter on an engine's authority alone. FALSE is replayed on a real JVM;
//! TRUE rests on invariants re-checked by a separate, small, boring pass."
//! `JvmReplay` is that pass for FALSE. This is the beginning of it for TRUE.
//!
//! # What is checked, and what is not
//!
//! A safety proof by invariant `I` at point `P` for obligation `o` rests on
//! three claims. Two are checkable against a single invariant and are
//! implemented here:
//!
//! * **Sufficiency** — `I` rules out the violation: `I ∧ error(o)` is UNSAT.
//!   This is the claim that matters most, because it is the one the discharge
//!   directly asserts: *the state I say holds at this check makes the check
//!   pass*.
//! * **Preservation** — `I` survives the transition relation:
//!   `I(pre) ∧ T ∧ ¬I(post)` is UNSAT.
//!
//! The third, **initiation**, is deliberately absent, and the reason is a
//! design point rather than an omission. "Holds initially" is a property of an
//! invariant *map* — one assertion per program point — not of a single
//! invariant at a single point. An invariant at a non-entry block is
//! established by its predecessors, which is preservation over the map, so
//! certifying one invariant in isolation cannot express it. Until an engine
//! publishes a map rather than a point, this pass can refuse bad proofs but
//! cannot confirm good ones as *inductive* in the full sense. `check_inductive`
//! therefore returns `Confirmed` for "sufficient and locally preserved", and
//! the caller must know that is weaker than inductive. A3 decides whether to
//! publish maps.
//!
//! # The theory, and why a float invariant cannot be confirmed
//!
//! Checking happens in LIA, reusing `interpolation::encode_body_lia` so the
//! transition relation and the per-obligation error formula are the same ones
//! the rest of the tree reasons about. LIA has no floats, so an invariant
//! mentioning a float or double variable cannot be stated, let alone checked —
//! those return `Inconclusive`, which refuses the discharge. That is the right
//! answer and not a limitation to route around: ajave's one confirmed wrong
//! TRUE (`benchmarks/ajave/jvm-floats/FloatIsNotDouble`, #48) is exactly a
//! float-arithmetic proof, and a checker that cannot see floats must decline
//! rather than wave them through.
//!
//! # The honest limit on independence
//!
//! This shares `encode_body_lia` with `imc` and `cegar`. A checker that reuses
//! the encoder of the engine it checks is not fully independent — an identical
//! misunderstanding in both is invisible. Full independence needs a second
//! implementation of JVM semantics, which `certify.rs` concedes is a
//! multi-year project. What this buys is a separate pass, a different code
//! path, and three explicit obligations, which catches engine-specific
//! defects; every finding in the 2026-10-26 audit was exactly that.

use ajave_core::artifact::Invariant;
use ajave_core::certify::CertResult;
use ajave_core::term::{Expr, Op};
use ajave_ir::{Body, ObligationId, Ty, VarId};
use log::debug;

use crate::interpolation::{encode_body_lia, run_solver_batch_pub};

/// Which program variables an invariant mentions.
fn mentioned_vars(e: &Expr, out: &mut Vec<VarId>) {
    match e {
        Expr::Var(v) => out.push(*v),
        Expr::Bin(_, a, b) => {
            mentioned_vars(a, out);
            mentioned_vars(b, out);
        }
        Expr::Not(a) => mentioned_vars(a, out),
        Expr::Apply { args, .. } => args.iter().for_each(|a| mentioned_vars(a, out)),
        _ => {}
    }
}

/// Render an `Expr` as SMT-LIB over integer variables named `{prefix}v{i}`.
///
/// Returns `None` for anything LIA cannot state — a double, an uninterpreted
/// library application, a division (whose JVM semantics is truncating and not
/// SMT-LIB's `div`). Declining is the safe direction: the caller turns `None`
/// into `Inconclusive`, which refuses the discharge.
fn render(e: &Expr, prefix: &str) -> Option<String> {
    Some(match e {
        Expr::Var(v) => format!("{prefix}v{}", v.0),
        Expr::Int(n) => {
            if *n < 0 {
                format!("(- {})", -n)
            } else {
                n.to_string()
            }
        }
        Expr::Bool(b) => b.to_string(),
        Expr::Not(a) => format!("(not {})", render(a, prefix)?),
        Expr::Bin(op, a, b) => {
            let (l, r) = (render(a, prefix)?, render(b, prefix)?);
            let sym = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Lt => "<",
                Op::Le => "<=",
                Op::Gt => ">",
                Op::Ge => ">=",
                Op::Eq => "=",
                Op::And => "and",
                Op::Or => "or",
                // `Ne` is not an SMT-LIB operator; `Div`/`Rem` do not agree
                // with the JVM's truncating semantics in LIA.
                Op::Ne => return Some(format!("(not (= {l} {r}))")),
                Op::Div | Op::Rem => return None,
            };
            format!("({sym} {l} {r})")
        }
        // A double is held as a bit pattern and means nothing in LIA; an
        // `Apply` is an unmodelled library call by construction.
        Expr::Double(_) | Expr::Apply { .. } => return None,
    })
}

/// Ask the solver whether `script`'s assertions are unsatisfiable.
///
/// `unknown`, a solver error, or anything unparseable is **not** UNSAT. A
/// proof may only rest on a definite answer.
fn is_unsat(solver: &str, script: &str) -> Option<bool> {
    match run_solver_batch_pub(solver, &["-in", "-smt2"], script) {
        Ok(lines) => {
            let answer = lines.iter().find(|l| {
                let t = l.trim();
                t == "sat" || t == "unsat" || t == "unknown"
            })?;
            match answer.trim() {
                "unsat" => Some(true),
                "sat" => Some(false),
                _ => None,
            }
        }
        Err(e) => {
            debug!("invariant-check: solver failed: {e}");
            None
        }
    }
}

/// Check an invariant-backed proof of `oid` in `body`.
///
/// `Confirmed` means sufficient and locally preserved — see the module doc for
/// why that is weaker than inductive. `Refuted` means a definite UNSAT was
/// expected and the solver said SAT: the invariant does not justify the claim.
/// `Inconclusive` covers everything else, including anything LIA cannot state.
pub fn check_inductive(
    body: &Body,
    inv: &Invariant,
    oid: ObligationId,
    solver: &str,
) -> CertResult {
    // An invariant about a float says nothing checkable here, and must not be
    // waved through. See the module doc.
    let mut vars = Vec::new();
    mentioned_vars(&inv.formula, &mut vars);
    if vars.iter().any(|v| {
        body.vars
            .get(v.0 as usize)
            .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
            .unwrap_or(true)
    }) {
        debug!(
            "invariant-check: {} mentions a float or unknown var",
            inv.id
        );
        return CertResult::Inconclusive;
    }

    let Some(pre) = render(&inv.formula, "") else {
        debug!("invariant-check: {} is not expressible in LIA", inv.id);
        return CertResult::Inconclusive;
    };

    let enc = encode_body_lia(body, &[oid], "");
    let errors: Vec<&String> = enc
        .error_formulas
        .iter()
        .filter(|(id, _)| *id == oid)
        .map(|(_, f)| f)
        .collect();
    if errors.is_empty() {
        // The obligation's check is not in this body, so there is nothing for
        // an invariant here to justify.
        return CertResult::Inconclusive;
    }
    let error = if errors.len() == 1 {
        errors[0].clone()
    } else {
        format!(
            "(or {})",
            errors
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        )
    };

    // 1. Sufficiency: the invariant rules out the violation.
    let sufficiency = format!(
        "{}\n(assert {pre})\n(assert {error})\n(check-sat)\n",
        enc.declarations
    );
    match is_unsat(solver, &sufficiency) {
        Some(true) => {}
        Some(false) => {
            debug!(
                "invariant-check: {} does not imply safety of {oid:?}",
                inv.id
            );
            return CertResult::Refuted;
        }
        None => return CertResult::Inconclusive,
    }

    // 2. Preservation: the invariant survives one step of the transition.
    let Some(post) = render(&inv.formula, "post_") else {
        return CertResult::Inconclusive;
    };
    // `encode_body_lia` names the post-state `v{i}p`; rebind those to the
    // `post_v{i}` the renderer produced, rather than teaching the renderer the
    // other convention and having two spellings of the same thing.
    let mut binds = String::new();
    for i in 0..enc.n_vars {
        binds.push_str(&format!("(assert (= post_v{i} v{i}p))\n"));
    }
    let mut decls = enc.declarations.clone();
    for i in 0..enc.n_vars {
        decls.push_str(&format!("(declare-fun post_v{i} () Int)\n"));
    }
    let preservation = format!(
        "{decls}\n(assert {pre})\n(assert {})\n{binds}(assert (not {post}))\n(check-sat)\n",
        enc.transition
    );
    match is_unsat(solver, &preservation) {
        Some(true) => CertResult::Confirmed,
        Some(false) => {
            debug!("invariant-check: {} is not preserved", inv.id);
            CertResult::Refuted
        }
        None => CertResult::Inconclusive,
    }
}

#[cfg(test)]
mod tests {
    //! One fixture per failure mode, so a pass means the specific obligation
    //! held rather than that the checker declined for an unrelated reason.
    //! The control comes first: if `Confirmed` is unreachable, every negative
    //! result below is vacuous.

    use super::*;
    use ajave_core::artifact::ProgramPoint;
    use ajave_core::term::Expr;
    use ajave_ir::{
        Block, BlockId, Const, MethodKey, Obligation, ObligationKind, Operand, Rvalue, Stmt,
        Terminator, VarInfo, VarKind,
    };

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "m".into(),
            desc: "()V".into(),
        }
    }

    /// `check(v1);` with `v1` never assigned — so the obligation is violable
    /// exactly where `v1 == 0`, and an invariant has real work to do.
    ///
    /// The first version of this fixture assigned `v1 := 5` before the check.
    /// That made the error formula `(= 5 0)`, already UNSAT, so sufficiency
    /// passed for *any* invariant including `true` — the invariant was never
    /// load-bearing and the negative test could not fail. A fixture where the
    /// property holds without the thing under test proves nothing about it.
    fn body_check_only(ty: Ty) -> Body {
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Int,
                },
                VarInfo {
                    kind: VarKind::Local(1),
                    ty,
                },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(1)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![Stmt::Check(ObligationId(0))],
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    /// The same check, plus a block that assigns `v1 := 0` and loops back. An
    /// invariant like `v1 >= 1` is *sufficient* here but not *preserved*,
    /// which is what separates the two queries.
    fn body_that_breaks_the_invariant() -> Body {
        let mut b = body_check_only(Ty::Int);
        b.blocks[0].term = Terminator::Goto(BlockId(1));
        b.blocks.push(Block {
            id: BlockId(1),
            bytecode_offset: 1,
            stmts: vec![Stmt::Assign(
                VarId(1),
                Rvalue::Use(Operand::Const(Const::Int(0))),
            )],
            term: Terminator::Goto(BlockId(0)),
            exceptional: vec![],
        });
        b
    }

    fn inv(formula: Expr) -> Invariant {
        Invariant {
            id: 1,
            at: ProgramPoint {
                method: mk(),
                block: BlockId(0),
                index: 0,
            },
            formula,
            status: ajave_core::artifact::InvStatus::Candidate,
        }
    }

    fn ge(v: u32, n: i64) -> Expr {
        Expr::bin(Op::Ge, Expr::Var(VarId(v)), Expr::Int(n))
    }

    fn solver() -> Option<&'static str> {
        match std::process::Command::new("z3").arg("--version").output() {
            Ok(o) if o.status.success() => Some("z3"),
            _ => {
                eprintln!("no z3 on PATH; skipping");
                None
            }
        }
    }

    /// Control. Without this, every `Refuted` below could come from the
    /// checker being unable to confirm anything at all.
    #[test]
    fn a_sufficient_and_preserved_invariant_is_confirmed() {
        let Some(s) = solver() else { return };
        // `v1 >= 1` rules out `v1 == 0`, and the only assignment sets v1 := 5.
        // `v1 >= 1` excludes `v1 == 0`, and nothing in this body assigns v1.
        let r = check_inductive(
            &body_check_only(Ty::Int),
            &inv(ge(1, 1)),
            ObligationId(0),
            s,
        );
        assert_eq!(r, CertResult::Confirmed, "the control fixture must confirm");
    }

    #[test]
    fn an_invariant_that_does_not_imply_safety_is_refuted() {
        let Some(s) = solver() else { return };
        // `true` holds everywhere and rules out nothing, so it cannot justify
        // a discharge however inductive it is.
        let r = check_inductive(
            &body_check_only(Ty::Int),
            &inv(Expr::Bool(true)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "sufficiency must fail: `true` does not exclude the violation"
        );
    }

    #[test]
    fn an_invariant_the_transition_breaks_is_refuted() {
        let Some(s) = solver() else { return };
        // `v1 >= 1` is sufficient (it excludes v1 == 0) but a block assigns
        // v1 := 0, so it is not preserved. This isolates preservation from
        // sufficiency: the first query passes and the second must not.
        let r = check_inductive(
            &body_that_breaks_the_invariant(),
            &inv(ge(1, 1)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "preservation must fail: a block assigns v1 := 0"
        );
    }

    /// LIA cannot state a float invariant, and a checker that cannot see
    /// floats must decline rather than wave them through. ajave's one
    /// confirmed wrong TRUE is a float-arithmetic proof (#48).
    #[test]
    fn a_float_invariant_cannot_be_confirmed() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &body_check_only(Ty::Float),
            &inv(ge(1, 1)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Inconclusive,
            "a float invariant must be Inconclusive, never Confirmed"
        );
    }

    #[test]
    fn an_unmodelled_library_application_cannot_be_confirmed() {
        let Some(s) = solver() else { return };
        let apply = Expr::call("java/lang/Math", "sin", "(D)D", vec![Expr::Var(VarId(0))]);
        let r = check_inductive(
            &body_check_only(Ty::Int),
            &inv(Expr::bin(Op::Ge, apply, Expr::Int(0))),
            ObligationId(0),
            s,
        );
        assert_eq!(r, CertResult::Inconclusive);
    }
}
