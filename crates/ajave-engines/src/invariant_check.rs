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

/// The SMT array a field's cells live in.
///
/// Shared by the checker and `interpolation`'s encoder so the two cannot spell
/// it differently. Non-identifier characters in a class name are mapped, since
/// `java/lang/Object` is not an SMT-LIB symbol.
pub fn field_array_name(f: &ajave_ir::FieldKey) -> String {
    let sanitise = |t: &str| {
        t.chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect::<String>()
    };
    format!("fld_{}_{}", sanitise(&f.class), sanitise(&f.name))
}

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
fn render(e: &Expr, post: bool) -> Option<String> {
    Some(match e {
        // `v{i}p` directly, not a separate `post_v{i}` bound to it. The
        // indirection hid a bug: only *variables* were being prefixed, so a
        // heap term rendered its pre-state array in the post-state formula and
        // preservation degenerated to `inv ∧ T ∧ ¬inv` over the same state —
        // trivially UNSAT, so it confirmed whatever it was given.
        Expr::Var(v) => format!("v{}{}", v.0, if post { "p" } else { "" }),
        Expr::Int(n) => {
            if *n < 0 {
                format!("(- {})", -n)
            } else {
                n.to_string()
            }
        }
        Expr::Bool(b) => b.to_string(),
        Expr::Not(a) => format!("(not {})", render(a, post)?),
        Expr::Bin(op, a, b) => {
            let (l, r) = (render(a, post)?, render(b, post)?);
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
        // The array constant the LIA encoder declares for this site. The
        // naming must match `encode_body_lia`'s `arr_name` exactly: a checker
        // that invented its own spelling would read a different array from the
        // one the transition relation writes, and then confirm invariants
        // about nothing. Producer and consumer disagreeing about an artifact
        // is worse than no artifact.
        Expr::Select { site, index } => {
            format!(
                "(select arr{}_{}{} {})",
                site.block.0,
                site.index,
                if post { "p" } else { "" },
                render(index, post)?
            )
        }
        // A field of a particular object, Burstall-style: one array per field
        // name, indexed by the receiver. The naming must match the encoder's
        // `fld_name` exactly, for the same reason `Select` must — a checker
        // reading a different array from the one the transition relation
        // writes confirms invariants about nothing.
        //
        // A `double`- or `float`-typed field is declined: the array is
        // `(Array Int Int)` and a float cell could not be stated in it.
        Expr::Field { field, obj } => {
            if field.desc == "D" || field.desc == "F" {
                return None;
            }
            format!(
                "(select {}{} {})",
                field_array_name(field),
                if post { "p" } else { "" },
                render(obj, post)?
            )
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
    // waved through. See the module doc. `Expr::Select`'s index is screened by
    // this too, via `mentioned_vars`; the *element* type is integer by
    // construction, because `encode_body_lia` declares every site's array as
    // `(Array Int Int)` and a float array would have fallen through to an
    // unconstrained read rather than a `select`.
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

    let Some(pre) = render(&inv.formula, false) else {
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
    let Some(post) = render(&inv.formula, true) else {
        return CertResult::Inconclusive;
    };
    let decls = enc.declarations.clone();
    let preservation = format!(
        "{decls}\n(assert {pre})\n(assert {})\n(assert (not {post}))\n(check-sat)\n",
        enc.transition
    );
    if std::env::var("AJAVE_DUMP_PRESERVATION").is_ok() {
        // Kept. Every bug in this function so far has been found by reading
        // the script z3 was actually given, and all three were invisible from
        // the Rust side: an undeclared binder, a post-state that was secretly
        // the pre-state, and a path condition added after the formula that
        // needed it.
        eprintln!("--- PRESERVATION ---\n{preservation}\n--- END ---");
    }
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
            scope: ajave_core::artifact::Scope::Point(ProgramPoint {
                method: mk(),
                block: BlockId(0),
                index: 0,
            }),
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
    /// `a = new int[4]; a[0] = 7; check(a[0]);` — the obligation is violated
    /// where the element is 0, and the invariant says it is 7.
    ///
    /// Before H2/H4 this was uncheckable: `ArrayLoad` fell through to a fresh
    /// unconstrained constant, so two reads of the same element were unrelated
    /// and no invariant could mention an array at all.
    fn array_body(store_value: i32) -> Body {
        let site = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 0,
        };
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                ajave_ir::VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Ref,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(1),
                    ty: Ty::Int,
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
                stmts: vec![
                    Stmt::Assign(
                        VarId(0),
                        Rvalue::NewArray {
                            elem: "I".into(),
                            len: Operand::Const(Const::Int(4)),
                            site,
                        },
                    ),
                    Stmt::ArrayStore {
                        arr: Operand::Var(VarId(0)),
                        idx: Operand::Const(Const::Int(0)),
                        val: Operand::Const(Const::Int(store_value)),
                    },
                    Stmt::Assign(
                        VarId(1),
                        Rvalue::ArrayLoad {
                            arr: Operand::Var(VarId(0)),
                            idx: Operand::Const(Const::Int(0)),
                        },
                    ),
                    Stmt::Check(ObligationId(0)),
                ],
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    fn elem_eq(n: i64) -> Expr {
        Expr::bin(
            Op::Eq,
            Expr::Select {
                site: ajave_ir::AllocSite {
                    block: BlockId(0),
                    index: 0,
                },
                index: Box::new(Expr::Int(0)),
            },
            Expr::Int(n),
        )
    }

    /// `o.f = stored; e = o.f; c = (e == asserted); check(c)` with `o` from a
    /// fresh allocation. Two receivers when `two` is set, so the aliasing case
    /// can be stated.
    fn field_body(stored: i32, asserted: i32, two: bool) -> Body {
        let site = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 0,
        };
        let site2 = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 3,
        };
        let f = ajave_ir::FieldKey {
            class: "Box".into(),
            name: "v".into(),
            desc: "I".into(),
        };
        let mut stmts = vec![
            Stmt::Assign(
                VarId(0),
                Rvalue::New {
                    class: "Box".into(),
                    site,
                },
            ),
            Stmt::PutField {
                obj: Operand::Var(VarId(0)),
                field: f.clone(),
                val: Operand::Const(Const::Int(stored)),
            },
        ];
        if two {
            // A second, distinct object whose field holds something else. The
            // flat abstraction would merge these; field-as-array must not.
            stmts.push(Stmt::Assign(
                VarId(3),
                Rvalue::New {
                    class: "Box".into(),
                    site: site2,
                },
            ));
            stmts.push(Stmt::PutField {
                obj: Operand::Var(VarId(3)),
                field: f.clone(),
                val: Operand::Const(Const::Int(99)),
            });
        }
        stmts.push(Stmt::Assign(
            VarId(1),
            Rvalue::GetField {
                obj: Operand::Var(VarId(0)),
                field: f.clone(),
            },
        ));
        stmts.push(Stmt::Assign(
            VarId(2),
            Rvalue::Bin(
                ajave_ir::BinOp::Eq,
                Operand::Var(VarId(1)),
                Operand::Const(Const::Int(asserted)),
            ),
        ));
        stmts.push(Stmt::Check(ObligationId(0)));
        // Fix the site indices to where the statements actually sit.
        if two {
            if let Stmt::Assign(_, Rvalue::New { site, .. }) = &mut stmts[2] {
                site.index = 2;
            }
        }
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                ajave_ir::VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Ref,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(1),
                    ty: Ty::Int,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(2),
                    ty: Ty::Int,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(3),
                    ty: Ty::Ref,
                },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(2)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts,
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    fn fld_eq(n: i64) -> Expr {
        Expr::Bin(
            Op::Eq,
            Box::new(Expr::Field {
                field: ajave_ir::FieldKey {
                    class: "Box".into(),
                    name: "v".into(),
                    desc: "I".into(),
                },
                obj: Box::new(Expr::Var(VarId(0))),
            }),
            Box::new(Expr::Int(n)),
        )
    }

    /// A1/A2 control. Before field-as-array, `GetField` fell through to a
    /// fresh constant and no invariant could mention a field at all.
    #[test]
    fn a_field_invariant_can_be_confirmed() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &field_body(7, 7, false),
            &inv(fld_eq(7)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Confirmed,
            "the store writes 7, so `o.v == 7` is sufficient and preserved"
        );
    }

    #[test]
    fn a_field_invariant_contradicted_by_the_store_is_refuted() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &field_body(0, 7, false),
            &inv(fld_eq(7)),
            ObligationId(0),
            s,
        );
        assert_ne!(r, CertResult::Confirmed, "the store writes 0");
    }

    /// The reason the Burstall model was chosen. A second object's field write
    /// must not disturb the first's — which the flat abstraction in
    /// `interval.rs` cannot express, and which this gets from the solver for
    /// free because `o` and `p` are distinct references.
    #[test]
    fn a_second_receivers_write_does_not_disturb_the_first() {
        let Some(s) = solver() else { return };
        let r = check_inductive(&field_body(7, 7, true), &inv(fld_eq(7)), ObligationId(0), s);
        assert_eq!(
            r,
            CertResult::Confirmed,
            "p.v = 99 must not make o.v == 7 unprovable; if this fails the \
             field cells are merged rather than indexed by receiver"
        );
    }

    /// The control for the array path. If this cannot confirm, every negative
    /// array result below is vacuous.
    #[test]
    fn an_array_element_invariant_can_be_confirmed() {
        let Some(s) = solver() else { return };
        let r = check_inductive(&array_body(7), &inv(elem_eq(7)), ObligationId(0), s);
        assert_eq!(
            r,
            CertResult::Confirmed,
            "the store writes 7, so `a[0] == 7` is sufficient and preserved"
        );
    }

    /// The store writes 0, so the element *is* the violating value and an
    /// invariant claiming otherwise must not be confirmed. This is the test
    /// that would have passed vacuously before the encoder modelled arrays:
    /// an unconstrained read makes every array invariant unprovable, so a
    /// `Refuted` here would have meant nothing without the control above.
    #[test]
    fn an_array_invariant_contradicted_by_the_store_is_refuted() {
        let Some(s) = solver() else { return };
        let r = check_inductive(&array_body(0), &inv(elem_eq(7)), ObligationId(0), s);
        assert_ne!(
            r,
            CertResult::Confirmed,
            "the store writes 0; `a[0] == 7` cannot be confirmed"
        );
    }

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
