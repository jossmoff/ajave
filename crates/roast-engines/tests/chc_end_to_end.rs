//! End-to-end check of the CHC engine against a real Horn solver.
//!
//! The engine's answer polarity was inverted: it discharged on `unsat`, which
//! under the encoding it emits means the error state *is* reachable. That is a
//! false TRUE, the single most expensive thing this tool can produce, and it
//! survived because nothing exercised the engine directly — in the portfolio
//! the cheap engines usually decide first, so CHC's answer rarely reached the
//! verdict.
//!
//! These tests run the real engine against the real solver on two bodies whose
//! correct verdicts are not in doubt, so the polarity is pinned by execution
//! rather than by reading the SMT-LIB standard.
//!
//! Skipped when no Horn solver is on `PATH`.

use roast_core::artifact::{Direction, EngineId, ObligationRef, Status};
use roast_core::blackboard::Blackboard;
use roast_core::engine::{Budget, Engine};
use roast_engines::chc::ChcEngine;
use roast_ir::*;

fn solver_available() -> bool {
    let binary = std::env::var("ROAST_CHC_SOLVER").unwrap_or_else(|_| "z3".into());
    std::process::Command::new("which")
        .arg(&binary)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn key() -> MethodKey {
    MethodKey {
        class: "Main".into(),
        name: "main".into(),
        desc: "([Ljava/lang/String;)V".into(),
    }
}

fn int_var(slot: u16) -> VarInfo {
    VarInfo {
        kind: VarKind::Local(slot),
        ty: Ty::Int,
    }
}

/// Build a single-block body with the given statements and one obligation
/// whose safety condition is `cond`.
fn program_with(stmts: Vec<Stmt>, n_vars: usize, cond: Operand) -> Program {
    let body = Body {
        key: key(),
        entry: BlockId(0),
        blocks: vec![Block {
            id: BlockId(0),
            bytecode_offset: 0,
            stmts,
            term: Terminator::Return(None),
            exceptional: vec![],
        }],
        vars: (0..n_vars).map(|i| int_var(i as u16)).collect(),
        obligations: vec![Obligation {
            id: ObligationId(0),
            kind: ObligationKind::Assertion,
            cond,
            bytecode_offset: 0,
            line: None,
            guarded: false,
        }],
    };
    let mut prog = Program::default();
    prog.bodies.insert(key(), body);
    prog.entry = Some(key());
    prog
}

/// `v0` unconstrained; `assume(v0 >= 4)`; `assert(v0 > 3)`.
/// Safe: the assumption implies the assertion.
fn safe_program() -> Program {
    program_with(
        vec![
            Stmt::Assign(
                VarId(1),
                Rvalue::Bin(BinOp::Ge, Operand::Var(VarId(0)), Operand::int(4)),
            ),
            Stmt::Assume(Operand::Var(VarId(1))),
            Stmt::Assign(
                VarId(2),
                Rvalue::Bin(BinOp::Gt, Operand::Var(VarId(0)), Operand::int(3)),
            ),
            Stmt::Check(ObligationId(0)),
        ],
        3,
        Operand::Var(VarId(2)),
    )
}

/// `v0` unconstrained; `assert(v0 > 3)`. Unsafe: nothing rules out `v0 <= 3`.
fn unsafe_program() -> Program {
    program_with(
        vec![
            Stmt::Assign(
                VarId(1),
                Rvalue::Bin(BinOp::Gt, Operand::Var(VarId(0)), Operand::int(3)),
            ),
            Stmt::Check(ObligationId(0)),
        ],
        2,
        Operand::Var(VarId(1)),
    )
}

fn run_chc(prog: &Program) -> Status {
    let oref = ObligationRef {
        method: key(),
        id: ObligationId(0),
    };
    let mut bb = Blackboard::new();
    bb.seed(prog, true);
    assert!(
        matches!(bb.status(&oref), Status::Open),
        "the obligation must be seeded, or the engine's answer is discarded"
    );

    let mut engine = ChcEngine::new();
    bb.register_engine(engine.id(), engine.direction());
    engine.step(prog, &mut bb, Budget::default());
    bb.status(&oref).clone()
}

#[test]
fn a_safe_program_is_discharged() {
    if !solver_available() {
        eprintln!("skipping: no Horn solver on PATH");
        return;
    }
    let status = run_chc(&safe_program());
    assert!(
        matches!(status, Status::Discharged { .. }),
        "assume(v0 >= 4) implies v0 > 3, so CHC should discharge; got {status:?}"
    );
}

#[test]
fn an_unsafe_program_is_not_discharged() {
    if !solver_available() {
        eprintln!("skipping: no Horn solver on PATH");
        return;
    }
    // This is the direction that used to be wrong. The engine answered `unsat`
    // here -- error reachable -- and read it as a proof.
    let status = run_chc(&unsafe_program());
    assert!(
        !matches!(status, Status::Discharged { .. }),
        "v0 is unconstrained so v0 > 3 can fail; CHC must not discharge; got {status:?}"
    );
}

/// Same as `safe_program`, but the unconstrained value comes from an explicit
/// `Rvalue::Nondet` rather than an unwritten variable.
///
/// This is the case that exercised the fresh-symbol bug: `Nondet` encoded to a
/// name that was never bound in the script, and z3 responds to an unbound
/// symbol by discarding the clause mentioning it and printing a verdict anyway.
/// Since a discarded clause is a discarded constraint, the answer drifted
/// toward `sat` -- toward a spurious proof.
fn safe_program_with_nondet() -> Program {
    program_with(
        vec![
            Stmt::Assign(VarId(0), Rvalue::Nondet(Ty::Int, None)),
            Stmt::Assign(
                VarId(1),
                Rvalue::Bin(BinOp::Ge, Operand::Var(VarId(0)), Operand::int(4)),
            ),
            Stmt::Assume(Operand::Var(VarId(1))),
            Stmt::Assign(
                VarId(2),
                Rvalue::Bin(BinOp::Gt, Operand::Var(VarId(0)), Operand::int(3)),
            ),
            Stmt::Check(ObligationId(0)),
        ],
        3,
        Operand::Var(VarId(2)),
    )
}

fn unsafe_program_with_nondet() -> Program {
    program_with(
        vec![
            Stmt::Assign(VarId(0), Rvalue::Nondet(Ty::Int, None)),
            Stmt::Assign(
                VarId(1),
                Rvalue::Bin(BinOp::Gt, Operand::Var(VarId(0)), Operand::int(3)),
            ),
            Stmt::Check(ObligationId(0)),
        ],
        2,
        Operand::Var(VarId(1)),
    )
}

#[test]
fn a_nondet_input_does_not_break_the_script() {
    if !solver_available() {
        eprintln!("skipping: no Horn solver on PATH");
        return;
    }
    let status = run_chc(&safe_program_with_nondet());
    assert!(
        matches!(status, Status::Discharged { .. }),
        "a body with a nondet input must still produce a well-formed script; got {status:?}"
    );
}

#[test]
fn a_nondet_input_does_not_produce_a_spurious_proof() {
    if !solver_available() {
        eprintln!("skipping: no Horn solver on PATH");
        return;
    }
    let status = run_chc(&unsafe_program_with_nondet());
    assert!(
        !matches!(status, Status::Discharged { .. }),
        "nondet > 3 can fail, so this must not be discharged; got {status:?}"
    );
}

#[test]
fn the_engine_declares_and_publishes_as_over_approximating() {
    let engine = ChcEngine::new();
    assert_eq!(engine.direction(), Direction::Over);
    assert_eq!(engine.id(), EngineId("chc"));
}
