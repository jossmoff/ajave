//! Per-pass tests, with one case per exclusion in `dce::removable`.
//!
//! Those exclusions are the safety argument, so each gets a test that fails if
//! the exclusion is dropped. A test that only checks "the optimiser removes
//! things" would pass with every one of them removed.

use super::*;
use ajave_ir::*;

fn key() -> MethodKey {
    MethodKey { class: "Main".into(), name: "main".into(), desc: "()V".into() }
}

fn var(kind: VarKind) -> VarInfo {
    VarInfo { kind, ty: Ty::Int }
}

/// One block, `nstack` stack temporaries after `nlocal` locals.
fn body(stmts: Vec<Stmt>, nlocal: usize, nstack: usize, term: Terminator) -> Body {
    let mut vars: Vec<VarInfo> = (0..nlocal).map(|i| var(VarKind::Local(i as u16))).collect();
    vars.extend((0..nstack).map(|i| var(VarKind::Stack(i as u16))));
    Body {
        key: key(),
        entry: BlockId(0),
        vars,
        obligations: vec![],
        blocks: vec![Block {
            id: BlockId(0),
            bytecode_offset: 0,
            stmts,
            term,
            exceptional: vec![],
        }],
        is_static: true,
    }
}

fn opt(mut b: Body) -> (Body, Stats) {
    let s = reduce_body(&mut b, Level::Optimise);
    assert!(validate(&b).is_ok(), "invalid after reduction: {:?}", validate(&b));
    (b, s)
}

fn stmts(b: &Body) -> &[Stmt] {
    &b.blocks[0].stmts
}

// ---------------------------------------------------------------------------
// What it is for
// ---------------------------------------------------------------------------

/// The shape the lifter actually emits: the operand stack materialised into
/// copies. Measured at 35-47% of all assignments across the corpus.
#[test]
fn the_copy_chain_the_lifter_emits_collapses() {
    // v3 = v0; v4 = v3; v5 = v4; return v5   (v0 local, v3..v5 stack)
    let (v0, v3, v4, v5) = (VarId(0), VarId(1), VarId(2), VarId(3));
    let b = body(
        vec![
            Stmt::Assign(v3, Rvalue::Use(Operand::Var(v0))),
            Stmt::Assign(v4, Rvalue::Use(Operand::Var(v3))),
            Stmt::Assign(v5, Rvalue::Use(Operand::Var(v4))),
        ],
        1,
        3,
        Terminator::Return(Some(Operand::Var(v5))),
    );
    let (b, stats) = opt(b);
    assert!(stmts(&b).is_empty(), "the whole chain is dead once reads point at v0");
    assert!(
        matches!(b.blocks[0].term, Terminator::Return(Some(Operand::Var(v))) if b.vars[v.0 as usize].kind == VarKind::Local(0)),
        "the return must read the original local, not a removed copy"
    );
    assert!(stats.vars_removed >= 3, "the three stack temporaries go: {stats:?}");
}

// ---------------------------------------------------------------------------
// One test per exclusion. Each fails if its exclusion is dropped.
// ---------------------------------------------------------------------------

/// A witness is a *sequence* replayed on a real JVM, so removing an unread
/// nondet shifts every later value and a witness that reproduced stops
/// reproducing.
#[test]
fn an_unread_nondet_is_never_removed() {
    let (a, b_) = (VarId(0), VarId(1));
    let src = body(
        vec![
            Stmt::Assign(a, Rvalue::Nondet(Ty::Int, None)),
            Stmt::Assign(b_, Rvalue::Nondet(Ty::Int, None)),
        ],
        0,
        2,
        Terminator::Return(Some(Operand::Var(b_))),
    );
    let (out, _) = opt(src);
    assert_eq!(
        stmts(&out).len(),
        2,
        "the unread first nondet must stay; dropping it renumbers the witness sequence"
    );
}

/// A call writes fields, starts threads and throws, none of which is visible in
/// its result.
#[test]
fn an_unread_opaque_call_is_never_removed() {
    let r = VarId(0);
    let src = body(
        vec![Stmt::Assign(
            r,
            Rvalue::Call {
                target: MethodKey {
                    class: "Helper".into(),
                    name: "mutate".into(),
                    desc: "()I".into(),
                },
                args: vec![],
                is_virtual: false,
            },
        )],
        0,
        1,
        Terminator::Return(None),
    );
    let (out, _) = opt(src);
    assert_eq!(stmts(&out).len(), 1, "an opaque call has effects beyond its result");
}

/// `new int[n]` throws for n < 0, and object identity is observable through
/// reference equality.
#[test]
fn an_unread_allocation_is_never_removed() {
    let (n, a) = (VarId(0), VarId(1));
    let src = body(
        vec![
            Stmt::Assign(n, Rvalue::Nondet(Ty::Int, None)),
            Stmt::Assign(a, Rvalue::NewArray { elem: "I".into(), len: Operand::Var(n) }),
        ],
        0,
        2,
        Terminator::Return(None),
    );
    let (out, _) = opt(src);
    assert_eq!(
        stmts(&out).len(),
        2,
        "allocation is observable through NegativeArraySize and reference identity"
    );
}

/// The value an assertion tests is read by the *obligation*, not by the
/// `Check` statement. An optimiser that misses that deletes what the assertion
/// is about.
#[test]
fn a_value_read_only_by_an_obligation_is_never_removed() {
    let (x, c) = (VarId(0), VarId(1));
    let mut src = body(
        vec![
            Stmt::Assign(x, Rvalue::Nondet(Ty::Int, None)),
            Stmt::Assign(c, Rvalue::Bin(BinOp::Gt, Operand::Var(x), Operand::int(0))),
            Stmt::Check(ObligationId(0)),
        ],
        0,
        2,
        Terminator::Return(None),
    );
    src.obligations = vec![Obligation {
        id: ObligationId(0),
        kind: ObligationKind::Assertion,
        cond: Operand::Var(c),
        bytecode_offset: 0,
        line: None,
        guarded: false,
    }];
    let (out, _) = opt(src);
    assert!(
        stmts(&out).iter().any(|s| matches!(s, Stmt::Check(_))),
        "the Check is the product and must survive"
    );
    let cond = out.obligations[0].cond.clone();
    let Operand::Var(cv) = cond else { panic!("obligation condition lost its variable") };
    assert!(
        stmts(&out).iter().any(|s| matches!(s, Stmt::Assign(d, _) if *d == cv)),
        "the assignment computing the obligation's condition must survive"
    );
}

/// The concurrency engine cannot reconstruct a critical section that was
/// optimised away; the lifter discarded these once already and had to be fixed.
#[test]
fn monitors_are_never_removed() {
    let m = VarId(0);
    let src = body(
        vec![
            Stmt::Assign(m, Rvalue::New("java/lang/Object".into())),
            Stmt::MonitorEnter(Operand::Var(m)),
            Stmt::MonitorExit(Operand::Var(m)),
        ],
        0,
        1,
        Terminator::Return(None),
    );
    let (out, _) = opt(src);
    assert_eq!(stmts(&out).len(), 3, "monitors and the object they lock must survive");
}

// ---------------------------------------------------------------------------
// Compaction's invariant
// ---------------------------------------------------------------------------

/// `find_param_var_indices` maps parameters by `VarKind::Local` slot and
/// `is_static` decides whether slot 0 is `this`. Renumbering that shifted a
/// slot would bind every argument one position out -- the same class of defect
/// as the obligation-id collision.
#[test]
fn compaction_preserves_local_slots() {
    let (p0, p1, t) = (VarId(0), VarId(1), VarId(2));
    let src = body(
        vec![
            // t is dead; the two locals are parameters and must survive.
            Stmt::Assign(t, Rvalue::Bin(BinOp::Add, Operand::Var(p0), Operand::int(1))),
        ],
        2,
        1,
        Terminator::Return(Some(Operand::Var(p1))),
    );
    let (out, stats) = opt(src);
    let slots: Vec<VarKind> = out.vars.iter().map(|v| v.kind).collect();
    assert_eq!(
        slots,
        vec![VarKind::Local(0), VarKind::Local(1)],
        "both parameter slots survive, in order: {slots:?}"
    );
    assert_eq!(stats.vars_removed, 1, "only the dead temporary goes");
}

/// Normalise must not remove anything: it is always on, so it has to be the
/// level that cannot lose a statement an engine depends on.
#[test]
fn normalise_rewrites_but_never_removes() {
    let (v0, v1, v2) = (VarId(0), VarId(1), VarId(2));
    let mut b = body(
        vec![
            Stmt::Assign(v1, Rvalue::Use(Operand::Var(v0))),
            Stmt::Assign(v2, Rvalue::Bin(BinOp::Add, Operand::Var(v1), Operand::int(1))),
        ],
        1,
        2,
        Terminator::Return(Some(Operand::Var(v2))),
    );
    let before = b.blocks[0].stmts.len();
    let vars_before = b.vars.len();
    reduce_body(&mut b, Level::Normalise);
    assert_eq!(b.blocks[0].stmts.len(), before, "Normalise removes no statements");
    assert_eq!(b.vars.len(), vars_before, "Normalise removes no variables");
    assert!(
        matches!(&b.blocks[0].stmts[1], Stmt::Assign(_, Rvalue::Bin(_, Operand::Var(v), _)) if *v == v0),
        "but it does rewrite the read through the copy"
    );
    assert!(validate(&b).is_ok());
}

/// A pass that reports "changed" without changing anything would spin; the cap
/// bounds that bug rather than tuning a result.
#[test]
fn reduction_reaches_a_fixpoint() {
    let (v0, v1, v2, v3) = (VarId(0), VarId(1), VarId(2), VarId(3));
    let mut b = body(
        vec![
            Stmt::Assign(v1, Rvalue::Use(Operand::Var(v0))),
            Stmt::Assign(v2, Rvalue::Use(Operand::Var(v1))),
            Stmt::Assign(v3, Rvalue::Use(Operand::Var(v2))),
        ],
        1,
        3,
        Terminator::Return(Some(Operand::Var(v3))),
    );
    reduce_body(&mut b, Level::Optimise);
    let again = reduce_body(&mut b.clone(), Level::Optimise);
    assert_eq!(
        again,
        Stats { bodies: 0, ..Default::default() },
        "a second reduction of an already-reduced body must change nothing: {again:?}"
    );
}
