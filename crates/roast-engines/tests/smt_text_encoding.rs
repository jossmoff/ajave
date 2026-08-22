//! Tests for the shared SMT text encoder.
//!
//! `smt_text` is pure string production over a `Body` — no solver, no I/O — and
//! had no tests at all, which is how three separate defects survived in it:
//!
//! * every fresh symbol it minted (`Nondet`, array reads, allocations, LIA
//!   bitwise ops) went undeclared, and z3 answers a script with an unbound
//!   symbol by silently discarding the clause that mentions it;
//! * fresh names came from a process-global `AtomicU64`, so the emitted text
//!   depended on how many bodies had been encoded earlier;
//! * assignment substituted rendered text into the variable map, so a block of
//!   n statements each mentioning a variable twice produced O(2^n) output.
//!
//! Each has a test below.

use std::collections::HashSet;

use roast_engines::smt_text::{self, BitvectorTheory, FreshPool, LiaTheory};
use roast_ir::*;

// ---------------------------------------------------------------------------
// Builders
// ---------------------------------------------------------------------------

fn key() -> MethodKey {
    MethodKey {
        class: "T".into(),
        name: "t".into(),
        desc: "()V".into(),
    }
}

/// A single-block body with the given statements and an int var per slot.
fn body_with(stmts: Vec<Stmt>, n_vars: usize, obligations: Vec<Obligation>) -> Body {
    Body {
        key: key(),
        entry: BlockId(0),
        blocks: vec![Block {
            id: BlockId(0),
            bytecode_offset: 0,
            stmts,
            term: Terminator::Return(None),
            exceptional: vec![],
        }],
        vars: (0..n_vars)
            .map(|i| VarInfo {
                kind: VarKind::Local(i as u16),
                ty: Ty::Int,
            })
            .collect(),
        obligations,
    }
}

fn v(i: u32) -> Operand {
    Operand::Var(VarId(i))
}

/// Collect everything the walk emits, flattened to text.
#[derive(Default)]
struct Collect {
    transitions: Vec<String>,
    errors: Vec<String>,
    fresh_seen: Vec<String>,
}

impl smt_text::ClauseSink for Collect {
    fn transition(&mut self, t: smt_text::Transition<'_>) {
        let mut parts: Vec<String> = t.bindings.to_vec();
        parts.extend_from_slice(t.conds);
        parts.extend(t.var_exprs.iter().cloned());
        self.transitions.push(parts.join(" "));
        self.fresh_seen
            .extend(t.fresh.iter().map(|(n, _)| n.clone()));
    }
    fn error(&mut self, e: smt_text::ErrorSite<'_>) {
        let mut parts: Vec<String> = e.bindings.to_vec();
        parts.extend_from_slice(e.conds);
        self.errors.push(parts.join(" "));
        self.fresh_seen
            .extend(e.fresh.iter().map(|(n, _)| n.clone()));
    }
}

fn walk_bv(body: &Body, obs: &[ObligationId]) -> (Collect, FreshPool) {
    let set: HashSet<ObligationId> = obs.iter().copied().collect();
    let mut fresh = FreshPool::new("t_");
    let mut sink = Collect::default();
    smt_text::walk_body(body, &BitvectorTheory, &set, &mut fresh, &mut sink);
    (sink, fresh)
}

// ---------------------------------------------------------------------------
// Fresh symbols must be reported so the caller can bind them
// ---------------------------------------------------------------------------

#[test]
fn nondet_produces_a_reported_fresh_symbol() {
    let body = body_with(
        vec![Stmt::Assign(VarId(0), Rvalue::Nondet(Ty::Int, None))],
        1,
        vec![],
    );
    let (sink, fresh) = walk_bv(&body, &[]);

    assert_eq!(fresh.issued().len(), 1, "nondet mints exactly one symbol");
    let (name, width) = &fresh.issued()[0];
    assert_eq!(*width, 32);
    assert!(
        sink.transitions.iter().any(|t| t.contains(name.as_str())),
        "the symbol must actually appear in the emitted text"
    );
}

#[test]
fn a_long_nondet_is_reported_as_64_bits() {
    let body = Body {
        vars: vec![VarInfo {
            kind: VarKind::Local(0),
            ty: Ty::Long,
        }],
        ..body_with(
            vec![Stmt::Assign(VarId(0), Rvalue::Nondet(Ty::Long, None))],
            1,
            vec![],
        )
    };
    let (_, fresh) = walk_bv(&body, &[]);
    assert_eq!(fresh.issued()[0].1, 64);
}

#[test]
fn unmodelled_rvalues_produce_fresh_symbols() {
    // Array reads, allocations and field reads all fall through to havoc. Each
    // must be reported, not quietly emitted as an unbound name.
    for rv in [
        Rvalue::ArrayLoad {
            arr: v(0),
            idx: Operand::int(0),
        },
        Rvalue::ArrayLength(v(0)),
        Rvalue::New("java/lang/Object".into()),
        Rvalue::GetStatic(FieldKey {
            class: "T".into(),
            name: "f".into(),
            desc: "I".into(),
        }),
    ] {
        let body = body_with(vec![Stmt::Assign(VarId(0), rv.clone())], 1, vec![]);
        let (_, fresh) = walk_bv(&body, &[]);
        assert!(
            !fresh.issued().is_empty(),
            "{rv:?} should have minted a fresh symbol"
        );
        assert!(!smt_text::is_precise(&BitvectorTheory, &rv), "{rv:?}");
    }
}

#[test]
fn lia_havocs_bitwise_ops_and_says_so() {
    // LIA cannot express `&`. The encoder havocs it, and `is_precise` has to
    // agree — a guard that thought this was exact would let a proving engine
    // trust a result over a body whose semantics were dropped.
    let rv = Rvalue::Bin(BinOp::And, v(0), v(1));
    let theory = LiaTheory::new("p_");
    assert!(!smt_text::is_precise(&theory, &rv));

    let body = body_with(vec![Stmt::Assign(VarId(2), rv)], 3, vec![]);
    let set = HashSet::new();
    let mut fresh = FreshPool::new("p_");
    let mut sink = Collect::default();
    smt_text::walk_body(&body, &theory, &set, &mut fresh, &mut sink);
    assert!(
        !fresh.issued().is_empty(),
        "a LIA bitwise op must mint a reported symbol"
    );
}

#[test]
fn bitvector_theory_expresses_bitwise_ops_exactly() {
    let rv = Rvalue::Bin(BinOp::And, v(0), v(1));
    assert!(smt_text::is_precise(&BitvectorTheory, &rv));
}

#[test]
fn arithmetic_is_precise_in_both_theories() {
    let rv = Rvalue::Bin(BinOp::Add, v(0), v(1));
    assert!(smt_text::is_precise(&BitvectorTheory, &rv));
    assert!(smt_text::is_precise(&LiaTheory::new("p_"), &rv));
}

// ---------------------------------------------------------------------------
// Determinism
// ---------------------------------------------------------------------------

#[test]
fn encoding_the_same_body_twice_gives_identical_text() {
    // Fresh names used to come from a process-global counter, so the text
    // depended on how much had been encoded before it.
    let body = body_with(
        vec![
            Stmt::Assign(VarId(0), Rvalue::Nondet(Ty::Int, None)),
            Stmt::Assign(VarId(1), Rvalue::Nondet(Ty::Int, None)),
        ],
        2,
        vec![],
    );
    let (first, _) = walk_bv(&body, &[]);
    // Encode something else in between, to move any shared counter along.
    let _ = walk_bv(
        &body_with(
            vec![Stmt::Assign(VarId(0), Rvalue::Nondet(Ty::Int, None))],
            1,
            vec![],
        ),
        &[],
    );
    let (second, _) = walk_bv(&body, &[]);

    assert_eq!(first.transitions, second.transitions);
}

// ---------------------------------------------------------------------------
// Output size stays linear in statements
// ---------------------------------------------------------------------------

#[test]
fn chained_assignments_do_not_blow_up_the_output() {
    // `x = x + x` repeated. Under text substitution each statement doubled the
    // rendered size of x, so the output grew as O(2^n). Measuring the *growth
    // ratio* rather than an absolute size is what actually separates linear
    // from exponential: doubling the statement count should roughly double the
    // output, not square it.
    let size_for = |n: usize| -> usize {
        let stmts: Vec<Stmt> = (0..n)
            .map(|_| Stmt::Assign(VarId(0), Rvalue::Bin(BinOp::Add, v(0), v(0))))
            .collect();
        let (sink, _) = walk_bv(&body_with(stmts, 1, vec![]), &[]);
        sink.transitions.iter().map(|t| t.len()).sum()
    };

    let small = size_for(10);
    let large = size_for(20);
    let ratio = large as f64 / small as f64;
    assert!(
        ratio < 3.0,
        "doubling statements grew output {ratio:.1}x ({small} -> {large} bytes); \
         anything near 2x is linear, an exponential encoder would be far larger"
    );

    // And the absolute size stays sane: substitution would have produced
    // roughly 2^20 nodes here.
    assert!(large < 4096, "20 statements produced {large} bytes");
}

#[test]
fn a_trivial_assignment_is_not_given_a_needless_name() {
    // `v1 = v0` should just alias, not mint a temporary.
    let body = body_with(vec![Stmt::Assign(VarId(1), Rvalue::Use(v(0)))], 2, vec![]);
    let (_, fresh) = walk_bv(&body, &[]);
    assert!(fresh.issued().is_empty());
}

// ---------------------------------------------------------------------------
// Structure of what the walk reports
// ---------------------------------------------------------------------------

#[test]
fn a_check_becomes_an_error_site_only_when_selected() {
    let ob = Obligation {
        id: ObligationId(0),
        kind: ObligationKind::Assertion,
        cond: v(0),
        bytecode_offset: 0,
        line: None,
        guarded: false,
    };
    let body = body_with(vec![Stmt::Check(ObligationId(0))], 1, vec![ob]);

    let (selected, _) = walk_bv(&body, &[ObligationId(0)]);
    assert_eq!(selected.errors.len(), 1);

    let (unselected, _) = walk_bv(&body, &[]);
    assert!(unselected.errors.is_empty());
}

#[test]
fn assume_becomes_a_path_condition_on_the_outgoing_edge() {
    let body = body_with(vec![Stmt::Assume(v(0))], 1, vec![]);
    let (sink, _) = walk_bv(&body, &[]);
    assert_eq!(sink.transitions.len(), 1);
    assert!(
        sink.transitions[0].contains("not (= v0"),
        "expected a nonzero constraint, got: {}",
        sink.transitions[0]
    );
}

#[test]
fn a_branch_emits_both_arms_with_opposite_guards() {
    let body = Body {
        blocks: vec![
            Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![],
                term: Terminator::Branch {
                    cond: v(0),
                    then_: BlockId(1),
                    else_: BlockId(2),
                },
                exceptional: vec![],
            },
            Block {
                id: BlockId(1),
                bytecode_offset: 0,
                stmts: vec![],
                term: Terminator::Return(None),
                exceptional: vec![],
            },
            Block {
                id: BlockId(2),
                bytecode_offset: 0,
                stmts: vec![],
                term: Terminator::Return(None),
                exceptional: vec![],
            },
        ],
        ..body_with(vec![], 1, vec![])
    };
    let (sink, _) = walk_bv(&body, &[]);
    // Two arms from bb0, plus one leaving-edge each from bb1 and bb2.
    assert_eq!(sink.transitions.len(), 4);
    assert!(sink.transitions[0].contains("not (= v0"));
    assert!(sink.transitions[1].contains("(= v0"));
}

#[test]
fn a_returning_block_still_reports_its_edge() {
    // CHC used to drop Return and Halt silently while the LIA encoder emitted a
    // clause for them. The walk reports the edge with `to: None` and lets each
    // sink decide, so the two cannot disagree by accident again.
    let body = body_with(vec![], 1, vec![]);
    let (sink, _) = walk_bv(&body, &[]);
    assert_eq!(sink.transitions.len(), 1);
}
