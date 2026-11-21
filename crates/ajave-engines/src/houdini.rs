//! Candidate-elimination invariant synthesis.
//!
//! Houdini (Flanagan & Leino, *Houdini, an Annotation Assistant for ESC/Java*,
//! FME 2001). Start from a map that assigns **every** candidate predicate to
//! **every** program point, then repeatedly delete any candidate that fails
//! initiation or preservation. What survives is inductive.
//!
//! # Why this and not a cleverer synthesiser
//!
//! Three properties, and the design in
//! `docs/proposals/invariant-synthesis.md` depends on all three.
//!
//! **Sound by construction.** The surviving map satisfies initiation and
//! preservation because that is the loop's termination condition. There is no
//! "trust the proposer" step: a bad candidate is deleted, never believed. That
//! is what makes it safe to feed this pool from speculative sources — a
//! learned proposer, a heuristic, another engine's guess — without any of them
//! being able to cause a wrong answer.
//!
//! **Terminates.** The assignment only ever shrinks, so there are at most
//! `|points| * |pool|` deletions.
//!
//! **Order-independent.** It computes the greatest inductive map inside the
//! candidate lattice, so the answer does not depend on which failure is found
//! first. `the_result_does_not_depend_on_the_order_of_the_pool` is that
//! theorem as a test rather than as a comment, which `CLAUDE.md` asks for.
//!
//! # And it is the checker, iterated
//!
//! The elimination step is exactly `invariant_check`'s initiation and
//! preservation obligations. That is the point: building this builds the
//! map certifier, and its output is `InvStatus::Inductive` by construction
//! rather than by a separate pass that has to be trusted.
//!
//! # The honest weakness
//!
//! Houdini finds only invariants expressible as a **conjunction of
//! candidates**. It will not invent `i*i <= n`. That is the price of
//! soundness-by-construction, and it is why the pool is where the judgement
//! goes: `candidates` draws on what the other engines already computed rather
//! than on syntax templates alone.
//!
//! Every limit of the checker applies: the shared LIA encoder, no floats, and
//! `Expr::Length` not yet renderable. A candidate the encoder cannot state is
//! dropped from the pool at the start rather than silently treated as `true`.

use std::collections::BTreeMap;

use ajave_core::artifact::ProgramPoint;
use ajave_core::term::{Expr, Op};
use ajave_ir::{BlockId, Body};
use log::debug;

use crate::interpolation::encode_body_lia;
use crate::invariant_check::{is_unsat, render};

/// Default solver queries one synthesis run may spend.
///
/// A fitted constant, and bounded for the reason `Progress::Suspended`
/// promises: a run without `--timeout` has no deadline to stop it. The
/// elimination loop is `O(|edges| * |pool|)` queries per round and rounds are
/// bounded by deletions, so the product is what needs a cap rather than any
/// one factor.
///
/// Passed as an argument rather than read from the environment inside this
/// function. A process-global `OnceLock` would make the budget untestable:
/// the first test to set it fixes it for every later one in the same process,
/// which is exactly what happened and silently made four passing tests fail
/// on an unrelated assertion. The engine that calls this reads the override.
pub const DEFAULT_MAX_QUERIES: usize = 4000;

/// The surviving inductive map, as point -> conjunction.
///
/// Empty when nothing survived, which is a legitimate answer: the empty map is
/// inductive and says nothing. A caller must not read an absent point as a
/// contradiction — see `InvariantMap`'s contract.
pub struct Synthesised {
    pub entries: BTreeMap<ProgramPoint, Expr>,
    /// Solver queries spent, so a caller can attribute cost.
    pub queries: usize,
    /// Whether the loop reached a fixpoint rather than running out of budget.
    ///
    /// **Load-bearing for soundness.** A map abandoned mid-elimination has
    /// *not* been shown inductive: a candidate that had not yet been tested
    /// may be false. A caller must publish an unfinished map as
    /// `InvStatus::Candidate` and never as `Inductive`.
    pub converged: bool,
}

/// Run candidate elimination over `pool`.
///
/// `points` restricts where candidates are placed; **empty means every block**,
/// which is the correct default and usually the only one that works.
///
/// # Why not just loop headers
///
/// An invariant at a loop header is what lets a consumer stop unrolling, so
/// annotating headers alone looks like the efficient choice. It is not, and
/// the reason is worth stating because it cost a round of debugging.
/// Preservation reasons from the assertion at an edge's *source*, and an
/// unannotated source carries no claim — so for `x := 0; while (x < n) x++;`
/// with a candidate only at the header, the back edge from the body asks
/// "assuming nothing, does `x + 1 >= 0`?", which is false for `x = -5`. The
/// candidate is deleted and the loop finds nothing.
///
/// With every block annotated the same candidate survives: the body inherits
/// `0 <= x` from the header, and `0 <= x` implies `0 <= x + 1`. This is why
/// the original presentation annotates every program point, and the cost is
/// what `budget` is for.
pub fn synthesise(
    body: &Body,
    pool: &[Expr],
    points: &[BlockId],
    solver: &str,
    budget: usize,
) -> Synthesised {
    let enc = encode_body_lia(body, &[], "");
    let mut queries = 0usize;

    // Drop what the encoder cannot state, once, rather than discovering it per
    // query. A candidate we cannot render is not `true` — it is unusable, and
    // keeping it would make every preservation check return Inconclusive and
    // delete the candidate anyway, at one solver call each.
    let usable: Vec<(usize, &Expr, String, String)> = pool
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            let pre = render(c, false)?;
            let post = render(c, true)?;
            Some((i, c, pre, post))
        })
        .collect();

    let mut blocks: Vec<BlockId> = if points.is_empty() {
        body.blocks.iter().map(|b| b.id).collect()
    } else {
        points.to_vec()
    };
    if !blocks.contains(&body.entry) {
        blocks.push(body.entry);
    }
    blocks.sort_by_key(|b| b.0);
    blocks.dedup();

    // alive[block] = indices into `usable` still assigned there.
    let mut alive: BTreeMap<u32, Vec<usize>> = blocks
        .iter()
        .map(|b| (b.0, (0..usable.len()).collect()))
        .collect();

    let conj_at = |alive: &BTreeMap<u32, Vec<usize>>, b: u32, post: bool| -> Option<String> {
        let idxs = alive.get(&b)?;
        if idxs.is_empty() {
            return None;
        }
        let parts: Vec<&str> = idxs
            .iter()
            .map(|i| {
                let (_, _, pre, pst) = &usable[*i];
                if post {
                    pst.as_str()
                } else {
                    pre.as_str()
                }
            })
            .collect();
        Some(if parts.len() == 1 {
            parts[0].to_string()
        } else {
            format!("(and {})", parts.join(" "))
        })
    };

    let mut converged = false;
    'outer: loop {
        let mut deleted = false;

        // Initiation: a candidate at the entry must be valid, because a
        // method's entry state is its unconstrained parameters.
        if let Some(idxs) = alive.get(&body.entry.0).cloned() {
            let mut keep = Vec::new();
            for i in idxs {
                if queries >= budget {
                    break 'outer;
                }
                let (_, _, pre, _) = &usable[i];
                let script = format!("{}\n(assert (not {pre}))\n(check-sat)\n", enc.declarations);
                queries += 1;
                match is_unsat(solver, &script) {
                    Some(true) => keep.push(i),
                    // SAT means a state violating it on entry; `unknown` means
                    // we cannot show it holds. Both delete, because a
                    // candidate we cannot establish must not survive into a
                    // map we will call inductive.
                    _ => deleted = true,
                }
            }
            alive.insert(body.entry.0, keep);
        }

        // Preservation, per CFG edge.
        for (from, to, clause) in &enc.edge_clauses {
            let Some(to) = to else { continue };
            if !alive.contains_key(&to.0) {
                continue;
            }
            // An unannotated source carries no claim, which reads as `true`.
            let pre = conj_at(&alive, from.0, false).unwrap_or_else(|| "true".to_string());
            let idxs = alive.get(&to.0).cloned().unwrap_or_default();
            let mut keep = Vec::new();
            for i in idxs {
                if queries >= budget {
                    break 'outer;
                }
                let (_, _, _, post) = &usable[i];
                let script = format!(
                    "{}\n(assert {pre})\n(assert {clause})\n(assert (not {post}))\n(check-sat)\n",
                    enc.declarations
                );
                queries += 1;
                match is_unsat(solver, &script) {
                    Some(true) => keep.push(i),
                    _ => deleted = true,
                }
            }
            alive.insert(to.0, keep);
        }

        if !deleted {
            converged = true;
            break;
        }
    }

    let mut entries: BTreeMap<ProgramPoint, Expr> = BTreeMap::new();
    for (b, idxs) in &alive {
        if idxs.is_empty() {
            continue;
        }
        // Canonical conjunct order, by rendered form.
        //
        // The surviving *set* is order-independent -- that is Houdini's
        // theorem -- but folding it in pool order would make the published
        // formula depend on how the pool happened to be assembled. A claim
        // whose shape varies between runs is the determinism defect
        // `CLAUDE.md` names: it makes two identical analyses produce
        // artifacts that compare unequal, so a consumer deduplicating or
        // intersecting them gets a different answer for no reason.
        let mut idxs: Vec<usize> = idxs.clone();
        idxs.sort_by(|a, b| usable[*a].2.cmp(&usable[*b].2));
        let mut it = idxs.iter().map(|i| usable[*i].1.clone());
        let first = it.next().expect("non-empty checked above");
        let formula = it.fold(first, |acc, c| Expr::bin(Op::And, acc, c));
        entries.insert(
            ProgramPoint {
                method: body.key.clone(),
                block: BlockId(*b),
                index: 0,
            },
            formula,
        );
    }

    debug!(
        "houdini: {} points={} pool={} usable={} survived={} queries={} converged={}",
        body.key,
        blocks.len(),
        pool.len(),
        usable.len(),
        entries.len(),
        queries,
        converged
    );

    Synthesised {
        entries,
        queries,
        converged,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{
        Block, Const, MethodKey, Obligation, ObligationId, ObligationKind, Operand, Rvalue, Stmt,
        Terminator, Ty, VarId, VarInfo, VarKind,
    };

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "m".into(),
            desc: "()V".into(),
        }
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

    /// `x := 0; while (x < n) { x++; }`
    ///
    /// bb0: x := 0            -> bb1
    /// bb1: branch (x < n)    -> bb2 (body) / bb3 (exit)
    /// bb2: x := x + 1        -> bb1
    /// bb3: check, return
    ///
    /// v0 = x, v1 = n.
    fn counting_loop() -> Body {
        let lt = VarId(2);
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                VarInfo { kind: VarKind::Local(0), ty: Ty::Int },
                VarInfo { kind: VarKind::Local(1), ty: Ty::Int },
                VarInfo { kind: VarKind::Local(2), ty: Ty::Int },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(0)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![
                Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![Stmt::Assign(
                        VarId(0),
                        Rvalue::Use(Operand::Const(Const::Int(0))),
                    )],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(1),
                    bytecode_offset: 1,
                    stmts: vec![Stmt::Assign(
                        lt,
                        Rvalue::Bin(
                            ajave_ir::BinOp::Lt,
                            Operand::Var(VarId(0)),
                            Operand::Var(VarId(1)),
                        ),
                    )],
                    term: Terminator::Branch {
                        cond: Operand::Var(lt),
                        then_: BlockId(2),
                        else_: BlockId(3),
                    },
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(2),
                    bytecode_offset: 2,
                    stmts: vec![Stmt::Assign(
                        VarId(0),
                        Rvalue::Bin(
                            ajave_ir::BinOp::Add,
                            Operand::Var(VarId(0)),
                            Operand::Const(Const::Int(1)),
                        ),
                    )],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(3),
                    bytecode_offset: 3,
                    stmts: vec![Stmt::Check(ObligationId(0))],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                },
            ],
        }
    }

    fn x() -> Expr { Expr::Var(VarId(0)) }
    fn n() -> Expr { Expr::Var(VarId(1)) }

    /// The plan's fixture. `0 <= x` survives (x starts at 0 and only
    /// increments); `false` and `x <= -1` cannot.
    #[test]
    fn elimination_keeps_what_is_inductive_and_drops_what_is_not() {
        let Some(s) = solver() else { return };
        let pool = vec![
            Expr::bin(Op::Le, Expr::Int(0), x()),
            Expr::bin(Op::Le, x(), Expr::Int(-1)),
            Expr::Bool(false),
        ];
        let r = synthesise(&counting_loop(), &pool, &[], s, DEFAULT_MAX_QUERIES);
        assert!(r.converged, "must reach a fixpoint on a four-block body");
        let at_header = r
            .entries
            .iter()
            .find(|(p, _)| p.block == BlockId(1))
            .map(|(_, f)| f.to_string());
        assert_eq!(
            at_header.as_deref(),
            Some("(0 <= v0)"),
            "only the true lower bound may survive at the loop header"
        );
    }

    /// Houdini's central theorem, as a test rather than a comment: the result
    /// is the greatest inductive map in the candidate lattice, so it cannot
    /// depend on which failing candidate is found first.
    #[test]
    fn the_result_does_not_depend_on_the_order_of_the_pool() {
        let Some(s) = solver() else { return };
        let a = Expr::bin(Op::Le, Expr::Int(0), x());
        let b = Expr::Bool(false);
        let c = Expr::bin(Op::Le, x(), Expr::Int(-1));
        let d = Expr::bin(Op::Le, Expr::Int(0), n());

        let orders = vec![
            vec![a.clone(), b.clone(), c.clone(), d.clone()],
            vec![d.clone(), c.clone(), b.clone(), a.clone()],
            vec![b.clone(), d.clone(), a.clone(), c.clone()],
        ];
        let mut results = Vec::new();
        for pool in orders {
            let r = synthesise(&counting_loop(), &pool, &[], s, DEFAULT_MAX_QUERIES);
            assert!(r.converged);
            let mut got: Vec<String> = r
                .entries
                .iter()
                .map(|(p, f)| format!("bb{}: {f}", p.block.0))
                .collect();
            got.sort();
            results.push(got);
        }
        // Compared as rendered formulas, not as sets: canonical conjunct
        // ordering means the *artifact* is order-independent too, which is
        // what a consumer actually sees.
        assert_eq!(results[0], results[1], "pool order changed the answer");
        assert_eq!(results[1], results[2], "pool order changed the answer");
    }

    /// `false` is never inductive, and a pool of nothing but falsehoods must
    /// yield the empty map rather than a map asserting a contradiction.
    #[test]
    fn a_pool_of_falsehoods_yields_the_empty_map() {
        let Some(s) = solver() else { return };
        let pool = vec![Expr::Bool(false), Expr::bin(Op::Le, x(), Expr::Int(-5))];
        let r = synthesise(&counting_loop(), &pool, &[], s, DEFAULT_MAX_QUERIES);
        assert!(r.converged);
        assert!(
            r.entries.is_empty(),
            "nothing survived, so the map must say nothing: {:?}",
            r.entries.values().map(|f| f.to_string()).collect::<Vec<_>>()
        );
    }

    /// An unfinished run must not be read as inductive. `converged` is the
    /// only thing that licenses promotion, and a budget of one query cannot
    /// have tested the pool.
    /// An unfinished run must say so. `converged` is the only thing that
    /// licenses promotion to `Inductive`: a map abandoned mid-elimination may
    /// contain a candidate that was never tested and is false.
    #[test]
    fn running_out_of_budget_is_reported_rather_than_hidden() {
        let Some(s) = solver() else { return };
        let pool = vec![Expr::bin(Op::Le, Expr::Int(0), x()), Expr::Bool(false)];
        let r = synthesise(&counting_loop(), &pool, &[], s, 1);
        assert!(!r.converged, "a budget of one query cannot have tested a pool of two");
        assert!(r.queries <= 1, "budget was not respected: {}", r.queries);
    }

    /// A candidate the LIA encoder cannot state is dropped from the pool, not
    /// treated as `true`. `Expr::Length` is the live case: expressible in the
    /// vocabulary, not yet renderable.
    #[test]
    fn an_unrenderable_candidate_is_dropped_from_the_pool() {
        let Some(s) = solver() else { return };
        let pool = vec![
            Expr::bin(Op::Le, Expr::Int(0), x()),
            Expr::bin(Op::Gt, Expr::length(n()), Expr::Int(0)),
        ];
        let r = synthesise(&counting_loop(), &pool, &[], s, DEFAULT_MAX_QUERIES);
        assert!(r.converged);
        let at_header = r
            .entries
            .iter()
            .find(|(p, _)| p.block == BlockId(1))
            .map(|(_, f)| f.to_string());
        assert_eq!(
            at_header.as_deref(),
            Some("(0 <= v0)"),
            "the length candidate must be dropped, not conjoined as true"
        );
    }
}
