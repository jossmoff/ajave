//! The IR's control-flow edges.
//!
//! Which statements can throw, when an exceptional edge exists, and what a
//! terminator leads to. This is a statement about the IR's semantics, not about
//! any analysis: it lived in `cpa.rs` for a while because the fixpoint is its
//! only caller, which filed 90 lines of JVM exception semantics under a name
//! that described neither.
//!
//! Three separate wrong answers came from edges here, and each one is now a
//! test in this module rather than only a comment.

use crate::artifact::ProgramPoint;
use ajave_ir::{Edge, Program, Stmt, Terminator};

/// All outgoing edges from a point, paired with the point they lead to.
pub fn successors(prog: &Program, at: &ProgramPoint) -> Vec<(Edge, ProgramPoint)> {
    let Some(body) = prog.body(&at.method) else {
        return Vec::new();
    };
    let block = body.block(at.block);

    let point_at = |b: ajave_ir::BlockId| ProgramPoint {
        method: at.method.clone(),
        block: b,
        index: 0,
    };

    // Only `Stmt::Check` can throw in the IR — every implicit exception
    // (DivByZero, NullDeref, ArrayBounds, …) is modelled as a Check.
    // Other statement kinds (Assign, Assume, PutStatic, …) are non-throwing
    // by construction. Emitting exceptional edges from non-Check positions
    // lets pre-assume states reach handlers, making provably-unreachable catch
    // blocks appear live to the interval AI.
    if at.index < block.stmts.len() {
        let next = ProgramPoint {
            method: at.method.clone(),
            block: at.block,
            index: at.index + 1,
        };
        let mut out = vec![(Edge::Stmt(at.block, at.index), next)];
        // A call can propagate any exception its callee raises, so a handler
        // guarding the call site is genuinely reachable. Omitting this edge
        // makes such a handler invisible to the analysis — and because a check
        // that is never visited is treated as vacuously safe, an obligation
        // inside the handler would be discharged without ever being examined.
        let throwing_call = matches!(
            block.stmts[at.index],
            Stmt::Assign(_, ajave_ir::Rvalue::Call { .. })
        );
        if matches!(block.stmts[at.index], Stmt::Check(_)) || throwing_call {
            out.extend(
                block
                    .exceptional
                    .iter()
                    .map(|e| (Edge::Term(at.block, None, e.target), point_at(e.target))),
            );
        }
        return out;
    }

    // At the terminator, only `Throw` can raise an exception in the IR.
    // All implicit exceptions (Check failures) already produced exceptional
    // edges at their statement positions above; including them again here
    // would reintroduce the spurious pre-assume states that the fix above
    // eliminates.
    let mut out: Vec<(Edge, ProgramPoint)> = if matches!(block.term, Terminator::Throw(_)) {
        block
            .exceptional
            .iter()
            .map(|e| (Edge::Term(at.block, None, e.target), point_at(e.target)))
            .collect()
    } else {
        Vec::new()
    };

    match &block.term {
        Terminator::Goto(t) => out.push((Edge::Term(at.block, None, *t), point_at(*t))),
        Terminator::Branch { then_, else_, .. } => {
            out.push((Edge::Term(at.block, Some(true), *then_), point_at(*then_)));
            out.push((Edge::Term(at.block, Some(false), *else_), point_at(*else_)));
        }
        Terminator::Switch { cases, default, .. } => {
            out.push((Edge::Term(at.block, None, *default), point_at(*default)));
            for (_, b) in cases {
                out.push((Edge::Term(at.block, None, *b), point_at(*b)));
            }
        }
        // No successors. `Diverge` is deliberately indistinguishable from an
        // exit *here* — it is the engines' job to notice they are below one and
        // decline to claim TRUE, via `Body::is_fully_lifted`.
        Terminator::Return(_)
        | Terminator::Throw(_)
        | Terminator::Halt
        | Terminator::Diverge(_) => {
            out.push((Edge::Exit(at.block), at.clone()));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{
        Block, BlockId, Body, Const, ExcEdge, MethodKey, ObligationId, Operand, Rvalue, VarId,
    };

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "main".into(),
            desc: "()V".into(),
        }
    }

    /// A one-method program whose entry block has the given statements,
    /// terminator and handlers.
    fn prog_with(stmts: Vec<Stmt>, term: Terminator, handlers: Vec<BlockId>) -> Program {
        let mut blocks = vec![Block {
            id: BlockId(0),
            bytecode_offset: 0,
            stmts,
            term,
            exceptional: handlers
                .iter()
                .map(|t| ExcEdge {
                    class: None,
                    target: *t,
                })
                .collect(),
        }];
        // Pad out enough blocks that every referenced target exists.
        for i in 1..6u32 {
            blocks.push(Block {
                id: BlockId(i),
                bytecode_offset: i as u16,
                stmts: vec![],
                term: Terminator::Return(None),
                exceptional: vec![],
            });
        }
        let mut prog = Program::default();
        prog.bodies.insert(
            mk(),
            Body {
                is_static: true,
                key: mk(),
                entry: BlockId(0),
                vars: vec![],
                obligations: vec![],
                blocks,
            },
        );
        prog.entry = Some(mk());
        prog
    }

    fn at(index: usize) -> ProgramPoint {
        ProgramPoint {
            method: mk(),
            block: BlockId(0),
            index,
        }
    }

    fn exceptional(edges: &[(Edge, ProgramPoint)]) -> usize {
        edges
            .iter()
            .filter(|(e, _)| matches!(e, Edge::Term(_, None, _)))
            .count()
    }

    /// Emitting exceptional edges from a non-`Check` position let pre-assume
    /// states reach handlers, which made provably-dead catch blocks look live
    /// to the interval AI.
    #[test]
    fn an_assign_has_only_a_fallthrough_edge() {
        let prog = prog_with(
            vec![Stmt::Assign(
                VarId(0),
                Rvalue::Use(Operand::Const(Const::Int(1))),
            )],
            Terminator::Return(None),
            vec![BlockId(1), BlockId(2)],
        );
        let out = successors(&prog, &at(0));
        assert_eq!(out.len(), 1, "no exceptional edges from an Assign");
        assert!(matches!(out[0].0, Edge::Stmt(BlockId(0), 0)));
        assert_eq!(out[0].1.index, 1, "falls through to the next statement");
    }

    #[test]
    fn a_check_emits_every_exceptional_edge() {
        let prog = prog_with(
            vec![Stmt::Check(ObligationId(0))],
            Terminator::Return(None),
            vec![BlockId(1), BlockId(2)],
        );
        let out = successors(&prog, &at(0));
        assert_eq!(out.len(), 3, "fallthrough plus both handlers");
        assert_eq!(exceptional(&out), 2);
    }

    /// A callee can propagate any exception it raises, so a handler guarding a
    /// call site is genuinely reachable. Omitting this edge made the handler
    /// invisible — and an obligation inside it was then discharged without
    /// ever being examined.
    #[test]
    fn a_call_emits_exceptional_edges_too() {
        let prog = prog_with(
            vec![Stmt::Assign(
                VarId(0),
                Rvalue::Call {
                    target: mk(),
                    args: vec![],
                    is_virtual: false,
                },
            )],
            Terminator::Return(None),
            vec![BlockId(1)],
        );
        let out = successors(&prog, &at(0));
        assert_eq!(exceptional(&out), 1, "a call can throw into the handler");
    }

    /// Implicit exceptions already produced their edges at the statement
    /// positions above. Re-emitting them at the terminator reintroduced the
    /// spurious pre-assume states that `an_assign_has_only_a_fallthrough_edge`
    /// exists to prevent.
    #[test]
    fn a_terminator_does_not_re_emit_check_handlers() {
        let prog = prog_with(
            vec![Stmt::Check(ObligationId(0))],
            Terminator::Goto(BlockId(3)),
            vec![BlockId(1), BlockId(2)],
        );
        let out = successors(&prog, &at(1)); // at the terminator
        assert_eq!(out.len(), 1, "only the goto edge");
        assert!(matches!(out[0].0, Edge::Term(BlockId(0), None, BlockId(3))));
    }

    #[test]
    fn a_throw_emits_its_handlers() {
        let prog = prog_with(
            vec![],
            Terminator::Throw(Operand::Var(VarId(0))),
            vec![BlockId(1), BlockId(2)],
        );
        let out = successors(&prog, &at(0));
        assert_eq!(exceptional(&out), 2, "throw is the one terminator that can");
    }

    #[test]
    fn a_branch_yields_both_sides_tagged() {
        let prog = prog_with(
            vec![],
            Terminator::Branch {
                cond: Operand::Const(Const::Int(1)),
                then_: BlockId(1),
                else_: BlockId(2),
            },
            vec![],
        );
        let out = successors(&prog, &at(0));
        assert_eq!(out.len(), 2);
        assert!(out
            .iter()
            .any(|(e, _)| matches!(e, Edge::Term(_, Some(true), BlockId(1)))));
        assert!(out
            .iter()
            .any(|(e, _)| matches!(e, Edge::Term(_, Some(false), BlockId(2)))));
    }

    #[test]
    fn a_switch_yields_the_default_and_every_case() {
        let prog = prog_with(
            vec![],
            Terminator::Switch {
                value: Operand::Const(Const::Int(0)),
                cases: vec![(1, BlockId(1)), (2, BlockId(2)), (3, BlockId(3))],
                default: BlockId(4),
            },
            vec![],
        );
        let out = successors(&prog, &at(0));
        assert_eq!(out.len(), 4, "three cases plus the default");
        assert!(out
            .iter()
            .any(|(e, _)| matches!(e, Edge::Term(_, None, BlockId(4)))));
    }

    /// `Diverge` marks an instruction we could not lift. It is deliberately
    /// indistinguishable from a return *here*: hiding it in the CFG would make
    /// the truncation invisible, so soundness rests on engines checking
    /// `Body::is_fully_lifted` instead. If this test ever fails because
    /// `Diverge` grew its own edge shape, that contract moved.
    #[test]
    fn diverge_is_indistinguishable_from_return() {
        let div = prog_with(vec![], Terminator::Diverge("unlifted".into()), vec![]);
        let ret = prog_with(vec![], Terminator::Return(None), vec![]);
        let d = successors(&div, &at(0));
        let r = successors(&ret, &at(0));
        assert_eq!(d.len(), 1);
        assert!(matches!(d[0].0, Edge::Exit(BlockId(0))));
        assert_eq!(d.len(), r.len());
        assert!(matches!(r[0].0, Edge::Exit(BlockId(0))));
    }

    #[test]
    fn an_unknown_method_has_no_successors() {
        let prog = prog_with(vec![], Terminator::Return(None), vec![]);
        let elsewhere = ProgramPoint {
            method: MethodKey {
                class: "Nope".into(),
                name: "gone".into(),
                desc: "()V".into(),
            },
            block: BlockId(0),
            index: 0,
        };
        assert!(successors(&prog, &elsewhere).is_empty());
    }
}
