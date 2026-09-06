//! Which variables a block actually needs on entry.
//!
//! A relational encoding that describes a block by *every* variable in the
//! method makes the solver carry state that cannot affect anything. For CHC
//! that is not merely wasteful: Spacer has to synthesise an interpretation for
//! each predicate, and the difficulty grows sharply with arity. Measured
//! 2026-09-06 on a five-line recursive program whose summary is `f(n) >= 0`,
//! the block encoding declared 14-ary predicates and Z3 timed out, while the
//! same program written with the two variables that matter is `sat` in 0.01s.
//!
//! # Why an imprecise answer here cannot cause a wrong verdict
//!
//! This is the property that makes the analysis safe to rely on. Suppose the
//! live set omits index `k` that some later block really does read. Then the
//! transition clause never transmits `w_k`, so when the successor reads it the
//! variable is a fresh universally quantified binder -- unconstrained, i.e.
//! *any* value. The encoding therefore describes a superset of the reachable
//! states, which is an over-approximation: a proof of safety over it is still
//! a proof of safety, and the only cost is that the proof may fail.
//!
//! A live set that is too *large* costs arity and nothing else. So errors in
//! either direction are precision, never soundness -- which is the reason this
//! can be applied to an engine that publishes `Over`.

use std::collections::{BTreeMap, BTreeSet};

use ajave_ir::*;

/// Variables read by an operand.
fn operand_var(op: &Operand, out: &mut BTreeSet<usize>) {
    if let Operand::Var(v) = op {
        out.insert(v.0 as usize);
    }
}

fn operands_var(ops: &[Operand], out: &mut BTreeSet<usize>) {
    for op in ops {
        operand_var(op, out);
    }
}

/// Variables read by an rvalue.
///
/// Deliberately exhaustive with no catch-all arm: a new `Rvalue` variant must
/// fail to compile here rather than be silently treated as reading nothing.
fn rvalue_uses(rv: &Rvalue, out: &mut BTreeSet<usize>) {
    match rv {
        Rvalue::Use(a) | Rvalue::Neg(a) | Rvalue::ArrayLength(a) | Rvalue::Cast(_, _, a) => {
            operand_var(a, out)
        }
        Rvalue::Bin(_, a, b) | Rvalue::Cmp(_, a, b) => {
            operand_var(a, out);
            operand_var(b, out);
        }
        Rvalue::GetField { obj, .. } | Rvalue::InstanceOf { obj, .. } => operand_var(obj, out),
        Rvalue::ArrayLoad { arr, idx } => {
            operand_var(arr, out);
            operand_var(idx, out);
        }
        Rvalue::NewArray { len, .. } => operand_var(len, out),
        Rvalue::Call { args, .. } => operands_var(args, out),
        Rvalue::Nondet(..) | Rvalue::Havoc(..) | Rvalue::GetStatic(_) | Rvalue::New(_) => {}
    }
}

/// Variables read by a statement, and the variable it defines if any.
fn stmt_uses_defs(st: &Stmt, uses: &mut BTreeSet<usize>, def: &mut Option<usize>) {
    match st {
        Stmt::Assign(v, rv) => {
            rvalue_uses(rv, uses);
            *def = Some(v.0 as usize);
        }
        Stmt::PutStatic(_, val) | Stmt::Assume(val) => operand_var(val, uses),
        Stmt::PutField { obj, val, .. } => {
            operand_var(obj, uses);
            operand_var(val, uses);
        }
        Stmt::ArrayStore { arr, idx, val } => {
            operand_var(arr, uses);
            operand_var(idx, uses);
            operand_var(val, uses);
        }
        Stmt::MonitorEnter(o) | Stmt::MonitorExit(o) => operand_var(o, uses),
        Stmt::Check(_) | Stmt::Nop => {}
    }
}

/// Variables read by a terminator, and the blocks it can reach.
fn term_uses_succs(t: &Terminator, uses: &mut BTreeSet<usize>) -> Vec<BlockId> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::Branch { cond, then_, else_ } => {
            operand_var(cond, uses);
            vec![*then_, *else_]
        }
        Terminator::Return(op) => {
            if let Some(op) = op {
                operand_var(op, uses);
            }
            vec![]
        }
        Terminator::Switch {
            value,
            cases,
            default,
        } => {
            operand_var(value, uses);
            cases
                .iter()
                .map(|(_, b)| *b)
                .chain(std::iter::once(*default))
                .collect()
        }
        Terminator::Throw(op) => {
            operand_var(op, uses);
            vec![]
        }
        Terminator::Halt | Terminator::Diverge(_) => vec![],
    }
}

/// `live_in[b]` — variables some path from the entry of `b` reads before
/// writing. Standard backward dataflow to a fixpoint:
///
/// ```text
/// live_out(b) = union over successors s of live_in(s)
/// live_in(b)  = use(b) union (live_out(b) minus def(b))
/// ```
///
/// `BTreeSet`/`BTreeMap` throughout: the result decides what a solver sees, and
/// `CLAUDE.md` requires that such an order be deterministic.
///
/// A block's exceptional successors are included. An obligation inside a
/// handler is reached along that edge, and dropping it would shrink the live
/// set for reasons that have nothing to do with the program.
pub fn live_in(body: &Body) -> BTreeMap<BlockId, BTreeSet<usize>> {
    let mut live: BTreeMap<BlockId, BTreeSet<usize>> = body
        .blocks
        .iter()
        .map(|b| (b.id, BTreeSet::new()))
        .collect();

    // Per-block use/def, computed once: statements run in order, so a variable
    // read before the block writes it is a use of the *incoming* value, while
    // one read after is not.
    let mut local: BTreeMap<BlockId, (BTreeSet<usize>, Vec<BlockId>)> = BTreeMap::new();
    for block in &body.blocks {
        let mut uses = BTreeSet::new();
        let mut killed: BTreeSet<usize> = BTreeSet::new();
        for st in &block.stmts {
            let mut this_uses = BTreeSet::new();
            let mut def = None;
            stmt_uses_defs(st, &mut this_uses, &mut def);
            for u in this_uses {
                if !killed.contains(&u) {
                    uses.insert(u);
                }
            }
            if let Some(d) = def {
                killed.insert(d);
            }
        }
        let mut term_uses = BTreeSet::new();
        let mut succs = term_uses_succs(&block.term, &mut term_uses);
        for u in term_uses {
            if !killed.contains(&u) {
                uses.insert(u);
            }
        }
        succs.extend(block.exceptional.iter().map(|e| e.target));
        local.insert(block.id, (uses, succs));
        // `killed` is recomputed below as part of the transfer; storing the
        // use set alone keeps this map small.
    }

    // Definitions per block, for the `live_out minus def` term.
    let defs: BTreeMap<BlockId, BTreeSet<usize>> = body
        .blocks
        .iter()
        .map(|b| {
            let mut d = BTreeSet::new();
            for st in &b.stmts {
                if let Stmt::Assign(v, _) = st {
                    d.insert(v.0 as usize);
                }
            }
            (b.id, d)
        })
        .collect();

    // Backward fixpoint. Monotone and bounded by the variable count, so it
    // terminates; the loop guard is a changed flag rather than an iteration
    // cap, because a cap would silently return a non-fixpoint.
    loop {
        let mut changed = false;
        for block in body.blocks.iter().rev() {
            let (uses, succs) = &local[&block.id];
            let mut out: BTreeSet<usize> = BTreeSet::new();
            for s in succs {
                if let Some(ls) = live.get(s) {
                    out.extend(ls.iter().copied());
                }
            }
            let empty = BTreeSet::new();
            let d = defs.get(&block.id).unwrap_or(&empty);
            let mut next: BTreeSet<usize> = uses.clone();
            next.extend(out.difference(d).copied());
            if next != live[&block.id] {
                live.insert(block.id, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    live
}
