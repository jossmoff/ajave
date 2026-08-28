//! Configurable Program Analysis: the shared fixpoint substrate.
//!
//! One reachability algorithm, parameterised by `(initial, transfer, merge,
//! stop, prec)` after Beyer/Henzinger/Theoduloz. The payoff is that the choice
//! of operators, not the choice of algorithm, decides the technique:
//!
//!   * `merge_sep` + `stop_sep`   -> explicit-state model checking
//!   * `merge_join` + `stop_join` -> abstract interpretation
//!   * predicate domain, `prec` doing refinement -> lazy abstraction
//!
//! A new domain is a new `Cpa` impl and nothing else in the tree changes.

use crate::artifact::ProgramPoint;
use ajave_ir::{Edge, Program, Stmt, Terminator};

pub trait Lattice: Clone {
    fn leq(&self, other: &Self) -> bool;
    fn join(&self, other: &Self) -> Self;
    fn is_bottom(&self) -> bool;
}

/// States must know where they are, so the driver can find successor edges.
/// (In the original formulation this is a LocationCPA composed into the
/// product; folding it in keeps the driver readable.)
pub trait HasLocation {
    fn location(&self) -> &ProgramPoint;
}

pub enum MergeResult<S> {
    /// Keep the states apart (path-sensitive).
    Sep,
    /// Replace the reached state with this join (path-insensitive).
    Joined(S),
}

pub trait Cpa {
    type State: Lattice + HasLocation;
    type Prec: Clone;

    fn initial(&self, prog: &Program, at: &ProgramPoint) -> Self::State;

    fn transfer(
        &self,
        state: &Self::State,
        prog: &Program,
        edge: &Edge,
        to: &ProgramPoint,
        prec: &Self::Prec,
    ) -> Vec<Self::State>;

    /// Default is `merge_sep`, the path-sensitive choice.
    fn merge(
        &self,
        _new: &Self::State,
        _reached: &Self::State,
        _prec: &Self::Prec,
    ) -> MergeResult<Self::State> {
        MergeResult::Sep
    }

    /// Default is `stop_sep`: covered iff some *already-reached state at the
    /// same location* subsumes this one.
    ///
    /// The location filter is not optional. Without it, a state's `leq` check
    /// runs against every reached state regardless of where it sits in the
    /// program -- and since a variable absent from a state's map reads as Top
    /// (unconstrained), the very first state explored (an empty map, i.e. Top
    /// everywhere) is `leq`-comparable to almost anything. Every later state,
    /// at completely unrelated program points, would then be judged "already
    /// covered" by that one early state and dropped before ever being added
    /// to `reached` -- silently truncating exploration far short of the
    /// obligations that matter. This exact bug produced a real false TRUE
    /// on `assert2` in the interval domain (see `engines::interval`): the
    /// state actually reaching the failing assertion was live and correctly
    /// narrowed, but never made it into `reached` because of this.
    fn stop(&self, state: &Self::State, reached: &[Self::State], _prec: &Self::Prec) -> bool {
        reached
            .iter()
            .any(|r| r.location() == state.location() && state.leq(r))
    }

    /// Dynamic precision adjustment. The hook CEGAR lives in.
    fn prec(&self, state: &Self::State, prec: &Self::Prec) -> (Self::State, Self::Prec) {
        (state.clone(), prec.clone())
    }
}

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

/// The shared fixpoint loop. Every technique riding the CPA substrate runs
/// through exactly this function.
///
/// Returns the reached set and whether the search actually converged.
/// `complete = false` means the state cap cut exploration short -- and a
/// caller claiming a TRUE proof on an incomplete search would be exactly the
/// silent-unsoundness failure mode this whole design exists to prevent, so
/// the flag is not optional to check.
pub fn reachability<C: Cpa>(
    cpa: &C,
    prog: &Program,
    start: &ProgramPoint,
    prec: C::Prec,
    max_states: usize,
) -> (Vec<C::State>, bool) {
    let mut reached: Vec<C::State> = Vec::new();
    let mut waitlist: Vec<C::State> = vec![cpa.initial(prog, start)];

    while let Some(state) = waitlist.pop() {
        if reached.len() >= max_states {
            return (reached, false);
        }
        let (state, prec) = cpa.prec(&state, &prec);
        if state.is_bottom() {
            continue;
        }

        for (edge, to) in successors(prog, state.location()) {
            if matches!(edge, Edge::Exit(_)) {
                continue;
            }
            for succ in cpa.transfer(&state, prog, &edge, &to, &prec) {
                if succ.is_bottom() {
                    continue;
                }
                let mut merged = succ;
                let mut replaced = false;
                for r in reached.iter_mut() {
                    if let MergeResult::Joined(j) = cpa.merge(&merged, r, &prec) {
                        *r = j.clone();
                        merged = j;
                        replaced = true;
                    }
                }
                if !replaced && cpa.stop(&merged, &reached, &prec) {
                    continue;
                }
                reached.push(merged.clone());
                waitlist.push(merged);
            }
        }
    }
    (reached, true)
}
