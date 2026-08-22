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

use std::collections::BTreeMap;

use crate::artifact::ProgramPoint;
use roast_ir::{Edge, Program, Stmt, Terminator};

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
    ///
    /// `reached` is always a state at the *same location* as `new` -- the
    /// driver buckets the reached set by `ProgramPoint`, so an implementation
    /// never has to check that itself. Joining states from different program
    /// points is meaningless (the result would carry one point's location and
    /// the other's facts), and making it unrepresentable here is cheaper than
    /// asking every domain to remember the guard.
    fn merge(
        &self,
        _new: &Self::State,
        _reached: &Self::State,
        _prec: &Self::Prec,
    ) -> MergeResult<Self::State> {
        MergeResult::Sep
    }

    /// Default is `stop_sep`: covered iff some already-reached state subsumes
    /// this one.
    ///
    /// `reached` holds only states **at `state`'s own location** -- the driver
    /// buckets the reached set by `ProgramPoint` and hands over the matching
    /// bucket. That filter is not a convenience, and it used to live here as an
    /// explicit `r.location() == state.location()` guard. Without it, `leq`
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
    ///
    /// Moving the filter into the driver keeps that property structural rather
    /// than per-implementation: an override of this method cannot reintroduce
    /// the bug, because it is never shown a state from elsewhere in the
    /// program. The same guarantee applies to `merge`.
    fn stop(&self, state: &Self::State, reached: &[Self::State], _prec: &Self::Prec) -> bool {
        reached.iter().any(|r| state.leq(r))
    }

    /// Dynamic precision adjustment. The hook CEGAR lives in.
    fn prec(&self, state: &Self::State, prec: &Self::Prec) -> (Self::State, Self::Prec) {
        (state.clone(), prec.clone())
    }
}

/// Product of two CPAs. Composition is how domains get combined without either
/// of them knowing about the other.
pub struct Product<A, B>(pub A, pub B);

#[derive(Clone)]
pub struct Pair<X, Y>(pub X, pub Y);

impl<X: Lattice, Y: Lattice> Lattice for Pair<X, Y> {
    fn leq(&self, other: &Self) -> bool {
        self.0.leq(&other.0) && self.1.leq(&other.1)
    }
    fn join(&self, other: &Self) -> Self {
        Pair(self.0.join(&other.0), self.1.join(&other.1))
    }
    fn is_bottom(&self) -> bool {
        self.0.is_bottom() || self.1.is_bottom()
    }
}

impl<X: HasLocation, Y> HasLocation for Pair<X, Y> {
    fn location(&self) -> &ProgramPoint {
        self.0.location()
    }
}

impl<A, B> Cpa for Product<A, B>
where
    A: Cpa,
    B: Cpa,
    A::State: HasLocation,
{
    type State = Pair<A::State, B::State>;
    type Prec = (A::Prec, B::Prec);

    fn initial(&self, prog: &Program, at: &ProgramPoint) -> Self::State {
        Pair(self.0.initial(prog, at), self.1.initial(prog, at))
    }

    fn transfer(
        &self,
        state: &Self::State,
        prog: &Program,
        edge: &Edge,
        to: &ProgramPoint,
        prec: &Self::Prec,
    ) -> Vec<Self::State> {
        let ls = self.0.transfer(&state.0, prog, edge, to, &prec.0);
        let rs = self.1.transfer(&state.1, prog, edge, to, &prec.1);
        let mut out = Vec::new();
        for l in &ls {
            for r in &rs {
                out.push(Pair(l.clone(), r.clone()));
            }
        }
        out
    }
}

/// All outgoing edges from a point, paired with the point they lead to.
pub fn successors(prog: &Program, at: &ProgramPoint) -> Vec<(Edge, ProgramPoint)> {
    let Some(body) = prog.body(&at.method) else {
        return Vec::new();
    };
    let block = body.block(at.block);

    let point_at = |b: roast_ir::BlockId| ProgramPoint {
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
        if matches!(block.stmts[at.index], Stmt::Check(_)) {
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
    // Bucketed by location, for two reasons that are really one.
    //
    // Correctness: `merge` and `stop` are only ever shown states at the same
    // program point, so neither a domain author nor a future refactor can
    // reintroduce the cross-location comparison described on `Cpa::stop`.
    //
    // Cost: both were linear scans over the entire reached set, once per
    // successor, which is quadratic in the size of the search. Scanning one
    // bucket is proportional to the states actually at that point.
    //
    // `BTreeMap` rather than `HashMap` so the flattened result is in a
    // deterministic order -- CEGAR picks a counterexample trace out of it, and
    // a verifier that reports different traces across runs of the same input
    // is miserable to debug.
    let mut reached: BTreeMap<ProgramPoint, Vec<C::State>> = BTreeMap::new();
    let mut count = 0usize;
    let mut waitlist: Vec<C::State> = vec![cpa.initial(prog, start)];

    let flatten = |m: BTreeMap<ProgramPoint, Vec<C::State>>| -> Vec<C::State> {
        m.into_values().flatten().collect()
    };

    while let Some(state) = waitlist.pop() {
        if count >= max_states {
            return (flatten(reached), false);
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
                let bucket = reached.entry(succ.location().clone()).or_default();

                // Absorb every reached state the domain wants joined into
                // `merged`, *removing* each one as it is absorbed. Leaving the
                // old entry behind (and then pushing the join as well) meant a
                // merge_join domain accumulated redundant copies of the same
                // state at the same point, which inflated every later scan and
                // burned the `max_states` budget on bookkeeping -- and a search
                // that hits the cap reports `complete = false`, which correctly
                // forbids an over-approximating engine from claiming TRUE. So
                // the leak cost verdicts, not just cycles.
                let mut merged = succ;
                let mut i = 0;
                while i < bucket.len() {
                    match cpa.merge(&merged, &bucket[i], &prec) {
                        MergeResult::Joined(j) => {
                            merged = j;
                            bucket.swap_remove(i);
                            count -= 1;
                        }
                        MergeResult::Sep => i += 1,
                    }
                }

                if cpa.stop(&merged, bucket, &prec) {
                    continue;
                }
                bucket.push(merged.clone());
                count += 1;
                waitlist.push(merged);
            }
        }
    }
    (flatten(reached), true)
}
