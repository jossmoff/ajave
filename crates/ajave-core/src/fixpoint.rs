//! The shared fixpoint: an abstract domain, a merge policy, and one loop.
//!
//! This is the substrate under every over-approximating state-space engine in
//! the tree. It descends from Configurable Program Analysis
//! (Beyer/Henzinger/Theoduloz), and the two names worth keeping from that
//! formulation are `merge` and `stop`, because a reader who knows the paper
//! knows immediately what they select.
//!
//! What it is *not* is a five-operator framework. The CPA tuple
//! `(initial, transfer, merge, stop, prec)` was implemented in full, and
//! measured on 2026-10-26: across all three implementors, `stop` and `prec`
//! were never once overridden, and the module header advertised three
//! configurations — explicit-state model checking, abstract interpretation,
//! lazy abstraction — of which **none** was what any implementor did. `prec`
//! was documented as "the hook CEGAR lives in" while CEGAR refined from
//! outside it, re-entering the loop with a larger `Prec`.
//!
//! So the split here is the one the implementors actually use:
//!
//!   * **`AbstractDomain`** — what the abstraction means and how it steps.
//!   * **`MergePolicy`** — how exploration combines states.
//!
//! These are orthogonal, and `WideningIntervalCpa` was the proof: it existed
//! purely to override `merge`, delegating `initial` and `transfer` to the
//! non-widening domain verbatim. One domain under two policies is two
//! techniques, and that is now expressible without a second domain.
//!
//! `stop` is fixed at `stop_sep` (see `covered_by`) and precision is fixed for
//! the duration of a call. A caller wanting more precision re-enters with a
//! larger `Prec`, which is what CEGAR does and all it ever did.

use crate::artifact::ProgramPoint;
use crate::cfg::successors;
use ajave_ir::{Edge, Program};

/// The ordering an abstract domain's states carry.
///
/// **Contract.** `leq` is a preorder — reflexive and transitive — and `join` is
/// an upper bound in it: `a.leq(a.join(b))` and `b.leq(a.join(b))`. Everything
/// below depends on the second clause, because coverage and merging both
/// replace states with ones claimed to subsume them. `lattice_laws` in this
/// module's tests checks both on every domain in the workspace.
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

/// What the abstraction means and how it steps.
///
/// Says nothing about how exploration combines states — that is
/// `MergePolicy`, and the two compose freely.
pub trait AbstractDomain {
    type State: Lattice + HasLocation;

    /// Read-only configuration for one `explore` call.
    ///
    /// Deliberately not adjusted mid-flight. The CPA formulation has a `prec`
    /// operator for that; it was implemented, never overridden, and its
    /// absence is why CEGAR's refinement loop sits outside this module instead.
    type Prec: Clone;

    fn initial(&self, prog: &Program, at: &ProgramPoint) -> Self::State;

    /// Successor states along one edge.
    ///
    /// **Contract.** Returning no states means the edge is infeasible under
    /// this abstraction. Returning several means the abstraction could not
    /// decide between them, and all are explored. For an over-approximating
    /// domain the returned set must cover every concrete successor — dropping
    /// one leaves an obligation unexamined, and an unexamined check is treated
    /// as vacuously safe.
    fn transfer(
        &self,
        state: &Self::State,
        prog: &Program,
        edge: &Edge,
        to: &ProgramPoint,
        prec: &Self::Prec,
    ) -> Vec<Self::State>;
}

/// How exploration combines a new state with one already reached.
///
/// **Contract**, both clauses load-bearing and both enforced by
/// `debug_assert` at the call site in `explore`:
///
/// 1. **Soundness.** `Joined(j)` requires `new.leq(j)` *and* `reached.leq(j)`.
///    The driver overwrites `reached` with `j` and discards `new`, so a `j`
///    covering neither silently loses states. A lost state is an unexamined
///    obligation, which is then discharged as vacuously safe — the −16
///    direction.
///
/// 2. **Progress.** `Joined(j)` requires `!j.leq(reached)`. The driver skips
///    its coverage check whenever a merge fires, so returning a `j` already
///    subsumed by `reached` re-enqueues forever. Report `Sep` instead and let
///    coverage subsume it.
///
/// Both clauses are vacuous for a policy that never joins, which is why `Sep`
/// is always safe and never terminating-relevant.
pub trait MergePolicy<D: AbstractDomain> {
    fn merge(&self, new: &D::State, reached: &D::State, prec: &D::Prec) -> MergeResult<D::State>;
}

/// `merge_sep`: never combine. Exploration stays path-sensitive.
pub struct Sep;

impl<D: AbstractDomain> MergePolicy<D> for Sep {
    fn merge(
        &self,
        _new: &D::State,
        _reached: &D::State,
        _prec: &D::Prec,
    ) -> MergeResult<D::State> {
        MergeResult::Sep
    }
}

/// `merge_join`: combine states at the same program point.
///
/// Generic over the domain because the join is the lattice's. The predicate
/// domain hand-rolled this with a `values != values` comparison, which is
/// equivalent to the `leq` test below on that lattice — `join` there keeps only
/// agreeing predicates, so the result differs from `reached` exactly when some
/// predicate disagreed, which is exactly when `reached` holds knowledge the
/// join dropped. `the_join_policy_matches_the_old_predicate_merge` pins that
/// equivalence rather than trusting the argument.
pub struct Join;

impl<D: AbstractDomain> MergePolicy<D> for Join {
    fn merge(&self, new: &D::State, reached: &D::State, _prec: &D::Prec) -> MergeResult<D::State> {
        if new.location() != reached.location() {
            return MergeResult::Sep;
        }
        let joined = new.join(reached);
        // Clause 2: a join that adds nothing must not be reported as one.
        if joined.leq(reached) {
            MergeResult::Sep
        } else {
            MergeResult::Joined(joined)
        }
    }
}

/// `stop_sep`: covered iff some already-reached state *at the same location*
/// subsumes this one.
///
/// The location filter is not optional. Without it, a state's `leq` check runs
/// against every reached state regardless of where it sits in the program --
/// and since a variable absent from a state's map reads as Top
/// (unconstrained), the very first state explored (an empty map, i.e. Top
/// everywhere) is `leq`-comparable to almost anything. Every later state, at
/// completely unrelated program points, would then be judged "already covered"
/// by that one early state and dropped before ever being added to `reached` --
/// silently truncating exploration far short of the obligations that matter.
/// This exact bug produced a real false TRUE on `assert2` in the interval
/// domain; `coverage_is_filtered_by_location` is the test that would now catch
/// it.
pub fn covered_by<S: Lattice + HasLocation>(state: &S, reached: &[S]) -> bool {
    reached
        .iter()
        .any(|r| r.location() == state.location() && state.leq(r))
}

/// The shared fixpoint loop. Every technique riding this substrate runs
/// through exactly this function.
///
/// Returns the reached set and whether the search actually converged.
/// `complete = false` means the state cap cut exploration short -- and a
/// caller claiming a TRUE proof on an incomplete search would be exactly the
/// silent-unsoundness failure mode this whole design exists to prevent, so
/// the flag is not optional to check.
pub fn explore<D, M>(
    domain: &D,
    policy: &M,
    prog: &Program,
    start: &ProgramPoint,
    prec: D::Prec,
    max_states: usize,
) -> (Vec<D::State>, bool)
where
    D: AbstractDomain,
    M: MergePolicy<D>,
{
    let mut reached: Vec<D::State> = Vec::new();
    let mut waitlist: Vec<D::State> = vec![domain.initial(prog, start)];

    while let Some(state) = waitlist.pop() {
        if reached.len() >= max_states {
            return (reached, false);
        }
        if state.is_bottom() {
            continue;
        }

        for (edge, to) in successors(prog, state.location()) {
            if matches!(edge, Edge::Exit(_)) {
                continue;
            }
            for succ in domain.transfer(&state, prog, &edge, &to, &prec) {
                if succ.is_bottom() {
                    continue;
                }
                let mut merged = succ;
                let mut replaced = false;
                for r in reached.iter_mut() {
                    if let MergeResult::Joined(j) = policy.merge(&merged, r, &prec) {
                        debug_assert!(
                            merged.leq(&j) && r.leq(&j),
                            "MergePolicy clause 1: Joined must be an upper bound of both inputs"
                        );
                        debug_assert!(
                            !j.leq(r),
                            "MergePolicy clause 2: Joined must add something to the reached state"
                        );
                        *r = j.clone();
                        merged = j;
                        replaced = true;
                    }
                }
                if replaced {
                    // `reached` already holds this state: the entry was
                    // overwritten in place above. Pushing it again appended a
                    // duplicate at the same program point, and the duplicate
                    // was not harmless — `reached.len() >= max_states` is what
                    // reports a search incomplete, and an incomplete search
                    // forfeits the proof, so every duplicate spent part of the
                    // completeness budget on a state that said nothing new.
                    //
                    // It does still need re-propagating, which is the waitlist.
                    waitlist.push(merged);
                    continue;
                }
                if covered_by(&merged, &reached) {
                    continue;
                }
                reached.push(merged.clone());
                waitlist.push(merged);
            }
        }
    }
    (reached, true)
}

/// Executable statements of the contracts above.
///
/// These live in the crate rather than in a test module so that a domain added
/// later gets the laws for free: implementing `Lattice` and `MergePolicy` is
/// not the same as satisfying them, and the gap is where a lost state becomes
/// a wrong TRUE. Call both from the domain's own tests.
pub mod laws {
    use super::{AbstractDomain, HasLocation, Lattice, MergePolicy, MergeResult};

    /// `leq` is a preorder and `join` is an upper bound in it.
    ///
    /// Checked over every pair drawn from `samples`, so the caller's job is to
    /// supply states that actually differ — Top, a narrow one, two that
    /// disagree, and anything the domain treats specially.
    pub fn check_lattice_laws<L: Lattice + std::fmt::Debug>(samples: &[L]) {
        assert!(
            samples.len() >= 2,
            "a law check over fewer than two samples proves nothing"
        );
        for a in samples {
            assert!(a.leq(a), "leq is not reflexive at {a:?}");
            if a.is_bottom() {
                for b in samples {
                    assert!(a.leq(b), "bottom {a:?} is not below {b:?}");
                }
            }
        }
        for a in samples {
            for b in samples {
                let j = a.join(b);
                assert!(
                    a.leq(&j),
                    "join is not an upper bound of its left input: {a:?} ⊔ {b:?}"
                );
                assert!(
                    b.leq(&j),
                    "join is not an upper bound of its right input: {a:?} ⊔ {b:?}"
                );
                let k = b.join(a);
                assert!(
                    j.leq(&k) && k.leq(&j),
                    "join is not commutative up to leq at {a:?}, {b:?}"
                );
            }
            let s = a.join(a);
            assert!(
                s.leq(a) && a.leq(&s),
                "join is not idempotent up to leq at {a:?}"
            );
        }
    }

    /// Both `MergePolicy` clauses, over every ordered pair from `samples`.
    ///
    /// Clause 1 (soundness): a `Joined` result covers both inputs, because the
    /// driver keeps only it. Clause 2 (progress): a `Joined` result adds
    /// something to the reached state, because the driver skips its coverage
    /// check when a merge fires and would otherwise re-enqueue forever.
    pub fn check_merge_policy<D, M>(policy: &M, samples: &[D::State], prec: &D::Prec)
    where
        D: AbstractDomain,
        D::State: std::fmt::Debug,
        M: MergePolicy<D>,
    {
        assert!(
            samples.len() >= 2,
            "a policy check over fewer than two samples proves nothing"
        );
        for new in samples {
            for reached in samples {
                if let MergeResult::Joined(j) = policy.merge(new, reached, prec) {
                    assert!(
                        new.leq(&j),
                        "clause 1: {j:?} does not cover the new state {new:?}"
                    );
                    assert!(
                        reached.leq(&j),
                        "clause 1: {j:?} does not cover the reached state {reached:?}"
                    );
                    assert!(
                        !j.leq(reached),
                        "clause 2: {j:?} adds nothing to {reached:?}, so the driver \
                         would re-enqueue it forever"
                    );
                    assert_eq!(
                        new.location(),
                        reached.location(),
                        "a policy joined states at different program points"
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ajave_ir::{
        Block, BlockId, Body, Const, MethodKey, Operand, Program, Rvalue, Stmt, Terminator, VarId,
        VarInfo, VarKind,
    };

    /// A two-point lattice over a set of known facts: fewer facts is higher.
    /// Deliberately not the interval domain — the generic policies must be
    /// correct for any lattice, and the real domains are checked in
    /// `ajave-engines` where they live.
    #[derive(Clone, Debug, PartialEq)]
    struct Facts {
        at: ProgramPoint,
        known: Vec<u8>,
    }

    impl Lattice for Facts {
        fn leq(&self, other: &Self) -> bool {
            // More facts = lower. self ≤ other iff self knows everything other does.
            other.known.iter().all(|k| self.known.contains(k))
        }
        fn join(&self, other: &Self) -> Self {
            Facts {
                at: self.at.clone(),
                known: self
                    .known
                    .iter()
                    .filter(|k| other.known.contains(k))
                    .copied()
                    .collect(),
            }
        }
        fn is_bottom(&self) -> bool {
            false
        }
    }

    impl HasLocation for Facts {
        fn location(&self) -> &ProgramPoint {
            &self.at
        }
    }

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "main".into(),
            desc: "()V".into(),
        }
    }

    fn pp(block: u32, index: usize) -> ProgramPoint {
        ProgramPoint {
            method: mk(),
            block: BlockId(block),
            index,
        }
    }

    fn facts(block: u32, known: &[u8]) -> Facts {
        Facts {
            at: pp(block, 0),
            known: known.to_vec(),
        }
    }

    fn samples() -> Vec<Facts> {
        vec![
            facts(0, &[]),     // Top: nothing known
            facts(0, &[1]),    //
            facts(0, &[2]),    // incomparable with the above
            facts(0, &[1, 2]), // below both
        ]
    }

    /// The domain the generic tests drive. Its `transfer` walks one statement
    /// at a time and learns a fact per block, which is enough to exercise the
    /// loop without reimplementing an analysis.
    struct FactsDomain;

    impl AbstractDomain for FactsDomain {
        type State = Facts;
        type Prec = ();

        fn initial(&self, _prog: &Program, at: &ProgramPoint) -> Facts {
            Facts {
                at: at.clone(),
                known: vec![],
            }
        }

        fn transfer(
            &self,
            state: &Facts,
            _prog: &Program,
            _edge: &Edge,
            to: &ProgramPoint,
            _prec: &(),
        ) -> Vec<Facts> {
            let mut known = state.known.clone();
            known.push(to.block.0 as u8);
            known.sort_unstable();
            known.dedup();
            vec![Facts {
                at: to.clone(),
                known,
            }]
        }
    }

    fn two_block_program() -> Program {
        let mut prog = Program::default();
        prog.bodies.insert(
            mk(),
            Body {
                is_static: true,
                key: mk(),
                entry: BlockId(0),
                vars: vec![VarInfo {
                    kind: VarKind::Local(0),
                    ty: ajave_ir::Ty::Int,
                }],
                obligations: vec![],
                blocks: vec![
                    Block {
                        id: BlockId(0),
                        bytecode_offset: 0,
                        stmts: vec![Stmt::Assign(
                            VarId(0),
                            Rvalue::Use(Operand::Const(Const::Int(1))),
                        )],
                        term: Terminator::Goto(BlockId(1)),
                        exceptional: vec![],
                    },
                    Block {
                        id: BlockId(1),
                        bytecode_offset: 1,
                        stmts: vec![],
                        term: Terminator::Return(None),
                        exceptional: vec![],
                    },
                ],
            },
        );
        prog.entry = Some(mk());
        prog
    }

    /// `Join`, but it records how many times it actually joined.
    ///
    /// A test about what a merge *does* has to establish that one happened.
    /// The first version of `merging_does_not_leave_duplicate_states_behind`
    /// inferred that from the duplication it was testing for, so once the bug
    /// was fixed the precondition became unsatisfiable — the assertion and its
    /// own premise were the same fact.
    struct CountingJoin(std::cell::Cell<usize>);

    impl MergePolicy<FactsDomain> for CountingJoin {
        fn merge(&self, new: &Facts, reached: &Facts, prec: &()) -> MergeResult<Facts> {
            let r = MergePolicy::<FactsDomain>::merge(&Join, new, reached, prec);
            if matches!(r, MergeResult::Joined(_)) {
                self.0.set(self.0.get() + 1);
            }
            r
        }
    }

    /// `if (c) {} else {}` — block 3 is reached from both 1 and 2, so a merge
    /// policy actually fires there. `two_block_program` visits every point once
    /// from a single predecessor, which makes any merge assertion vacuous.
    fn diamond_program() -> Program {
        let blk = |id: u32, term: Terminator| ajave_ir::Block {
            id: BlockId(id),
            bytecode_offset: id as u16,
            stmts: vec![],
            term,
            exceptional: vec![],
        };
        let mut prog = Program::default();
        prog.bodies.insert(
            mk(),
            Body {
                is_static: true,
                key: mk(),
                entry: BlockId(0),
                vars: vec![VarInfo {
                    kind: VarKind::Local(0),
                    ty: ajave_ir::Ty::Int,
                }],
                obligations: vec![],
                blocks: vec![
                    blk(
                        0,
                        Terminator::Branch {
                            cond: Operand::Const(Const::Int(1)),
                            then_: BlockId(1),
                            else_: BlockId(2),
                        },
                    ),
                    blk(1, Terminator::Goto(BlockId(3))),
                    blk(2, Terminator::Goto(BlockId(3))),
                    blk(3, Terminator::Return(None)),
                ],
            },
        );
        prog.entry = Some(mk());
        prog
    }

    #[test]
    fn the_sample_lattice_satisfies_the_laws() {
        laws::check_lattice_laws(&samples());
    }

    #[test]
    fn sep_never_joins() {
        let s = samples();
        for a in &s {
            for b in &s {
                assert!(
                    matches!(
                        MergePolicy::<FactsDomain>::merge(&Sep, a, b, &()),
                        MergeResult::Sep
                    ),
                    "Sep joined {a:?} with {b:?}"
                );
            }
        }
    }

    #[test]
    fn the_join_policy_satisfies_both_clauses() {
        laws::check_merge_policy::<FactsDomain, _>(&Join, &samples(), &());
    }

    #[test]
    fn sep_satisfies_both_clauses_vacuously() {
        laws::check_merge_policy::<FactsDomain, _>(&Sep, &samples(), &());
    }

    #[test]
    fn the_join_policy_keeps_different_locations_apart() {
        let a = facts(0, &[1]);
        let b = facts(1, &[2]);
        assert!(matches!(
            MergePolicy::<FactsDomain>::merge(&Join, &a, &b, &()),
            MergeResult::Sep
        ));
    }

    #[test]
    fn the_join_policy_reports_sep_when_the_join_adds_nothing() {
        // {1,2} ⊔ {1} = {1}, which is exactly `reached`. Clause 2 forbids
        // reporting that as a join: the driver would re-enqueue it forever.
        let new = facts(0, &[1, 2]);
        let reached = facts(0, &[1]);
        assert!(matches!(
            MergePolicy::<FactsDomain>::merge(&Join, &new, &reached, &()),
            MergeResult::Sep
        ));
    }

    /// Without the location filter in `covered_by`, the first state explored
    /// (Top everywhere) subsumes states at unrelated program points, and
    /// exploration is truncated before the obligations that matter. That is
    /// the false TRUE on `assert2`.
    #[test]
    fn coverage_is_filtered_by_location() {
        let top_here = facts(0, &[]);
        let narrow_elsewhere = Facts {
            at: pp(1, 0),
            known: vec![9],
        };
        assert!(
            narrow_elsewhere.leq(&top_here),
            "precondition: the states are leq-comparable, which is what makes \
             the missing filter dangerous"
        );
        assert!(
            !covered_by(&narrow_elsewhere, std::slice::from_ref(&top_here)),
            "a state at another program point must not be covered"
        );
        let top_there = Facts {
            at: pp(1, 0),
            known: vec![],
        };
        assert!(
            covered_by(&narrow_elsewhere, std::slice::from_ref(&top_there)),
            "but it is covered by a Top state at its own point"
        );
    }

    /// A merge must not leave a duplicate behind.
    ///
    /// When a policy joins, the driver overwrites the reached state *and* then
    /// pushes the merged one, because `replaced` skips the coverage check that
    /// would otherwise have subsumed it. Both copies sit at the same program
    /// point, so a later successor merges with each in turn.
    ///
    /// That is not only imprecision: `reached.len() >= max_states` is what
    /// reports a search incomplete, and an incomplete search forfeits the
    /// proof, so duplicates spend the completeness budget on states that say
    /// nothing new.
    ///
    /// The first version of this test used `two_block_program`, where every
    /// point is reached once from a single predecessor — so no merge ever
    /// fired and the assertion held vacuously. Hence `merge_fired` below:
    /// a test for what a merge does must establish that one happened.
    #[test]
    fn merging_does_not_leave_duplicate_states_behind() {
        let prog = diamond_program();
        let start = pp(0, 0);
        let policy = CountingJoin(std::cell::Cell::new(0));
        let (reached, complete) = explore(&FactsDomain, &policy, &prog, &start, (), 1000);
        assert!(complete);

        // Premise, observed rather than inferred.
        assert!(
            policy.0.get() > 0,
            "no merge fired, so this test proves nothing"
        );

        let mut points: Vec<(u32, usize)> =
            reached.iter().map(|f| (f.at.block.0, f.at.index)).collect();
        let total = points.len();
        points.sort_unstable();
        let mut distinct = points.clone();
        distinct.dedup();
        assert_eq!(
            total,
            distinct.len(),
            "{total} reached states cover only {} distinct points after {} merge(s); \
             duplicates: {points:?}",
            distinct.len(),
            policy.0.get()
        );
    }

    #[test]
    fn an_incomplete_search_is_reported_incomplete() {
        let prog = two_block_program();
        let start = pp(0, 0);
        let (_, complete) = explore(&FactsDomain, &Sep, &prog, &start, (), 1);
        assert!(
            !complete,
            "a one-state cap cannot cover a two-block program"
        );
        let (reached, complete) = explore(&FactsDomain, &Sep, &prog, &start, (), 1000);
        assert!(complete);
        assert!(
            reached.len() > 1,
            "the uncapped search reaches more than one state"
        );
    }

    #[test]
    fn exploration_is_deterministic() {
        // Iteration order over `reached` decides which states get folded
        // together, so a `HashMap` anywhere in a domain's state would make
        // verdicts depend on the process hash seed.
        let prog = two_block_program();
        let start = pp(0, 0);
        let first = explore(&FactsDomain, &Join, &prog, &start, (), 1000);
        for _ in 0..4 {
            let again = explore(&FactsDomain, &Join, &prog, &start, (), 1000);
            assert_eq!(first.1, again.1);
            assert_eq!(
                first.0.iter().map(|f| f.known.clone()).collect::<Vec<_>>(),
                again.0.iter().map(|f| f.known.clone()).collect::<Vec<_>>()
            );
        }
    }
}
