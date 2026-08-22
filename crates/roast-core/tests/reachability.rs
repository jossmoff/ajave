//! Tests for the shared CPA fixpoint loop.
//!
//! Every technique riding the CPA substrate runs through `reachability`, so a
//! defect here is a defect everywhere. Until these existed the loop had no
//! direct coverage at all — the only thing exercising it was the end-to-end
//! corpus suite, which asserts a final verdict and cannot localise a fault.
//!
//! The domain below is deliberately trivial (a single monotone counter). The
//! point is to pin down the *driver's* contract — what lands in the reached
//! set, how merge and stop interact, whether the state cap is reported
//! honestly — independently of any real abstract domain.

use std::collections::{BTreeMap, BTreeSet};

use roast_core::artifact::ProgramPoint;
use roast_core::cpa::*;
use roast_ir::*;

// ---------------------------------------------------------------------------
// A minimal test domain: a set of integers per state.
//
// Subset ordering, union join. Chosen over a plain counter because two states
// carrying {4} and {5} are genuinely *incomparable* — which is what makes the
// merge_sep and merge_join cases distinguishable. Under a totally ordered
// domain `stop_sep` would legitimately collapse them and the tests could not
// tell a correct driver from a broken one.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Counter {
    at: ProgramPoint,
    ns: BTreeSet<i64>,
}

impl Counter {
    fn new(at: ProgramPoint, n: i64) -> Self {
        Counter {
            at,
            ns: BTreeSet::from([n]),
        }
    }
    /// Largest element, for readable assertions.
    fn max(&self) -> i64 {
        self.ns.iter().copied().max().unwrap_or(0)
    }
}

impl Lattice for Counter {
    fn leq(&self, other: &Self) -> bool {
        self.ns.is_subset(&other.ns)
    }
    fn join(&self, other: &Self) -> Self {
        Counter {
            at: self.at.clone(),
            ns: self.ns.union(&other.ns).copied().collect(),
        }
    }
    fn is_bottom(&self) -> bool {
        self.ns.is_empty()
    }
}

impl HasLocation for Counter {
    fn location(&self) -> &ProgramPoint {
        &self.at
    }
}

/// `merge_sep` + `stop_sep` — the path-sensitive defaults.
struct SepCpa;

impl Cpa for SepCpa {
    type State = Counter;
    type Prec = ();

    fn initial(&self, _prog: &Program, at: &ProgramPoint) -> Counter {
        Counter::new(at.clone(), 0)
    }

    fn transfer(
        &self,
        s: &Counter,
        _prog: &Program,
        _edge: &Edge,
        to: &ProgramPoint,
        _prec: &(),
    ) -> Vec<Counter> {
        // Increment by the destination block id, so the two arms of a diamond
        // arrive at the join point carrying genuinely different values.
        vec![Counter::new(to.clone(), s.max() + to.block.0 as i64)]
    }
}

/// `merge_join` at the same location — what `PredicateCpa` does.
struct JoinCpa;

impl Cpa for JoinCpa {
    type State = Counter;
    type Prec = ();

    fn initial(&self, _prog: &Program, at: &ProgramPoint) -> Counter {
        Counter::new(at.clone(), 0)
    }

    fn transfer(
        &self,
        s: &Counter,
        _prog: &Program,
        _edge: &Edge,
        to: &ProgramPoint,
        _prec: &(),
    ) -> Vec<Counter> {
        vec![Counter::new(to.clone(), s.max() + to.block.0 as i64)]
    }

    fn merge(&self, new: &Counter, reached: &Counter, _prec: &()) -> MergeResult<Counter> {
        if new.ns != reached.ns {
            MergeResult::Joined(new.join(reached))
        } else {
            MergeResult::Sep
        }
    }
}

/// A domain whose merge ignores location entirely. The driver is responsible
/// for only ever offering same-location states, so this must still never
/// produce a cross-location join.
struct BlindJoinCpa;

impl Cpa for BlindJoinCpa {
    type State = Counter;
    type Prec = ();

    fn initial(&self, _prog: &Program, at: &ProgramPoint) -> Counter {
        Counter::new(at.clone(), 0)
    }

    fn transfer(
        &self,
        s: &Counter,
        _prog: &Program,
        _edge: &Edge,
        to: &ProgramPoint,
        _prec: &(),
    ) -> Vec<Counter> {
        vec![Counter::new(to.clone(), s.max() + 1)]
    }

    fn merge(&self, new: &Counter, reached: &Counter, _prec: &()) -> MergeResult<Counter> {
        // Deliberately no location check.
        MergeResult::Joined(new.join(reached))
    }
}

// ---------------------------------------------------------------------------
// CFG builders
// ---------------------------------------------------------------------------

fn key() -> MethodKey {
    MethodKey {
        class: "T".into(),
        name: "t".into(),
        desc: "()V".into(),
    }
}

fn blk(id: u32, term: Terminator) -> Block {
    Block {
        id: BlockId(id),
        bytecode_offset: 0,
        stmts: vec![],
        term,
        exceptional: vec![],
    }
}

fn program(blocks: Vec<Block>) -> (Program, ProgramPoint) {
    let k = key();
    let body = Body {
        key: k.clone(),
        entry: BlockId(0),
        blocks,
        vars: vec![],
        obligations: vec![],
    };
    let mut p = Program::default();
    p.bodies.insert(k.clone(), body);
    p.entry = Some(k.clone());
    let start = ProgramPoint {
        method: k,
        block: BlockId(0),
        index: 0,
    };
    (p, start)
}

/// bb0 branches to bb1 and bb2; both go to bb3; bb3 returns.
fn diamond() -> (Program, ProgramPoint) {
    program(vec![
        blk(
            0,
            Terminator::Branch {
                cond: Operand::int(1),
                then_: BlockId(1),
                else_: BlockId(2),
            },
        ),
        blk(1, Terminator::Goto(BlockId(3))),
        blk(2, Terminator::Goto(BlockId(3))),
        blk(3, Terminator::Return(None)),
    ])
}

/// bb0 -> bb1 -> bb2 -> bb1 (a loop with no exit condition the domain can see).
fn unbounded_loop() -> (Program, ProgramPoint) {
    program(vec![
        blk(0, Terminator::Goto(BlockId(1))),
        blk(1, Terminator::Goto(BlockId(2))),
        blk(2, Terminator::Goto(BlockId(1))),
    ])
}

fn counts_per_block(reached: &[Counter]) -> BTreeMap<u32, usize> {
    let mut m = BTreeMap::new();
    for s in reached {
        *m.entry(s.at.block.0).or_insert(0) += 1;
    }
    m
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn merge_join_leaves_exactly_one_state_per_location() {
    // The regression this file was written for. When `merge` returned
    // `Joined`, the old driver overwrote the reached entry *and* pushed the
    // joined state again, with the `stop` check short-circuited by the same
    // flag — so the join point ended up in `reached` twice. Under merge_join a
    // location holds one state by definition; that is what joining means.
    let (prog, start) = diamond();
    let (reached, complete) = reachability(&JoinCpa, &prog, &start, (), 10_000);

    assert!(complete, "search should converge on a 4-block acyclic CFG");
    for (block, count) in counts_per_block(&reached) {
        assert_eq!(
            count, 1,
            "bb{block} holds {count} states after merge_join, expected 1"
        );
    }
}

#[test]
fn merge_join_keeps_the_joined_value_not_a_stale_one() {
    // Absorbing the old entry must not lose what it carried. bb3 is reached
    // from bb1 (n = 1 + 3 = 4) and from bb2 (n = 2 + 3 = 5); the join is 5.
    let (prog, start) = diamond();
    let (reached, _) = reachability(&JoinCpa, &prog, &start, (), 10_000);

    let bb3: Vec<&Counter> = reached.iter().filter(|s| s.at.block.0 == 3).collect();
    assert_eq!(bb3.len(), 1);
    assert_eq!(
        bb3[0].ns,
        BTreeSet::from([4, 5]),
        "the joined state must carry both arms, not just the survivor"
    );
}

#[test]
fn merge_is_only_offered_states_at_the_same_location() {
    // The location filter belongs to the driver, not to each domain. A domain
    // that does not check location itself must still never see a
    // cross-location join — otherwise every `Cpa` impl has to carry the same
    // defensive guard, and forgetting it is silent.
    let (prog, start) = diamond();
    let (reached, complete) = reachability(&BlindJoinCpa, &prog, &start, (), 10_000);

    assert!(complete);
    // With a blind merge, a driver that offered cross-location states would
    // collapse the whole CFG into one entry. Four blocks are reachable, and
    // each must survive as its own state.
    let counts = counts_per_block(&reached);
    assert_eq!(
        counts.keys().copied().collect::<Vec<_>>(),
        vec![1, 2, 3],
        "each reachable location keeps its own state"
    );
}

#[test]
fn stop_sep_keeps_distinct_states_at_one_location() {
    // The dual of the merge_join test: with the path-sensitive defaults, two
    // genuinely different states at the same location must both survive.
    let (prog, start) = diamond();
    let (reached, complete) = reachability(&SepCpa, &prog, &start, (), 10_000);

    assert!(complete);
    let bb3 = counts_per_block(&reached).get(&3).copied().unwrap_or(0);
    assert_eq!(bb3, 2, "the two arms of the diamond reach bb3 separately");
}

#[test]
fn state_cap_is_reported_as_incomplete() {
    // `complete = false` is the only thing standing between an over-
    // approximating engine and a false TRUE on a truncated search, so the flag
    // has to be right when the cap actually bites.
    let (prog, start) = unbounded_loop();
    let (reached, complete) = reachability(&SepCpa, &prog, &start, (), 32);

    assert!(!complete, "an unbounded loop must not report convergence");
    assert!(
        reached.len() <= 32 + 8,
        "cap should bound the reached set, got {}",
        reached.len()
    );
}

#[test]
fn converged_search_reports_complete() {
    let (prog, start) = diamond();
    let (_, complete) = reachability(&SepCpa, &prog, &start, (), 10_000);
    assert!(complete);
}

#[test]
fn successors_do_not_leave_the_entry_block_unreachable() {
    // Every non-entry block in the diamond is reachable, and the driver must
    // actually visit them rather than stopping at the first join.
    let (prog, start) = diamond();
    let (reached, _) = reachability(&SepCpa, &prog, &start, (), 10_000);
    let blocks: Vec<u32> = counts_per_block(&reached).keys().copied().collect();
    assert_eq!(blocks, vec![1, 2, 3]);
}
