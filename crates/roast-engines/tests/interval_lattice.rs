//! Lattice and soundness laws for the interval domain.
//!
//! This domain produced a real false TRUE once (`assert2`, documented in
//! `docs/strategies/interval.md`) and until now had no direct test — the only
//! thing exercising it was the end-to-end corpus suite, which asserts a final
//! verdict and cannot say *which* operator was wrong.
//!
//! The tests below are of two kinds. The first pin down the lattice laws that
//! `cpa::reachability` relies on. The second are the ones that actually matter:
//! **soundness by exhaustive concretisation**. For small intervals we can
//! enumerate every concrete value they denote, apply the concrete operation,
//! and check the abstract result contains it. An abstract operation that ever
//! excludes a reachable concrete value is exactly how this domain produces a
//! false TRUE, and that is checkable directly rather than argued in a comment.

use roast_engines::interval::{Interval, NEG_INF, POS_INF};

/// Small intervals to enumerate over. Deliberately includes negatives, zero,
/// and singletons, since sign handling is where interval arithmetic goes wrong.
fn samples() -> Vec<Interval> {
    let mut out = Vec::new();
    for lo in -4i64..=4 {
        for hi in lo..=4 {
            out.push(Interval { lo, hi });
        }
    }
    out.push(Interval::top());
    out.push(Interval::point(0));
    out
}

/// Every concrete value an interval denotes. `None` for Top — too big to
/// enumerate, and the concretisation tests skip it.
fn concretise(i: Interval) -> Option<Vec<i64>> {
    if i == Interval::top() || i.is_bottom() {
        return None;
    }
    if i.hi - i.lo > 64 {
        return None;
    }
    Some((i.lo..=i.hi).collect())
}

// ---------------------------------------------------------------------------
// Lattice laws
// ---------------------------------------------------------------------------

#[test]
fn join_is_an_upper_bound() {
    for a in samples() {
        for b in samples() {
            let j = a.join(b);
            assert!(a.leq(j), "{a:?} should be leq its join with {b:?} = {j:?}");
            assert!(b.leq(j), "{b:?} should be leq its join with {a:?} = {j:?}");
        }
    }
}

#[test]
fn join_is_commutative_and_idempotent() {
    for a in samples() {
        assert_eq!(a.join(a), a, "join is idempotent");
        for b in samples() {
            assert_eq!(a.join(b), b.join(a), "join is commutative");
        }
    }
}

#[test]
fn leq_is_reflexive_and_transitive() {
    let s = samples();
    for a in &s {
        assert!(a.leq(*a), "{a:?} should be leq itself");
    }
    for a in &s {
        for b in &s {
            for c in &s {
                if a.leq(*b) && b.leq(*c) {
                    assert!(
                        a.leq(*c),
                        "transitivity: {a:?} <= {b:?} <= {c:?} but not {a:?} <= {c:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn bottom_is_the_least_element_and_top_the_greatest() {
    for a in samples() {
        assert!(Interval::bottom().leq(a), "bottom <= {a:?}");
        assert!(a.leq(Interval::top()), "{a:?} <= top");
    }
}

#[test]
fn bottom_is_recognised_however_it_is_spelled() {
    assert!(Interval::bottom().is_bottom());
    assert!(Interval { lo: 5, hi: 4 }.is_bottom());
    assert!(!Interval::point(0).is_bottom());
    assert!(!Interval::top().is_bottom());
}

// ---------------------------------------------------------------------------
// Soundness: the abstract result must contain every concrete result
// ---------------------------------------------------------------------------

fn check_binop(
    name: &str,
    abstract_op: impl Fn(Interval, Interval) -> Interval,
    concrete_op: impl Fn(i64, i64) -> i64,
) {
    for a in samples() {
        for b in samples() {
            let (Some(avs), Some(bvs)) = (concretise(a), concretise(b)) else {
                continue;
            };
            let result = abstract_op(a, b);
            if result == Interval::top() {
                continue; // Top contains everything; nothing to check.
            }
            for x in &avs {
                for y in &bvs {
                    let concrete = concrete_op(*x, *y);
                    // Values outside i32 are the overflow case, which `clamp`
                    // widens to Top -- already skipped above.
                    if !(NEG_INF..=POS_INF).contains(&concrete) {
                        continue;
                    }
                    assert!(
                        result.contains(concrete),
                        "{name}: {a:?} op {b:?} = {result:?} does not contain \
                         {x} op {y} = {concrete}"
                    );
                }
            }
        }
    }
}

#[test]
fn add_is_sound() {
    check_binop("add", |a, b| a + b, |x, y| x + y);
}

#[test]
fn sub_is_sound() {
    check_binop("sub", |a, b| a - b, |x, y| x - y);
}

#[test]
fn mul_is_sound() {
    // The one most likely to be wrong: the result bounds are the min and max
    // of the four corner products, and getting the sign cases wrong silently
    // produces a too-narrow interval.
    check_binop("mul", |a, b| a * b, |x, y| x * y);
}

#[test]
fn neg_is_sound() {
    for a in samples() {
        let Some(vs) = concretise(a) else { continue };
        let result = -a;
        if result == Interval::top() {
            continue;
        }
        for x in vs {
            assert!(
                result.contains(-x),
                "neg: -{a:?} = {result:?} does not contain -{x}"
            );
        }
    }
}

#[test]
fn arithmetic_on_bottom_stays_bottom() {
    let b = Interval::bottom();
    for a in samples() {
        assert!((a + b).is_bottom(), "{a:?} + bottom");
        assert!((b + a).is_bottom(), "bottom + {a:?}");
        assert!((a - b).is_bottom(), "{a:?} - bottom");
        assert!((a * b).is_bottom(), "{a:?} * bottom");
    }
    assert!((-b).is_bottom());
}

#[test]
fn overflow_widens_to_top_rather_than_wrapping() {
    // Java ints wrap; this domain does not model that, so anything that could
    // leave the i32 range must widen to Top. A narrow-but-wrong answer here is
    // unsound; a wide one only costs precision.
    let big = Interval::point(POS_INF);
    assert_eq!(big + Interval::point(1), Interval::top());
    assert_eq!(
        Interval::point(NEG_INF) - Interval::point(1),
        Interval::top()
    );
    assert_eq!(big * Interval::point(2), Interval::top());
    assert_eq!(-Interval::point(NEG_INF), Interval::top());
}

// ---------------------------------------------------------------------------
// Narrowing soundness -- the property that decides whether a branch is pruned
// ---------------------------------------------------------------------------

/// `narrow` must never discard a concrete pair that satisfies the comparison.
/// Dropping one is precisely how a reachable failing state disappears from the
/// search and an obligation looks provably safe when it is not.
fn check_narrow(op: roast_ir::BinOp, holds: impl Fn(i64, i64) -> bool) {
    for a in samples() {
        for b in samples() {
            let (Some(avs), Some(bvs)) = (concretise(a), concretise(b)) else {
                continue;
            };
            let Some((na, nb)) = Interval::narrow(op, a, b) else {
                continue; // declining to narrow is always safe
            };
            for x in &avs {
                for y in &bvs {
                    if !holds(*x, *y) {
                        continue;
                    }
                    assert!(
                        na.contains(*x),
                        "narrow {op:?}: {a:?},{b:?} -> {na:?} dropped satisfying lhs {x} (rhs {y})"
                    );
                    assert!(
                        nb.contains(*y),
                        "narrow {op:?}: {a:?},{b:?} -> {nb:?} dropped satisfying rhs {y} (lhs {x})"
                    );
                }
            }
        }
    }
}

#[test]
fn narrow_lt_keeps_every_satisfying_pair() {
    check_narrow(roast_ir::BinOp::Lt, |x, y| x < y);
}

#[test]
fn narrow_le_keeps_every_satisfying_pair() {
    check_narrow(roast_ir::BinOp::Le, |x, y| x <= y);
}

#[test]
fn narrow_gt_keeps_every_satisfying_pair() {
    check_narrow(roast_ir::BinOp::Gt, |x, y| x > y);
}

#[test]
fn narrow_ge_keeps_every_satisfying_pair() {
    check_narrow(roast_ir::BinOp::Ge, |x, y| x >= y);
}

#[test]
fn narrow_eq_keeps_every_satisfying_pair() {
    check_narrow(roast_ir::BinOp::Eq, |x, y| x == y);
}

#[test]
fn narrow_actually_narrows_the_motivating_case() {
    // The case the module doc is built around: `assume(x > 5)` must leave
    // `x >= 6`, which is what makes `assert(x > 3)` provable.
    let x = Interval::top();
    let five = Interval::point(5);
    let (nx, _) = Interval::narrow(roast_ir::BinOp::Gt, x, five).unwrap();
    assert_eq!(nx.lo, 6);
    assert!(!nx.contains(5));
    assert!(nx.contains(6));
}

// ---------------------------------------------------------------------------
// Predicates the engines act on
// ---------------------------------------------------------------------------

#[test]
fn definitely_nonzero_is_conservative() {
    for a in samples() {
        let Some(vs) = concretise(a) else { continue };
        if a.definitely_nonzero() {
            assert!(
                vs.iter().all(|v| *v != 0),
                "{a:?} claims definitely-nonzero but contains 0"
            );
        }
    }
    assert!(!Interval::top().definitely_nonzero());
    assert!(!Interval { lo: -1, hi: 1 }.definitely_nonzero());
    assert!(Interval { lo: 1, hi: 5 }.definitely_nonzero());
    assert!(Interval { lo: -5, hi: -1 }.definitely_nonzero());
}

#[test]
fn definitely_zero_only_for_the_singleton_zero() {
    assert!(Interval::point(0).definitely_zero());
    assert!(!Interval { lo: 0, hi: 1 }.definitely_zero());
    assert!(!Interval { lo: -1, hi: 0 }.definitely_zero());
    assert!(!Interval::top().definitely_zero());
}
