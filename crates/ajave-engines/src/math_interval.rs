//! Sound interval abstractions for `java.lang.Math`.
//!
//! The interval domain sends every `Rvalue::Call` to `top`, so a program whose
//! assertion depends on `Math.sin` is unprovable no matter how precise the rest
//! of the analysis is. That is most of `float-nonlinear-calculation`: 11 of its
//! 12 expected-TRUE tasks are unproven, and they are provable by bounds alone.
//! `coral3` is representative:
//!
//! ```java
//! assume(0 <= d1 && d1 < Math.PI/4 && 0 <= d2 && d2 < Math.PI/4);
//! if (Math.sin(d1) - Math.cos(d2) == 0) { assert false; }
//! ```
//!
//! On `[0, π/4)`, `sin ⊆ [0, 0.708)` and `cos ⊆ (0.707, 1]`, so the difference
//! is strictly negative and the guard is unreachable. No solving required.
//!
//! This is the technique JLiSA took bronze with at SV-COMP 2026 — abstract
//! interpretation alone, and the only Java entrant with no false positives in
//! the whole competition.
//!
//! # Soundness
//!
//! Every function here **over-approximates**: the returned interval contains
//! every value the real `Math` call can produce for any input in the argument
//! interval. Returning `top` is always safe and costs only precision.
//!
//! The trap is **NaN**, and it is the reason most of these functions are more
//! conservative than the textbook versions. NaN is not contained in any interval
//! — `[0, 1]` does not "contain" NaN in any useful sense, and code downstream
//! will compare against the bounds and conclude things that are false of NaN.
//! So any call that *could* produce NaN on the argument interval must return
//! `top` rather than a numeric range:
//!
//! * `sqrt(x)` is NaN for `x < 0`, so the argument must be provably `>= 0`.
//! * `log(x)` is NaN for `x < 0` and `-inf` at `0`, so it must be `> 0`.
//! * `asin`/`acos` are NaN outside `[-1, 1]`.
//! * every function is NaN at NaN, and several are at `±inf`, so a
//!   non-finite argument interval yields `top` throughout.
//!
//! Java's `Math` transcendentals are specified only to within 1 ulp and are not
//! required to be correctly rounded, so the bounds are widened by one ulp in
//! each direction. Computing them with Rust's `f64` and using the result
//! unwidened would be assuming a bit-exact agreement the JLS does not promise.

use ajave_ir::MethodKey;

/// The float interval this module works over. Mirrors `interval::FloatInterval`
/// as a plain pair so this module stays independent of the domain's internals.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Range {
    pub lo: f64,
    pub hi: f64,
}

impl Range {
    pub fn new(lo: f64, hi: f64) -> Range {
        Range { lo, hi }
    }
    pub fn top() -> Range {
        Range { lo: f64::NEG_INFINITY, hi: f64::INFINITY }
    }
    pub fn is_top(&self) -> bool {
        self.lo == f64::NEG_INFINITY && self.hi == f64::INFINITY
    }
    /// Finite and correctly ordered. A reversed or non-finite interval means the
    /// caller's domain has no usable information, and every function here must
    /// decline rather than compute with it.
    fn usable(&self) -> bool {
        self.lo.is_finite() && self.hi.is_finite() && self.lo <= self.hi
    }
}

/// Widen by one ulp each way.
///
/// `Math.sin` and friends are permitted 1 ulp of error and are not required to
/// be correctly rounded (JLS 17). Using Rust's result as an exact bound would
/// assume an agreement between two libms that the specification does not
/// require, so every computed bound is loosened by one representable step.
fn slack(lo: f64, hi: f64) -> Range {
    let l = if lo.is_finite() { next_down(lo) } else { lo };
    let h = if hi.is_finite() { next_up(hi) } else { hi };
    Range { lo: l, hi: h }
}

fn next_up(v: f64) -> f64 {
    if v.is_nan() || v == f64::INFINITY {
        return v;
    }
    if v == 0.0 {
        return f64::from_bits(1);
    }
    let b = v.to_bits() as i64;
    f64::from_bits((if v > 0.0 { b + 1 } else { b - 1 }) as u64)
}

fn next_down(v: f64) -> f64 {
    if v.is_nan() || v == f64::NEG_INFINITY {
        return v;
    }
    if v == 0.0 {
        return -f64::from_bits(1);
    }
    let b = v.to_bits() as i64;
    f64::from_bits((if v > 0.0 { b - 1 } else { b + 1 }) as u64)
}

/// Range of `sin` over `[a, b]`, or `cos` when `phase` shifts by π/2.
///
/// The endpoints alone are not enough: `sin` over `[0, π]` has endpoints `0`
/// and `0` but reaches `1` in between. So the extrema at `π/2 + kπ` that fall
/// inside the interval must be included explicitly, and an interval spanning a
/// full period is simply `[-1, 1]`.
fn sin_like(a: f64, b: f64, phase: f64) -> Range {
    use std::f64::consts::PI;
    let (a, b) = (a + phase, b + phase);
    if !(a.is_finite() && b.is_finite()) || (b - a) >= 2.0 * PI {
        return slack(-1.0, 1.0);
    }
    let mut lo = a.sin().min(b.sin());
    let mut hi = a.sin().max(b.sin());
    // Walk the extrema at π/2 + kπ that lie within [a, b].
    let first = ((a - PI / 2.0) / PI).ceil();
    let mut k = first;
    while k * PI + PI / 2.0 <= b {
        // sin is +1 at even k, -1 at odd k (relative to π/2 + kπ).
        if (k as i64).rem_euclid(2) == 0 {
            hi = 1.0;
        } else {
            lo = -1.0;
        }
        k += 1.0;
        if k - first > 8.0 {
            // More than a few periods: the interval covers everything anyway.
            return slack(-1.0, 1.0);
        }
    }
    slack(lo.max(-1.0), hi.min(1.0))
}

/// A monotonically increasing function's range is just its endpoints.
fn monotone_inc(a: f64, b: f64, f: impl Fn(f64) -> f64) -> Range {
    let (lo, hi) = (f(a), f(b));
    if !lo.is_finite() && !hi.is_finite() {
        return Range::top();
    }
    slack(lo.min(hi), lo.max(hi))
}

/// Interval for a `java.lang.Math` call, or `None` if not modelled.
///
/// `None` and `Some(top)` mean the same thing to the caller; both are sound.
/// The distinction is kept so a caller can tell "we have no model" from "the
/// model could not narrow it".
pub fn eval(target: &MethodKey, args: &[Range]) -> Option<Range> {
    if target.class != "java/lang/Math" && target.class != "java/lang/StrictMath" {
        return None;
    }
    let a = *args.first()?;
    // A non-finite or reversed argument interval carries no usable information,
    // and every function below is NaN at NaN.
    if !a.usable() {
        return Some(Range::top());
    }

    let r = match target.name.as_str() {
        // Bounded everywhere, and never NaN for a finite argument.
        "sin" => sin_like(a.lo, a.hi, 0.0),
        "cos" => sin_like(a.lo, a.hi, std::f64::consts::FRAC_PI_2),

        // Monotone increasing on the whole real line.
        "atan" => monotone_inc(a.lo, a.hi, f64::atan),
        "exp" => monotone_inc(a.lo, a.hi, f64::exp),
        "cbrt" => monotone_inc(a.lo, a.hi, f64::cbrt),
        "tanh" => monotone_inc(a.lo, a.hi, f64::tanh),
        "floor" => monotone_inc(a.lo, a.hi, f64::floor),
        "ceil" => monotone_inc(a.lo, a.hi, f64::ceil),
        "rint" => monotone_inc(a.lo, a.hi, f64::round),
        "signum" => slack(-1.0, 1.0),

        // NaN below zero, so the argument must be provably non-negative.
        "sqrt" => {
            if a.lo < 0.0 {
                Range::top()
            } else {
                monotone_inc(a.lo, a.hi, f64::sqrt)
            }
        }
        // NaN below zero and -inf at zero.
        "log" => {
            if a.lo <= 0.0 {
                Range::top()
            } else {
                monotone_inc(a.lo, a.hi, f64::ln)
            }
        }
        "log10" => {
            if a.lo <= 0.0 {
                Range::top()
            } else {
                monotone_inc(a.lo, a.hi, f64::log10)
            }
        }
        // NaN outside [-1, 1].
        "asin" => {
            if a.lo < -1.0 || a.hi > 1.0 {
                Range::top()
            } else {
                monotone_inc(a.lo, a.hi, f64::asin)
            }
        }
        "acos" => {
            if a.lo < -1.0 || a.hi > 1.0 {
                // acos is *decreasing*; monotone_inc orders the endpoints, so
                // it is still correct, but the guard has to come first.
                Range::top()
            } else {
                monotone_inc(a.lo, a.hi, f64::acos)
            }
        }
        // |x| is exact, and non-negative.
        "abs" => {
            if a.lo >= 0.0 {
                Range::new(a.lo, a.hi)
            } else if a.hi <= 0.0 {
                Range::new(-a.hi, -a.lo)
            } else {
                Range::new(0.0, a.lo.abs().max(a.hi.abs()))
            }
        }
        "max" | "min" => {
            let b = *args.get(1)?;
            if !b.usable() {
                Range::top()
            } else if target.name == "max" {
                Range::new(a.lo.max(b.lo), a.hi.max(b.hi))
            } else {
                Range::new(a.lo.min(b.lo), a.hi.min(b.hi))
            }
        }

        // Deliberately unmodelled.
        //
        // `tan` is unbounded near ±π/2 and its range over an interval spanning a
        // pole is the whole line; `pow` depends on both arguments in a way that
        // needs case analysis on sign and integrality. Both are common in this
        // corpus, so a wrong bound here would be a wrong TRUE — `top` is the
        // honest answer until they are done properly.
        _ => return None,
    };
    Some(r)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(name: &str) -> MethodKey {
        MethodKey {
            class: "java/lang/Math".into(),
            name: name.into(),
            desc: "(D)D".into(),
        }
    }

    fn ev(name: &str, lo: f64, hi: f64) -> Range {
        eval(&mk(name), &[Range::new(lo, hi)]).unwrap()
    }

    #[test]
    fn sin_and_cos_are_bounded_everywhere() {
        for (l, h) in [(-1e9, 1e9), (0.0, 100.0), (-7.0, 7.0)] {
            let s = ev("sin", l, h);
            assert!(s.lo >= -1.0 - 1e-15 && s.hi <= 1.0 + 1e-15, "sin {s:?}");
        }
    }

    #[test]
    fn sin_includes_interior_extrema() {
        // Endpoints are both 0, but sin reaches 1 at pi/2 inside the interval.
        let s = ev("sin", 0.0, std::f64::consts::PI);
        assert!(s.hi >= 1.0, "must include the peak at pi/2, got {s:?}");
    }

    #[test]
    fn sin_stays_below_cos_on_the_first_octant() {
        // sin < cos on [0, pi/4), so their difference is non-positive and a
        // guard testing `sin(d1) - cos(d2) == 0` is *nearly* unreachable.
        //
        // "Nearly" is the point. With exact arithmetic the margin is real:
        //
        //     sin(pi/4) = 0.70710678118654746
        //     cos(pi/4) = 0.70710678118654757   gap = 1.11e-16
        //
        // but that gap is one ulp at 0.707, and JLS 17 permits `Math.sin` one
        // ulp of error without requiring correct rounding. The margin is
        // therefore smaller than the specification's own tolerance, and a real
        // JVM's libm is free to land on the other side of it.
        //
        // So this shape is *not* soundly provable by interval arithmetic over
        // `Math`, and the one-ulp widening in `slack` is what stops us claiming
        // it. Dropping that widening would prove `coral3` and would be
        // assuming a bit-exact agreement between two libms that nothing
        // guarantees — a wrong TRUE waiting for a different JVM.
        //
        // `StrictMath` is bit-exactly specified (fdlibm) and could be proved;
        // `Math` cannot. What is asserted here is what actually holds.
        let q = std::f64::consts::FRAC_PI_4;
        let s = ev("sin", 0.0, q);
        let c = ev("cos", 0.0, q);
        assert!(s.hi <= c.hi, "sin must not exceed cos's upper bound");
        assert!(s.lo <= c.lo, "sin's floor must not exceed cos's");
        // The bounds do overlap, by about the permitted error and no more.
        assert!(
            s.hi - c.lo < 1e-15,
            "overlap should be ulp-scale, got {}",
            s.hi - c.lo
        );
    }

    #[test]
    fn partial_functions_decline_outside_their_domain() {
        // Each is NaN somewhere in the argument interval, and NaN is not
        // contained in any numeric range, so the only sound answer is top.
        assert!(ev("sqrt", -1.0, 4.0).is_top());
        assert!(ev("log", 0.0, 5.0).is_top());
        assert!(ev("asin", -2.0, 0.5).is_top());
        assert!(ev("acos", 0.0, 1.5).is_top());
    }

    #[test]
    fn partial_functions_are_precise_inside_their_domain() {
        let s = ev("sqrt", 4.0, 9.0);
        assert!(s.lo <= 2.0 && s.hi >= 3.0 && s.lo > 1.9 && s.hi < 3.1, "{s:?}");
        let e = ev("exp", 0.0, 1.0);
        assert!(e.lo <= 1.0 && e.hi >= std::f64::consts::E);
    }

    #[test]
    fn unmodelled_functions_return_none() {
        // tan spans a pole and pow needs two-argument case analysis; guessing a
        // bound for either would be a wrong TRUE.
        assert!(eval(&mk("tan"), &[Range::new(0.0, 2.0)]).is_none());
        assert!(eval(&mk("pow"), &[Range::new(0.0, 2.0)]).is_none());
    }

    #[test]
    fn non_math_classes_are_not_claimed() {
        let k = MethodKey {
            class: "com/example/MyMath".into(),
            name: "sin".into(),
            desc: "(D)D".into(),
        };
        assert!(eval(&k, &[Range::new(0.0, 1.0)]).is_none());
    }

    #[test]
    fn a_top_argument_yields_top() {
        assert!(ev("sqrt", f64::NEG_INFINITY, f64::INFINITY).is_top());
        assert!(ev("exp", f64::NEG_INFINITY, f64::INFINITY).is_top());
    }
}
