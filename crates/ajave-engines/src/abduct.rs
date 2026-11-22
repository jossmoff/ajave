//! Abduction: ask the solver what fact is *missing*, instead of guessing one.
//!
//! Every invariant mechanism in the tool enumerates candidates and filters
//! them — Houdini over a pool, the interval domain over a lattice. Abduction
//! inverts that. Given premises `Γ` and a goal `φ`, abductive inference returns
//! a simple `ψ` with
//!
//! ```text
//! Γ ∧ ψ ⊨ φ     and     Γ ∧ ψ consistent
//! ```
//!
//! Dillig, Dillig and Aiken brought this into verification for error diagnosis
//! (PLDI 2012) and loop invariants (OOPSLA 2013, with Li); Reynolds, Barbosa,
//! Larraz and Tinelli made it scale via enumerative SyGuS (IJCAR 2020), which
//! is what cvc5 ships as `get-abduct`.
//!
//! ## Why this module exists at all, and what it is *not*
//!
//! It is a **measurement instrument** first. On 2026-11-22 four candidate
//! directions were estimated and three measured zero — a raised unroll cap
//! converted 0 of 69, suppressing refuted witnesses converted 0 of 79, forced
//! FPA converted 1 of 8. The common thread was that each bucket in the blocker
//! census is named after what *blocks* a verdict, and removing the blocker
//! leaves the obligation unprovable underneath.
//!
//! So the question worth answering before building another domain is: **what
//! facts does the corpus actually need?** Abduce over open obligations, cluster
//! the answers by shape — scalar relation, index-quantified array fact, string
//! fact, nothing — and let that choose the next build. See
//! `docs/proposals/research-what-is-unexplored.md`.
//!
//! Nothing here publishes an artifact. An abduct is a *candidate*, exactly like
//! a Houdini candidate: to be used in a proof it must pass initiation and the
//! overflow-guarded preservation query (`docs/proposals/lia-faithfulness.md`
//! §3), because every published abduction result is stated over mathematical
//! integers and on a JVM `0 <= sum` is false the moment the addition wraps.
//! Skipping that step would manufacture #130's wrong TRUE faster than Houdini
//! could.

use cvc5::{InputLanguage, InputParser, Solver, SymbolManager, TermManager};

/// Per-query solver budget, in milliseconds.
///
/// Not optional. Unbounded `(get-abduct-next)` enumeration was measured
/// diverging on the smallest nullness goal in the suite: 79 minutes at 100% of
/// a core and 643 MB resident, with no answer and no sign of stopping. A census
/// over 2675 obligations issues thousands of these queries, so a query that can
/// run forever is a census that never finishes — and worse, one that finishes
/// having silently skipped whatever it hung on.
///
/// `:tlimit-per` bounds each `check-sat`-like command rather than the script, so
/// one slow goal cannot eat the budget of the goals after it.
///
/// Overridable with `AJAVE_ABDUCT_BUDGET_MS`, because the budget is the
/// instrument's main dial: a shape that answers at 5 s and a shape that needs
/// 120 s are different findings, and "returned nothing" means nothing without
/// the budget it returned nothing under.
fn query_budget_ms() -> u32 {
    static N: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *N.get_or_init(|| {
        std::env::var("AJAVE_ABDUCT_BUDGET_MS")
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
            .filter(|v| *v > 0)
            .unwrap_or(5_000)
    })
}

/// The options every abduction script needs: abducts produced, and a budget.
fn preamble(prelude: &str, premises: &[&str]) -> String {
    let mut s = String::new();
    s.push_str("(set-option :produce-abducts true)\n");
    s.push_str(&format!("(set-option :tlimit-per {})\n", query_budget_ms()));
    s.push_str(prelude);
    s.push('\n');
    for p in premises {
        s.push_str(&format!("(assert {p})\n"));
    }
    s
}

/// Run an SMT-LIB 2.6 script in-process and collect the output of every
/// command that produced any.
///
/// The script carries its own `set-logic`, declarations, assertions and
/// `get-abduct`. Going through the parser rather than building terms by hand is
/// deliberate: the LIA encoder this will consume
/// (`interpolation::LiaEncoding`) already emits SMT-LIB text, and a second
/// term-building path would be a second place for the producer and the consumer
/// to disagree.
pub fn run_script(script: &str) -> Result<Vec<String>, String> {
    let tm = TermManager::new();
    let solver = Solver::new(&tm);
    let sm = SymbolManager::new(&tm);
    let mut parser = InputParser::new(solver, Some(&sm));
    parser.set_str_input(InputLanguage::SmtLib26, script, "abduct");
    let mut sm2 = parser.get_symbol_manager();
    let mut out = Vec::new();
    loop {
        match parser.next_command() {
            Ok(Some(cmd)) => {
                let o = cmd.invoke(parser.get_solver(), &mut sm2);
                let o = o.trim();
                if !o.is_empty() {
                    out.push(o.to_string());
                }
            }
            Ok(None) => break,
            Err(e) => return Err(e),
        }
    }
    Ok(out)
}

/// Ask for the missing hypothesis that would make `goal` follow from `premises`.
///
/// `prelude` holds `set-logic` and declarations; `premises` is a list of
/// assertion bodies; `goal` is the conjecture. Returns whatever cvc5 says,
/// which is `None` when it declines — and a decline is a result, not a failure:
/// it says this obligation needs something outside the grammar.
pub fn abduce(prelude: &str, premises: &[&str], goal: &str) -> Result<Option<String>, String> {
    let mut s = preamble(prelude, premises);
    s.push_str(&format!("(get-abduct A {goal})\n"));
    let out = run_script(&s)?;
    // cvc5 answers a successful get-abduct with `(define-fun A () Bool ...)`,
    // and `none` when it has nothing.
    let hit = out
        .iter()
        .find(|o| o.contains("define-fun") || o.starts_with('('))
        .cloned();
    Ok(match hit {
        Some(h) if !h.contains("none") => Some(h),
        _ => None,
    })
}

/// Ask for up to `n` successive abducts for the same goal.
///
/// The first answer is often degenerate. Measured on the three dominant
/// obligation shapes: for a nullness goal cvc5 returns the **goal itself**
/// (`(not (= r nullref))`), which entails the goal and says nothing; for a
/// quantified sortedness goal it returns `(and (= n 2) ...)`, satisfying the
/// quantifier by shrinking its range to a single index. Both are valid
/// abducts and useless as invariants.
///
/// So a census built on first answers alone would have collected 2675 restated
/// goals and concluded nothing.
///
/// Enumeration looked like the cheap half of the fix and is not. Measured on
/// the nullness goal in `enumeration_gets_past_the_restated_goal`, unbounded
/// `(get-abduct-next)` ran **79 minutes at 100% of a core and 643 MB resident**
/// without answering. The grammar is the half that works: the same scalar bound
/// that `abduce` answers with the useless `(= len n)` comes back from
/// `abduce_with_grammar` as `(<= n len)` in under 10 ms.
///
/// This is kept, bounded by `query_budget_ms`, for the one thing it is good
/// for: asking whether a *second* answer exists at all when no grammar is
/// obvious. Prefer `abduce_with_grammar` for anything run at scale.
pub fn abduce_many(
    prelude: &str,
    premises: &[&str],
    goal: &str,
    n: usize,
) -> Result<Vec<String>, String> {
    let mut s = preamble(prelude, premises);
    s.push_str(&format!("(get-abduct A {goal})\n"));
    for _ in 1..n {
        s.push_str("(get-abduct-next)\n");
    }
    let out = run_script(&s)?;
    Ok(out
        .into_iter()
        .filter(|o| o.contains("define-fun") && !o.contains("none"))
        .collect())
}

/// Ask for an abduct drawn only from `grammar`, in SyGuS grammar syntax.
///
/// This is the half that makes the census mean something: restricting the
/// vocabulary to relations over program variables stops the solver answering
/// with the goal restated, because the goal's own atoms are not in the grammar.
pub fn abduce_with_grammar(
    prelude: &str,
    premises: &[&str],
    goal: &str,
    grammar: &str,
) -> Result<Option<String>, String> {
    let mut s = preamble(prelude, premises);
    s.push_str(&format!("(get-abduct A {goal} {grammar})\n"));
    let out = run_script(&s)?;
    Ok(out
        .into_iter()
        .find(|o| o.contains("define-fun") && !o.contains("none")))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The instrument has to work before it can measure anything. This is the
    /// smallest possible check that the parser path and the abduction option
    /// are both live in this build.
    #[test]
    fn the_solver_answers_a_trivial_abduction() {
        let r = abduce(
            "(set-logic QF_LIA)\n(declare-fun x () Int)",
            &["(> x 0)"],
            "(> x 5)",
        );
        let got = r.expect("the parser path must work");
        assert!(
            got.is_some(),
            "cvc5 declined a trivial abduction, so the instrument is not live"
        );
    }

    /// Shape 1 of the census: an `ArrayBounds` obligation in a counting loop.
    /// 900 of 2675 open obligations are this kind.
    ///
    /// The fact a human would supply is `n <= len`. This test does not demand
    /// that exact answer — it demands *some* answer, because the census question
    /// is which shapes cvc5 can serve at all.
    #[test]
    fn a_scalar_array_bound_gets_an_abduct() {
        let got = abduce(
            "(set-logic QF_LIA)\n(declare-fun i () Int)\n(declare-fun n () Int)\n\
             (declare-fun len () Int)",
            &["(and (<= 0 i) (< i n))"],
            "(< i len)",
        )
        .expect("script must parse");
        assert!(got.is_some(), "no abduct for the dominant obligation shape");
        println!("scalar array bound -> {}", got.unwrap());
    }

    /// Shape 2: nullness, 1468 of 2675 open obligations.
    #[test]
    fn a_nullness_obligation_gets_an_abduct() {
        let got = abduce(
            "(set-logic QF_UFLIA)\n(declare-sort Ref 0)\n(declare-fun r () Ref)\n\
             (declare-fun nullref () Ref)\n(declare-fun initialised () Bool)",
            &["initialised"],
            "(not (= r nullref))",
        )
        .expect("script must parse");
        println!("nullness -> {got:?}");
    }

    /// Enumeration was the obvious way past a restated goal, and it diverges.
    ///
    /// Unbounded, this exact query ran 79 minutes at 100% CPU and 643 MB with
    /// no answer. The assertion is therefore about *termination*, not about
    /// finding something: a census issues thousands of these, so what matters
    /// is that every one returns. An empty result is a legitimate answer and
    /// means the budget expired -- which is itself the finding that sends the
    /// census to `abduce_with_grammar`.
    #[test]
    fn enumeration_terminates_under_budget_even_when_it_finds_nothing() {
        let got = abduce_many(
            "(set-logic QF_UFLIA)\n(declare-sort Ref 0)\n(declare-fun r () Ref)\n\
             (declare-fun q () Ref)\n(declare-fun nullref () Ref)\n\
             (declare-fun initialised () Bool)",
            &["initialised", "(not (= q nullref))"],
            "(not (= r nullref))",
            4,
        )
        .expect("script must parse");
        println!("nullness enumeration returned {} abduct(s)", got.len());
        for (i, a) in got.iter().enumerate() {
            println!("nullness abduct #{i} -> {a}");
        }
    }

    /// A grammar is what stops the solver answering with the goal. The
    /// vocabulary here is the relation the obligation actually needs -- a
    /// bound linking the loop counter to the array length -- and nothing from
    /// the goal itself.
    #[test]
    fn a_grammar_forces_the_relation_the_obligation_needs() {
        let got = abduce_with_grammar(
            "(set-logic QF_LIA)\n(declare-fun i () Int)\n(declare-fun n () Int)\n\
             (declare-fun len () Int)",
            &["(and (<= 0 i) (< i n))"],
            "(< i len)",
            "((Start Bool)) ((Start Bool ((<= n len) (< n len) (<= len n) (= n len))))",
        )
        .expect("script must parse");
        println!("grammar-restricted scalar bound -> {got:?}");
        assert!(
            got.is_some(),
            "no abduct inside a grammar that contains a sufficient relation"
        );
    }

    /// The decisive one: can a *grammar* carry a quantified template?
    ///
    /// Plain `abduce` answers the sortedness goal in ~20 s with
    /// `(and (= n 2) (= (select a 0) (select a 1)))` -- it satisfies the
    /// quantifier by shrinking its range to a single index, which is valid and
    /// useless. A grammar is what fixed the scalar case, turning `(= len n)`
    /// into `(<= n len)` in under 10 ms.
    ///
    /// So: offer a grammar whose only production *is* sortedness over the
    /// array. If cvc5 selects it, abduction can locate index-quantified facts
    /// when told their shape, and the array-content domain
    /// (FunArray-style segmentation, or quantified SyGuS a la FreqHorn) has a
    /// candidate generator. If cvc5 rejects quantified productions, the census
    /// has found a hard boundary: the facts the hard obligations need cannot be
    /// abduced, and the generator has to come from somewhere else.
    ///
    /// Printed, not asserted. Both answers are results.
    #[test]
    fn whether_a_grammar_can_carry_a_quantified_template() {
        let sortedness = "(forall ((k Int)) (=> (and (<= 0 k) (< k (- n 1))) \
                          (<= (select a k) (select a (+ k 1)))))";
        let got = abduce_with_grammar(
            "(set-logic ALL)\n(declare-fun a () (Array Int Int))\n(declare-fun n () Int)",
            &["(> n 1)"],
            "(<= (select a 0) (select a 1))",
            &format!("((Start Bool)) ((Start Bool ({sortedness} (> n 1) (>= n 2))))"),
        );
        println!("quantified template in a grammar -> {got:?}");
    }

    /// Selection from a *library*, which is the question that decides the design.
    ///
    /// `whether_a_grammar_can_carry_a_quantified_template` offered three
    /// productions and one of them was the answer, so it shows cvc5 will
    /// **select** a quantified template -- not that it will **search** a space
    /// of them. A template library is only useful if adding the templates a
    /// program does not need leaves the one it does need findable.
    ///
    /// So this offers eight plausible array invariants -- sortedness, reverse
    /// sortedness, non-negativity, boundedness, all-equal, strictness,
    /// constancy against a scalar, and a prefix-max -- and prints which one
    /// came back and how fast. Measured: sortedness, in 15 ms.
    ///
    /// **What this does not show.** Four of the eight entail the goal
    /// (sortedness, all-equal, all-equal-to-`n`, and the prefix-max, which
    /// gives `a[0] <= a[1]` outright), so the result is *a* sufficient
    /// template and most likely simply the first in grammar order. It is not
    /// evidence that cvc5 discriminates between sufficient templates, and it
    /// is certainly not evidence that it returns the **weakest** one -- which
    /// is the one that matters, because a too-strong fact is the one least
    /// likely to survive the preservation check.
    ///
    /// The consequence for the design is the one the module header already
    /// states: an abduct is a candidate. Selection is cheap, so the pipeline
    /// is abduce a set, then put each through initiation and the
    /// overflow-guarded preservation query, and keep what survives. Ranking
    /// inside the solver is not something to rely on.
    #[test]
    fn selection_still_works_from_a_library_of_templates() {
        let templates = [
            "(forall ((k Int)) (=> (and (<= 0 k) (< k (- n 1))) \
             (<= (select a k) (select a (+ k 1)))))",
            "(forall ((k Int)) (=> (and (<= 0 k) (< k (- n 1))) \
             (>= (select a k) (select a (+ k 1)))))",
            "(forall ((k Int)) (=> (and (<= 0 k) (< k n)) (<= 0 (select a k))))",
            "(forall ((k Int)) (=> (and (<= 0 k) (< k n)) (< (select a k) n)))",
            "(forall ((k Int)) (=> (and (<= 0 k) (< k n)) (= (select a k) (select a 0))))",
            "(forall ((k Int)) (=> (and (<= 0 k) (< k (- n 1))) \
             (< (select a k) (select a (+ k 1)))))",
            "(forall ((k Int)) (=> (and (<= 0 k) (< k n)) (= (select a k) n)))",
            "(forall ((k Int)) (=> (and (<= 1 k) (< k n)) (<= (select a 0) (select a k))))",
        ];
        let grammar = format!("((Start Bool)) ((Start Bool ({})))", templates.join(" "));
        let t0 = std::time::Instant::now();
        let got = abduce_with_grammar(
            "(set-logic ALL)\n(declare-fun a () (Array Int Int))\n(declare-fun n () Int)",
            &["(> n 1)"],
            "(<= (select a 0) (select a 1))",
            &grammar,
        );
        let dt = t0.elapsed();
        println!("library of {} templates -> {:?}", templates.len(), got);
        println!("library selection took {dt:?}");
    }

    /// Shape 3, and the one that decides whether Theory B is needed: a fact
    /// quantified over an array index. This is what `assert data[0] < data[1]`
    /// after a merge sort actually requires, and nothing in the portfolio can
    /// state it.
    ///
    /// Printed rather than asserted. A decline here is the most informative
    /// outcome available: it would mean abduction can locate scalar facts but
    /// not the quantified ones the hard obligations need, which is exactly the
    /// boundary the census exists to find.
    #[test]
    fn whether_a_quantified_array_fact_can_be_abduced_at_all() {
        let got = abduce(
            "(set-logic ALL)\n(declare-fun a () (Array Int Int))\n(declare-fun n () Int)",
            &["(> n 1)"],
            "(<= (select a 0) (select a 1))",
        );
        println!("array element goal -> {got:?}");

        let quantified = abduce(
            "(set-logic ALL)\n(declare-fun a () (Array Int Int))\n(declare-fun n () Int)",
            &["(> n 1)"],
            "(forall ((k Int)) (=> (and (<= 0 k) (< k (- n 1))) \
             (<= (select a k) (select a (+ k 1)))))",
        );
        println!("quantified sortedness goal -> {quantified:?}");
    }
}
