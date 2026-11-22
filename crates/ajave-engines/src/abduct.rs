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

/// What kind of fact an open obligation turned out to need.
///
/// This is the census's whole output, and the five cases are chosen so that
/// each one sends the work somewhere different. The first is the one the
/// previous four capability probes were missing: three directions measured
/// exactly zero because each bucket in `tools/blocker_census.py` is named
/// after what *blocks* a verdict, and an obligation can be blocked while
/// needing no invariant at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Shape {
    /// The goal is already valid with no added hypothesis. **No invariant is
    /// missing**: whatever keeps this obligation open is upstream — a
    /// truncated search, an unmodelled call — and no invariant domain, however
    /// good, converts it.
    AlreadyValid,
    /// A relation between integer variables suffices. The scalar learner
    /// (Houdini over a relational pool, `docs/proposals/learned-loop-invariants.md`)
    /// is the build that serves these.
    Scalar,
    /// An index-quantified fact about array contents suffices. Nothing in the
    /// portfolio can state one of these; it is what FunArray-style
    /// segmentation (Cousot/Cousot/Logozzo POPL 2011) or quantified SyGuS
    /// (FreqHorn, CAV 2019) exists for.
    Quantified,
    /// Some fact exists, but outside both vocabularies offered. Worth reading
    /// individually — it is where a vocabulary is missing rather than a domain.
    Outside,
    /// An abduct exists and is **not a fact about a state**: it constrains
    /// post-state symbols.
    ///
    /// These are not near-misses, they are artefacts, and they dominated the
    /// first census run at 95% of rows. The mechanism is worth stating because
    /// it is a property of our own encoding: the integer range axioms are
    /// asserted over the **pre-state only** (`docs/proposals/lia-faithfulness.md`
    /// §3 argues why, and `interpolation.rs` enforces it), so nothing stops a
    /// hypothesis asserting `v2p = 2147483648` — a post-state outside the
    /// 32-bit range. That is consistent in LIA and excludes the error
    /// vacuously. `Verifier.nondetInt` produced exactly that.
    ///
    /// An invariant is a predicate on one state, so a hypothesis over the
    /// successor was never a candidate. Counting these as "a fact exists"
    /// would have reported a capability that does not exist.
    Unusable,
    /// No abduct inside the budget. Either genuinely unprovable or too
    /// expensive to locate; the budget travels with the row so the two are not
    /// conflated.
    Nothing,
}

impl Shape {
    pub fn tag(self) -> &'static str {
        match self {
            Shape::AlreadyValid => "already-valid",
            Shape::Scalar => "scalar",
            Shape::Quantified => "quantified",
            Shape::Outside => "outside",
            Shape::Unusable => "unusable-poststate",
            Shape::Nothing => "nothing",
        }
    }
}

/// One obligation's answer.
#[derive(Debug, Clone)]
pub struct Verdict {
    pub shape: Shape,
    /// The abduct cvc5 returned, with `(define-fun A () Bool …)` stripped.
    pub fact: Option<String>,
}

/// Is `goal` valid under `premises` with no extra hypothesis?
///
/// Asked **before** any abduction, because an obligation that needs no fact is
/// not evidence for any invariant domain, and counting it as one is how a
/// census manufactures a mandate. UNSAT of the negation is validity; anything
/// else (SAT, unknown, a budget expiry) is treated as "a fact is needed",
/// which errs toward more work rather than less.
pub fn already_valid(prelude: &str, premises: &[&str], goal: &str) -> Result<bool, String> {
    let mut s = preamble(prelude, premises);
    s.push_str(&format!("(assert (not {goal}))\n(check-sat)\n"));
    let out = run_script(&s)?;
    Ok(out.iter().any(|o| o.trim() == "unsat"))
}

/// Strip cvc5's `(define-fun A () Bool …)` wrapper down to the formula.
fn unwrap_define(s: &str) -> String {
    let t = s.trim();
    let marker = "() Bool ";
    match t.find(marker) {
        Some(i) => {
            let body = &t[i + marker.len()..];
            body.strip_suffix(')').unwrap_or(body).trim().to_string()
        }
        None => t.to_string(),
    }
}

/// A grammar of relations between integer-sorted **terms**.
///
/// Terms, not variable names, and that distinction is the whole reason the
/// first census run returned nothing usable. An array's length in this
/// encoding is `(select ghost_len r)`, so the single most common missing fact
/// in an array-bounds obligation -- `i < a.length` -- is not a relation
/// between two variables at all. A grammar built from variable names cannot
/// state it, and the census then reports "no scalar fact suffices" for
/// precisely the population a scalar domain serves.
///
/// Pairwise, which is quadratic and therefore capped. `(<= a b)` and `(< a b)`
/// over ordered pairs plus equality: the asymmetric forms both ways give the
/// full ordering vocabulary without needing negation in the grammar.
pub fn scalar_grammar(vars: &[String], cap: usize) -> Option<String> {
    let mut prods: Vec<String> = Vec::new();
    'outer: for (i, a) in vars.iter().enumerate() {
        for b in vars.iter().skip(i + 1) {
            for f in ["<=", "<", "="] {
                prods.push(format!("({f} {a} {b})"));
            }
            prods.push(format!("(<= {b} {a})"));
            prods.push(format!("(< {b} {a})"));
            if prods.len() >= cap {
                break 'outer;
            }
        }
        // Against zero as well: `0 <= i` is the single most common missing
        // fact in an array-bounds obligation and is not a pairwise relation.
        prods.push(format!("(<= 0 {a})"));
        prods.push(format!("(< 0 {a})"));
        if prods.len() >= cap {
            break 'outer;
        }
    }
    if prods.is_empty() {
        return None;
    }
    Some(format!(
        "((Start Bool)) ((Start Bool ({})))",
        prods.join(" ")
    ))
}

/// A grammar of index-quantified array-content templates.
///
/// Measured as the thing that works: unguided, cvc5 answers a sortedness goal
/// in ~20 s with `(and (= n 2) …)`, shrinking the quantifier's range to one
/// index. Given the template it returns the sortedness formula itself in 20 ms,
/// and still does from a library of eight in 15 ms. So the generator is a
/// template library, not free-form synthesis.
///
/// Each template is instantiated per (array, bound variable) pair. The bound
/// is a program variable rather than a literal because the length of an array
/// in this encoding is `(select ghost_len r)` for a reference the census
/// cannot resolve to a site — using the integer variables as candidate bounds
/// lets the solver pick whichever one happens to be the length.
pub fn quantified_grammar(arrays: &[String], bounds: &[String], cap: usize) -> Option<String> {
    let mut prods: Vec<String> = Vec::new();
    'outer: for a in arrays {
        for n in bounds {
            for t in [
                // sortedness, and strictly so
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k (- {n} 1))) (<= (select {a} k) (select {a} (+ k 1)))))"),
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k (- {n} 1))) (< (select {a} k) (select {a} (+ k 1)))))"),
                // descending
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k (- {n} 1))) (>= (select {a} k) (select {a} (+ k 1)))))"),
                // every element non-negative, and bounded by the bound
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k {n})) (<= 0 (select {a} k))))"),
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k {n})) (< (select {a} k) {n})))"),
                // constant, and constant at a known value
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k {n})) (= (select {a} k) (select {a} 0))))"),
                format!("(forall ((k Int)) (=> (and (<= 0 k) (< k {n})) (= (select {a} k) 0)))"),
                // the first element is the minimum -- a prefix-max/min fact,
                // which is what a partially-sorted loop establishes
                format!("(forall ((k Int)) (=> (and (<= 1 k) (< k {n})) (<= (select {a} 0) (select {a} k))))"),
            ] {
                prods.push(t);
                if prods.len() >= cap {
                    break 'outer;
                }
            }
        }
    }
    if prods.is_empty() {
        return None;
    }
    Some(format!(
        "((Start Bool)) ((Start Bool ({})))",
        prods.join(" ")
    ))
}

/// Rewrite a formula into the post-state, token-wise.
///
/// `encode_body_lia` names the successor copy of every symbol by suffixing
/// `p` -- `v12`/`v12p`, `ghost_len`/`ghost_lenp`, `arr0_1`/`arr0_1p` -- and an
/// edge clause relates the unprimed state to the primed one. Composing an
/// obligation's error formula with an edge therefore needs the error moved
/// into the post-state, because the successor's entry state *is* the edge's
/// post-state.
///
/// Token-wise against the declared symbol list, never by substring: `v1` is a
/// substring of both `v1p` and `v12`, so a textual replace would prime `v12`
/// into `v1p2` and double-prime anything already primed.
pub fn prime_formula(formula: &str, symbols: &[String]) -> String {
    let set: std::collections::BTreeSet<&str> = symbols.iter().map(|s| s.as_str()).collect();
    let mut out = String::with_capacity(formula.len() + 16);
    let mut tok = String::new();
    let flush = |tok: &mut String, out: &mut String| {
        if !tok.is_empty() {
            if set.contains(tok.as_str()) {
                out.push_str(tok);
                out.push('p');
            } else {
                out.push_str(tok);
            }
            tok.clear();
        }
    };
    for c in formula.chars() {
        if c.is_alphanumeric() || c == '_' {
            tok.push(c);
        } else {
            flush(&mut tok, &mut out);
            out.push(c);
        }
    }
    flush(&mut tok, &mut out);
    out
}

/// Is this edge clause nothing but the frame — no guard, no assignment?
///
/// # Why anything needs to know
///
/// A Java `assert` compiles to a guarded jump into a failure block, and the
/// failure block's *own* error clause is `(= 0 0)`: once control is there the
/// property has already failed. Safety therefore means the block is
/// unreachable — and `encode_body_lia` has **no program counter**. Its
/// `transition` is a flat disjunction over blocks and its `error_formulas` are
/// keyed by obligation, so "control is not in block 19" is not a state
/// predicate the encoding can express at all. The engines that do discharge
/// these carry block identity themselves: CHC has a predicate per block, IMC
/// unrolls with one.
///
/// Measured consequence, on `InsertionSort-FunSat01`: the edge into the check
/// block is `(and (= arr5_2p arr5_2) (= ghost_lenp ghost_len) (= v0p v0) …)`,
/// pure frame. No pre-state fact entails its negation, because a frame is
/// satisfiable from every pre-state. The only abducts available were
/// post-state contradictions like `(= v0p 2147483648)`, and a census that
/// believed them would have reported "a fact exists, outside the vocabulary"
/// for every assertion in the corpus.
///
/// So a census question asked at an unguarded edge is vacuous, and this is how
/// it is detected: walk back to the nearest edge that actually constrains
/// something.
///
/// Syntactic and deliberately conservative — an unrecognised conjunct counts
/// as a guard, so the walk stops early rather than wandering past the
/// condition it is looking for.
pub fn is_frame_only(clause: &str) -> bool {
    let inner = match clause.trim().strip_prefix("(and ") {
        Some(r) => r.strip_suffix(')').unwrap_or(r),
        // A single conjunct with no `and` wrapper is still judged on its own.
        None => clause.trim(),
    };
    let mut conjuncts = Vec::new();
    let mut depth = 0usize;
    let mut cur = String::new();
    for c in inner.chars() {
        match c {
            '(' => {
                depth += 1;
                cur.push(c);
            }
            ')' => {
                depth -= 1;
                cur.push(c);
                if depth == 0 {
                    conjuncts.push(std::mem::take(&mut cur));
                }
            }
            _ if depth > 0 => cur.push(c),
            _ => {}
        }
    }
    if conjuncts.is_empty() {
        return false;
    }
    conjuncts.iter().all(|c| is_frame_conjunct(c))
}

/// `(= Xp Y)` where both sides are plain symbols and the left is a post-state
/// copy: a frame conjunct, carrying no constraint on the pre-state.
fn is_frame_conjunct(c: &str) -> bool {
    let Some(body) = c
        .trim()
        .strip_prefix("(= ")
        .and_then(|r| r.strip_suffix(')'))
    else {
        // `(and …)` nested one level deeper is how the encoder writes a
        // single-element group; recurse rather than call it a guard.
        if let Some(r) = c
            .trim()
            .strip_prefix("(and ")
            .and_then(|r| r.strip_suffix(')'))
        {
            return is_frame_only(&format!("(and {r})"));
        }
        return false;
    };
    let parts: Vec<&str> = body.split_whitespace().collect();
    if parts.len() != 2 {
        return false;
    }
    let plain = |s: &str| s.chars().all(|c| c.is_alphanumeric() || c == '_');
    plain(parts[0]) && plain(parts[1]) && parts[0].ends_with('p')
}

/// The vocabulary a census row is allowed to answer in.
///
/// A struct rather than five positional arguments because `poststate` is the
/// one that is easy to forget and the one whose absence silently invalidates
/// the whole run — see `Shape::Unusable`.
pub struct Vocab<'a> {
    /// Integer-sorted **terms** over the pre-state, including `(select
    /// ghost_len r)` length terms. Not just variable names.
    pub terms: &'a [String],
    /// Content arrays, excluding the length array.
    pub arrays: &'a [String],
    /// Post-state symbols. Any abduct mentioning one of these is not a fact
    /// about a state and is reported as `Shape::Unusable`.
    pub poststate: &'a [String],
    /// Production cap. A grammar too large to search is indistinguishable
    /// from one that does not contain the answer.
    pub cap: usize,
}

/// Does `fact` mention a post-state symbol?
///
/// Token-wise, not by substring: `v1` is a substring of `v1p` and of `v12`, so
/// a substring test would both over- and under-report.
fn mentions_any(fact: &str, syms: &[String]) -> bool {
    let toks: std::collections::BTreeSet<&str> = fact
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|t| !t.is_empty())
        .collect();
    syms.iter().any(|s| toks.contains(s.as_str()))
}

/// Classify one obligation: what shape of fact would discharge it?
///
/// Asked cheapest-first, and the order is the point. Validity first, because
/// an obligation needing nothing is not evidence for any domain. Then scalar,
/// because a scalar fact is both cheaper to find and cheaper to check than a
/// quantified one, and a census that offered the quantified grammar first
/// would report array work for obligations a relational pool already covers.
///
/// The unrestricted probe runs last and only to distinguish "no fact exists"
/// from "a fact exists that we cannot use". Its answer is screened against
/// `Vocab::poststate` before it is believed.
pub fn classify(
    prelude: &str,
    premises: &[&str],
    goal: &str,
    v: &Vocab<'_>,
) -> Result<Verdict, String> {
    if already_valid(prelude, premises, goal)? {
        return Ok(Verdict {
            shape: Shape::AlreadyValid,
            fact: None,
        });
    }
    if let Some(g) = scalar_grammar(v.terms, v.cap) {
        if let Some(a) = abduce_with_grammar(prelude, premises, goal, &g)? {
            return Ok(Verdict {
                shape: Shape::Scalar,
                fact: Some(unwrap_define(&a)),
            });
        }
    }
    if let Some(g) = quantified_grammar(v.arrays, v.terms, v.cap) {
        if let Some(a) = abduce_with_grammar(prelude, premises, goal, &g)? {
            return Ok(Verdict {
                shape: Shape::Quantified,
                fact: Some(unwrap_define(&a)),
            });
        }
    }
    match abduce(prelude, premises, goal)? {
        Some(a) => {
            let fact = unwrap_define(&a);
            let shape = if mentions_any(&fact, v.poststate) {
                Shape::Unusable
            } else {
                Shape::Outside
            };
            Ok(Verdict {
                shape,
                fact: Some(fact),
            })
        }
        None => Ok(Verdict {
            shape: Shape::Nothing,
            fact: None,
        }),
    }
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

    /// A malformed grammar must be an error, not an empty answer.
    ///
    /// This is the inert-measurement failure mode in its purest form. cvc5
    /// reports a bad grammar on stdout and carries on; `run_script` collects
    /// that text, no line contains `define-fun`, and the wrapper returned
    /// `Ok(None)` -- byte-identical to "no fact of this shape suffices". A
    /// census built on that reports a capability boundary wherever it has a
    /// typo. `docs/measurement-validity.md` is about exactly this shape.
    #[test]
    fn a_malformed_grammar_is_an_error_not_an_empty_answer() {
        let r = abduce_with_grammar(
            "(set-logic QF_LIA)\n(declare-fun i () Int)\n(declare-fun n () Int)",
            &["(and (<= 0 i) (< i n))"],
            "(< i n)",
            "((Start Bool)) ((Start Bool ((<= n THIS_SYMBOL_IS_NOT_DECLARED))))",
        );
        println!("malformed grammar -> {r:?}");
        assert!(
            r.is_err(),
            "a grammar naming an undeclared symbol came back as Ok, so a typo \
             is indistinguishable from a capability boundary"
        );
    }

    /// Priming must be token-wise. `v1` is a substring of `v1p` and of `v12`.
    #[test]
    fn priming_a_formula_does_not_corrupt_overlapping_names() {
        let syms: Vec<String> = ["v1", "v12", "ghost_len"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let got = prime_formula(
            "(and (<= v1 v12) (>= (select ghost_len v1) 0) (= v1p v1p))",
            &syms,
        );
        assert_eq!(
            got, "(and (<= v1p v12p) (>= (select ghost_lenp v1p) 0) (= v1p v1p))",
            "a substring rewrite would have produced v1p2 and v1pp"
        );
    }

    /// The frame detector, against the real clause that exposed the need for it.
    #[test]
    fn a_pure_frame_edge_is_recognised_and_a_guarded_one_is_not() {
        // Verbatim from `InsertionSort-FunSat01`, edge BlockId(18) -> BlockId(19).
        let frame = "(and (and (= arr5_2p arr5_2)) (= ghost_lenp ghost_len) \
                     (= v0p v0) (= v1p v1) (= v12p v12))";
        assert!(
            is_frame_only(frame),
            "the edge into the check block carries no guard and must be seen as such"
        );
        // The same shape with one branch condition added is a guard.
        let guarded = "(and (not (= v1 0)) (= v0p v0) (= v1p v1))";
        assert!(
            !is_frame_only(guarded),
            "a branch condition must stop the walk-back"
        );
        // An assignment is not a frame either: it constrains the post-state
        // from the pre-state in a way a fact can contradict.
        let assign = "(and (= v3p (+ v3 1)) (= v1p v1))";
        assert!(!is_frame_only(assign), "an assignment is not a frame");
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
