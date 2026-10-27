//! Interpolation support for IMC and CEGAR.
//!
//! Shells out to an interpolation-capable solver (Z3 or SMTInterpol) in batch
//! mode and returns Craig interpolants for partitioned formulas. Uses QF_LIA
//! (linear integer arithmetic) since bitvector interpolation is not widely
//! supported.
//!
//! Both IMC and CEGAR depend on this module.

use std::io::Write as IoWrite;
use std::process::{Command, Stdio};

use log::{debug, trace};

use crate::smt_text::{self, LiaTheory, SmtTheory};

/// Result of an interpolation query.
#[derive(Debug)]
pub enum InterpolationResult {
    /// The conjunction is UNSAT and an interpolant was computed.
    Interpolant(String),
    /// The conjunction is SAT (no interpolant).
    Sat,
    /// The solver doesn't support interpolation or returned an error.
    Unsupported,
}

/// Find an interpolation-capable solver binary.
/// Prefers SMTInterpol (java -jar) if available, falls back to Z3.
pub fn find_interpolation_solver() -> Option<InterpolationSolver> {
    // Cached: the probe spawns a solver process, and this is called more than
    // once per run (the engine constructs one, and `available()` consults it).
    // Paying for a z3 spawn per call on every one of 1,784 tasks is not free,
    // and the answer cannot change within a process.
    static FOUND: std::sync::OnceLock<Option<InterpolationSolver>> = std::sync::OnceLock::new();
    FOUND.get_or_init(probe_interpolation_solver).clone()
}

fn probe_interpolation_solver() -> Option<InterpolationSolver> {
    // Probe the *capability*, not the binary.
    //
    // This used to return `Some(Z3)` whenever `z3 --version` succeeded, which
    // is true on every machine that has z3 at all and says nothing about
    // interpolation. **Z3 removed interpolation support** — on 4.16.0,
    // `produce_interpolants` is not even a legal parameter — so the engine was
    // handed a solver that failed on every single call with
    // `Err("interpolation not supported")`, and `imc.rs` discarded that error
    // with `if let Ok(..)`. The engine ran, proved nothing, and reported
    // nothing; the census recorded it on 1 of 121 tasks discharging 0 and that
    // was read as gating rather than as total failure (#43).
    //
    // A capability check that cannot fail is not a capability check.
    if let Ok(out) = Command::new("z3")
        .args(["-in", "-smt2"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut c| {
            use std::io::Write;
            if let Some(mut si) = c.stdin.take() {
                let _ = si.write_all(
                    b"(set-option :produce-interpolants true)\n                      (declare-fun x () Int)\n                      (assert (! (> x 5) :named a))\n                      (assert (! (< x 3) :named b))\n                      (check-sat)\n(get-interpolant a b)\n",
                );
            }
            c.wait_with_output()
        })
    {
        let text = String::from_utf8_lossy(&out.stdout);
        let errs = String::from_utf8_lossy(&out.stderr);
        if !text.contains("unknown parameter")
            && !errs.contains("unknown parameter")
            && !text.contains("unsupported")
        {
            return Some(InterpolationSolver::Z3("z3".to_string()));
        }
        log::warn!(
            "imc: z3 is present but cannot interpolate (support was removed \
             upstream); the interpolation engine will not run. Install \
             SMTInterpol and set AJAVE_SMTINTERPOL_JAR to enable it."
        );
    }

    // SMTInterpol, which does support interpolation. The `SmtInterpol` variant
    // existed from the start and nothing ever looked for it, so it was dead.
    if let Ok(jar) = std::env::var("AJAVE_SMTINTERPOL_JAR") {
        if std::path::Path::new(&jar).is_file() {
            return Some(InterpolationSolver::SmtInterpol(jar));
        }
        log::warn!("imc: AJAVE_SMTINTERPOL_JAR={jar} is not a file; ignoring");
    }
    None
}

#[derive(Clone, Debug)]
pub enum InterpolationSolver {
    Z3(String),
    SmtInterpol(String), // path to JAR
}

impl InterpolationSolver {
    /// Compute a Craig interpolant for two partitions A and B.
    ///
    /// Given that A ∧ B is UNSAT, returns I such that A ⟹ I and I ∧ B is UNSAT.
    /// All formulas use QF_LIA (integer arithmetic).
    pub fn interpolate(
        &self,
        declarations: &str,
        formula_a: &str,
        formula_b: &str,
    ) -> InterpolationResult {
        match self {
            InterpolationSolver::Z3(binary) => {
                interpolate_z3(binary, declarations, formula_a, formula_b)
            }
            InterpolationSolver::SmtInterpol(jar) => {
                interpolate_smtinterpol(jar, declarations, formula_a, formula_b)
            }
        }
    }

    /// Compute a sequence of interpolants for a path formula.
    ///
    /// Given partitions [P0, P1, ..., Pn] such that their conjunction is UNSAT,
    /// returns [I1, ..., In] where:
    ///   P0 ⟹ I1
    ///   I_k ∧ P_k ⟹ I_{k+1}
    ///   I_n ∧ P_n is UNSAT
    pub fn sequence_interpolants(
        &self,
        declarations: &str,
        partitions: &[String],
    ) -> Result<Vec<String>, String> {
        if partitions.len() < 2 {
            return Ok(vec![]);
        }

        let mut interpolants = Vec::new();
        for k in 1..partitions.len() {
            let prefix = if k == 1 {
                partitions[0].clone()
            } else {
                format!("(and {})", partitions[..k].join(" "))
            };
            let suffix = if k == partitions.len() - 1 {
                partitions[k].clone()
            } else {
                format!("(and {})", partitions[k..].join(" "))
            };

            match self.interpolate(declarations, &prefix, &suffix) {
                InterpolationResult::Interpolant(itp) => interpolants.push(itp),
                InterpolationResult::Sat => {
                    return Err("path formula is SAT at cut point".to_string())
                }
                InterpolationResult::Unsupported => {
                    return Err("interpolation not supported by solver".to_string())
                }
            }
        }
        Ok(interpolants)
    }
}

fn interpolate_z3(
    binary: &str,
    declarations: &str,
    formula_a: &str,
    formula_b: &str,
) -> InterpolationResult {
    // Z3 4.12+ supports (get-interpolant <name> <formula>).
    // The formula specifies what goes in partition A; everything else is B.
    let script = format!(
        "(set-logic QF_LIA)\n\
         {declarations}\n\
         (assert (! {formula_a} :named partA))\n\
         (assert (! {formula_b} :named partB))\n\
         (check-sat)\n\
         (get-interpolant itp partA)\n\
         (exit)\n"
    );

    trace!("interpolation script:\n{}", script);

    match run_solver_batch(binary, &["-in", "-smt2"], &script) {
        Ok(lines) => parse_interpolant_response(&lines),
        Err(e) => {
            debug!("z3 interpolation failed: {}", e);
            InterpolationResult::Unsupported
        }
    }
}

fn interpolate_smtinterpol(
    jar_path: &str,
    declarations: &str,
    formula_a: &str,
    formula_b: &str,
) -> InterpolationResult {
    let script = format!(
        "(set-option :produce-interpolants true)\n\
         (set-logic QF_LIA)\n\
         {declarations}\n\
         (assert (! {formula_a} :named partA))\n\
         (assert (! {formula_b} :named partB))\n\
         (check-sat)\n\
         (get-interpolants partA partB)\n\
         (exit)\n"
    );

    match run_solver_batch("java", &["-jar", jar_path], &script) {
        Ok(lines) => parse_interpolant_response(&lines),
        Err(e) => {
            debug!("smtinterpol interpolation failed: {}", e);
            InterpolationResult::Unsupported
        }
    }
}

/// Public wrapper for running a solver script in batch mode.
pub fn run_solver_batch_pub(
    binary: &str,
    args: &[&str],
    script: &str,
) -> Result<Vec<String>, String> {
    run_solver_batch(binary, args, script)
}

fn run_solver_batch(binary: &str, args: &[&str], script: &str) -> Result<Vec<String>, String> {
    let mut child = Command::new(binary)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn {}: {}", binary, e))?;

    {
        let stdin = child.stdin.as_mut().ok_or("no stdin")?;
        stdin
            .write_all(script.as_bytes())
            .map_err(|e| format!("write failed: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("wait failed: {}", e))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    Ok(stdout.lines().map(|s| s.trim().to_string()).collect())
}

fn parse_interpolant_response(lines: &[String]) -> InterpolationResult {
    if lines.is_empty() {
        return InterpolationResult::Unsupported;
    }

    match lines[0].as_str() {
        "sat" => InterpolationResult::Sat,
        "unsat" => {
            // Look for the interpolant in subsequent lines.
            // Skip "unsat", any empty lines, and error/unsupported messages.
            for line in &lines[1..] {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                if trimmed == "unsupported"
                    || trimmed.starts_with("(error")
                    || trimmed.starts_with(";")
                {
                    debug!("interpolation unsupported: {}", trimmed);
                    return InterpolationResult::Unsupported;
                }
                // The interpolant is an S-expression (possibly multi-line).
                // For now handle single-line interpolants.
                return InterpolationResult::Interpolant(trimmed.to_string());
            }
            InterpolationResult::Unsupported
        }
        _ => {
            debug!("unexpected interpolation response: {}", lines[0]);
            InterpolationResult::Unsupported
        }
    }
}

/// Encode a method body's transition relation in QF_LIA format.
///
/// Returns (declarations, transition_formula, init_formula, error_formulas).
/// Variables are encoded as integers (not bitvectors) since interpolation
/// requires LIA.
/// Which array allocation site each reference variable names, within one body.
///
/// Deliberately tiny and deliberately conservative. A variable assigned from
/// exactly one `NewArray` site names that site; a copy inherits its source's;
/// anything else, or a variable that could name two sites, names **none** and
/// every read through it stays unconstrained.
///
/// That last case is the whole soundness argument. A `select` on the wrong
/// array is a fact about a different program, and an engine publishing `Over`
/// cannot afford one — so an ambiguous reference buys nothing rather than
/// guessing. A points-to analysis worth the name would do better; this is the
/// cheapest thing that is *correct*, and the loss is precision only.
///
/// A site is not an object: a `newarray` in a loop produces many arrays at one
/// site, and they share a cell here. That conflation is an over-approximation
/// in the direction a proof needs, because a claim about the cell must then
/// hold for every array the site produced.
pub fn array_sites_of(
    body: &ajave_ir::Body,
) -> std::collections::BTreeMap<ajave_ir::VarId, ajave_ir::AllocSite> {
    use ajave_ir::{Operand, Rvalue, Stmt};
    let mut out: std::collections::BTreeMap<ajave_ir::VarId, ajave_ir::AllocSite> =
        std::collections::BTreeMap::new();
    let mut ambiguous: std::collections::BTreeSet<ajave_ir::VarId> = Default::default();

    // Two passes so a copy from a variable defined later still resolves.
    for _ in 0..2 {
        for block in &body.blocks {
            for st in &block.stmts {
                let Stmt::Assign(v, rv) = st else { continue };
                let found = match rv {
                    Rvalue::NewArray { site, .. } => Some(*site),
                    Rvalue::Use(Operand::Var(w)) => out.get(w).copied(),
                    _ => None,
                };
                match found {
                    Some(site) => match out.get(v) {
                        Some(prev) if *prev != site => {
                            ambiguous.insert(*v);
                        }
                        _ => {
                            out.insert(*v, site);
                        }
                    },
                    // Assigned from something that is not a known array: the
                    // variable may name anything, so it names nothing.
                    None => {
                        if matches!(rv, Rvalue::NewArray { .. }) {
                        } else if out.contains_key(v) {
                            ambiguous.insert(*v);
                        }
                    }
                }
            }
        }
    }
    for v in ambiguous {
        out.remove(&v);
    }
    out
}

/// The allocation site an operand names, if exactly one.
pub fn operand_site(
    op: &ajave_ir::Operand,
    sites: &std::collections::BTreeMap<ajave_ir::VarId, ajave_ir::AllocSite>,
) -> Option<ajave_ir::AllocSite> {
    match op {
        ajave_ir::Operand::Var(v) => sites.get(v).copied(),
        _ => None,
    }
}

pub fn encode_body_lia(
    body: &ajave_ir::Body,
    obligations: &[ajave_ir::ObligationId],
    prefix: &str,
) -> LiaEncoding {
    use ajave_ir::*;

    let theory = LiaTheory::new(prefix);
    let n_vars = body.vars.len();

    // Variable declarations: pre-state and post-state.
    let mut decls = String::new();
    for i in 0..n_vars {
        decls.push_str(&format!("(declare-fun {prefix}v{i} () Int)\n"));
        decls.push_str(&format!("(declare-fun {prefix}v{i}p () Int)\n"));
    }
    // One SMT array per allocation site, threaded pre-state to post-state
    // exactly as the locals are. Before this, `ArrayLoad` fell through to a
    // fresh unconstrained constant, so two reads of the same element were
    // unrelated and nothing about array contents could be proved — the
    // regression #95 measured as valid-assert 867 -> 860, where the losses
    // were `unsat` answers that stopped being provable rather than timeouts.
    // One SMT array per field name, indexed by the receiver reference
    // (Burstall field-as-array). Aliasing is then the solver's: `o.f` and
    // `p.f` are the same cell exactly when `o = p`, so this needs no
    // points-to analysis — unlike arrays, whose identity has to come from the
    // allocation site because the IR gives a reference no array sort.
    let mut fields: std::collections::BTreeSet<ajave_ir::FieldKey> = Default::default();
    for block in &body.blocks {
        for st in &block.stmts {
            match st {
                ajave_ir::Stmt::PutField { field, .. } => {
                    fields.insert(field.clone());
                }
                ajave_ir::Stmt::Assign(_, ajave_ir::Rvalue::GetField { field, .. }) => {
                    fields.insert(field.clone());
                }
                _ => {}
            }
        }
    }
    // A float-valued field cannot live in an `(Array Int Int)`, and claiming
    // otherwise would let the checker confirm something it cannot state.
    fields.retain(|f| f.desc != "D" && f.desc != "F");
    let fld_name = crate::invariant_check::field_array_name;
    for f in &fields {
        decls.push_str(&format!(
            "(declare-fun {} () (Array Int Int))\n",
            fld_name(f)
        ));
        decls.push_str(&format!(
            "(declare-fun {}p () (Array Int Int))\n",
            fld_name(f)
        ));
    }

    let array_sites = array_sites_of(body);
    let sites: std::collections::BTreeSet<ajave_ir::AllocSite> =
        array_sites.values().copied().collect();
    let arr_name = |site: &ajave_ir::AllocSite, post: bool| {
        format!(
            "{prefix}arr{}_{}{}",
            site.block.0,
            site.index,
            if post { "p" } else { "" }
        )
    };
    for site in &sites {
        decls.push_str(&format!(
            "(declare-fun {} () (Array Int Int))\n",
            arr_name(site, false)
        ));
        decls.push_str(&format!(
            "(declare-fun {} () (Array Int Int))\n",
            arr_name(site, true)
        ));
    }

    // Build per-block transition clauses.
    let mut block_clauses: Vec<String> = Vec::new();
    let mut error_clauses: Vec<(ObligationId, String)> = Vec::new();

    for block in &body.blocks {
        let mut var_exprs: Vec<String> = (0..n_vars).map(|i| format!("{prefix}v{i}")).collect();
        let mut path_conds: Vec<String> = Vec::new();

        // Track whether this block is the entry block.
        let _is_entry = block.id == body.entry;

        // One encoder per block. It owns naming, records the binders it
        // introduces, and collects overflow side conditions -- which this
        // encoder previously did not collect at all, so its proofs held only
        // for unbounded integers and not for Java's 32-bit arithmetic.
        let mut enc = smt_text::Encoder::new(&theory, &format!("{prefix}e{}_", block.id.0));
        // Collected into `declarations` at the end of the block, below.
        //
        // They were not collected at all before, which `invariant_check`'s
        // preservation query silently depended on being harmless: a
        // fresh binder appeared in the transition relation and nowhere else,
        // so z3 reported `unknown constant`, *dropped that whole assertion*,
        // and answered `sat` on what was left. The query then read as "the
        // invariant is not preserved" when it had never been checked.
        //
        // It stayed hidden because the post-state renderer only prefixed
        // variables, so the preservation check was `inv ∧ T ∧ ¬inv` over one
        // state — trivially UNSAT, and therefore confirming regardless. Two
        // defects, each concealing the other.
        let is_wide = |op: &Operand| -> bool {
            match op {
                Operand::Const(Const::Long(_)) | Operand::Const(Const::Double(_)) => true,
                Operand::Var(v) => body
                    .vars
                    .get(v.0 as usize)
                    .map(|vi| vi.ty.is_wide())
                    .unwrap_or(false),
                _ => false,
            }
        };

        // Current symbolic value of each site's array, starting at its
        // pre-state constant and rewritten by each store.
        let mut arr_exprs: std::collections::BTreeMap<ajave_ir::AllocSite, String> =
            sites.iter().map(|st| (*st, arr_name(st, false))).collect();
        let mut fld_exprs: std::collections::BTreeMap<ajave_ir::FieldKey, String> =
            fields.iter().map(|f| (f.clone(), fld_name(f))).collect();
        // References produced by allocations in this block.
        //
        // The JLS guarantees `new` yields a reference distinct from every live
        // one and from null, and nothing here said so: each `New` became a
        // fresh *name* with no constraint relating it to the others, so the
        // solver was free to decide two separate allocations were the same
        // object. With field cells indexed by receiver that is immediately
        // visible — `o.f = 7; p.f = 99` then permits `o.f == 99` — and it is
        // the difference between modelling the heap's *storage* and modelling
        // its *identity*.
        let mut fresh_refs: Vec<String> = Vec::new();

        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(vid, rv) => {
                    // An element read resolves to a `select` on the site's
                    // array when the reference names exactly one site.
                    // Otherwise it falls through to the encoder's fresh
                    // constant, which is what every heap read used to do.
                    let expr = match rv {
                        // `o.f` is a select on the field's array at the
                        // receiver. No points-to needed: if the receiver is a
                        // variable, the solver relates it to any aliased name
                        // itself — which is the whole reason for this model.
                        Rvalue::GetField { field, obj } if fld_exprs.contains_key(field) => {
                            let cur = fld_exprs[field].clone();
                            let o = smt_text::encode_operand(&theory, obj, &var_exprs);
                            Some(format!("(select {cur} {o})"))
                        }
                        Rvalue::ArrayLoad { arr, idx } => {
                            match operand_site(arr, &array_sites)
                                .and_then(|st| arr_exprs.get(&st).cloned())
                            {
                                Some(cur) => {
                                    let i = smt_text::encode_operand(&theory, idx, &var_exprs);
                                    Some(format!("(select {cur} {i})"))
                                }
                                None => None,
                            }
                        }
                        _ => None,
                    };
                    let expr = match expr {
                        Some(e) => e,
                        None => enc.rvalue(rv, &var_exprs, &is_wide),
                    };
                    if matches!(rv, Rvalue::New { .. } | Rvalue::NewArray { .. }) {
                        // Pushed *here*, not after the loop: an error formula
                        // snapshots `path_conds` at its `Check`, so a
                        // condition added later never reaches it. An
                        // allocation's freshness holds from the allocation
                        // onward, which is exactly this point.
                        path_conds.push(format!("(not (= {expr} 0))"));
                        for prev in &fresh_refs {
                            path_conds.push(format!("(not (= {expr} {prev}))"));
                        }
                        fresh_refs.push(expr.clone());
                    }
                    var_exprs[vid.0 as usize] = expr;
                }
                Stmt::PutField { obj, field, val } => {
                    // A write to `o.f` cannot alter `o.g`, so only this
                    // field's array changes — unlike an array store through an
                    // unresolvable reference, which may land anywhere.
                    if fld_exprs.contains_key(field) {
                        let o = smt_text::encode_operand(&theory, obj, &var_exprs);
                        let v = smt_text::encode_operand(&theory, val, &var_exprs);
                        let cur = fld_exprs[field].clone();
                        fld_exprs.insert(field.clone(), format!("(store {cur} {o} {v})"));
                    }
                }
                Stmt::ArrayStore { arr, idx, val } => {
                    let i = smt_text::encode_operand(&theory, idx, &var_exprs);
                    let v = smt_text::encode_operand(&theory, val, &var_exprs);
                    match operand_site(arr, &array_sites) {
                        Some(st) => {
                            if let Some(cur) = arr_exprs.get(&st).cloned() {
                                arr_exprs.insert(st, format!("(store {cur} {i} {v})"));
                            }
                        }
                        // A store through a reference naming no single site
                        // may land in any array, so no site's contents
                        // survive it. Dropping only *some* of them would be
                        // the unsound direction.
                        None => {
                            for st in sites.iter() {
                                arr_exprs.insert(*st, arr_name(st, true));
                            }
                        }
                    }
                }
                Stmt::Assume(op) => {
                    let expr = smt_text::encode_operand(&theory, op, &var_exprs);
                    path_conds.push(theory.encode_nonzero(&expr));
                }

                Stmt::Check(oid) if obligations.contains(oid) => {
                    let ob = body.obligation(*oid);
                    let cond_expr = smt_text::encode_operand(&theory, &ob.cond, &var_exprs);
                    let mut econds = path_conds.clone();
                    econds.push(theory.encode_is_zero(&cond_expr));
                    let error_cond = if econds.is_empty() {
                        "true".to_string()
                    } else if econds.len() == 1 {
                        econds[0].clone()
                    } else {
                        format!("(and {})", econds.join(" "))
                    };
                    error_clauses.push((*oid, error_cond));
                }
                _ => {}
            }
        }

        // Overflow on a reachable path makes the program unsafe, so it belongs
        // in `error` alongside the obligation's own condition. Without this the
        // fixpoint proves the property only for unbounded integers, and Java's
        // are 32- and 64-bit: `x + 1 > x` holds in the encoding and fails on a
        // JVM. The conditions come from `Encoder`, shared with CHC so the two
        // cannot drift (#77).
        if !enc.side_conditions.is_empty() {
            let ovf = if enc.side_conditions.len() == 1 {
                enc.side_conditions[0].clone()
            } else {
                format!("(or {})", enc.side_conditions.join(" "))
            };
            let mut conds = path_conds.clone();
            conds.push(ovf);
            let cond = if conds.len() == 1 {
                conds[0].clone()
            } else {
                format!("(and {})", conds.join(" "))
            };
            for oid in obligations {
                error_clauses.push((*oid, cond.clone()));
            }
        }

        for (name, wide) in enc.binders.drain(..) {
            let _ = wide;
            if !decls.contains(&format!("(declare-fun {name} ")) {
                decls.push_str(&format!("(declare-fun {name} () Int)\n"));
            }
        }

        // Build successor transition clauses.
        let mk_assign = |var_exprs: &[String]| -> Vec<String> {
            let mut out: Vec<String> = var_exprs
                .iter()
                .enumerate()
                .filter_map(|(i, e)| {
                    let post = format!("{prefix}v{i}p");
                    if *e != post {
                        Some(format!("(= {} {})", post, e))
                    } else {
                        None
                    }
                })
                .collect();
            // Arrays are part of the state, so the post-state must say what
            // happened to them. Omitting this would leave `arr{site}p`
            // unconstrained, and an invariant about it could then be
            // "preserved" by a transition that in fact clobbers the array.
            for (st, cur) in arr_exprs.iter() {
                let post = arr_name(st, true);
                if *cur != post {
                    out.push(format!("(= {post} {cur})"));
                }
            }
            for (f, cur) in fld_exprs.iter() {
                let post = format!("{}p", fld_name(f));
                if *cur != post {
                    out.push(format!("(= {post} {cur})"));
                }
            }
            out
        };

        match &block.term {
            Terminator::Goto(_) | Terminator::Return(_) | Terminator::Halt => {
                let mut conds = path_conds.clone();
                conds.extend(mk_assign(&var_exprs));
                if !conds.is_empty() {
                    let clause = if conds.len() == 1 {
                        conds[0].clone()
                    } else {
                        format!("(and {})", conds.join(" "))
                    };
                    block_clauses.push(clause);
                }
            }
            Terminator::Branch { cond, .. } => {
                let cond_expr = smt_text::encode_operand(&theory, cond, &var_exprs);
                let assigns = mk_assign(&var_exprs);

                // Then branch: condition is nonzero.
                let mut then_conds = path_conds.clone();
                then_conds.push(theory.encode_nonzero(&cond_expr));
                then_conds.extend(assigns.iter().cloned());
                if !then_conds.is_empty() {
                    block_clauses.push(format!("(and {})", then_conds.join(" ")));
                }

                // Else branch: condition is zero.
                let mut else_conds = path_conds.clone();
                else_conds.push(theory.encode_is_zero(&cond_expr));
                else_conds.extend(assigns);
                if !else_conds.is_empty() {
                    block_clauses.push(format!("(and {})", else_conds.join(" ")));
                }
            }
            Terminator::Switch {
                value,
                cases,
                default: _,
            } => {
                let val_expr = smt_text::encode_operand(&theory, value, &var_exprs);
                let assigns = mk_assign(&var_exprs);
                let mut neg_cases = Vec::new();

                for (cv, _) in cases {
                    let mut case_conds = path_conds.clone();
                    case_conds.push(format!("(= {} {})", val_expr, cv));
                    case_conds.extend(assigns.iter().cloned());
                    block_clauses.push(format!("(and {})", case_conds.join(" ")));
                    neg_cases.push(format!("(not (= {} {}))", val_expr, cv));
                }

                // Default case.
                let mut def_conds = path_conds.clone();
                def_conds.extend(neg_cases);
                def_conds.extend(assigns);
                if !def_conds.is_empty() {
                    block_clauses.push(format!("(and {})", def_conds.join(" ")));
                }
            }
            _ => {}
        }
    }

    // The transition relation is the disjunction of all block clauses.
    let transition = if block_clauses.is_empty() {
        "true".to_string()
    } else if block_clauses.len() == 1 {
        block_clauses[0].clone()
    } else {
        format!("(or {})", block_clauses.join(" "))
    };

    // Error formula: disjunction of all error clauses.
    let error_formulas: Vec<(ObligationId, String)> = error_clauses;

    LiaEncoding {
        declarations: decls,
        transition,
        error_formulas,
        n_vars,
    }
}

pub struct LiaEncoding {
    pub declarations: String,
    pub transition: String,
    pub error_formulas: Vec<(ajave_ir::ObligationId, String)>,
    pub n_vars: usize,
}

/// Extract predicate atoms from an interpolant formula string.
///
/// Parses simple S-expression interpolants and extracts atomic comparisons
/// like `(< v0 5)`, `(= v1 v2)` etc. Used by CEGAR for predicate refinement.
pub fn extract_predicates_from_interpolant(itp: &str) -> Vec<String> {
    let mut predicates = Vec::new();
    extract_atoms(itp, &mut predicates);
    predicates
}

fn extract_atoms(expr: &str, out: &mut Vec<String>) {
    let expr = expr.trim();
    if expr.is_empty() {
        return;
    }

    // Check if this is an atomic comparison.
    if expr.starts_with('(') {
        let inner = &expr[1..expr.len().saturating_sub(1)];
        let op = inner.split_whitespace().next().unwrap_or("");
        match op {
            "<" | "<=" | ">" | ">=" | "=" => {
                out.push(expr.to_string());
                return;
            }
            "and" | "or" | "not" => {
                // Recurse into sub-expressions.
                let args = split_sexp_args(&inner[op.len()..]);
                for arg in args {
                    extract_atoms(&arg, out);
                }
                return;
            }
            _ => {}
        }
    }
    // Not a recognized form; treat the whole thing as a predicate if non-trivial.
    if expr != "true" && expr != "false" {
        out.push(expr.to_string());
    }
}

/// Split an S-expression argument list into individual sub-expressions.
fn split_sexp_args(s: &str) -> Vec<String> {
    let s = s.trim();
    let mut args = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    let bytes = s.as_bytes();

    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' | b'\n' | b'\t' if depth == 0 => {
                let arg = s[start..i].trim();
                if !arg.is_empty() {
                    args.push(arg.to_string());
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    let arg = s[start..].trim();
    if !arg.is_empty() {
        args.push(arg.to_string());
    }
    args
}
