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
/// Returns a `LiaEncoding`: declarations, the monolithic transition relation,
/// the same clauses tagged per CFG edge, and one error formula per obligation.
/// There is no init formula — a method's entry state is its parameters, which
/// are unconstrained — and the doc claimed one for a long time.
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
/// Every array allocation site in a body.
///
/// Distinct from `array_sites_of().values()`, which was being used for this and
/// is wrong for it. That map drops a variable the moment it becomes ambiguous,
/// so a body whose only array variable is a reused slot produced an **empty**
/// site set — and then the encoder threaded no array state at all, compiling
/// each load to a fresh unconstrained constant.
///
/// Which site set a body has is a whole-body, syntactic fact. Whether a
/// particular *use* resolves to one of them is a flow question, and
/// `array_sites_at_block_entry` is what answers that. Using one map for both
/// let an ambiguity at a use delete the state the other uses needed.
pub fn array_sites_in(body: &ajave_ir::Body) -> Vec<ajave_ir::AllocSite> {
    use ajave_ir::{Rvalue, Stmt};
    let mut v: Vec<ajave_ir::AllocSite> = Vec::new();
    for block in &body.blocks {
        for st in &block.stmts {
            if let Stmt::Assign(_, Rvalue::NewArray { site, .. }) = st {
                v.push(*site);
            }
        }
    }
    v.sort();
    v.dedup();
    v
}

/// Flow-sensitive allocation sites: which array each reference *names at each
/// program point*, rather than one answer per variable for the whole body.
///
/// # Why this exists, and what it cost before
///
/// `array_sites_of` gives one answer per `VarId`, and marks a variable
/// ambiguous the moment it is assigned from anything that is not a known
/// array. That is correct as a whole-body statement and useless in practice,
/// because **javac reuses local slots**. In
///
/// ```text
/// A[] a = new A[3];
/// for (int i = 0; i < 3; i++) { a[i] = new A(); }
/// for (int i = 0; i < 3; i++) { assert a[i] != null; }
/// ```
///
/// the lifted body assigns one slot the array, then an *element* of it, then
/// an `AssertionError`. The variable the store goes through is therefore
/// ambiguous and the store havocs every array, while the reads happen to go
/// through a different variable that is not reused and so resolve fine.
///
/// The CHC encoding for that program contained **twenty** uses of the havoc
/// destination and **zero** `store`s: it read an array it never wrote. Every
/// element therefore read as unconstrained, including null, so the assertion
/// was reachable and the program was reported unprovable — with a *constant*
/// loop bound, where no quantified invariant is needed at all.
///
/// This is what made modelling array contents worth nothing in this engine.
/// Expressibility was never the gate.
///
/// # The analysis
///
/// A forward dataflow over `VarId -> AllocSite`, with join by agreement: a
/// variable keeps a site only if every predecessor agrees on it. Absence means
/// "may name any array", which is what every consumer must treat
/// conservatively — and is what `operand_site` returning `None` already means.
///
/// Returned per block entry; a consumer walking a block's statements updates
/// its copy with `update_sites_for` as it goes, which is exactly how the
/// encoders already traverse.
pub fn array_sites_at_block_entry(
    body: &ajave_ir::Body,
) -> std::collections::BTreeMap<ajave_ir::BlockId, SiteMap> {
    use std::collections::BTreeMap;
    let mut entry: BTreeMap<ajave_ir::BlockId, SiteMap> = BTreeMap::new();
    for b in &body.blocks {
        entry.insert(b.id, SiteMap::new());
    }

    // Successors including exceptional edges: a handler is reachable from the
    // block it guards, and giving it an empty-but-not-bottom map would let it
    // claim a site no predecessor established.
    let succs = |b: &ajave_ir::Block| -> Vec<ajave_ir::BlockId> {
        use ajave_ir::Terminator::*;
        let mut v = match &b.term {
            Goto(t) => vec![*t],
            Branch { then_, else_, .. } => vec![*then_, *else_],
            Switch { cases, default, .. } => {
                let mut c: Vec<_> = cases.iter().map(|(_, t)| *t).collect();
                c.push(*default);
                c
            }
            // `Return`, `Throw`, `Halt` and `Diverge` leave the body. For
            // `Diverge` in particular there is nothing to propagate *to*: the
            // lift stopped, and a successor map that invented one would be
            // claiming knowledge about code nobody read.
            Return(_) | Throw(_) | Halt | Diverge(_) => vec![],
        };
        v.extend(b.exceptional.iter().map(|e| e.target));
        v
    };

    // `None` distinguishes "not yet reached" from "reached, knows nothing".
    // Without it the entry block's empty map would look like a predecessor
    // that disagrees with everything, and no site would ever propagate.
    let mut reached: BTreeMap<ajave_ir::BlockId, bool> =
        body.blocks.iter().map(|b| (b.id, false)).collect();
    reached.insert(body.entry, true);

    // Bounded by the block count: each round can only shrink a map or mark one
    // block reached, and both are monotone over a finite domain.
    for _ in 0..=body.blocks.len() {
        let mut changed = false;
        for b in &body.blocks {
            if !reached[&b.id] {
                continue;
            }
            let mut out = entry[&b.id].clone();
            for st in &b.stmts {
                update_sites_for(&mut out, st);
            }
            for s in succs(b) {
                let merged = if reached[&s] {
                    // Join by agreement: keep only what both sides assert, with
                    // the same site. A disagreement is a variable that names
                    // different arrays on different paths, so it names none.
                    out.iter()
                        .filter(|(v, site)| entry[&s].get(v) == Some(*site))
                        .map(|(v, site)| (*v, *site))
                        .collect()
                } else {
                    out.clone()
                };
                if !reached[&s] || merged != entry[&s] {
                    entry.insert(s, merged);
                    reached.insert(s, true);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    entry
}

/// `VarId -> AllocSite` at one program point. Absence means "may name any
/// array", never "names no array".
pub type SiteMap = std::collections::BTreeMap<ajave_ir::VarId, ajave_ir::AllocSite>;

/// Apply one statement's effect on which array each variable names.
///
/// Every assignment must be handled, including the ones that destroy
/// knowledge: a slot reassigned from an element load or a `new` of a
/// non-array no longer names the array it did, and leaving the stale entry is
/// the unsound direction — it would let a store be attributed to an array the
/// variable no longer points at.
pub fn update_sites_for(map: &mut SiteMap, st: &ajave_ir::Stmt) {
    use ajave_ir::{Operand, Rvalue, Stmt};
    let Stmt::Assign(v, rv) = st else { return };
    match rv {
        Rvalue::NewArray { site, .. } => {
            map.insert(*v, *site);
        }
        Rvalue::Use(Operand::Var(w)) => match map.get(w).copied() {
            Some(site) => {
                map.insert(*v, site);
            }
            None => {
                map.remove(v);
            }
        },
        // Anything else: the variable now holds something we cannot attribute
        // to a site.
        _ => {
            map.remove(v);
        }
    }
}

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

    // The ghost length array, declared unconditionally.
    //
    // In `declarations` rather than in `ghost_preamble` because the term
    // `(select ghost_len a)` appears in the *transition relation* -- that is
    // the whole point of P2, and an undeclared symbol makes z3 report an
    // unknown constant and **drop the whole assertion**, which for `imc` and
    // `cegar` would silently discard the transition relation. Its
    // *assumptions* stay in `ghost_preamble`; a declaration is about sorts, an
    // axiom is about values, and only the second changes what a consumer that
    // does not opt in may conclude.
    //
    // Unconditional, not only for bodies that allocate: an array-typed
    // parameter has no allocation site in this body and its length is still a
    // thing an invariant may talk about.
    // **Unprefixed**, matching `field_array_name` and `depth_array_name` rather
    // than `arr_name`. That looks inconsistent and is the deliberate choice:
    // `invariant_check::render` spells ghost symbols without a prefix, so a
    // prefixed declaration here would make the checker read a different array
    // from the one the transition relation writes. Producer and consumer
    // disagreeing about a symbol is the fault the comments on `Select` and
    // `Field` exist to prevent, and `Expr::Depth` is what it looks like when
    // it happens. Every caller passes `""` today, so this is latent — which is
    // exactly when to get it right. `the_checker_and_the_encoder_spell_the_length_array_alike`
    // is the test.
    let len_pre = crate::invariant_check::LENGTH_ARRAY.to_string();
    let len_post = format!("{len_pre}p");
    decls.push_str(&format!("(declare-fun {len_pre} () (Array Int Int))\n"));
    decls.push_str(&format!("(declare-fun {len_post} () (Array Int Int))\n"));

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
    // The same clauses, tagged with the edge each one takes.
    //
    // `transition` is their disjunction and stays byte-identical, so `imc` and
    // `cegar` are unaffected. This exists because checking an invariant *map*
    // needs per-edge preservation — "the assertion at the source, this
    // transition, therefore the assertion at the target" — and the disjunction
    // cannot express that: the encoding has no program counter, so a monolithic
    // relation cannot say which point it is at. Adding a pc would change the
    // relation every other consumer reasons about; tagging what is already
    // built does not.
    //
    // `None` as the target means control leaves the method (return, throw,
    // halt), so there is no successor assertion to preserve.
    let mut edge_clauses: Vec<EdgeClause> = Vec::new();
    let mut error_clauses: Vec<(ObligationId, String)> = Vec::new();

    for block in &body.blocks {
        // Where this block's edges begin, so the per-edge fields can be filled
        // in **one** place at the end of the iteration rather than at each of
        // the six `push` sites. A field set at six sites is a field forgotten
        // at one of them, and the one that matters is `overflow`.
        let edges_before = edge_clauses.len();
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
        // The operand's JVM type, which answers both of `Encoder`'s questions:
        // the width an overflow condition is computed at, and whether the
        // operand is floating-point. The second is what enforces the float
        // quarantine (`docs/proposals/lia-faithfulness.md` §2.2); this closure
        // used to answer only the first, and that is why floats leaked into
        // integer terms here.
        let operand_ty = |op: &Operand| -> Option<ajave_ir::Ty> {
            smt_text::operand_ty(body, op)
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
                        // `a.length`, as a read of the ghost array at the
                        // receiver. Before this there was no arm at all: it
                        // fell through to `Encoder::rvalue`'s `_ => fresh`, so
                        // two reads of one array's length were *unrelated*
                        // integers, `new int[n]` did not relate the array to
                        // `n`, and the JVMS guarantee `length >= 0` was absent.
                        // `invariant_check::render` therefore had to decline
                        // `Expr::Length`, which dropped every length fact the
                        // interval domain publishes.
                        //
                        // This strengthens `transition`, which `imc` and
                        // `cegar` consume, and the strengthening is sound: for
                        // a fixed receiver `(select ghost_len a)` is as
                        // unconstrained as the fresh binder it replaces, so the
                        // only states it removes are ones where a single array
                        // has two different lengths, and those are not JVM
                        // states.
                        Rvalue::ArrayLength(o) => {
                            let r = smt_text::encode_operand(&theory, o, &var_exprs);
                            Some(format!("(select {len_pre} {r})"))
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
                        None => enc.rvalue(rv, &var_exprs, &operand_ty),
                    };
                    // `new T[n]` fixes the array's length to `n`, and on the
                    // normal continuation that length is non-negative.
                    //
                    // The second is not an extra assumption about `n`: if
                    // `n < 0` the JVM throws `NegativeArraySizeException` and
                    // there is no array, so the normal successor is
                    // unreachable. The throwing behaviour stays
                    // over-approximated by the block's exceptional edge (whose
                    // clause is `true`) and by the `NegArraySize` obligation's
                    // error formula.
                    //
                    // In `path_conds` for the same reason the freshness facts
                    // are: an error formula snapshots them at its `Check`, so a
                    // fact added after the loop never reaches it, and these
                    // hold from the allocation onward.
                    if let Rvalue::NewArray { len, .. } = rv {
                        let n = smt_text::encode_operand(&theory, len, &var_exprs);
                        path_conds.push(format!("(= (select {len_pre} {expr}) {n})"));
                        path_conds.push(format!("(>= (select {len_pre} {expr}) 0)"));
                    }
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
        let block_overflow: Option<String> = if enc.side_conditions.is_empty() {
            None
        } else if enc.side_conditions.len() == 1 {
            Some(enc.side_conditions[0].clone())
        } else {
            Some(format!("(or {})", enc.side_conditions.join(" ")))
        };
        if let Some(ovf) = block_overflow.clone() {
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
                    let to = match &block.term {
                        Terminator::Goto(t) => Some(*t),
                        _ => None,
                    };
                    edge_clauses.push(EdgeClause::new(block.id, to, clause.clone()));
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
                    let c = format!("(and {})", then_conds.join(" "));
                    if let Terminator::Branch { then_, .. } = &block.term {
                        edge_clauses.push(EdgeClause::new(block.id, Some(*then_), c.clone()));
                    }
                    block_clauses.push(c);
                }

                // Else branch: condition is zero.
                let mut else_conds = path_conds.clone();
                else_conds.push(theory.encode_is_zero(&cond_expr));
                else_conds.extend(assigns);
                if !else_conds.is_empty() {
                    let c = format!("(and {})", else_conds.join(" "));
                    if let Terminator::Branch { else_, .. } = &block.term {
                        edge_clauses.push(EdgeClause::new(block.id, Some(*else_), c.clone()));
                    }
                    block_clauses.push(c);
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

                for (cv, target) in cases {
                    let mut case_conds = path_conds.clone();
                    case_conds.push(format!("(= {} {})", val_expr, cv));
                    case_conds.extend(assigns.iter().cloned());
                    let c = format!("(and {})", case_conds.join(" "));
                    edge_clauses.push(EdgeClause::new(block.id, Some(*target), c.clone()));
                    block_clauses.push(c);
                    neg_cases.push(format!("(not (= {} {}))", val_expr, cv));
                }

                // Default case.
                let mut def_conds = path_conds.clone();
                def_conds.extend(neg_cases);
                def_conds.extend(assigns);
                if !def_conds.is_empty() {
                    let c = format!("(and {})", def_conds.join(" "));
                    if let Terminator::Switch { default, .. } = &block.term {
                        edge_clauses.push(EdgeClause::new(block.id, Some(*default), c.clone()));
                    }
                    block_clauses.push(c);
                }
            }
            _ => {}
        }

        // Exceptional edges, with an **unconstrained** post-state.
        //
        // Without these, `edge_clauses` describes normal control flow only,
        // and an invariant map checked against it is inductive *over normal
        // edges* while a consumer reads it as "true at this block". Those
        // differ exactly where exceptions flow, and for the
        // no-runtime-exception property that is the whole property. It
        // produced a wrong TRUE on `algorithms/BellmanFord-FunUnsat01`: a
        // bound survived elimination at a handler block where it does not
        // hold, the BMC pruned on it as a hint, and claimed
        // `all_paths_complete` over a search that had missed the throwing
        // path. See `benchmarks/ajave/engine-ai/
        // AnInvariantAtAHandlerMustSurviveTheThrow`.
        //
        // The clause is deliberately vacuous rather than modelled. An
        // exception may be raised at any point inside the block, so the state
        // at the handler is the block's entry state with an arbitrary prefix
        // of its writes applied — and enumerating those prefixes would be a
        // second encoder. Leaving the post-state unconstrained over-deletes
        // candidates at handler blocks, which is the sound direction: a
        // candidate survives there only if it is valid.
        //
        // Deliberately NOT added to `transition`. That formula is shared with
        // `imc` and `cegar`, and widening it would change what they reason
        // about. The consequence is that `check_inductive`, which uses
        // `transition`, keeps this hole for single-point claims — recorded as
        // an issue rather than fixed silently here.
        for exc in &block.exceptional {
            edge_clauses.push(EdgeClause::new(block.id, Some(exc.target), "true".to_string()));
        }

        // The per-edge fields, in one place for every edge out of this block.
        //
        // `ghost`: the length array is immutable (JVMS §6.5), so its only
        // threading constraint is the identity. It is carried here rather than
        // through `mk_assign` so that `transition` -- which `imc` and `cegar`
        // consume -- is not widened with a post-state they never read.
        //
        // `overflow`: the block's own arithmetic conditions, which
        // `preservation_query` turns into a second disjunct of the transition
        // with an unconstrained post-state — overflow as an exceptional edge.
        // The exceptional edges get it too, which is inert there: their clause
        // is already `true`, and `true ∨ ovf` is `true`.
        for e in edge_clauses[edges_before..].iter_mut() {
            e.ghost.push(format!("(= {len_post} {len_pre})"));
            e.overflow = block_overflow.clone();
        }
    }

    // `ghost_preamble`: the assumptions the *edge* encoding rests on.
    //
    // Kept out of `declarations` so `imc` and `cegar` are unaffected. They are
    // sound for them too -- every axiom here removes only states no JVM can
    // represent -- but "sound for them" is not "measured for them", and an
    // over-approximating engine's proofs are what would change.
    let mut ghost_preamble = String::new();

    // # Integer range axioms, and why (P) is vacuous without them
    //
    // LIA integers are unbounded and nothing here said otherwise. So guarded
    // preservation on `x := x + 1` asks whether `x + 1 > 2147483647` is
    // possible given whatever the invariant says, and in LIA a bound like
    // `x < n` does not help because `n` may be 2^40. It is always possible, so
    // every candidate dies and the empty map is the only fixpoint for any
    // method containing arithmetic. P3 and P4 are only meaningful together.
    //
    // **Soundness.** Every value a JVM local of type `int` can hold lies in
    // [-2^31, 2^31-1] (JVMS §2.3.1), and a `long` in the 64-bit range, so the
    // axiom removes no reachable state. It restricts the LIA state space to a
    // superset of -- in fact, on these coordinates, exactly -- the JVM's. An
    // over-approximating proof over a superset is sound.
    //
    // It is also a precision *gain* for initiation: an entry assertion now
    // only has to hold of states a JVM can represent.
    //
    // Three deliberate omissions, each conservative (see
    // `docs/proposals/lia-faithfulness.md` §4):
    //
    // * **Binders are not constrained.** `Encoder::binders` records a sort,
    //   not a width, and `LiaTheory::sort_of` answers `Int` for both, so the
    //   information is not recoverable here. Unconstrained is loose, hence
    //   sound -- and the axiom reaches a binder anyway exactly where it is
    //   justified: `v := binder` on an edge yields `v' = binder` beside
    //   `range(v')`, which bounds the binder because it was stored into a
    //   typed variable.
    // * **References are not constrained.** `Ty::Ref`/`Str` are abstract
    //   identifiers with `0` for null, not JVM integers. Bounding them would
    //   be a claim about a representation this encoding invented.
    // * **Array and field cells are not constrained.** That needs a
    //   quantifier, and a quantifier in every query risks `unknown`, which
    //   refuses the proof.
    let range_of = |t: ajave_ir::Ty| -> Option<(&'static str, &'static str)> {
        match t {
            // `Ty::Int` also carries byte, short, char and boolean; the 32-bit
            // range is sound for all of them, just not tight.
            ajave_ir::Ty::Int => Some(("(- 2147483648)", "2147483647")),
            ajave_ir::Ty::Long => Some(("(- 9223372036854775808)", "9223372036854775807")),
            ajave_ir::Ty::Float | ajave_ir::Ty::Double => None,
            ajave_ir::Ty::Ref | ajave_ir::Ty::Str => None,
        }
    };
    //
    // # Pre-state only, and this is the subtle part
    //
    // The axiom must **not** be asserted of `v{i}p`. The post-state is where
    // LIA and the JVM disagree: this relation says `xp = x + 1` where a JVM
    // says `xp = wrap(x + 1)`, so `xp` is only the JVM's value when nothing
    // overflowed. Asserting `range(xp)` beside `xp = x + 1` therefore does not
    // *state a fact* — it **removes the overflowing transition from the
    // model**, which is the unsound "assume no overflow" that
    // `preservation_query`'s doc warns about, arriving through the axioms
    // instead of through the query.
    //
    // It is also self-concealing: with `range(xp)` present, `ovf` is
    // unsatisfiable on every edge, so the guard this plan exists to add
    // silently does nothing and `0 <= sum` is "preserved" by `sum = sum + 2`
    // again. `an_overflowing_increment_does_not_preserve_a_lower_bound` is the
    // test that would fail.
    //
    // A *reference*'s post-state is not affected: references do not wrap, so
    // the length axioms below are asserted of both states.
    for (i, vi) in body.vars.iter().enumerate() {
        if let Some((min, max)) = range_of(vi.ty) {
            let name = format!("{prefix}v{i}");
            ghost_preamble.push_str(&format!(
                "(assert (and (<= {min} {name}) (<= {name} {max})))\n"
            ));
        }
    }

    // # Array lengths are non-negative, instantiated at each reference
    //
    // The JVMS invariant for every array that exists. The allocation-site
    // facts in `path_conds` cover arrays this body creates; an array-typed
    // *parameter* has no allocation site here, so without these nothing says
    // its length is non-negative and no `ArrayBounds` lower bound is provable.
    //
    // Ground instances rather than `(forall ((r Int)) (>= (select ghost_len r) 0))`
    // deliberately: a quantifier in every query risks turning `unsat` into
    // `unknown`, and `unknown` refuses the proof.
    //
    // A non-array reference's cell is constrained too, which is harmless: the
    // cell is otherwise unconstrained and nothing reads it, because
    // `Expr::Length` is only produced for references the interval domain
    // tracked as arrays.
    for (i, vi) in body.vars.iter().enumerate() {
        if vi.ty != ajave_ir::Ty::Ref {
            continue;
        }
        ghost_preamble.push_str(&format!(
            "(assert (>= (select {len_pre} {prefix}v{i}) 0))\n"
        ));
        ghost_preamble.push_str(&format!(
            "(assert (>= (select {len_post} {prefix}v{i}p) 0))\n"
        ));
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
        edge_clauses,
        error_formulas,
        n_vars,
        ghost_preamble,
    }
}

/// One CFG edge's transition, with everything a query over it must not forget.
///
/// # Why this is a struct and not a tuple
///
/// Checking an invariant across an edge needs three things beyond the clause:
/// the ghost facts that hold on it, the overflow conditions the invariant must
/// exclude, and the axioms the ghost sorts rest on. A consumer that assembles
/// that query by hand and forgets the overflow disjunct gets the **unsound**
/// behaviour, silently -- which is how `algorithms/BellmanFord-FunUnsat01`
/// became a wrong TRUE. Two consumers assembled it by hand and a third was
/// coming.
///
/// So the data carries its own obligations, and `LiaEncoding::preservation_query`
/// is the only code in the tree that writes a preservation script. See
/// `docs/proposals/lia-faithfulness.md` §6, and `CLAUDE.md` on `Bounded { k }`
/// for the general form of this mistake.
pub struct EdgeClause {
    pub from: ajave_ir::BlockId,
    /// `None` where control leaves the method (return, throw, halt), so there
    /// is no successor assertion to preserve.
    pub to: Option<ajave_ir::BlockId>,
    /// The transition relation restricted to this edge. **Byte-identical to
    /// the matching disjunct of `transition`**, which `imc` and `cegar`
    /// consume; `edge_clauses_are_the_disjuncts_of_transition` pins that.
    pub clause: String,
    /// Extra conjuncts true of this edge that `transition` deliberately omits,
    /// because widening `transition` would change what `imc` and `cegar`
    /// reason about: ghost-length threading and allocation-site length facts.
    pub ghost: Vec<String>,
    /// This edge's arithmetic overflow conditions, as one disjunct, over the
    /// **pre**-state. `None` when the source block has no overflowing
    /// arithmetic.
    ///
    /// A consumer may not assume this false. It must require the invariant to
    /// *exclude* it — see `preservation_query`.
    pub overflow: Option<String>,
}

impl EdgeClause {
    fn new(from: ajave_ir::BlockId, to: Option<ajave_ir::BlockId>, clause: String) -> Self {
        EdgeClause {
            from,
            to,
            clause,
            ghost: Vec::new(),
            overflow: None,
        }
    }
}

pub struct LiaEncoding {
    pub declarations: String,
    pub transition: String,
    /// One entry per CFG edge. The disjunction of the `clause` fields is
    /// `transition`.
    pub edge_clauses: Vec<EdgeClause>,
    pub error_formulas: Vec<(ajave_ir::ObligationId, String)>,
    pub n_vars: usize,
    /// Declarations and assumptions the *edge* encoding needs and `transition`
    /// does not: the ghost length array, and the integer range axioms.
    ///
    /// Separate from `declarations` so that formula stays byte-identical for
    /// `imc` and `cegar`. Reached through `edge_preamble`, never directly.
    pub ghost_preamble: String,
}

impl LiaEncoding {
    /// Everything a query over the edge encoding must declare and assume.
    pub fn edge_preamble(&self) -> String {
        format!("{}{}", self.declarations, self.ghost_preamble)
    }

    /// The initiation query for an assertion at the entry block.
    ///
    /// A method's entry state is its unconstrained parameters, so there is no
    /// precondition to assume: the assertion must be **valid**, which is UNSAT
    /// of its negation. The range axioms make this weaker, and therefore more
    /// provable, than it was: the assertion now only has to hold of states a
    /// JVM can represent.
    pub fn initiation_query(&self, assertion: &str) -> String {
        format!(
            "{}\n(assert (not {assertion}))\n(check-sat)\n",
            self.edge_preamble()
        )
    }

    /// The preservation query for `post` at `edge.to`, assuming `pre` at
    /// `edge.from`. **UNSAT means preserved, on a JVM and not only in LIA.**
    ///
    /// # The shape
    ///
    /// `pre ∧ ghost ∧ (clause ∨ ovf) ∧ ¬post′`
    ///
    /// # Why the overflow condition is a *disjunct of the transition*
    ///
    /// Overflow is an exceptional edge in disguise, and the encoding already
    /// knows how to model one of those: with an **unconstrained post-state**.
    ///
    /// This relation says `xp = x + 1` where a JVM says `xp = wrap(x + 1)`, so
    /// the clause describes the JVM's step only when nothing overflowed. When
    /// something did, we know nothing about the successor beyond that it is
    /// some state — which is exactly `ovf` as a disjunct with no post-state
    /// constraint. The assertion at the target then has to hold of an
    /// arbitrary state, i.e. be valid, precisely as it must across a `throw`.
    ///
    /// Two shapes were tried before this one and both are wrong:
    ///
    /// * `pre ∧ clause ∧ ¬ovf ∧ ¬post′` — *assuming* no overflow. Unsound: it
    ///   proves the invariant of overflow-free runs and says nothing about the
    ///   run that wraps.
    /// * `pre ∧ clause ∧ (¬post′ ∨ ovf)` — requiring the invariant to
    ///   *exclude* overflow. Sound, but needlessly destructive: it deletes
    ///   every candidate at the target of any edge whose arithmetic the source
    ///   cannot bound, including candidates that are **valid** and so cannot
    ///   be broken by a wrap. A tautology about a variable the block never
    ///   touches died under it.
    ///
    /// The form here is sound for both cases of the induction. If the JVM step
    /// does not overflow it satisfies `clause`, so UNSAT gives `post′`. If it
    /// does, the pre-state satisfies `ovf` — which depends on the pre-state
    /// alone — so the real `(s, s′)` pair satisfies the disjunction anyway and
    /// UNSAT gives `post′` again. See `docs/proposals/lia-faithfulness.md` §3,
    /// and `smt_text::lia_overflow_cond` for the arithmetic.
    ///
    /// `ghost` is asserted **outside** the disjunction: an array's length is
    /// immutable, so `ghost_lenp = ghost_len` holds across a wrapped step as
    /// much as a faithful one, and putting it inside would throw the fact away
    /// exactly where it is still true.
    pub fn preservation_query(&self, edge: &EdgeClause, pre: &str, post: &str) -> String {
        let mut script = self.edge_preamble();
        script.push_str(&format!("\n(assert {pre})\n"));
        for g in &edge.ghost {
            script.push_str(&format!("(assert {g})\n"));
        }
        match &edge.overflow {
            Some(ovf) => script.push_str(&format!("(assert (or {} {ovf}))\n", edge.clause)),
            None => script.push_str(&format!("(assert {})\n", edge.clause)),
        }
        script.push_str(&format!("(assert (not {post}))\n(check-sat)\n"));
        script
    }
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

#[cfg(test)]
mod lia_encoding_tests {
    use super::*;
    use crate::houdini::tests_support::counting_loop;

    /// `transition` is what `imc` and `cegar` reason about, and `EdgeClause`
    /// exists to carry per-edge information *without* changing it. This pins
    /// the relationship the struct's doc asserts: every clause is a disjunct
    /// of `transition` and every disjunct is some edge's clause.
    ///
    /// Checked as a multiset, because two edges may legitimately carry the
    /// same clause (two `case` labels onto one target), and as exact strings,
    /// because a difference of a single space would mean two encoders.
    #[test]
    fn edge_clauses_are_the_disjuncts_of_transition() {
        let body = counting_loop();
        let enc = encode_body_lia(&body, &[], "");

        // Exceptional edges are deliberately absent from `transition`; this
        // fixture has none, so the two sets must match exactly.
        assert!(
            body.blocks.iter().all(|b| b.exceptional.is_empty()),
            "fixture must have no exceptional edges for this comparison"
        );

        let mut from_edges: Vec<&str> = enc
            .edge_clauses
            .iter()
            .map(|e| e.clause.as_str())
            .collect();
        from_edges.sort_unstable();

        // `transition` is `(or c1 c2 ...)`; recover the disjuncts by matching
        // parentheses rather than by splitting, since the clauses contain
        // spaces and nested parens.
        let t = enc.transition.as_str();
        assert!(t.starts_with("(or "), "unexpected shape: {t}");
        let inner = &t[4..t.len() - 1];
        let mut disjuncts: Vec<&str> = Vec::new();
        let (mut depth, mut start) = (0i32, 0usize);
        for (i, c) in inner.char_indices() {
            match c {
                '(' => {
                    if depth == 0 {
                        start = i;
                    }
                    depth += 1;
                }
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        disjuncts.push(&inner[start..=i]);
                    }
                }
                _ => {}
            }
        }
        disjuncts.sort_unstable();
        assert_eq!(
            from_edges, disjuncts,
            "an edge clause is not a disjunct of `transition`, so `imc` and \
             `cegar` are reasoning about a different relation from the checker"
        );
    }

    /// The trap that concealed the overflow guard for one iteration of this
    /// work, as a test.
    ///
    /// A range axiom on the **post**-state does not state a fact: this
    /// relation says `xp = x + 1` where a JVM says `xp = wrap(x + 1)`, so
    /// `range(xp)` beside `xp = x + 1` removes the overflowing transition from
    /// the model instead of describing it. With it present every `ovf` is
    /// unsatisfiable and `an_overflowing_increment_does_not_preserve_a_lower_bound`
    /// starts passing for the wrong reason.
    #[test]
    fn range_axioms_are_asserted_of_the_pre_state_only() {
        let enc = encode_body_lia(&counting_loop(), &[], "");
        assert!(
            enc.ghost_preamble.contains("(<= v0 2147483647)"),
            "the pre-state range axiom is what makes the guard non-vacuous: {}",
            enc.ghost_preamble
        );
        assert!(
            !enc.ghost_preamble.contains("v0p"),
            "a post-state range axiom silently assumes no overflow: {}",
            enc.ghost_preamble
        );
    }

    /// The guard reaches the query as a disjunct of the transition, not as a
    /// disjunct of the negated conclusion. Those differ exactly where the
    /// target's assertion is valid — see `preservation_query`'s doc.
    #[test]
    fn the_overflow_condition_is_a_disjunct_of_the_transition() {
        let enc = encode_body_lia(&counting_loop(), &[], "");
        // bb2 is `x := x + 1`, the only arithmetic in the fixture.
        let edge = enc
            .edge_clauses
            .iter()
            .find(|e| e.from == ajave_ir::BlockId(2))
            .expect("bb2 has an outgoing edge");
        let ovf = edge
            .overflow
            .as_deref()
            .expect("an int add must carry an overflow condition");
        assert!(ovf.contains("2147483647"), "32-bit bound: {ovf}");

        let q = enc.preservation_query(edge, "true", "(<= 0 v0p)");
        assert!(
            q.contains(&format!("(or {} {ovf})", edge.clause)),
            "the overflow condition must be disjoined with the clause: {q}"
        );
        assert!(
            q.contains("(assert (not (<= 0 v0p)))"),
            "the conclusion is negated on its own: {q}"
        );
    }

    /// A block with no arithmetic carries no overflow condition, so the guard
    /// costs nothing where there is nothing to guard.
    #[test]
    fn a_block_without_arithmetic_carries_no_overflow_condition() {
        let enc = encode_body_lia(&counting_loop(), &[], "");
        // bb0 assigns a constant; bb1 compares. Neither adds, subtracts or
        // multiplies, which is what `smt_text::overflowing` admits.
        for b in [0u32, 1] {
            for e in enc
                .edge_clauses
                .iter()
                .filter(|e| e.from == ajave_ir::BlockId(b))
            {
                assert!(
                    e.overflow.is_none(),
                    "bb{b} has no overflowing arithmetic, got {:?}",
                    e.overflow
                );
            }
        }
    }

    /// Every edge carries the ghost length identity, including the ones that
    /// leave the method — a length is immutable however control departs.
    #[test]
    fn every_edge_threads_the_ghost_length_array() {
        let enc = encode_body_lia(&counting_loop(), &[], "");
        assert!(!enc.edge_clauses.is_empty());
        for e in &enc.edge_clauses {
            assert!(
                e.ghost.iter().any(|g| g == "(= ghost_lenp ghost_len)"),
                "bb{} -> {:?} is missing the length identity: {:?}",
                e.from.0,
                e.to,
                e.ghost
            );
        }
        assert!(
            enc.declarations.contains("(declare-fun ghost_len () (Array Int Int))"),
            "the term appears in `transition`, so the declaration must be in \
             `declarations` or z3 drops the assertion that uses it"
        );
    }

    /// Producer and consumer must spell the ghost array identically.
    ///
    /// `invariant_check::render` emits ghost symbols unprefixed while
    /// `arr_name` prefixes allocation arrays, so "which convention does this
    /// one follow" is a live question with a wrong answer available. A
    /// prefixed declaration would make the checker read an array the
    /// transition relation never writes, and z3 answers such a query by
    /// dropping the assertion and reporting on what is left — silently.
    /// `Expr::Depth` is what that looks like in the tree.
    ///
    /// Asserted against the rendered claim rather than against a literal, so
    /// the test fails if either side moves.
    #[test]
    fn the_checker_and_the_encoder_spell_the_length_array_alike() {
        let enc = encode_body_lia(&counting_loop(), &[], "");
        let pre = crate::invariant_check::render(
            &ajave_core::term::Expr::length(ajave_core::term::Expr::Var(ajave_ir::VarId(1))),
            false,
        )
        .expect("a length claim must render now");
        let post = crate::invariant_check::render(
            &ajave_core::term::Expr::length(ajave_core::term::Expr::Var(ajave_ir::VarId(1))),
            true,
        )
        .expect("a length claim must render now");
        assert_eq!(pre, "(select ghost_len v1)");
        assert_eq!(post, "(select ghost_lenp v1p)");
        for sym in ["ghost_len", "ghost_lenp"] {
            assert!(
                enc.declarations
                    .contains(&format!("(declare-fun {sym} () (Array Int Int))")),
                "`render` reads {sym}; the encoder must declare it: {}",
                enc.declarations
            );
        }
    }
}