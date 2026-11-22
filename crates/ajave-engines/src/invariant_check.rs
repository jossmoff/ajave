//! Independent checking of invariant-backed TRUE claims.
//!
//! Workstream A2 of `docs/plans/codebase-health.md`.
//!
//! `certify.rs` states the project's trust rule: "no artifact reaches the
//! reporter on an engine's authority alone. FALSE is replayed on a real JVM;
//! TRUE rests on invariants re-checked by a separate, small, boring pass."
//! `JvmReplay` is that pass for FALSE. This is the beginning of it for TRUE.
//!
//! # What is checked, and what is not
//!
//! A safety proof by invariant `I` at point `P` for obligation `o` rests on
//! three claims. Two are checkable against a single invariant and are
//! implemented here:
//!
//! * **Sufficiency** — `I` rules out the violation: `I ∧ error(o)` is UNSAT.
//!   This is the claim that matters most, because it is the one the discharge
//!   directly asserts: *the state I say holds at this check makes the check
//!   pass*.
//! * **Preservation** — `I` survives the transition relation:
//!   `I(pre) ∧ T ∧ ¬I(post)` is UNSAT.
//!
//! The third, **initiation**, is deliberately absent, and the reason is a
//! design point rather than an omission. "Holds initially" is a property of an
//! invariant *map* — one assertion per program point — not of a single
//! invariant at a single point. An invariant at a non-entry block is
//! established by its predecessors, which is preservation over the map, so
//! certifying one invariant in isolation cannot express it. Until an engine
//! publishes a map rather than a point, this pass can refuse bad proofs but
//! cannot confirm good ones as *inductive* in the full sense. `check_inductive`
//! therefore returns `Confirmed` for "sufficient and locally preserved", and
//! the caller must know that is weaker than inductive. A3 decides whether to
//! publish maps.
//!
//! # The theory, and why a float invariant cannot be confirmed
//!
//! Checking happens in LIA, reusing `interpolation::encode_body_lia` so the
//! transition relation and the per-obligation error formula are the same ones
//! the rest of the tree reasons about. LIA has no floats, so an invariant
//! mentioning a float or double variable cannot be stated, let alone checked —
//! those return `Inconclusive`, which refuses the discharge. That is the right
//! answer and not a limitation to route around: ajave's one confirmed wrong
//! TRUE (`benchmarks/ajave/jvm-floats/FloatIsNotDouble`, #48) is exactly a
//! float-arithmetic proof, and a checker that cannot see floats must decline
//! rather than wave them through.
//!
//! # The honest limit on independence
//!
//! This shares `encode_body_lia` with `imc` and `cegar`. A checker that reuses
//! the encoder of the engine it checks is not fully independent — an identical
//! misunderstanding in both is invisible. Full independence needs a second
//! implementation of JVM semantics, which `certify.rs` concedes is a
//! multi-year project. What this buys is a separate pass, a different code
//! path, and three explicit obligations, which catches engine-specific
//! defects; every finding in the 2026-10-26 audit was exactly that.

use ajave_core::artifact::{Invariant, InvariantMap};
use ajave_core::certify::CertResult;
use ajave_core::term::{Expr, Op};
use ajave_ir::{BlockId, Body, ObligationId, Ty, VarId};
use log::debug;

use crate::interpolation::{encode_body_lia, run_solver_batch_pub};

/// The SMT array a field's cells live in.
///
/// Shared by the checker and `interpolation`'s encoder so the two cannot spell
/// it differently. Non-identifier characters in a class name are mapped, since
/// The SMT name of the ghost depth array for a reference field.
///
/// E1. Distinct from `field_array_name` because the two arrays hold different
/// things about the same field: `fld_C_f` maps a receiver to the reference it
/// stores, `depth_C_f` maps it to the number of `f` links from it to null.
/// Sharing a name would make a depth claim read as a value claim, which is the
/// producer-and-consumer-disagree fault `CLAUDE.md` names.
pub fn depth_array_name(f: &ajave_ir::FieldKey) -> String {
    format!("depth_{}_{}", f.class.replace('/', "_"), f.name)
}

/// The SMT array holding every array's length, indexed by the **reference**.
///
/// `(select ghost_len r)` is `r.length`. McCarthy's theory of arrays (1962)
/// applied the way Burstall (1972) applies it to fields, which is how Boogie,
/// VCC, Why3 and Dafny all encode array lengths, and how `field_array_name`
/// already encodes fields here: aliasing is the solver's problem, and two
/// references to one array have one length without any points-to analysis.
///
/// Indexed by reference and not by `AllocSite` because that is what the claim
/// language says. `Expr::Length { obj }` is a fact about a reference, and
/// `ai.rs` gives the reason — it "survives reassignment", unlike
/// `array_len_var`, which is a fact about a local and dies with it.
///
/// **Immutable.** JVMS §6.5: `newarray` takes the length as an operand and
/// `arraylength` returns it unchanged. Nothing writes this array, so the only
/// threading constraint is the identity `ghost_lenp = ghost_len`, which each
/// `EdgeClause` carries in its `ghost` field.
///
/// Named with a `ghost_` prefix so it cannot collide with a sanitised field
/// name: `field_array_name` emits `fld_*` and `depth_array_name` `depth_*`.
pub const LENGTH_ARRAY: &str = "ghost_len";

/// `java/lang/Object` is not an SMT-LIB symbol.
pub fn field_array_name(f: &ajave_ir::FieldKey) -> String {
    let sanitise = |t: &str| {
        t.chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect::<String>()
    };
    format!("fld_{}_{}", sanitise(&f.class), sanitise(&f.name))
}

/// Which program variables an invariant mentions.
fn mentioned_vars(e: &Expr, out: &mut Vec<VarId>) {
    match e {
        Expr::Var(v) => out.push(*v),
        Expr::Bin(_, a, b) => {
            mentioned_vars(a, out);
            mentioned_vars(b, out);
        }
        Expr::Not(a) => mentioned_vars(a, out),
        Expr::Apply { args, .. } => args.iter().for_each(|a| mentioned_vars(a, out)),
        _ => {}
    }
}

/// Render an `Expr` as SMT-LIB over integer variables named `{prefix}v{i}`.
///
/// Returns `None` for anything LIA cannot state — a double, an uninterpreted
/// library application, a division (whose JVM semantics is truncating and not
/// SMT-LIB's `div`). Declining is the safe direction: the caller turns `None`
/// into `Inconclusive`, which refuses the discharge.
pub(crate) fn render(e: &Expr, post: bool) -> Option<String> {
    Some(match e {
        // `v{i}p` directly, not a separate `post_v{i}` bound to it. The
        // indirection hid a bug: only *variables* were being prefixed, so a
        // heap term rendered its pre-state array in the post-state formula and
        // preservation degenerated to `inv ∧ T ∧ ¬inv` over the same state —
        // trivially UNSAT, so it confirmed whatever it was given.
        Expr::Var(v) => format!("v{}{}", v.0, if post { "p" } else { "" }),
        Expr::Int(n) => {
            if *n < 0 {
                format!("(- {})", -n)
            } else {
                n.to_string()
            }
        }
        Expr::Bool(b) => b.to_string(),
        Expr::Not(a) => format!("(not {})", render(a, post)?),
        Expr::Bin(op, a, b) => {
            let (l, r) = (render(a, post)?, render(b, post)?);
            let sym = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Lt => "<",
                Op::Le => "<=",
                Op::Gt => ">",
                Op::Ge => ">=",
                Op::Eq => "=",
                Op::And => "and",
                Op::Or => "or",
                // `Ne` is not an SMT-LIB operator; `Div`/`Rem` do not agree
                // with the JVM's truncating semantics in LIA.
                Op::Ne => return Some(format!("(not (= {l} {r}))")),
                Op::Div | Op::Rem => return None,
            };
            format!("({sym} {l} {r})")
        }
        // The array constant the LIA encoder declares for this site. The
        // naming must match `encode_body_lia`'s `arr_name` exactly: a checker
        // that invented its own spelling would read a different array from the
        // one the transition relation writes, and then confirm invariants
        // about nothing. Producer and consumer disagreeing about an artifact
        // is worse than no artifact.
        Expr::Select { site, index } => {
            format!(
                "(select arr{}_{}{} {})",
                site.block.0,
                site.index,
                if post { "p" } else { "" },
                render(index, post)?
            )
        }
        // A field of a particular object, Burstall-style: one array per field
        // name, indexed by the receiver. The naming must match the encoder's
        // `fld_name` exactly, for the same reason `Select` must — a checker
        // reading a different array from the one the transition relation
        // writes confirms invariants about nothing.
        //
        // A `double`- or `float`-typed field is declined: the array is
        // `(Array Int Int)` and a float cell could not be stated in it.
        Expr::Field { field, obj } => {
            if field.desc == "D" || field.desc == "F" {
                return None;
            }
            format!(
                "(select {}{} {})",
                field_array_name(field),
                if post { "p" } else { "" },
                render(obj, post)?
            )
        }
        // The ghost depth array for a reference field, named to match the
        // encoder for the same reason `Select` and `Field` must.
        //
        // Declining a float-typed field is not a concern here — depth is only
        // defined along a *reference* field — but a non-reference descriptor
        // means the producer published a claim it had no business making, and
        // the safe reading of a claim we cannot interpret is to refuse the
        // discharge rather than to guess at it.
        // Declined, and this is a *correction* rather than a limit.
        //
        // This arm used to emit `(select depth_C_f obj)`, and **nothing
        // declares that array**: `depth_array_name` occurs twice in the tree
        // and both are in this file. z3 reports an unknown constant, drops the
        // whole assertion, and answers on what is left -- the mechanism
        // `interpolation.rs` records. The direction happens to be
        // conservative (a query missing its assertion comes back `sat`, which
        // deletes a candidate and refuses a discharge), but it is exactly the
        // fault the comments on `Select` and `Field` exist to prevent: a
        // checker reading a symbol the transition relation never writes
        // confirms invariants about nothing.
        //
        // `Expr::Depth` has **zero producers**, so declining costs nothing
        // today. Building a second ghost model on speculation is what
        // `CLAUDE.md` refuses: "Adding a variant to `Artifact` with neither a
        // producer nor a consumer is not design, it is a comment with a type."
        // When an engine maintains depth the way `ghost_len` is now
        // maintained, this arm comes back with it.
        Expr::Depth { .. } => return None,
        // Null is the integer 0, which is the representation every encoder in
        // the tree already chose for it -- `smt_encode` emits
        // `bv_const(0, 32)`, `concrete` and `concurrent_exec` use `Ref(0)`,
        // `nra` uses `mk_real(0)`. Matching that convention is the same
        // requirement as matching `arr_name` and `fld_name`: a checker that
        // spelled null differently from the transition relation would be
        // checking a claim about a value the program never produces.
        //
        // The claim language keeps `Null` and `Int(0)` distinct even though
        // this encoding does not, and that is deliberate rather than
        // inconsistent. The distinction buys type discipline *in the
        // vocabulary* -- it stops a producer writing `r + 1` or a consumer
        // ordering two references -- and is discharged here, at the one place
        // that is allowed to know how references are represented.
        Expr::Null => "0".to_string(),
        // `r.length`, as a read of the ghost length array at the reference.
        //
        // The naming must match `encode_body_lia`'s exactly, for the same
        // reason `Select` and `Field` must, which is why it comes from the
        // shared `LENGTH_ARRAY` rather than being spelled here.
        //
        // The post-state reads `ghost_lenp` even though an array's length is
        // immutable, because the *receiver* is not: `i < a.length` after the
        // step is `(< ip (select ghost_lenp ap))`. Each `EdgeClause` carries
        // `(= ghost_lenp ghost_len)` in its `ghost` field, so the immutability
        // is stated as a constraint in the relation rather than inferred here.
        //
        // This arm declined until the LIA encoder tracked lengths at all. It
        // was not a gap that could be closed from this side: rendering a name
        // the transition relation never writes would have made preservation a
        // question about an unconstrained symbol.
        Expr::Length { obj } => format!(
            "(select {}{} {})",
            LENGTH_ARRAY,
            if post { "p" } else { "" },
            render(obj, post)?
        ),
        // A double is held as a bit pattern and means nothing in LIA; an
        // `Apply` is an unmodelled library call by construction.
        Expr::Double(_) | Expr::Apply { .. } => return None,
    })
}

/// Ask the solver whether `script`'s assertions are unsatisfiable.
///
/// `unknown`, a solver error, or anything unparseable is **not** UNSAT. A
/// proof may only rest on a definite answer.
pub(crate) fn is_unsat(solver: &str, script: &str) -> Option<bool> {
    match run_solver_batch_pub(solver, &["-in", "-smt2"], script) {
        Ok(lines) => {
            let answer = lines.iter().find(|l| {
                let t = l.trim();
                t == "sat" || t == "unsat" || t == "unknown"
            })?;
            match answer.trim() {
                "unsat" => Some(true),
                "sat" => Some(false),
                _ => None,
            }
        }
        Err(e) => {
            debug!("invariant-check: solver failed: {e}");
            None
        }
    }
}

/// Check an invariant-backed proof of `oid` in `body`.
///
/// `Confirmed` means sufficient and locally preserved — see the module doc for
/// why that is weaker than inductive. `Refuted` means a definite UNSAT was
/// expected and the solver said SAT: the invariant does not justify the claim.
/// `Inconclusive` covers everything else, including anything LIA cannot state.
/// Check an invariant **map** for initiation and preservation.
///
/// This is the obligation `check_inductive` could not express, and the reason
/// nothing has ever been promoted to `InvStatus::Inductive`. Its own module
/// doc states the problem: "Holds initially" is a property of a map, not of a
/// single invariant at a single point, so certifying one invariant in
/// isolation can refuse bad proofs but cannot confirm good ones.
///
/// # The two obligations
///
/// **Initiation.** `entries[entry]` must hold on entry. A method's entry state
/// is its parameters, which are unconstrained, so there is no precondition to
/// assume: the entry assertion must be *valid*, i.e. `¬entries[entry]` is
/// UNSAT. An absent entry carries no claim and passes trivially, which is the
/// normal case — a loop invariant lives at the loop header, not the entry.
///
/// **Preservation.** For every CFG edge `from → to`:
/// `entries[from] ∧ clause(from→to) ∧ ¬entries[to]'` is UNSAT. An edge whose
/// target carries no claim passes trivially; an edge leaving the method has no
/// successor assertion and is skipped.
///
/// **Sufficiency is not here**, deliberately. It is a property of a
/// *discharge* — this map rules out *that* obligation's violation — not of the
/// map, so it stays per-obligation in `map_implies_safety`. Mixing them is how
/// a map that is inductive but useless would look like a proof.
///
/// # What a `Confirmed` here licenses
///
/// That the map is inductive: true at the entry and preserved by every
/// transition the LIA encoder can express. Combined with `map_implies_safety`
/// for an obligation, that is a complete safety proof for it. Alone it is not
/// — an inductive `true` is inductive.
///
/// Every limit `check_inductive` carries applies here too: the shared encoder,
/// LIA's lack of floats, and `Expr::Length`'s missing ghost array. Any
/// `unknown` or unrenderable formula is `Inconclusive`, never `Confirmed`.
pub fn check_map_inductive(body: &Body, map: &InvariantMap, solver: &str) -> CertResult {
    // A map about a float says nothing checkable here, exactly as a point
    // claim about one does not.
    for formula in map.entries.values() {
        let mut vars = Vec::new();
        mentioned_vars(formula, &mut vars);
        if vars.iter().any(|v| {
            body.vars
                .get(v.0 as usize)
                .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
                .unwrap_or(true)
        }) {
            debug!(
                "invariant-check: map {} mentions a float or unknown var",
                map.id
            );
            return CertResult::Inconclusive;
        }
    }

    let enc = encode_body_lia(body, &[], "");

    // The assertion at a block, as a renderable formula. `None` means the
    // point carries no claim, which reads as `true`.
    let at = |block: BlockId, post: bool| -> Option<Option<String>> {
        let Some((_, f)) = map
            .entries
            .iter()
            .find(|(p, _)| p.method == body.key && p.block == block)
        else {
            return Some(None);
        };
        // An entry we cannot render must refuse the whole map rather than be
        // read as `true`: treating an unrenderable claim as no claim would
        // make preservation pass for a map nobody checked.
        render(f, post).map(Some)
    };

    // 1. Initiation.
    match at(body.entry, false) {
        None => return CertResult::Inconclusive,
        Some(None) => {}
        Some(Some(e)) => {
            let script = enc.initiation_query(&e);
            match is_unsat(solver, &script) {
                Some(true) => {}
                Some(false) => {
                    debug!("invariant-check: map {} fails initiation", map.id);
                    return CertResult::Refuted;
                }
                None => return CertResult::Inconclusive,
            }
        }
    }

    // 2. Preservation, one query per edge.
    for edge in &enc.edge_clauses {
        let Some(to) = edge.to else { continue };
        let (pre, post) = (at(edge.from, false), at(to, true));
        let (Some(pre), Some(post)) = (pre, post) else {
            return CertResult::Inconclusive;
        };
        let Some(post) = post else { continue };
        let pre = pre.unwrap_or_else(|| "true".to_string());
        // The guarded query, built by the one method allowed to build it. A
        // `Refuted` here may now mean either "not preserved" or "the map does
        // not exclude this edge's overflow", and the two are the same defect
        // for a consumer: the map is not an invariant of the JVM program.
        let script = enc.preservation_query(edge, &pre, &post);
        match is_unsat(solver, &script) {
            Some(true) => {}
            Some(false) => {
                debug!(
                    "invariant-check: map {} not preserved (or not overflow-free) on bb{} -> bb{}",
                    map.id, edge.from.0, to.0
                );
                return CertResult::Refuted;
            }
            None => return CertResult::Inconclusive,
        }
    }

    CertResult::Confirmed
}

/// Whether a map rules out an obligation's violation at its check point.
///
/// The third obligation, kept separate from `check_map_inductive` because it
/// is a property of the discharge rather than of the map.
pub fn map_implies_safety(
    body: &Body,
    map: &InvariantMap,
    oid: ObligationId,
    solver: &str,
) -> CertResult {
    let enc = encode_body_lia(body, &[oid], "");
    let errors: Vec<&String> = enc
        .error_formulas
        .iter()
        .filter(|(id, _)| *id == oid)
        .map(|(_, f)| f)
        .collect();
    if errors.is_empty() {
        return CertResult::Inconclusive;
    }
    // The block the obligation is checked in. Its assertion is the one that
    // has to exclude the violation; a claim at some other point says nothing
    // about this check.
    let Some(block) = body
        .blocks
        .iter()
        .find(|b| {
            b.stmts
                .iter()
                .any(|st| matches!(st, ajave_ir::Stmt::Check(o) if *o == oid))
        })
        .map(|b| b.id)
    else {
        return CertResult::Inconclusive;
    };
    let Some((_, formula)) = map
        .entries
        .iter()
        .find(|(p, _)| p.method == body.key && p.block == block)
    else {
        // No claim at the check means nothing to justify the discharge.
        return CertResult::Inconclusive;
    };
    let Some(pre) = render(formula, false) else {
        return CertResult::Inconclusive;
    };
    let error = if errors.len() == 1 {
        errors[0].clone()
    } else {
        format!(
            "(or {})",
            errors
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    // `edge_preamble`, not `declarations`: the range axioms and the
    // length non-negativity facts are needed here as much as on an edge. A
    // sufficiency query over unbounded integers asks whether the invariant
    // rules out a violation in states no JVM can reach, and refuses the
    // discharge when it cannot.
    let script = format!(
        "{}\n(assert {pre})\n(assert {error})\n(check-sat)\n",
        enc.edge_preamble()
    );
    match is_unsat(solver, &script) {
        Some(true) => CertResult::Confirmed,
        Some(false) => CertResult::Refuted,
        None => CertResult::Inconclusive,
    }
}

pub fn check_inductive(
    body: &Body,
    inv: &Invariant,
    oid: ObligationId,
    solver: &str,
) -> CertResult {
    // An invariant about a float says nothing checkable here, and must not be
    // waved through. See the module doc. `Expr::Select`'s index is screened by
    // this too, via `mentioned_vars`; the *element* type is integer by
    // construction, because `encode_body_lia` declares every site's array as
    // `(Array Int Int)` and a float array would have fallen through to an
    // unconstrained read rather than a `select`.
    let mut vars = Vec::new();
    mentioned_vars(&inv.formula, &mut vars);
    if vars.iter().any(|v| {
        body.vars
            .get(v.0 as usize)
            .map(|vi| matches!(vi.ty, Ty::Float | Ty::Double))
            .unwrap_or(true)
    }) {
        debug!(
            "invariant-check: {} mentions a float or unknown var",
            inv.id
        );
        return CertResult::Inconclusive;
    }

    let Some(pre) = render(&inv.formula, false) else {
        debug!("invariant-check: {} is not expressible in LIA", inv.id);
        return CertResult::Inconclusive;
    };

    let enc = encode_body_lia(body, &[oid], "");
    let errors: Vec<&String> = enc
        .error_formulas
        .iter()
        .filter(|(id, _)| *id == oid)
        .map(|(_, f)| f)
        .collect();
    if errors.is_empty() {
        // The obligation's check is not in this body, so there is nothing for
        // an invariant here to justify.
        return CertResult::Inconclusive;
    }
    let error = if errors.len() == 1 {
        errors[0].clone()
    } else {
        format!(
            "(or {})",
            errors
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        )
    };

    // 1. Sufficiency: the invariant rules out the violation.
    let sufficiency = format!(
        "{}\n(assert {pre})\n(assert {error})\n(check-sat)\n",
        enc.declarations
    );
    match is_unsat(solver, &sufficiency) {
        Some(true) => {}
        Some(false) => {
            debug!(
                "invariant-check: {} does not imply safety of {oid:?}",
                inv.id
            );
            return CertResult::Refuted;
        }
        None => return CertResult::Inconclusive,
    }

    // 2. Preservation: the invariant survives one step of the transition.
    let Some(post) = render(&inv.formula, true) else {
        return CertResult::Inconclusive;
    };
    let decls = enc.declarations.clone();
    let preservation = format!(
        "{decls}\n(assert {pre})\n(assert {})\n(assert (not {post}))\n(check-sat)\n",
        enc.transition
    );
    if std::env::var("AJAVE_DUMP_PRESERVATION").is_ok() {
        // Kept. Every bug in this function so far has been found by reading
        // the script z3 was actually given, and all three were invisible from
        // the Rust side: an undeclared binder, a post-state that was secretly
        // the pre-state, and a path condition added after the formula that
        // needed it.
        eprintln!("--- PRESERVATION ---\n{preservation}\n--- END ---");
    }
    match is_unsat(solver, &preservation) {
        Some(true) => CertResult::Confirmed,
        Some(false) => {
            debug!("invariant-check: {} is not preserved", inv.id);
            CertResult::Refuted
        }
        None => CertResult::Inconclusive,
    }
}

#[cfg(test)]
mod tests {
    //! One fixture per failure mode, so a pass means the specific obligation
    //! held rather than that the checker declined for an unrelated reason.
    //! The control comes first: if `Confirmed` is unreachable, every negative
    //! result below is vacuous.

    use super::*;
    use ajave_core::artifact::ProgramPoint;
    use ajave_core::term::Expr;
    use ajave_ir::{
        Block, BlockId, Const, MethodKey, Obligation, ObligationKind, Operand, Rvalue, Stmt,
        Terminator, VarInfo, VarKind,
    };

    fn mk() -> MethodKey {
        MethodKey {
            class: "Main".into(),
            name: "m".into(),
            desc: "()V".into(),
        }
    }

    /// `check(v1);` with `v1` never assigned — so the obligation is violable
    /// exactly where `v1 == 0`, and an invariant has real work to do.
    ///
    /// The first version of this fixture assigned `v1 := 5` before the check.
    /// That made the error formula `(= 5 0)`, already UNSAT, so sufficiency
    /// passed for *any* invariant including `true` — the invariant was never
    /// load-bearing and the negative test could not fail. A fixture where the
    /// property holds without the thing under test proves nothing about it.
    fn body_check_only(ty: Ty) -> Body {
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Int,
                },
                VarInfo {
                    kind: VarKind::Local(1),
                    ty,
                },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(1)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![Stmt::Check(ObligationId(0))],
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    /// The same check, plus a block that assigns `v1 := 0` and loops back. An
    /// invariant like `v1 >= 1` is *sufficient* here but not *preserved*,
    /// which is what separates the two queries.
    fn body_that_breaks_the_invariant() -> Body {
        let mut b = body_check_only(Ty::Int);
        b.blocks[0].term = Terminator::Goto(BlockId(1));
        b.blocks.push(Block {
            id: BlockId(1),
            bytecode_offset: 1,
            stmts: vec![Stmt::Assign(
                VarId(1),
                Rvalue::Use(Operand::Const(Const::Int(0))),
            )],
            term: Terminator::Goto(BlockId(0)),
            exceptional: vec![],
        });
        b
    }

    fn inv(formula: Expr) -> Invariant {
        Invariant {
            id: 1,
            at: ProgramPoint {
                method: mk(),
                block: BlockId(0),
                index: 0,
            },
            formula,
            status: ajave_core::artifact::InvStatus::Candidate,
            scope: ajave_core::artifact::Scope::Point(ProgramPoint {
                method: mk(),
                block: BlockId(0),
                index: 0,
            }),
        }
    }

    fn ge(v: u32, n: i64) -> Expr {
        Expr::bin(Op::Ge, Expr::Var(VarId(v)), Expr::Int(n))
    }

    fn solver() -> Option<&'static str> {
        match std::process::Command::new("z3").arg("--version").output() {
            Ok(o) if o.status.success() => Some("z3"),
            _ => {
                eprintln!("no z3 on PATH; skipping");
                None
            }
        }
    }

    // ── maps ──────────────────────────────────────────────────────────
    //
    // The fixture table from `docs/plans/codebase-health.md` A2, including the
    // row A2 could not express: "an invariant that holds everywhere but not at
    // entry -> Refuted (initiation fails)". That row is the whole reason maps
    // exist, so it is the one that matters most here.

    fn pt(block: u32) -> ProgramPoint {
        ProgramPoint {
            method: mk(),
            block: BlockId(block),
            index: 0,
        }
    }

    /// bb0 (entry): `v1 := 0`, goto bb1. bb1: the check, self-loop.
    ///
    /// The entry must *establish* something or no non-trivial map is
    /// inductive: in `body_that_breaks_the_invariant` the entry is itself the
    /// loop header, so a claim at the header needs the same claim of an
    /// unconstrained parameter, and refusing that is correct rather than a
    /// checker limitation. This fixture separates the two, which is the
    /// ordinary shape of a loop with an initialiser.
    fn body_initialised_loop() -> Body {
        let mut b = body_check_only(Ty::Int);
        b.blocks[0].stmts = vec![Stmt::Assign(
            VarId(1),
            Rvalue::Use(Operand::Const(Const::Int(0))),
        )];
        b.blocks[0].term = Terminator::Goto(BlockId(1));
        b.blocks.push(Block {
            id: BlockId(1),
            bytecode_offset: 1,
            stmts: vec![Stmt::Check(ObligationId(0))],
            term: Terminator::Goto(BlockId(1)),
            exceptional: vec![],
        });
        b
    }

    fn map_of(entries: Vec<(u32, Expr)>) -> InvariantMap {
        InvariantMap {
            id: 9,
            method: mk(),
            entries: entries.into_iter().map(|(b, e)| (pt(b), e)).collect(),
            status: ajave_core::artifact::InvStatus::Candidate,
            scope: ajave_core::artifact::Scope::Method(mk()),
        }
    }

    /// The control. `v1 := 0` on entry, so `v1 >= 0` holds at the loop header
    /// and the self-loop preserves it.
    #[test]
    fn a_map_true_at_entry_and_preserved_is_confirmed() {
        let Some(s) = solver() else { return };
        let m = map_of(vec![(0, Expr::Bool(true)), (1, ge(1, 0))]);
        assert_eq!(
            check_map_inductive(&body_initialised_loop(), &m, s),
            CertResult::Confirmed,
            "the control fixture must confirm, or every Refuted below is vacuous"
        );
    }

    /// The same body with a claim the initialiser contradicts: `v1 := 0` makes
    /// `v1 >= 1` false on the edge into the header.
    #[test]
    fn a_map_the_initialiser_contradicts_fails_preservation() {
        let Some(s) = solver() else { return };
        let m = map_of(vec![(0, Expr::Bool(true)), (1, ge(1, 1))]);
        assert_eq!(
            check_map_inductive(&body_initialised_loop(), &m, s),
            CertResult::Refuted,
            "`v1 >= 1` cannot survive `v1 := 0` on the edge into the header"
        );
    }

    /// The row a point claim cannot express. `v1 >= 1` is preserved nowhere
    /// relevant but, more to the point, it is **not valid at the entry** — and
    /// initiation is precisely the obligation `check_inductive` omitted.
    #[test]
    fn a_map_that_does_not_hold_at_entry_fails_initiation() {
        let Some(s) = solver() else { return };
        let m = map_of(vec![(0, ge(1, 1))]);
        assert_eq!(
            check_map_inductive(&body_check_only(Ty::Int), &m, s),
            CertResult::Refuted,
            "an entry claim that is not valid must fail initiation"
        );
    }

    /// An absent point carries no claim and must read as `true`, not as a
    /// contradiction — otherwise an unmentioned block would look unreachable
    /// and preservation would pass vacuously for every map.
    #[test]
    fn a_map_with_no_entry_for_a_point_is_not_read_as_a_contradiction() {
        let Some(s) = solver() else { return };
        let m = map_of(vec![]);
        assert_eq!(
            check_map_inductive(&body_initialised_loop(), &m, s),
            CertResult::Confirmed,
            "the empty map is inductive, and says nothing"
        );
    }

    /// And the empty map must not be able to *discharge* anything, which is
    /// the separation between inductiveness and sufficiency.
    #[test]
    fn an_inductive_map_that_says_nothing_cannot_discharge() {
        let Some(s) = solver() else { return };
        let m = map_of(vec![]);
        assert_eq!(
            map_implies_safety(&body_check_only(Ty::Int), &m, ObligationId(0), s),
            CertResult::Inconclusive,
            "no claim at the check means nothing to justify the discharge"
        );
    }

    /// The nullness claim from P1, now as a map entry discharging a
    /// dereference. This is the end-to-end shape the whole design is for.
    #[test]
    fn a_map_claiming_non_nullness_discharges_a_dereference() {
        let Some(s) = solver() else { return };
        let m = map_of(vec![(0, Expr::non_null(Expr::Var(VarId(1))))]);
        assert_eq!(
            map_implies_safety(&body_deref(), &m, ObligationId(0), s),
            CertResult::Confirmed,
        );
    }

    /// `body_check_only`, but the obligation is a dereference of a reference.
    ///
    /// The error formula is `cond == 0` for every obligation kind, and null is
    /// encoded as 0, so for this obligation the error *is* `ref == null` and a
    /// nullness invariant is exactly what sufficiency wants.
    fn body_deref() -> Body {
        let mut b = body_check_only(Ty::Ref);
        b.obligations[0].kind = ObligationKind::NullDeref;
        b
    }

    /// `NullDeref` is 53% of the corpus's open obligations and its safety
    /// condition could not be *stated* before `Expr::Null`. This is the test
    /// that the vocabulary addition does the thing it was added for.
    #[test]
    fn a_nullness_claim_is_sufficient_for_a_dereference() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &body_deref(),
            &inv(Expr::non_null(Expr::Var(VarId(1)))),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Confirmed,
            "`r != null` must discharge a dereference of `r`"
        );
    }

    /// The negative control for the same addition. Without it, `Confirmed`
    /// above could come from the checker waving through anything mentioning
    /// `Null`.
    #[test]
    fn claiming_the_reference_is_null_cannot_discharge_a_dereference() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &body_deref(),
            &inv(Expr::bin(Op::Eq, Expr::Var(VarId(1)), Expr::Null)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "`r == null` is the violation, not a proof of its absence"
        );
    }

    /// A length claim is now *checkable*, and correctly refuses to discharge a
    /// **null dereference**: `(select ghost_len r) > 0` is satisfiable with
    /// `r = 0`, so it does not rule out the violation.
    ///
    /// This replaces `a_length_claim_refuses_the_discharge_until_lia_tracks_ghost_lengths`,
    /// which asserted `Inconclusive` because `render` declined `Expr::Length`
    /// entirely. That test existed to fail the moment the encoder learned
    /// lengths, and it did. The outcome is still a refusal — but for the right
    /// reason, from a solver that can now read the claim, rather than because
    /// the claim was unreadable.
    #[test]
    fn a_length_claim_is_read_and_still_cannot_discharge_a_dereference() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &body_deref(),
            &inv(Expr::bin(
                Op::Gt,
                Expr::length(Expr::Var(VarId(1))),
                Expr::Int(0),
            )),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "a non-empty array may still be a null reference"
        );
    }

    /// `v1 := new int[v0]`, then `v2 := v1.length`.
    ///
    /// bb0: v1 := new int[v0]; v2 := v1.length  -> bb1
    /// bb1: check, return
    fn body_new_array() -> Body {
        let site = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 0,
        };
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Int,
                },
                VarInfo {
                    kind: VarKind::Local(1),
                    ty: Ty::Ref,
                },
                VarInfo {
                    kind: VarKind::Local(2),
                    ty: Ty::Int,
                },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(2)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![
                Block {
                    id: BlockId(0),
                    bytecode_offset: 0,
                    stmts: vec![
                        Stmt::Assign(
                            VarId(1),
                            Rvalue::NewArray {
                                elem: "I".into(),
                                len: Operand::Var(VarId(0)),
                                site,
                            },
                        ),
                        Stmt::Assign(VarId(2), Rvalue::ArrayLength(Operand::Var(VarId(1)))),
                    ],
                    term: Terminator::Goto(BlockId(1)),
                    exceptional: vec![],
                },
                Block {
                    id: BlockId(1),
                    bytecode_offset: 1,
                    stmts: vec![Stmt::Check(ObligationId(0))],
                    term: Terminator::Return(None),
                    exceptional: vec![],
                },
            ],
        }
    }

    fn map_at(block: BlockId, formula: Expr) -> InvariantMap {
        let mut entries = std::collections::BTreeMap::new();
        entries.insert(
            ProgramPoint {
                method: mk(),
                block,
                index: 0,
            },
            formula,
        );
        InvariantMap {
            id: 1,
            method: mk(),
            entries,
            status: ajave_core::artifact::InvStatus::Candidate,
            scope: ajave_core::artifact::Scope::Method(mk()),
        }
    }

    /// The fact the ghost array exists to carry: after `new int[n]`, the
    /// array's length **is** `n`, and `arraylength` reads back that same value.
    ///
    /// Before P2 this was unprovable twice over. `Rvalue::ArrayLength` had no
    /// arm in `encode_body_lia`, so it fell through to an unconstrained binder
    /// — a *fresh* one per read, so two reads of one length were unrelated —
    /// and `render(Expr::Length)` declined, so the claim could not even be
    /// stated to the solver.
    #[test]
    fn an_array_length_equals_its_allocation_size_and_reads_back() {
        let Some(s) = solver() else { return };
        let r = check_map_inductive(
            &body_new_array(),
            &map_at(
                BlockId(1),
                Expr::bin(
                    Op::Eq,
                    Expr::length(Expr::Var(VarId(1))),
                    Expr::Var(VarId(2)),
                ),
            ),
            s,
        );
        assert_eq!(
            r,
            CertResult::Confirmed,
            "`a.length == v2` must hold where `v2 := a.length`"
        );
    }

    /// The negative control. Without it, `Confirmed` above could come from the
    /// checker waving through anything mentioning `Length`.
    #[test]
    fn a_false_length_claim_is_refuted() {
        let Some(s) = solver() else { return };
        let r = check_map_inductive(
            &body_new_array(),
            &map_at(
                BlockId(1),
                Expr::bin(
                    Op::Eq,
                    Expr::length(Expr::Var(VarId(1))),
                    Expr::bin(Op::Add, Expr::Var(VarId(2)), Expr::Int(1)),
                ),
            ),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "`a.length == v2 + 1` is false where `v2 := a.length`"
        );
    }

    /// The JVMS invariant, for an array this body never allocates.
    ///
    /// `v1` is a parameter here, so the allocation-site facts say nothing about
    /// it; the non-negativity comes from `ghost_preamble`'s ground instances.
    /// Without them no `ArrayBounds` lower bound is provable for any array
    /// reaching a method from outside, which is most of them.
    #[test]
    fn a_parameter_arrays_length_is_non_negative() {
        let Some(s) = solver() else { return };
        let r = check_map_inductive(
            &body_deref(),
            &map_at(
                BlockId(0),
                Expr::bin(Op::Le, Expr::Int(0), Expr::length(Expr::Var(VarId(1)))),
            ),
            s,
        );
        assert_eq!(
            r,
            CertResult::Confirmed,
            "JVMS: an array that exists has a non-negative length"
        );
    }

    /// The mechanism of the p0, at the pass whose job is to catch it.
    ///
    /// `{bb1: 0 <= x, bb2: 0 <= x}` over `x := 0; while (x < n) x++;` was
    /// `Confirmed` before guarded preservation, and it is **not** an invariant
    /// of the Java program: `x = Integer.MAX_VALUE` satisfies `0 <= x`, and
    /// `x++` wraps it negative. That is the same shape as the `0 <= sum`
    /// across `sum = sum + 2` that made `algorithms/BellmanFord-FunUnsat01`
    /// answer TRUE on a program that throws.
    ///
    /// No entry for the entry block, so initiation passes trivially and the
    /// `Refuted` can only come from preservation.
    #[test]
    fn an_overflowing_increment_does_not_preserve_a_lower_bound() {
        let Some(s) = solver() else { return };
        let body = crate::houdini::tests_support::counting_loop();
        let bound = Expr::bin(Op::Le, Expr::Int(0), Expr::Var(VarId(0)));
        let mut entries = std::collections::BTreeMap::new();
        for b in [BlockId(1), BlockId(2)] {
            entries.insert(
                ProgramPoint {
                    method: body.key.clone(),
                    block: b,
                    index: 0,
                },
                bound.clone(),
            );
        }
        let map = InvariantMap {
            id: 1,
            method: body.key.clone(),
            entries,
            status: ajave_core::artifact::InvStatus::Candidate,
            scope: ajave_core::artifact::Scope::Method(body.key.clone()),
        };
        assert_eq!(
            check_map_inductive(&body, &map, s),
            CertResult::Refuted,
            "nothing in this map rules out the wrap on the back edge"
        );
    }

    /// The positive control for the test above, and the demonstration that the
    /// guard is a precision cost rather than a wall.
    ///
    /// Adding `x < n` at the loop body makes the map genuinely inductive: the
    /// pre-state range axiom gives `n <= Integer.MAX_VALUE`, so `x < n`
    /// implies `x + 1 <= MAX_VALUE` and the overflow disjunct is
    /// unsatisfiable. Without the range axiom this would still fail, because
    /// LIA's `n` could be 2^40 — which is why P3 and P4 are only meaningful
    /// together.
    #[test]
    fn the_same_bound_is_confirmed_once_the_map_bounds_the_increment() {
        let Some(s) = solver() else { return };
        let body = crate::houdini::tests_support::counting_loop();
        let bound = Expr::bin(Op::Le, Expr::Int(0), Expr::Var(VarId(0)));
        let mut entries = std::collections::BTreeMap::new();
        entries.insert(
            ProgramPoint {
                method: body.key.clone(),
                block: BlockId(1),
                index: 0,
            },
            bound.clone(),
        );
        entries.insert(
            ProgramPoint {
                method: body.key.clone(),
                block: BlockId(2),
                index: 0,
            },
            Expr::bin(
                Op::And,
                bound,
                Expr::bin(Op::Lt, Expr::Var(VarId(0)), Expr::Var(VarId(1))),
            ),
        );
        let map = InvariantMap {
            id: 2,
            method: body.key.clone(),
            entries,
            status: ajave_core::artifact::InvStatus::Candidate,
            scope: ajave_core::artifact::Scope::Method(body.key.clone()),
        };
        assert_eq!(
            check_map_inductive(&body, &map, s),
            CertResult::Confirmed,
            "`x < n` bounds the increment, so the wrap is excluded"
        );
    }

    /// `Expr::Depth` renders a `depth_*` array **nothing declares**, so the
    /// query z3 saw was missing an assertion. It now declines, and this pins
    /// that: the alternative is a checker confirming claims about an
    /// unconstrained symbol.
    #[test]
    fn a_depth_claim_is_declined_because_no_encoder_maintains_one() {
        let f = ajave_ir::FieldKey {
            class: "Node".into(),
            name: "next".into(),
            desc: "LNode;".into(),
        };
        assert_eq!(
            render(
                &Expr::Depth {
                    field: f,
                    obj: Box::new(Expr::Var(VarId(1)))
                },
                false
            ),
            None,
            "a depth claim must be declined while no encoder maintains depth"
        );
    }

    /// Control. Without this, every `Refuted` below could come from the
    /// checker being unable to confirm anything at all.
    #[test]
    fn a_sufficient_and_preserved_invariant_is_confirmed() {
        let Some(s) = solver() else { return };
        // `v1 >= 1` rules out `v1 == 0`, and the only assignment sets v1 := 5.
        // `v1 >= 1` excludes `v1 == 0`, and nothing in this body assigns v1.
        let r = check_inductive(
            &body_check_only(Ty::Int),
            &inv(ge(1, 1)),
            ObligationId(0),
            s,
        );
        assert_eq!(r, CertResult::Confirmed, "the control fixture must confirm");
    }

    #[test]
    fn an_invariant_that_does_not_imply_safety_is_refuted() {
        let Some(s) = solver() else { return };
        // `true` holds everywhere and rules out nothing, so it cannot justify
        // a discharge however inductive it is.
        let r = check_inductive(
            &body_check_only(Ty::Int),
            &inv(Expr::Bool(true)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "sufficiency must fail: `true` does not exclude the violation"
        );
    }

    #[test]
    fn an_invariant_the_transition_breaks_is_refuted() {
        let Some(s) = solver() else { return };
        // `v1 >= 1` is sufficient (it excludes v1 == 0) but a block assigns
        // v1 := 0, so it is not preserved. This isolates preservation from
        // sufficiency: the first query passes and the second must not.
        let r = check_inductive(
            &body_that_breaks_the_invariant(),
            &inv(ge(1, 1)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Refuted,
            "preservation must fail: a block assigns v1 := 0"
        );
    }

    /// LIA cannot state a float invariant, and a checker that cannot see
    /// floats must decline rather than wave them through. ajave's one
    /// confirmed wrong TRUE is a float-arithmetic proof (#48).
    /// `a = new int[4]; a[0] = 7; check(a[0]);` — the obligation is violated
    /// where the element is 0, and the invariant says it is 7.
    ///
    /// Before H2/H4 this was uncheckable: `ArrayLoad` fell through to a fresh
    /// unconstrained constant, so two reads of the same element were unrelated
    /// and no invariant could mention an array at all.
    fn array_body(store_value: i32) -> Body {
        let site = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 0,
        };
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                ajave_ir::VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Ref,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(1),
                    ty: Ty::Int,
                },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(1)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts: vec![
                    Stmt::Assign(
                        VarId(0),
                        Rvalue::NewArray {
                            elem: "I".into(),
                            len: Operand::Const(Const::Int(4)),
                            site,
                        },
                    ),
                    Stmt::ArrayStore {
                        arr: Operand::Var(VarId(0)),
                        idx: Operand::Const(Const::Int(0)),
                        val: Operand::Const(Const::Int(store_value)),
                    },
                    Stmt::Assign(
                        VarId(1),
                        Rvalue::ArrayLoad {
                            arr: Operand::Var(VarId(0)),
                            idx: Operand::Const(Const::Int(0)),
                        },
                    ),
                    Stmt::Check(ObligationId(0)),
                ],
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    fn elem_eq(n: i64) -> Expr {
        Expr::bin(
            Op::Eq,
            Expr::Select {
                site: ajave_ir::AllocSite {
                    block: BlockId(0),
                    index: 0,
                },
                index: Box::new(Expr::Int(0)),
            },
            Expr::Int(n),
        )
    }

    /// `o.f = stored; e = o.f; c = (e == asserted); check(c)` with `o` from a
    /// fresh allocation. Two receivers when `two` is set, so the aliasing case
    /// can be stated.
    fn field_body(stored: i32, asserted: i32, two: bool) -> Body {
        let site = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 0,
        };
        let site2 = ajave_ir::AllocSite {
            block: BlockId(0),
            index: 3,
        };
        let f = ajave_ir::FieldKey {
            class: "Box".into(),
            name: "v".into(),
            desc: "I".into(),
        };
        let mut stmts = vec![
            Stmt::Assign(
                VarId(0),
                Rvalue::New {
                    class: "Box".into(),
                    site,
                },
            ),
            Stmt::PutField {
                obj: Operand::Var(VarId(0)),
                field: f.clone(),
                val: Operand::Const(Const::Int(stored)),
            },
        ];
        if two {
            // A second, distinct object whose field holds something else. The
            // flat abstraction would merge these; field-as-array must not.
            stmts.push(Stmt::Assign(
                VarId(3),
                Rvalue::New {
                    class: "Box".into(),
                    site: site2,
                },
            ));
            stmts.push(Stmt::PutField {
                obj: Operand::Var(VarId(3)),
                field: f.clone(),
                val: Operand::Const(Const::Int(99)),
            });
        }
        stmts.push(Stmt::Assign(
            VarId(1),
            Rvalue::GetField {
                obj: Operand::Var(VarId(0)),
                field: f.clone(),
            },
        ));
        stmts.push(Stmt::Assign(
            VarId(2),
            Rvalue::Bin(
                ajave_ir::BinOp::Eq,
                Operand::Var(VarId(1)),
                Operand::Const(Const::Int(asserted)),
            ),
        ));
        stmts.push(Stmt::Check(ObligationId(0)));
        // Fix the site indices to where the statements actually sit.
        if two {
            if let Stmt::Assign(_, Rvalue::New { site, .. }) = &mut stmts[2] {
                site.index = 2;
            }
        }
        Body {
            is_static: true,
            key: mk(),
            entry: BlockId(0),
            vars: vec![
                ajave_ir::VarInfo {
                    kind: VarKind::Local(0),
                    ty: Ty::Ref,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(1),
                    ty: Ty::Int,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(2),
                    ty: Ty::Int,
                },
                ajave_ir::VarInfo {
                    kind: VarKind::Local(3),
                    ty: Ty::Ref,
                },
            ],
            obligations: vec![Obligation {
                id: ObligationId(0),
                kind: ObligationKind::Assertion,
                cond: Operand::Var(VarId(2)),
                guarded: false,
                bytecode_offset: 0,
                line: None,
            }],
            blocks: vec![Block {
                id: BlockId(0),
                bytecode_offset: 0,
                stmts,
                term: Terminator::Return(None),
                exceptional: vec![],
            }],
        }
    }

    fn fld_eq(n: i64) -> Expr {
        Expr::Bin(
            Op::Eq,
            Box::new(Expr::Field {
                field: ajave_ir::FieldKey {
                    class: "Box".into(),
                    name: "v".into(),
                    desc: "I".into(),
                },
                obj: Box::new(Expr::Var(VarId(0))),
            }),
            Box::new(Expr::Int(n)),
        )
    }

    /// A1/A2 control. Before field-as-array, `GetField` fell through to a
    /// fresh constant and no invariant could mention a field at all.
    #[test]
    fn a_field_invariant_can_be_confirmed() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &field_body(7, 7, false),
            &inv(fld_eq(7)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Confirmed,
            "the store writes 7, so `o.v == 7` is sufficient and preserved"
        );
    }

    #[test]
    fn a_field_invariant_contradicted_by_the_store_is_refuted() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &field_body(0, 7, false),
            &inv(fld_eq(7)),
            ObligationId(0),
            s,
        );
        assert_ne!(r, CertResult::Confirmed, "the store writes 0");
    }

    /// The reason the Burstall model was chosen. A second object's field write
    /// must not disturb the first's — which the flat abstraction in
    /// `interval.rs` cannot express, and which this gets from the solver for
    /// free because `o` and `p` are distinct references.
    #[test]
    fn a_second_receivers_write_does_not_disturb_the_first() {
        let Some(s) = solver() else { return };
        let r = check_inductive(&field_body(7, 7, true), &inv(fld_eq(7)), ObligationId(0), s);
        assert_eq!(
            r,
            CertResult::Confirmed,
            "p.v = 99 must not make o.v == 7 unprovable; if this fails the \
             field cells are merged rather than indexed by receiver"
        );
    }

    /// The control for the array path. If this cannot confirm, every negative
    /// array result below is vacuous.
    #[test]
    fn an_array_element_invariant_can_be_confirmed() {
        let Some(s) = solver() else { return };
        let r = check_inductive(&array_body(7), &inv(elem_eq(7)), ObligationId(0), s);
        assert_eq!(
            r,
            CertResult::Confirmed,
            "the store writes 7, so `a[0] == 7` is sufficient and preserved"
        );
    }

    /// The store writes 0, so the element *is* the violating value and an
    /// invariant claiming otherwise must not be confirmed. This is the test
    /// that would have passed vacuously before the encoder modelled arrays:
    /// an unconstrained read makes every array invariant unprovable, so a
    /// `Refuted` here would have meant nothing without the control above.
    #[test]
    fn an_array_invariant_contradicted_by_the_store_is_refuted() {
        let Some(s) = solver() else { return };
        let r = check_inductive(&array_body(0), &inv(elem_eq(7)), ObligationId(0), s);
        assert_ne!(
            r,
            CertResult::Confirmed,
            "the store writes 0; `a[0] == 7` cannot be confirmed"
        );
    }

    #[test]
    fn a_float_invariant_cannot_be_confirmed() {
        let Some(s) = solver() else { return };
        let r = check_inductive(
            &body_check_only(Ty::Float),
            &inv(ge(1, 1)),
            ObligationId(0),
            s,
        );
        assert_eq!(
            r,
            CertResult::Inconclusive,
            "a float invariant must be Inconclusive, never Confirmed"
        );
    }

    #[test]
    fn an_unmodelled_library_application_cannot_be_confirmed() {
        let Some(s) = solver() else { return };
        let apply = Expr::call("java/lang/Math", "sin", "(D)D", vec![Expr::Var(VarId(0))]);
        let r = check_inductive(
            &body_check_only(Ty::Int),
            &inv(Expr::bin(Op::Ge, apply, Expr::Int(0))),
            ObligationId(0),
            s,
        );
        assert_eq!(r, CertResult::Inconclusive);
    }
}
