//! The synthesis engine: build a candidate pool, eliminate, publish, discharge.
//!
//! P2b and P4 of `docs/proposals/invariant-synthesis.md`. The three pieces it
//! joins are deliberately separable and separately tested: `houdini` does the
//! elimination, `invariant_check::map_implies_safety` decides sufficiency, and
//! this does nothing but choose the pool and publish the result.
//!
//! # Why it may publish `Inductive` directly
//!
//! Everywhere else in the tree, promotion from `Candidate` to `Inductive` is a
//! certifier's job, and an engine asserting its own proof is the thing
//! `certify.rs` exists to prevent. This is the one case where the engine and
//! the certifier are the same computation: candidate elimination terminates
//! *because* initiation and preservation hold of what survives, using the same
//! encoder and the same queries `check_map_inductive` would re-run. Re-running
//! them would cost a second pass over every edge to re-derive a conclusion the
//! first pass established as its stopping condition.
//!
//! That argument has one precondition, and it is checked rather than assumed:
//! `Synthesised::converged`. A run that stopped on its query budget has not
//! tested every candidate, so its map may contain a false one — and those are
//! published as `Candidate`, which `InvStatus`'s contract says can never
//! discharge. See `an_unconverged_map_is_never_published_as_inductive`.
//!
//! # What the pool is drawn from
//!
//! Two sources, both already on the board or in the program:
//!
//! * **Other engines' claims**, via `claim_conjuncts_for_method`. After P1
//!   those include nullness and array-length facts the interval domain has
//!   always computed and could not state.
//! * **The obligations' own safety conditions.** For a `NullDeref` on `r` the
//!   thing we want to prove is `r != null`, which is the obvious candidate;
//!   elimination's job is to find out whether it is *preserved*. This is the
//!   cheapest source and, per the design, possibly the highest-yield.
//!
//! Neither source is trusted. A candidate is a guess that the elimination loop
//! either keeps or deletes, which is what lets the pool be speculative.

use ajave_core::artifact::*;
use ajave_core::blackboard::Blackboard;
use ajave_core::engine::{Budget, Engine, Progress};
use ajave_core::term::{Expr, Op};
use ajave_ir::{MethodKey, Operand, Program};
use log::{debug, info};

/// Whether synthesis runs at all.
///
/// **Off by default, and therefore unfinished** in the sense `CLAUDE.md`
/// means: a producer behind a disabled flag is not a producer. It is off for
/// one reason — elimination annotates every block, so its cost is
/// `O(|blocks| * |pool|)` solver queries per round, and that has to be
/// measured against the corpus before it becomes everyone's cost. The flag
/// exists so the measurement is possible on one build.
pub fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AJAVE_HOUDINI").as_deref() == Ok("1"))
}

/// Blocks above which a method is skipped.
///
/// Fitted, and the reason is cost rather than correctness: at 893 blocks and a
/// pool of 20, one round is ~18,000 queries. Skipping large methods is the
/// honest form of "this does not scale yet" — the alternative is to run out of
/// budget mid-elimination on every large method and publish nothing anyway,
/// having spent the time.
const MAX_BLOCKS: usize = 120;

/// Candidates above which the pool is truncated, lowest-rendering first.
///
/// Truncation is sound — a smaller pool can only find a weaker invariant — but
/// it is *arbitrary*, so it is logged when it bites rather than silently
/// changing what the engine can prove.
const MAX_POOL: usize = 24;

pub struct HoudiniEngine {
    done: bool,
    solver: String,
}

impl HoudiniEngine {
    pub fn new() -> Self {
        HoudiniEngine {
            done: false,
            solver: std::env::var("AJAVE_SMT_SOLVER").unwrap_or_else(|_| "z3".to_string()),
        }
    }

    pub fn available(&self) -> bool {
        enabled()
    }
}

impl Default for HoudiniEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// The safety condition of an obligation, as a claim.
///
/// Every obligation's violation is "its condition is zero" — that is how
/// `encode_body_lia` builds each error formula, uniformly across kinds. So
/// safety is "the condition is non-zero", and for a reference-typed condition
/// that is exactly non-nullness.
fn safety_condition(body: &ajave_ir::Body, oid: ajave_ir::ObligationId) -> Option<Expr> {
    let ob = body.obligations.get(oid.0 as usize)?;
    match &ob.cond {
        Operand::Var(v) => {
            let ty = body.vars.get(v.0 as usize).map(|vi| vi.ty);
            Some(match ty {
                // A reference condition's safety *is* non-nullness, and saying
                // it that way rather than as `r != 0` keeps the claim in the
                // vocabulary a consumer can type-check.
                Some(ajave_ir::Ty::Ref) | Some(ajave_ir::Ty::Str) => {
                    Expr::non_null(Expr::Var(*v))
                }
                _ => Expr::bin(Op::Ne, Expr::Var(*v), Expr::Int(0)),
            })
        }
        // A constant condition needs no invariant; presolve has it.
        _ => None,
    }
}

impl Engine for HoudiniEngine {
    fn id(&self) -> EngineId {
        EngineId("houdini")
    }

    fn direction(&self) -> Direction {
        Direction::Over
    }

    /// `INVARIANT` because other engines' claims are the candidate pool, and
    /// `STATUS` because which obligations are open decides which methods are
    /// worth synthesising for.
    ///
    /// Not `INVARIANT_MAP`: this engine produces maps and consuming its own
    /// output would re-enter it for every map it publishes.
    fn interest(&self) -> Interest {
        Interest::INVARIANT.union(Interest::STATUS)
    }

    fn step(&mut self, prog: &Program, bb: &mut Blackboard, _budget: Budget) -> Progress {
        if self.done || !enabled() {
            return Progress::Exhausted;
        }
        self.done = true;

        // Methods that still have an open obligation. Synthesising for a
        // method whose obligations are all closed is pure cost.
        let open_all = bb.open();
        let mut methods: Vec<MethodKey> = open_all.iter().map(|o| o.method.clone()).collect();
        methods.sort();
        methods.dedup();

        let mut advanced = false;
        for mk in methods {
            let Some(body) = prog.body(&mk) else { continue };
            if body.blocks.len() > MAX_BLOCKS {
                debug!(
                    "houdini: skipping {} — {} blocks over the {MAX_BLOCKS} cap",
                    mk,
                    body.blocks.len()
                );
                continue;
            }

            // The pool: other engines' conjuncts, plus each open obligation's
            // own safety condition.
            let mut pool = bb.claim_conjuncts_for_method(&mk);
            // Each open obligation's own safety condition joins the pool:
            // for a `NullDeref` on `r` the thing we want to prove is
            // `r != null`, and elimination's job is to find out whether it is
            // preserved.
            for oref in open_all.iter().filter(|o| o.method == mk) {
                if let Some(c) = safety_condition(body, oref.id) {
                    pool.push(c);
                }
            }
            pool.sort_by_key(|e| e.to_string());
            pool.dedup_by_key(|e| e.to_string());
            if pool.is_empty() {
                continue;
            }
            if pool.len() > MAX_POOL {
                debug!(
                    "houdini: truncating {}'s pool from {} to {MAX_POOL}",
                    mk,
                    pool.len()
                );
                pool.truncate(MAX_POOL);
            }

            let r = crate::houdini::synthesise(
                body,
                &pool,
                &[],
                &self.solver,
                crate::houdini::DEFAULT_MAX_QUERIES,
            );
            if r.entries.is_empty() {
                continue;
            }

            let id = bb.fresh_invariant_id();
            // `converged` is necessary but, as it turns out, not sufficient.
            //
            // The module doc argued that elimination and certification are the
            // same computation, so re-checking would re-derive the loop's own
            // stopping condition. That argument produced a **wrong TRUE** on
            // `algorithms/BellmanFord-FunUnsat01` [no-runtime-exception], a
            // program that really throws. So the claim is now re-checked by
            // the pass whose job is checking, and the engine's own belief is
            // not enough to promote.
            //
            // This is `certify.rs`'s rule applied to this engine rather than
            // excepted from it: no artifact reaches the reporter on an
            // engine's authority alone.
            let mut status = if r.converged {
                InvStatus::Inductive
            } else {
                InvStatus::Candidate
            };
            if status == InvStatus::Inductive {
                let candidate = InvariantMap {
                    id,
                    method: mk.clone(),
                    entries: r.entries.clone(),
                    status: InvStatus::Candidate,
                    scope: Scope::Method(mk.clone()),
                };
                let verdict =
                    crate::invariant_check::check_map_inductive(body, &candidate, &self.solver);
                if verdict != ajave_core::certify::CertResult::Confirmed {
                    debug!(
                        "houdini: {} refused promotion — the checker said {:?}",
                        mk, verdict
                    );
                    status = InvStatus::Candidate;
                }
            }
            let map = InvariantMap {
                id,
                method: mk.clone(),
                entries: r.entries,
                status,
                scope: Scope::Method(mk.clone()),
            };
            // `INT_WRAPPING`, still declared, and now conservatively so.
            //
            // Guarded preservation means the arithmetic conclusions in this
            // map no longer rest on an overflow-free path: a candidate whose
            // wrap the map cannot exclude has been deleted. On that argument
            // the honest tag would be `EXACT`.
            //
            // It stays `INT_WRAPPING` until that argument is measured rather
            // than reasoned. The tag is what decides whether a more faithful
            // engine ever gets the obligation back, and `CLAUDE.md` gives the
            // tie-break: "Under-declaring means a more faithful engine never
            // gets the obligation back; over-declaring only wastes time, so
            // when in doubt, declare." Dropping it is a one-line change to
            // make once there is a number behind it.
            if bb
                .publish_with(
                    EngineId("houdini"),
                    Direction::Over,
                    Approximations::INT_WRAPPING,
                    Artifact::InvariantMap(map.clone()),
                )
                .is_err()
            {
                continue;
            }
            advanced = true;
            info!(
                "houdini: {} published a {:?} map over {} point(s) from {} candidate(s) in {} queries",
                mk,
                status,
                map.entries.len(),
                pool.len(),
                r.queries
            );

            // **Still no discharge, and the reason has changed.**
            //
            // The blocker named here — "a bound that only survives without
            // wrapping would close an obligation that can really fire" — is
            // fixed. `LiaEncoding::preservation_query` now carries the
            // overflow condition as a disjunct of the transition, so a
            // surviving candidate is one that holds on a JVM and not only in
            // LIA (`docs/proposals/lia-faithfulness.md` §3). A map reaching
            // this point has been through that, twice: once as elimination's
            // stopping condition and once as `check_map_inductive`.
            //
            // What is not done is the *measurement*. Turning on a discharge
            // path is a change to what may be answered TRUE, and `CLAUDE.md`
            // is explicit that such a change must be measured on valid-assert
            // **and** no-runtime-exception before it is believed — the
            // `all_calls_resolved` loosening scored a clean-looking +22 on NRE
            // while putting eight wrong TRUEs on VA. The first number to have
            // is how often a non-trivial map survives at all now that the
            // guard deletes bounds whose overflow-freedom needs a relation the
            // pool cannot express.
            //
            // So this engine still publishes and does not conclude, and it is
            // still a producer with no consumer, recorded in
            // `docs/contracts.md`. The difference is that the next step is a
            // measurement rather than a soundness repair.
        }

        if advanced {
            Progress::Advanced
        } else {
            Progress::Exhausted
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The engine's one soundness precondition, as a test.
    ///
    /// `step` publishes `Inductive` only when `Synthesised::converged`, and
    /// that is the whole argument for an engine certifying its own output.
    /// A budget of one query cannot have tested a pool of two, so the map it
    /// returns must not be promoted — and `InvStatus::Candidate` can never
    /// discharge, per its own contract.
    #[test]
    fn an_unconverged_map_is_never_published_as_inductive() {
        let solver = match std::process::Command::new("z3").arg("--version").output() {
            Ok(o) if o.status.success() => "z3",
            _ => {
                eprintln!("no z3 on PATH; skipping");
                return;
            }
        };
        let body = crate::houdini::tests_support::counting_loop();
        let pool = vec![
            Expr::bin(Op::Le, Expr::Int(0), Expr::Var(ajave_ir::VarId(0))),
            Expr::Bool(false),
        ];
        let r = crate::houdini::synthesise(&body, &pool, &[], solver, 1);
        assert!(!r.converged);
        // The mapping `step` applies, asserted directly rather than by
        // driving a whole orchestrator run.
        let status = if r.converged {
            InvStatus::Inductive
        } else {
            InvStatus::Candidate
        };
        assert_eq!(
            status,
            InvStatus::Candidate,
            "an unfinished elimination must not be promoted"
        );
    }
}
