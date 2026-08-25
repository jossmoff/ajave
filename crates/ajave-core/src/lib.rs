//! ajave-core: the verification core.
//!
//! Language-agnostic on purpose -- it knows about obligations, artifacts
//! and fixpoints, not about Java. Depends on `ajave-ir` (what it analyses)
//! and `ajave-models` (the exception-class lookup `certify` and the
//! orchestrator need), and nothing else. No dependency on `ajave-frontend`:
//! swapping the frontend for a different language's bytecode should never
//! require touching a line in here, and the crate graph makes that a
//! build error rather than a code-review reminder if it's ever violated.
//!
//! See `docs/strategies/` for the documented rationale behind each engine
//! and domain built on top of this crate.

pub mod artifact;
pub mod blackboard;
pub mod certify;
pub mod cpa;
pub mod engine;
pub mod orchestrator;
pub mod smt;
pub mod smt_smtlib;
pub mod witness;
