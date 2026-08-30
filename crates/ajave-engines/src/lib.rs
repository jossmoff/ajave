//! ajave-engines: concrete strategies built on `ajave-core`.
//!
//! Each module here is deliberately small and independently removable.
//! Adding a technique means implementing `ajave_core::engine::Engine` or
//! `ajave_core::cpa::Cpa` in a new module and registering it in
//! `ajave-cli` -- nothing in this crate or `ajave-core` should need to
//! change. See `docs/strategies/` for the write-up of each one.

pub mod body_analysis;
// Re-exported for the CLI's verdict guard: an unmodelled throwing call means a
// TRUE for no-runtime-exception is not ours to claim.
pub use body_analysis::{body_has_unmodelled_throwing_call, first_unmodelled_throwing_call};
pub mod body_shape;
pub mod concurrency;
pub mod concurrent_exec;
pub mod concurrent_state;
pub mod threads;
pub mod ai;
pub mod cegar;
pub mod chc;
pub mod concrete;
pub mod float_search;
mod math_eval;
mod str_eval;
pub mod imc;
pub mod interpolation;
pub mod interval;
pub mod kinduction;
pub mod nra;
pub mod predicate;
pub mod presolve;
pub mod smt_bmc;
pub mod smt_encode;
pub mod smt_text;
