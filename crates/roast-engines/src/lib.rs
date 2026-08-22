//! roast-engines: concrete strategies built on `roast-core`.
//!
//! Each module here is deliberately small and independently removable.
//! Adding a technique means implementing `roast_core::engine::Engine` or
//! `roast_core::cpa::Cpa` in a new module and registering it in
//! `roast-cli` -- nothing in this crate or `roast-core` should need to
//! change. See `docs/strategies/` for the write-up of each one.

pub mod ai;
pub mod body_analysis;
pub mod body_shape;
pub mod cegar;
pub mod chc;
pub mod concrete;
pub mod imc;
pub mod interpolation;
pub mod interval;
pub mod kinduction;
mod math_eval;
#[cfg(feature = "nra")]
pub mod nra;
pub mod predicate;
pub mod presolve;
pub mod smt_bmc;
pub mod smt_encode;
pub mod smt_text;
mod str_eval;
