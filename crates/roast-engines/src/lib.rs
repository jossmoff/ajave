//! roast-engines: concrete strategies built on `roast-core`.
//!
//! Each module here is deliberately small and independently removable.
//! Adding a technique means implementing `roast_core::engine::Engine` or
//! `roast_core::cpa::Cpa` in a new module and registering it in
//! `roast-cli` -- nothing in this crate or `roast-core` should need to
//! change. See `docs/strategies/` for the write-up of each one.

pub mod ai;
pub mod concrete;
pub mod interval;
pub mod presolve;
pub mod smt_bmc;
