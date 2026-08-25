//! ajave-frontend: bytecode in, `ajave_ir::Program` out.
//!
//! Depends only on `ajave-ir` (the representation it produces) and
//! `ajave-models` (what it's allowed to assume about the standard
//! library). Deliberately has no dependency on `ajave-core`: the lifter
//! has no business knowing that verification engines exist, and this
//! is enforced by the crate graph, not just convention.

pub mod classfile;
pub mod lift;
