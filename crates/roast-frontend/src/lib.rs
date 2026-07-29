//! roast-frontend: bytecode in, `roast_ir::Program` out.
//!
//! Depends only on `roast-ir` (the representation it produces) and
//! `roast-models` (what it's allowed to assume about the standard
//! library). Deliberately has no dependency on `roast-core`: the lifter
//! has no business knowing that verification engines exist, and this
//! is enforced by the crate graph, not just convention.

pub mod classfile;
pub mod lift;
