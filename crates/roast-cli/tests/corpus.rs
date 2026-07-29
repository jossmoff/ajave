//! Integration tests: run the roast binary against every task and assert the
//! current verdict.
//!
//! # What these tests enforce
//!
//! Each test asserts the verdict roast *currently* produces, not necessarily
//! what SV-COMP expects. A comment on each test records the SV-COMP expected
//! verdict when they differ. CI fails if a verdict changes in *any* direction;
//! changing a test is the explicit signal that behaviour changed:
//!
//! - If you improve a task from UNKNOWN to the correct verdict, update the
//!   assert to match and note the improvement in the commit message.
//! - If a previously-correct verdict regresses, that is a soundness bug —
//!   fix it before changing the assert.
//!
//! Tests run in parallel by default via `cargo test`.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Absolute path to the workspace root (two directories above the CLI crate).
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// Run the roast binary against the given inputs and return the verdict line.
/// Panics if roast crashes or produces no output.
fn roast(inputs: &[&str]) -> String {
    let root = workspace_root();
    let binary = env!("CARGO_BIN_EXE_roast");
    let abs_inputs: Vec<PathBuf> = inputs.iter().map(|p| root.join(p)).collect();

    let out = Command::new(binary)
        .args(&abs_inputs)
        .output()
        .unwrap_or_else(|e| panic!("failed to run roast: {e}"));

    let stdout = String::from_utf8_lossy(&out.stdout);
    stdout
        .lines()
        .filter(|l| !l.trim().is_empty())
        .last()
        .unwrap_or("(no output)")
        .trim()
        .to_string()
}

// ─── Hand-crafted tasks ──────────────────────────────────────────────────────

#[test]
fn stage00_const() {
    // Trivial const assert failure: assert 1 == 2. SV-COMP: false.
    assert_eq!(roast(&["tasks/stage00_const", "tasks/common"]), "FALSE");
}

#[test]
fn stage01_nondet() {
    // nondetInt() with assume(x >= 4), assert x > 3. SV-COMP: true.
    assert_eq!(roast(&["tasks/common", "tasks/stage01_nondet"]), "TRUE");
}

#[test]
fn stage02_branch() {
    // Branch always sets y >= 10, assert y >= 10. SV-COMP: true.
    assert_eq!(roast(&["tasks/common", "tasks/stage02_branch"]), "TRUE");
}

#[test]
fn stage04_divzero() {
    // 100 / nondetInt() — zero is reachable. SV-COMP: false.
    assert_eq!(roast(&["tasks/common", "tasks/stage04_divzero"]), "FALSE");
}

#[test]
fn arithmetic_exception1() {
    // assume(i >= 4), divide 10/i — zero impossible. SV-COMP: true.
    assert_eq!(roast(&["tasks/common", "tasks/ArithmeticException1"]), "TRUE");
}

#[test]
fn arithmetic_exception2() {
    // No assume on divisor — i=0 triggers exception and assert false. SV-COMP: false.
    assert_eq!(roast(&["tasks/common", "tasks/ArithmeticException2"]), "FALSE");
}

#[test]
fn arithmetic_exception3() {
    // assume(i > 0), divide 10/i — zero impossible. SV-COMP: true.
    assert_eq!(roast(&["tasks/common", "tasks/ArithmeticException3"]), "TRUE");
}

#[test]
fn branch_divide1() {
    // Branch guards x != 0 before 100/x. SV-COMP: true.
    // UNKNOWN: interval domain does not yet track branch-guarded zero exclusion.
    assert_eq!(roast(&["tasks/common", "tasks/BranchDivide1"]), "UNKNOWN");
}

#[test]
fn bounded_loop1() {
    // Deterministic loop: sum += 2 five times, assert sum == 10. SV-COMP: true.
    // UNKNOWN: loop convergence not yet proven by interval domain.
    assert_eq!(roast(&["tasks/common", "tasks/BoundedLoop1"]), "UNKNOWN");
}

#[test]
fn bounded_loop2() {
    // n in [0,3], loop runs n times; n=0 gives sum=0, assert sum>=1 fails. SV-COMP: false.
    assert_eq!(roast(&["tasks/common", "tasks/BoundedLoop2"]), "FALSE");
}

#[test]
fn integer_arithmetic1() {
    // x in [1,100], y = x*2, assert y > 0. SV-COMP: true.
    assert_eq!(roast(&["tasks/common", "tasks/IntegerArithmetic1"]), "TRUE");
}

#[test]
fn integer_arithmetic2() {
    // x,y > 0 but x+y can wrap (MAX_VALUE+1). SV-COMP: false.
    assert_eq!(roast(&["tasks/common", "tasks/IntegerArithmetic2"]), "FALSE");
}

#[test]
fn modulo_zero1() {
    // x % 0 always throws. SV-COMP: false.
    assert_eq!(roast(&["tasks/common", "tasks/ModuloZero1"]), "FALSE");
}

#[test]
fn nested_branch1() {
    // Inputs bounded [1,1000], result = max(x,y) >= 1. SV-COMP: true.
    assert_eq!(roast(&["tasks/common", "tasks/NestedBranch1"]), "TRUE");
}

// ─── jbmc-regression tasks ───────────────────────────────────────────────────

#[test]
fn jbmc_assert1() {
    // if (i>=10) assert i>=10 — always holds. SV-COMP: true.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/assert1"]),
        "TRUE"
    );
}

#[test]
fn jbmc_assert2() {
    // if (i>=1000) assert i>1000 — i=1000 fails. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/assert2"]),
        "FALSE"
    );
}

#[test]
fn jbmc_arithmetic_exception5() {
    // double 10.0/0.0 = Infinity (no ArithmeticException). SV-COMP: true.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/ArithmeticException5"]),
        "TRUE"
    );
}

#[test]
fn jbmc_arithmetic_exception6() {
    // int 10/nondetInt() — denom can be 0. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/ArithmeticException6"]),
        "FALSE"
    );
}

#[test]
fn jbmc_negative_array_size_exception1() {
    // new int[-1] always throws NegativeArraySizeException. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/NegativeArraySizeException1"]),
        "FALSE"
    );
}

#[test]
fn jbmc_negative_array_size_exception2() {
    // new int[-1] caught by Exception. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/NegativeArraySizeException2"]),
        "FALSE"
    );
}

#[test]
fn jbmc_null_pointer_exception1() {
    // null.hashCode() throws NPE into empty catch; assert false unreachable. SV-COMP: true.
    // UNKNOWN: null-check exception routing not yet modelled for method calls.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/NullPointerException1"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_null_pointer_exception2() {
    // null.i = 0 throws NPE; catch has assert false. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/NullPointerException2"]),
        "FALSE"
    );
}

#[test]
fn jbmc_null_pointer_exception3() {
    // null.i (read) throws NPE; catch has assert false. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/NullPointerException3"]),
        "FALSE"
    );
}

#[test]
fn jbmc_null_pointer_exception4() {
    // null.i = 0 caught by Exception; assert false. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/NullPointerException4"]),
        "FALSE"
    );
}

#[test]
fn jbmc_class_cast_exception1() {
    // Integer cast to String always throws ClassCastException. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/ClassCastException1"]),
        "FALSE"
    );
}

#[test]
fn jbmc_class_cast_exception2() {
    // C extends B; (B) c succeeds, no exception. SV-COMP: true.
    // UNKNOWN: ClassCast check routing not yet modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/ClassCastException2"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_class_method1() {
    // assert f(String.class, true) where f returns its boolean arg. SV-COMP: true.
    // UNKNOWN: static method call with Class argument not yet inlined.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/Class_method1"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_inheritance1() {
    // Constructor-initialized fields across three levels. SV-COMP: true.
    // UNKNOWN: field-content tracking not yet implemented.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/Inheritance1"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_arraylength1() {
    // int_array.length == size after new int[size]. SV-COMP: true.
    // UNKNOWN: array length not tracked in current heap model.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/arraylength1"]),
        "UNKNOWN"
    );
}
