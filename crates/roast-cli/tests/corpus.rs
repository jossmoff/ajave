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
        .rfind(|l| !l.trim().is_empty())
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
    assert_eq!(
        roast(&["tasks/common", "tasks/ArithmeticException1"]),
        "TRUE"
    );
}

#[test]
fn arithmetic_exception2() {
    // No assume on divisor — i=0 triggers exception and assert false. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/ArithmeticException2"]),
        "FALSE"
    );
}

#[test]
fn arithmetic_exception3() {
    // assume(i > 0), divide 10/i — zero impossible. SV-COMP: true.
    assert_eq!(
        roast(&["tasks/common", "tasks/ArithmeticException3"]),
        "TRUE"
    );
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
    assert_eq!(
        roast(&["tasks/common", "tasks/IntegerArithmetic2"]),
        "FALSE"
    );
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
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/NegativeArraySizeException1"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_negative_array_size_exception2() {
    // new int[-1] caught by Exception. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/NegativeArraySizeException2"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_null_pointer_exception1() {
    // null.hashCode() throws NPE into empty catch; assert false unreachable. SV-COMP: true.
    // UNKNOWN: null-check exception routing not yet modelled for method calls.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/NullPointerException1"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_null_pointer_exception2() {
    // null.i = 0 throws NPE; catch has assert false. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/NullPointerException2"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_null_pointer_exception3() {
    // null.i (read) throws NPE; catch has assert false. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/NullPointerException3"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_null_pointer_exception4() {
    // null.i = 0 caught by Exception; assert false. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/NullPointerException4"
        ]),
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

#[test]
fn jbmc_arithmetic_exception1() {
    // nondetInt() with no assume, divide 10/i — i=0 reachable. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/ArithmeticException1"]),
        "FALSE"
    );
}

#[test]
fn jbmc_array_index_out_of_bounds_exception1() {
    // new int[4], a[size] = 0 where size nondet. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/ArrayIndexOutOfBoundsException1"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_array_index_out_of_bounds_exception2() {
    // new int[4], a[size] read where size nondet. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/ArrayIndexOutOfBoundsException2"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_array_index_out_of_bounds_exception3() {
    // new int[4], a[nondetInt()] — negative or >= 4 triggers exception. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/ArrayIndexOutOfBoundsException3"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_buffered_reader_read_line() {
    // BufferedReader.readLine on nondetString. SV-COMP: false.
    // UNKNOWN: BufferedReader/StringReader I/O not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/BufferedReaderReadLine"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_char_sequence_bug() {
    // s.replace('b','c') then assert indexOf('b') != -1. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/CharSequenceBug"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_char_sequence_to_string() {
    // CharSequence.toString() length check. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/CharSequenceToString"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_class_cast_exception3() {
    // (B) new A() always throws ClassCastException. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/ClassCastException3"]),
        "FALSE"
    );
}

#[test]
fn jbmc_regex_matches01() {
    // Regex match returns true for a matching pattern. SV-COMP: true.
    // UNKNOWN: regex/string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/RegexMatches01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_regex_matches02() {
    // Regex match assert failure. SV-COMP: false.
    // UNKNOWN: regex/string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/RegexMatches02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_regex_substitution01() {
    // Regex substitution result assertion. SV-COMP: true.
    // UNKNOWN: regex/string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/RegexSubstitution01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_regex_substitution02() {
    // Regex substitution assert failure. SV-COMP: false.
    // UNKNOWN: regex/string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/RegexSubstitution02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_regex_substitution03() {
    // Regex substitution result assertion. SV-COMP: true.
    // UNKNOWN: regex/string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/RegexSubstitution03"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_static_char_methods01() {
    // Character.isLetter etc. assertions hold. SV-COMP: true.
    // UNKNOWN: Character static methods not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StaticCharMethods01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_static_char_methods02() {
    // Character method assert failure. SV-COMP: false.
    // UNKNOWN: Character static methods not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StaticCharMethods02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_static_char_methods03() {
    // Character.isDefined(charAt(0)) == false fails for any defined char. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StaticCharMethods03"]),
        "FALSE"
    );
}

#[test]
fn jbmc_static_char_methods04() {
    // Character method assert failure — trivially detectable. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StaticCharMethods04"]),
        "FALSE"
    );
}

#[test]
fn jbmc_static_char_methods05() {
    // Character method assert failure. SV-COMP: false.
    // UNKNOWN: Character static methods not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StaticCharMethods05"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_static_char_methods06() {
    // Character method assertions hold. SV-COMP: true.
    // UNKNOWN: Character static methods not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StaticCharMethods06"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_append01() {
    // StringBuilder.append chain assertion holds. SV-COMP: true.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderAppend01"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_append02() {
    // StringBuilder.append: appended content is tracked. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderAppend02"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_cap_len01() {
    // StringBuilder capacity/length assertion holds. SV-COMP: true.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderCapLen01"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_cap_len02() {
    // StringBuilder capacity/length assert failure. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderCapLen02"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_cap_len03() {
    // StringBuilder capacity/length assert failure. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderCapLen03"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_cap_len04() {
    // StringBuilder capacity/length assert failure. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderCapLen04"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_chars01() {
    // StringBuilder char access assertion holds. SV-COMP: true.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringBuilderChars01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_chars02() {
    // StringBuilder char access assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringBuilderChars02"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_chars03() {
    // StringBuilder char access assert failure. SV-COMP: false.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringBuilderChars03"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_chars04() {
    // StringBuilder char access assert failure. SV-COMP: false.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringBuilderChars04"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_chars05() {
    // StringBuilder char access assert failure. SV-COMP: false.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringBuilderChars05"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_chars06() {
    // StringBuilder char access assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringBuilderChars06"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_constructors01() {
    // StringBuilder constructor assertion holds. SV-COMP: true.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderConstructors01"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_constructors02() {
    // StringBuilder constructor assert failure. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderConstructors02"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_builder_insert_delete01() {
    // StringBuilder insert/delete assertion holds. SV-COMP: true.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderInsertDelete01"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_insert_delete02() {
    // StringBuilder insert/delete assert failure. SV-COMP: false.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderInsertDelete02"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_builder_insert_delete03() {
    // StringBuilder insert/delete assert failure. SV-COMP: false.
    // UNKNOWN: StringBuilder not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringBuilderInsertDelete03"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_compare01() {
    // String comparison assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringCompare01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_compare02() {
    // String comparison assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringCompare02"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_compare03() {
    // String comparison: new String(s) != s (reference equality). SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringCompare03"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_compare04() {
    // String comparison assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringCompare04"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_compare05() {
    // new String(s) != s (different objects); else assert false. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringCompare05"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_concatenation01() {
    // String concatenation assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringConcatenation01"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_concatenation02() {
    // String concatenation assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringConcatenation02"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_concatenation03() {
    // String concatenation assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringConcatenation03"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_concatenation04() {
    // String concatenation assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringConcatenation04"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_constructors01() {
    // String constructor assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringConstructors01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_constructors02() {
    // String constructor: content tracked through new String(s). SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringConstructors02"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_constructors03() {
    // String constructor assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringConstructors03"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_constructors04() {
    // String constructor: equals() on new String(s). SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringConstructors04"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_constructors05() {
    // String constructor: length/content checks. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringConstructors05"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_contains01() {
    // assert ab.contains(s) fails when ab="" and s="a". SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringContains01"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_contains02() {
    // String.contains assert failure — trivially detectable. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringContains02"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_index_methods01() {
    // String index methods assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringIndexMethods01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_index_methods02() {
    // String index methods assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringIndexMethods02"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_index_methods03() {
    // String index methods assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringIndexMethods03"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_index_methods04() {
    // String index methods assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringIndexMethods04"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_index_methods05() {
    // String index methods assert failure. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringIndexMethods05"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_miscellaneous01() {
    // String misc assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringMiscellaneous01"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_miscellaneous02() {
    // String misc assert failure. SV-COMP: false.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringMiscellaneous02"
        ]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_miscellaneous03() {
    // String misc assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringMiscellaneous03"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_miscellaneous04() {
    // String misc assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&[
            "tasks/common",
            "tasks/jbmc-regression/StringMiscellaneous04"
        ]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_start_end01() {
    // String.startsWith/endsWith assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringStartEnd01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_start_end02() {
    // String.startsWith/endsWith assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringStartEnd02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_start_end03() {
    // String.startsWith/endsWith assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringStartEnd03"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of01() {
    // String.valueOf assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of02() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of03() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf03"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of04() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf04"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of05() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf05"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of06() {
    // String.valueOf assert failure — trivially detectable. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf06"]),
        "FALSE"
    );
}

#[test]
fn jbmc_string_value_of07() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf07"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of08() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf08"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of09() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf09"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_string_value_of10() {
    // String.valueOf assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/StringValueOf10"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_sub_string01() {
    // String.substring assertion holds. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/SubString01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_sub_string02() {
    // String.substring assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/SubString02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_sub_string03() {
    // String.substring assert failure. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/SubString03"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_token_test01() {
    // sentence.split(" ") returns 4 tokens. SV-COMP: true.
    // UNKNOWN: string split/array content not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/TokenTest01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_token_test02() {
    // nondetString().split(" ") token assertion. SV-COMP: false.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/TokenTest02"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_validate01() {
    // Validate fixed input strings — all pass validation. SV-COMP: true.
    // UNKNOWN: string operations not modelled.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/Validate01"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_validate02() {
    // Validate nondet strings — invalid input hits assert false. SV-COMP: false.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/Validate02"]),
        "FALSE"
    );
}

#[test]
fn jbmc_aastore_aaload1() {
    // Fill object array, assert elements non-null. SV-COMP: true.
    // UNKNOWN: array element content not tracked.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/aastore_aaload1"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_array1() {
    // int array filled with index values, assert a[7]==7. SV-COMP: true.
    // UNKNOWN: array element content not tracked.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/array1"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_array2() {
    // Conditional array creation and element access. SV-COMP: true.
    // UNKNOWN: array element content not tracked.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/array2"]),
        "UNKNOWN"
    );
}

#[test]
fn jbmc_arrayread1() {
    // New array element defaults to null; assert readback == null. SV-COMP: true.
    // UNKNOWN: array element default not tracked.
    assert_eq!(
        roast(&["tasks/common", "tasks/jbmc-regression/arrayread1"]),
        "UNKNOWN"
    );
}
