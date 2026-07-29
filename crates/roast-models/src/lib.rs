//! Standard library modelling.
//!
//! We do not analyse `java.base` bytecode. Every tool that tried to be faithful
//! to the JDK drowned in it. Instead this module describes, in a table, what a
//! library call *does* as far as the analysis is concerned.
//!
//! The soundness argument for `HavocResult` is currently easy, and will stop
//! being easy: with no heap model, an unconstrained result over-approximates
//! any pure computation, and there is no tracked state for a side effect to
//! corrupt. Once fields are tracked (stage 6), calls that mutate reachable
//! objects must additionally havoc the heap, and the ones marked `Pure` below
//! are exactly those for which that will not be needed.

use roast_ir::Ty;

pub const VERIFIER: &str = "org/sosy_lab/sv_benchmarks/Verifier";
pub const ASSERTION_ERROR: &str = "java/lang/AssertionError";

#[derive(Clone, Debug, PartialEq)]
pub enum CallModel {
    /// No observable effect; drop it. Constructors of exception types and
    /// `Object.<init>` land here.
    NoOp,
    /// `Verifier.assume(cond)`.
    Assume,
    /// Deterministic, no side effects on anything we track. Result is havocked
    /// because we do not model the value precisely.
    Pure(Option<Ty>),
    /// `Verifier.nondet*()` — an unconstrained value by definition.
    Nondet(Option<Ty>),
    /// Not modelled. The lifter diverges rather than guessing.
    Unmodelled,
    /// String/StringBuilder/CharSequence method: keep as Rvalue::Call so the
    /// concrete engine can evaluate it against a tracked string value.
    StrCall(Option<Ty>),
}

fn ret_ty(desc: &str) -> Option<Ty> {
    let after = desc.rfind(')')? + 1;
    match desc.as_bytes().get(after)? {
        b'V' => None,
        b'J' => Some(Ty::Long),
        b'F' => Some(Ty::Float),
        b'D' => Some(Ty::Double),
        b'L' | b'[' => Some(Ty::Ref),
        _ => Some(Ty::Int),
    }
}

/// Classes whose instance methods we treat as pure with respect to our state.
/// String is genuinely immutable. StringBuilder is not, but we never read its
/// fields, so havocking results is sound *given* that we track nothing about it.
/// String-related owners whose methods we keep in the IR as `Rvalue::Call`
/// so the concrete engine can evaluate them against tracked string content.
pub const STR_OWNERS: &[&str] = &[
    "java/lang/String",
    "java/lang/StringBuilder",
    "java/lang/StringBuffer",
    "java/lang/CharSequence",
];

const PURE_OWNERS: &[&str] = &[
    "java/lang/Integer",
    "java/lang/Long",
    "java/lang/Short",
    "java/lang/Byte",
    "java/lang/Character",
    "java/lang/Boolean",
    "java/lang/Float",
    "java/lang/Double",
    "java/lang/Math",
    "java/lang/Object",
    "java/util/Objects",
    "java/util/regex/Pattern",
    "java/util/regex/Matcher",
    "java/util/Arrays",
];

/// Constructors with no effect we care about: the whole `Throwable` family,
/// since the throw itself is what carries the obligation.
const THROWABLE_ROOTS: &[&str] = &[
    "java/lang/AssertionError",
    "java/lang/Throwable",
    "java/lang/Exception",
    "java/lang/RuntimeException",
    "java/lang/Error",
    "java/lang/IllegalArgumentException",
    "java/lang/IllegalStateException",
    "java/lang/NullPointerException",
    "java/lang/ArithmeticException",
    "java/lang/ArrayIndexOutOfBoundsException",
    "java/lang/IndexOutOfBoundsException",
    "java/lang/ClassCastException",
    "java/lang/NegativeArraySizeException",
    "java/lang/UnsupportedOperationException",
    "java/lang/StringIndexOutOfBoundsException",
];

pub fn model_for(owner: &str, name: &str, desc: &str) -> CallModel {
    if owner == VERIFIER {
        return match name {
            "assume" => CallModel::Assume,
            "nondetString" => CallModel::Nondet(Some(Ty::Str)),
            n if n.starts_with("nondet") => CallModel::Nondet(ret_ty(desc)),
            _ => CallModel::Unmodelled,
        };
    }

    if name == "<init>" && THROWABLE_ROOTS.contains(&owner) {
        return CallModel::NoOp;
    }
    if owner == "java/lang/Object" && name == "<init>" {
        return CallModel::NoOp;
    }

    // Assertions are enabled under SV-COMP, so this is a constant.
    if owner == "java/lang/Class" && name == "desiredAssertionStatus" {
        return CallModel::Pure(Some(Ty::Int));
    }

    if STR_OWNERS.contains(&owner) {
        return CallModel::StrCall(ret_ty(desc));
    }

    if PURE_OWNERS.contains(&owner) {
        return CallModel::Pure(ret_ty(desc));
    }

    // Printing is observable to a human, not to the property.
    if owner.starts_with("java/io/PrintStream") || owner.starts_with("java/lang/System") {
        return CallModel::Pure(ret_ty(desc));
    }

    CallModel::Unmodelled
}

/// Does a `new` of this class need field tracking? Exception objects do not:
/// we care only that one was thrown.
pub fn is_throwable(class: &str) -> bool {
    THROWABLE_ROOTS.contains(&class) || class.ends_with("Exception") || class.ends_with("Error")
}

/// The exception class an obligation kind raises, when it does. `Assertion`
/// has none: reaching it is the violation, independent of any handler --
/// SV-COMP's assert property is about the assert location being reached, not
/// about whether user code happens to catch `AssertionError` afterwards.
pub fn exception_class(kind: roast_ir::ObligationKind) -> Option<&'static str> {
    use roast_ir::ObligationKind::*;
    match kind {
        Assertion => None,
        DivByZero => Some("java/lang/ArithmeticException"),
        NullDeref => Some("java/lang/NullPointerException"),
        ArrayBounds => Some("java/lang/ArrayIndexOutOfBoundsException"),
        NegArraySize => Some("java/lang/NegativeArraySizeException"),
        ClassCast => Some("java/lang/ClassCastException"),
    }
}
