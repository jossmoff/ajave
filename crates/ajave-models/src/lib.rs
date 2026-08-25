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

use ajave_ir::Ty;

pub const VERIFIER: &str = "org/sosy_lab/sv_benchmarks/Verifier";
pub const ASSERTION_ERROR: &str = "java/lang/AssertionError";
/// Synthetic field name used to store the enum ordinal (set by `Enum.<init>`,
/// read by `Enum.ordinal()`). Prefixed with `$$` to avoid collisions with
/// user-defined fields.
pub const ENUM_ORDINAL_FIELD: &str = "$$ordinal";
/// Synthetic field name used to store the boxed primitive value.
pub const BOX_VALUE_FIELD: &str = "$$value";
/// Synthetic field name for the last element stored in a collection.
/// Used by `CollectionStore` / `CollectionLoad` to model add/get as field ops.
pub const COLL_LAST_FIELD: &str = "$$coll_last";

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
    /// The `u8` is the JVM return-type descriptor byte (e.g. `b'S'` for short).
    Nondet(Option<Ty>, u8),
    /// Not modelled. The lifter diverges rather than guessing.
    Unmodelled,
    /// String/StringBuilder/CharSequence method: keep as Rvalue::Call so the
    /// concrete engine can evaluate it against a tracked string value.
    StrCall(Option<Ty>),
    /// `Enum.<init>(String, int)` — store the ordinal to a synthetic field.
    EnumInit,
    /// `Enum.ordinal()` — read the ordinal from a synthetic field.
    EnumOrdinal,
    /// `Boolean.valueOf(z)` / `Integer.valueOf(i)` etc. — box a primitive.
    /// Allocates a new ref and stores the argument into a synthetic `$$value` field.
    BoxStore(Ty),
    /// `Boolean.booleanValue()` / `Integer.intValue()` etc. — unbox.
    /// Reads the `$$value` field from the receiver.
    Unbox(Ty),
    /// A static method whose result is a binary operation on its two arguments.
    /// E.g. `Boolean.logicalAnd(a, b)` → `a & b`.
    StaticBinOp(ajave_ir::BinOp),
    /// Math/Integer/Long method that the SMT engine can model precisely.
    /// Kept as `Rvalue::Call` so the BMC sees it (unlike `Pure` which becomes `Havoc`).
    MathCall(Option<Ty>),
    /// `Class.desiredAssertionStatus()` — always returns true (1) under SV-COMP.
    AssertionsEnabled,
    /// Collection store: `add`, `addLast`, `put`, etc. — store the element to
    /// a synthetic `$$coll_last` field on the receiver.  The argument index of
    /// the element is encoded: 0 for add(elem), 1 for put(key, elem) or
    /// add(idx, elem).
    CollectionStore(u8),
    /// Collection load: `get`, `getLast`, `next`, etc. — read from the
    /// synthetic `$$coll_last` field on the receiver.
    CollectionLoad(Option<Ty>),
    /// `iterator()` / `listIterator()` — return the receiver itself so that
    /// subsequent `next()` reads the same `$$coll_last`.
    CollectionIterator,
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
    "java/lang/StrictMath",
    "java/lang/Object",
    "java/util/Objects",
    "java/util/regex/Pattern",
    "java/util/regex/Matcher",
    "java/util/Arrays",
    // Collections — methods that read or iterate don't affect our tracked state.
    "java/util/Collections",
    "java/util/List",
    "java/util/ArrayList",
    "java/util/LinkedList",
    "java/util/Map",
    "java/util/HashMap",
    "java/util/TreeMap",
    "java/util/LinkedHashMap",
    "java/util/Set",
    "java/util/HashSet",
    "java/util/TreeSet",
    "java/util/LinkedHashSet",
    "java/util/Iterator",
    "java/util/ListIterator",
    "java/util/Map$Entry",
    "java/util/AbstractList",
    "java/util/AbstractMap",
    "java/util/AbstractSet",
    "java/util/AbstractCollection",
    // Deque/Queue
    "java/util/Queue",
    "java/util/Deque",
    "java/util/ArrayDeque",
    "java/util/Stack",
    "java/util/Vector",
    // Utility
    "java/util/Optional",
    "java/util/Random",
    "java/util/Scanner",
    "java/util/StringTokenizer",
    // Concurrent (rarely property-relevant)
    "java/util/concurrent/atomic/AtomicInteger",
    "java/util/concurrent/atomic/AtomicLong",
    "java/util/concurrent/atomic/AtomicBoolean",
    // I/O — PrintWriter is excluded: securibench benchmarks subclass it
    // with mock objects that contain assertion obligations.
    "java/io/PrintStream",
    "java/io/InputStream",
    "java/io/OutputStream",
    "java/io/BufferedReader",
    "java/io/InputStreamReader",
    // System
    "java/lang/System",
    "java/lang/Class",
    "java/lang/Runtime",
    "java/lang/Thread",
    "java/lang/Comparable",
    "java/lang/Number",
    "java/lang/Iterable",
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
            "nondetString" => CallModel::Nondet(Some(Ty::Str), b'L'),
            // nondetObject returns a factory-created object; must inline the
            // factory body rather than treating it as a raw nondet ref.
            "nondetObject" => CallModel::Unmodelled,
            n if n.starts_with("nondet") => {
                let jvm_byte = desc.as_bytes().get(desc.rfind(')').unwrap_or(0) + 1).copied().unwrap_or(b'I');
                CallModel::Nondet(ret_ty(desc), jvm_byte)
            }
            _ => CallModel::Unmodelled,
        };
    }

    if name == "<init>" && THROWABLE_ROOTS.contains(&owner) {
        return CallModel::NoOp;
    }
    if owner == "java/lang/Object" && name == "<init>" {
        return CallModel::NoOp;
    }
    // Constructors of pure/collection classes: no tracked state to set up.
    // The lifter preserves Pure(None) as a Call, so taint analysis can see
    // argument flow (e.g. `new StringTokenizer(taintedStr)`).
    if name == "<init>" && PURE_OWNERS.contains(&owner) {
        return CallModel::Pure(None);
    }

    // Enum support: model the ordinal field that javac's enum <clinit> sets.
    // <init> is always called via invokespecial on java/lang/Enum directly.
    // ordinal() is inherited but invoked with the subclass as owner, so we
    // match it by name+desc for any owner.
    if owner == "java/lang/Enum" && name == "<init>" {
        return CallModel::EnumInit;
    }
    if name == "ordinal" && desc == "()I" {
        return CallModel::EnumOrdinal;
    }
    if owner == "java/lang/Enum" {
        return CallModel::Pure(ret_ty(desc));
    }

    // Assertions are always enabled under SV-COMP rules.
    // desiredAssertionStatus() returns true (1), so $assertionsDisabled = false (0).
    // Modelling this as a constant rather than Havoc avoids tainting the
    // assertion-enabled branch and lets the BMC check assertions precisely.
    if owner == "java/lang/Class" && name == "desiredAssertionStatus" {
        return CallModel::AssertionsEnabled;
    }

    if STR_OWNERS.contains(&owner) {
        return CallModel::StrCall(ret_ty(desc));
    }

    // Boxing: T.valueOf(primitive) → BoxStore, T.primitiveValue() → Unbox.
    // This models the value flowing through the boxed object so that
    // unboxing returns the same value that was boxed, rather than havoc.
    if let Some(model) = box_model(owner, name, desc) {
        return model;
    }

    // Math/Integer/Long methods the SMT engine can model precisely.
    if is_math_call(owner, name) {
        return CallModel::MathCall(ret_ty(desc));
    }

    // Collection methods: add/get/put modelled as synthetic field ops.
    // Must come before the PURE_OWNERS catch-all so we intercept these.
    if let Some(model) = collection_model(owner, name, desc) {
        return model;
    }

    // Methods that can throw RuntimeException (NumberFormatException,
    // IllegalArgumentException, etc.) must NOT be Pure — the call must
    // remain visible so the BMC can flag it as potentially throwing for NRE.
    if matches!(name,
        "parseInt" | "parseLong" | "parseShort" | "parseByte"
        | "parseFloat" | "parseDouble" | "parseUnsignedInt" | "parseUnsignedLong"
        | "decode" | "getInteger" | "getLong"
    ) {
        return CallModel::Unmodelled;
    }

    if PURE_OWNERS.contains(&owner) {
        return CallModel::Pure(ret_ty(desc));
    }

    CallModel::Unmodelled
}

/// Match boxing (`valueOf`) and unboxing (`*Value()`) methods on wrapper types.
fn box_model(owner: &str, name: &str, desc: &str) -> Option<CallModel> {
    match owner {
        "java/lang/Boolean" => match name {
            "valueOf" if desc == "(Z)Ljava/lang/Boolean;" => Some(CallModel::BoxStore(Ty::Int)),
            "booleanValue" if desc == "()Z" => Some(CallModel::Unbox(Ty::Int)),
            "logicalAnd" => Some(CallModel::StaticBinOp(ajave_ir::BinOp::And)),
            "logicalOr" => Some(CallModel::StaticBinOp(ajave_ir::BinOp::Or)),
            "logicalXor" => Some(CallModel::StaticBinOp(ajave_ir::BinOp::Xor)),
            "compare" => Some(CallModel::StaticBinOp(ajave_ir::BinOp::Sub)),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            _ => None,
        },
        "java/lang/Integer" => match name {
            "valueOf" if desc == "(I)Ljava/lang/Integer;" => Some(CallModel::BoxStore(Ty::Int)),
            "intValue" if desc == "()I" => Some(CallModel::Unbox(Ty::Int)),
            "longValue" if desc == "()J" => Some(CallModel::Unbox(Ty::Int)),
            "floatValue" if desc == "()F" => Some(CallModel::MathCall(Some(Ty::Int))),
            "doubleValue" if desc == "()D" => Some(CallModel::MathCall(Some(Ty::Double))),
            "shortValue" if desc == "()S" => Some(CallModel::Unbox(Ty::Int)),
            "byteValue" if desc == "()B" => Some(CallModel::Unbox(Ty::Int)),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" | "toHexString" | "toBinaryString" | "toOctalString"
            | "toUnsignedString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            _ => None,
        },
        "java/lang/Long" => match name {
            "valueOf" if desc == "(J)Ljava/lang/Long;" => Some(CallModel::BoxStore(Ty::Long)),
            "longValue" if desc == "()J" => Some(CallModel::Unbox(Ty::Long)),
            "intValue" if desc == "()I" => Some(CallModel::Unbox(Ty::Long)),
            "byteValue" if desc == "()B" => Some(CallModel::Unbox(Ty::Long)),
            "shortValue" if desc == "()S" => Some(CallModel::Unbox(Ty::Long)),
            "floatValue" if desc == "()F" => Some(CallModel::MathCall(Some(Ty::Int))),
            "doubleValue" if desc == "()D" => Some(CallModel::MathCall(Some(Ty::Double))),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" | "toHexString" | "toBinaryString" | "toOctalString"
            | "toUnsignedString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            _ => None,
        },
        "java/lang/Short" => match name {
            "valueOf" if desc == "(S)Ljava/lang/Short;" => Some(CallModel::BoxStore(Ty::Int)),
            "shortValue" if desc == "()S" => Some(CallModel::Unbox(Ty::Int)),
            "intValue" if desc == "()I" => Some(CallModel::Unbox(Ty::Int)),
            "longValue" if desc == "()J" => Some(CallModel::Unbox(Ty::Int)),
            "byteValue" if desc == "()B" => Some(CallModel::Unbox(Ty::Int)),
            "floatValue" if desc == "()F" => Some(CallModel::MathCall(Some(Ty::Int))),
            "doubleValue" if desc == "()D" => Some(CallModel::MathCall(Some(Ty::Double))),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            _ => None,
        },
        "java/lang/Byte" => match name {
            "valueOf" if desc == "(B)Ljava/lang/Byte;" => Some(CallModel::BoxStore(Ty::Int)),
            "byteValue" if desc == "()B" => Some(CallModel::Unbox(Ty::Int)),
            "intValue" if desc == "()I" => Some(CallModel::Unbox(Ty::Int)),
            "longValue" if desc == "()J" => Some(CallModel::Unbox(Ty::Int)),
            "shortValue" if desc == "()S" => Some(CallModel::Unbox(Ty::Int)),
            "floatValue" if desc == "()F" => Some(CallModel::MathCall(Some(Ty::Int))),
            "doubleValue" if desc == "()D" => Some(CallModel::MathCall(Some(Ty::Double))),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            _ => None,
        },
        "java/lang/Character" => match name {
            "valueOf" if desc == "(C)Ljava/lang/Character;" => Some(CallModel::BoxStore(Ty::Int)),
            "charValue" if desc == "()C" => Some(CallModel::Unbox(Ty::Int)),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            _ => None,
        },
        "java/lang/Double" => match name {
            "valueOf" if desc == "(D)Ljava/lang/Double;" => Some(CallModel::BoxStore(Ty::Double)),
            "doubleValue" if desc == "()D" => Some(CallModel::Unbox(Ty::Double)),
            "intValue" if desc == "()I" => Some(CallModel::MathCall(Some(Ty::Int))),
            "longValue" if desc == "()J" => Some(CallModel::MathCall(Some(Ty::Long))),
            "floatValue" if desc == "()F" => Some(CallModel::MathCall(Some(Ty::Int))),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            "isNaN" if desc == "()Z" => Some(CallModel::MathCall(Some(Ty::Int))),
            "isInfinite" if desc == "()Z" => Some(CallModel::MathCall(Some(Ty::Int))),
            "byteValue" if desc == "()B" => Some(CallModel::MathCall(Some(Ty::Int))),
            "shortValue" if desc == "()S" => Some(CallModel::MathCall(Some(Ty::Int))),
            _ => None,
        },
        "java/lang/Float" => match name {
            "valueOf" if desc == "(F)Ljava/lang/Float;" => Some(CallModel::BoxStore(Ty::Int)),
            "floatValue" if desc == "()F" => Some(CallModel::Unbox(Ty::Int)),
            "intValue" if desc == "()I" => Some(CallModel::MathCall(Some(Ty::Int))),
            "longValue" if desc == "()J" => Some(CallModel::MathCall(Some(Ty::Long))),
            "doubleValue" if desc == "()D" => Some(CallModel::MathCall(Some(Ty::Double))),
            "compareTo" => Some(CallModel::MathCall(Some(Ty::Int))),
            "toString" => Some(CallModel::MathCall(Some(Ty::Ref))),
            "isNaN" if desc == "()Z" => Some(CallModel::MathCall(Some(Ty::Int))),
            "isInfinite" if desc == "()Z" => Some(CallModel::MathCall(Some(Ty::Int))),
            "byteValue" if desc == "()B" => Some(CallModel::MathCall(Some(Ty::Int))),
            "shortValue" if desc == "()S" => Some(CallModel::MathCall(Some(Ty::Int))),
            _ => None,
        },
        _ => None,
    }
}

/// Check whether a Math/Integer/Long static method should be kept as a Call
/// so the SMT engine can model it precisely instead of havocing.
fn is_math_call(owner: &str, name: &str) -> bool {
    match owner {
        "java/lang/Math" | "java/lang/StrictMath" => matches!(
            name,
            "abs" | "min" | "max" | "addExact" | "subtractExact"
                | "multiplyExact" | "negateExact" | "floorDiv" | "floorMod"
                | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "atan2"
                | "exp" | "log" | "log10" | "pow" | "sqrt" | "round"
                | "ceil" | "floor" | "toRadians" | "toDegrees"
                | "sinh" | "cosh" | "tanh"
                | "getExponent"
        ),
        "java/lang/Integer" => matches!(
            name,
            "parseInt" | "max" | "min" | "sum"
                | "reverseBytes" | "highestOneBit"
                | "lowestOneBit" | "signum" | "toUnsignedLong"
                | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
                | "hashCode" | "compare"
                | "rotateLeft" | "rotateRight"
                | "bitCount" | "numberOfLeadingZeros" | "numberOfTrailingZeros"
                | "reverse"
        ),
        "java/lang/Long" => matches!(
            name,
            "parseLong" | "max" | "min" | "sum" | "signum"
                | "divideUnsigned" | "remainderUnsigned" | "compareUnsigned"
                | "hashCode" | "compare"
                | "reverseBytes" | "highestOneBit" | "lowestOneBit"
                | "rotateLeft" | "rotateRight"
                | "bitCount" | "numberOfLeadingZeros" | "numberOfTrailingZeros"
                | "reverse"
        ),
        "java/lang/Character" => matches!(
            name,
            "isDigit" | "isLetter" | "isLetterOrDigit" | "isUpperCase" | "isLowerCase"
                | "isWhitespace" | "isSpaceChar" | "isAlphabetic" | "isBmpCodePoint"
                | "isSupplementaryCodePoint" | "isValidCodePoint"
                | "toUpperCase" | "toLowerCase" | "toTitleCase"
                | "digit" | "forDigit"
                | "charCount" | "toCodePoint"
                | "compare" | "compareTo" | "hashCode" | "reverseBytes"
                | "isISOControl" | "isSpace"
                | "isJavaIdentifierStart" | "isJavaIdentifierPart"
                | "isJavaLetter" | "isJavaLetterOrDigit"
                | "getType" | "isDefined" | "isMirrored" | "isTitleCase"
                | "isUnicodeIdentifierPart" | "isUnicodeIdentifierStart"
                | "isIdentifierIgnorable" | "getDirectionality"
                | "getNumericValue" | "isIdeographic"
        ),
        "java/lang/Short" => matches!(
            name,
            "parseShort" | "compare" | "compareTo" | "hashCode" | "reverseBytes"
                | "toUnsignedInt" | "toUnsignedLong"
        ),
        "java/lang/Byte" => matches!(
            name,
            "parseByte" | "compare" | "compareTo" | "hashCode"
                | "toUnsignedInt" | "toUnsignedLong"
        ),
        "java/lang/Boolean" => matches!(
            name,
            "logicalAnd" | "logicalOr" | "logicalXor" | "compare" | "hashCode"
        ),
        "java/lang/Float" => matches!(
            name,
            "floatToRawIntBits" | "floatToIntBits" | "intBitsToFloat"
                | "isNaN" | "isInfinite" | "isFinite"
                | "compare" | "max" | "min" | "sum"
                | "hashCode"
        ),
        "java/lang/Double" => matches!(
            name,
            "doubleToRawLongBits" | "doubleToLongBits" | "longBitsToDouble"
                | "isNaN" | "isInfinite" | "isFinite"
                | "compare" | "max" | "min" | "sum"
                | "hashCode"
        ),
        _ => false,
    }
}

/// Owners that are collection types (List, Set, Map, Queue, Deque + impls).
fn is_collection_owner(owner: &str) -> bool {
    matches!(
        owner,
        "java/util/List"
            | "java/util/ArrayList"
            | "java/util/LinkedList"
            | "java/util/Vector"
            | "java/util/Stack"
            | "java/util/Set"
            | "java/util/HashSet"
            | "java/util/TreeSet"
            | "java/util/LinkedHashSet"
            | "java/util/Collection"
            | "java/util/AbstractList"
            | "java/util/AbstractCollection"
            | "java/util/AbstractSet"
            | "java/util/Queue"
            | "java/util/Deque"
            | "java/util/ArrayDeque"
    )
}

fn is_map_owner(owner: &str) -> bool {
    matches!(
        owner,
        "java/util/Map"
            | "java/util/HashMap"
            | "java/util/TreeMap"
            | "java/util/LinkedHashMap"
            | "java/util/AbstractMap"
            | "java/util/Hashtable"
    )
}

fn is_iterator_owner(owner: &str) -> bool {
    matches!(
        owner,
        "java/util/Iterator" | "java/util/ListIterator"
    )
}

fn is_map_entry_owner(owner: &str) -> bool {
    matches!(
        owner,
        "java/util/Map$Entry" | "java/util/AbstractMap$SimpleEntry"
            | "java/util/AbstractMap$SimpleImmutableEntry"
    )
}

/// Model collection add/get/put/iterator as synthetic field operations.
/// Returns `None` for methods we don't specifically model (they fall through
/// to `Pure` via `PURE_OWNERS`).
fn collection_model(owner: &str, name: &str, desc: &str) -> Option<CallModel> {
    // Iterator methods
    if is_iterator_owner(owner) {
        return match name {
            "next" | "previous" => Some(CallModel::CollectionLoad(ret_ty(desc))),
            // hasNext → unconstrained boolean (Pure/Havoc)
            _ => None,
        };
    }

    // Map.Entry methods — getValue/getKey read from the same $coll_last
    if is_map_entry_owner(owner) {
        return match name {
            "getValue" | "getKey" => Some(CallModel::CollectionLoad(ret_ty(desc))),
            "setValue" => Some(CallModel::CollectionStore(0)),
            _ => None,
        };
    }

    // Map methods
    if is_map_owner(owner) {
        return match name {
            "put" | "putIfAbsent" => Some(CallModel::CollectionStore(1)), // put(key, val) → store arg[1]
            "get" | "remove" | "getOrDefault" => Some(CallModel::CollectionLoad(ret_ty(desc))),
            "values" | "keySet" | "entrySet" => Some(CallModel::CollectionIterator),
            _ => None,
        };
    }

    if !is_collection_owner(owner) {
        return None;
    }

    // Collection/List/Set/Queue/Deque store methods
    match name {
        "add" | "offer" => {
            // add(Object) → arg 0; add(int, Object) → arg 1
            let elem_idx = if desc.starts_with("(I") { 1 } else { 0 };
            Some(CallModel::CollectionStore(elem_idx))
        }
        "addLast" | "addFirst" | "push" | "offerFirst" | "offerLast" | "addElement" => {
            Some(CallModel::CollectionStore(0))
        }
        "set" => Some(CallModel::CollectionStore(1)), // set(int, Object) → arg 1

        // Collection/List/Queue/Deque load methods
        "get" | "remove" | "getLast" | "getFirst" | "peek" | "peekFirst" | "peekLast"
        | "poll" | "pollFirst" | "pollLast" | "pop" | "removeFirst" | "removeLast"
        | "element" | "elementAt" | "firstElement" | "lastElement" => {
            Some(CallModel::CollectionLoad(ret_ty(desc)))
        }

        // Iterator creation — return the collection itself
        "iterator" | "listIterator" => Some(CallModel::CollectionIterator),

        _ => None,
    }
}

/// Returns `true` if this is a transcendental Math method (sin, cos, exp, log,
/// pow, sqrt, etc.) that requires a nonlinear real arithmetic solver like dReal.
pub fn is_transcendental_math(owner: &str, name: &str) -> bool {
    matches!(owner, "java/lang/Math" | "java/lang/StrictMath")
        && matches!(
            name,
            "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "atan2"
                | "exp" | "log" | "log10" | "pow" | "sqrt"
                | "sinh" | "cosh" | "tanh"
                | "ceil" | "floor" | "toRadians" | "toDegrees"
        )
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
pub fn exception_class(kind: ajave_ir::ObligationKind) -> Option<&'static str> {
    use ajave_ir::ObligationKind::*;
    match kind {
        Assertion => None,
        DivByZero => Some("java/lang/ArithmeticException"),
        NullDeref => Some("java/lang/NullPointerException"),
        ArrayBounds => Some("java/lang/ArrayIndexOutOfBoundsException"),
        NegArraySize => Some("java/lang/NegativeArraySizeException"),
        ClassCast => Some("java/lang/ClassCastException"),
    }
}
