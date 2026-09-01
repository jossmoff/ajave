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
/// Synthetic field holding a collection's element count.
///
/// Without a size, `list.get(i)` has no expressible bound and every program
/// touching a collection is unprovable. Tracking it as an ordinary field means
/// the existing flat field abstraction reasons about it for free: `add` bumps
/// it, `size()` reads it, and `get(i)` carries an `i < size` obligation the
/// interval domain can discharge.
pub const COLL_SIZE_FIELD: &str = "$$coll_size";

/// What must hold at a call site for an external method not to throw.
///
/// The point of naming preconditions rather than just flagging a method as
/// "may throw" is that a named condition can be *discharged*. `s.charAt(i)`
/// throws only when `i` is out of range; if the analysis can show it is in
/// range, the call is safe and the program can still be proved. A bare
/// may-throw flag forces us to give up on every such program instead.
///
/// Argument indices are into the call's argument list *including* the
/// receiver at position 0 for instance methods, matching `Rvalue::Call`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Precondition {
    /// Argument `n` must not be null, else `NullPointerException`.
    NonNull(u8),
    /// `0 <= arg[index] < length(arg[seq])`, else an out-of-bounds exception.
    /// `seq` is a String, CharSequence or array-like receiver.
    IndexInRange { index: u8, seq: u8 },
    /// `0 <= arg[start] <= arg[end] <= length(arg[seq])` — the `substring`
    /// shape, where the bound is inclusive and the pair must be ordered.
    RangeInBounds { start: u8, end: Option<u8>, seq: u8 },
    /// Argument `n` must be >= 0, else `NegativeArraySizeException` or
    /// `IllegalArgumentException`.
    NonNegative(u8),
    /// Argument `n` must be != 0, else `ArithmeticException`.
    NonZero(u8),
    /// The receiver must be non-empty, else `NoSuchElementException` or
    /// `EmptyStackException`.
    NonEmpty,
    /// `arg[a] OP arg[b]` must not overflow the given width, else
    /// `ArithmeticException` — the `Math.*Exact` family.
    ///
    /// Expressible after all: the check is `(long)a OP (long)b` staying inside
    /// the 32-bit range, which the BMC encodes directly. Leaving it
    /// `Unexpressible` blocked the TRUE *and* prevented anything finding the
    /// FALSE, so such tasks were unanswerable in both directions.
    NoOverflow { a: u8, b: u8, op: ajave_ir::BinOp, width: u8 },
    /// The method can throw for a reason we cannot express as a condition over
    /// the call's arguments — a malformed format string, an overflow check, a
    /// comparator contract. Presence of this blocks a no-runtime-exception
    /// proof, which is the honest outcome: we genuinely do not know.
    Unexpressible,
}

impl Precondition {
    /// Does the lifter emit this as an obligation today?
    ///
    /// Only these may let the verdict guard stand down. The index-range kinds
    /// need the receiver's length, which means materialising a `length()` call
    /// during lifting — worth doing, but until it exists they must keep
    /// blocking rather than being silently assumed.
    pub fn is_seeded(&self) -> bool {
        matches!(
            self,
            Precondition::NonNull(_)
                | Precondition::NonNegative(_)
                | Precondition::NonZero(_)
                | Precondition::IndexInRange { .. }
                | Precondition::RangeInBounds { .. }
                | Precondition::NoOverflow { .. }
                | Precondition::NonEmpty
        )
    }
}

/// What an external method may write.
///
/// Replaces the previous rule that any callee without a body clobbers every
/// field the program writes — which made the flat field abstraction nearly
/// useless as soon as a single library call appeared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    /// Writes nothing we track.
    Pure,
    /// Mutates only its receiver.
    Receiver,
    /// May write anything; the conservative fallback.
    Unknown,
}

impl Effect {
    /// Position in the lattice `Pure < Receiver < Unknown`, where higher is
    /// more conservative: assuming a call writes more can only lose precision.
    pub fn rank(self) -> u8 {
        match self {
            Effect::Pure => 0,
            Effect::Receiver => 1,
            Effect::Unknown => 2,
        }
    }
}

/// Everything we claim about an external method, in one place.
///
/// Previously this knowledge was spread across `could_throw_runtime_exception`,
/// `pure_owner_member_may_throw`, `str_call_can_throw`, `PURE_OWNERS` and the
/// field-abstraction clobber sets — five representations that drifted apart and
/// produced the same class of unsoundness repeatedly (issues #48, #49). One
/// table, derived everywhere, is the fix.
#[derive(Clone, Copy, Debug)]
pub struct Contract {
    pub requires: &'static [Precondition],
    pub effect: Effect,
}

impl Contract {
    /// Total: cannot throw for any input.
    const TOTAL: Contract = Contract { requires: &[], effect: Effect::Pure };

    /// Cannot throw, but mutates its receiver.
    const TOTAL_MUT: Contract = Contract { requires: &[], effect: Effect::Receiver };

    /// `true` when no input can make this call raise a `RuntimeException`.
    pub fn is_total(&self) -> bool {
        self.requires.is_empty()
    }

    /// Is this contract at least as conservative as `other`?
    ///
    /// # Why an order exists at all
    ///
    /// Contracts are not symmetric under error. One that is **too strong** --
    /// claiming preconditions the real method does not have, or a broader
    /// effect -- costs precision: extra obligations, more UNKNOWN. One that is
    /// **too weak** flips a verdict, because `is_total()` returning true lets
    /// the BMC treat a havoced call as non-throwing, claim `all_paths_complete`
    /// and discharge an obligation as TRUE.
    ///
    /// So only movement *up* this order is safe, and the two kinds of mistake
    /// look identical without it. Issue #48 found 22 wrongly-allowlisted
    /// methods that accumulated precisely because nothing could tell them
    /// apart.
    ///
    /// More preconditions is more conservative; a wider effect is more
    /// conservative.
    pub fn at_least_as_conservative_as(&self, other: &Contract) -> bool {
        let covers = other
            .requires
            .iter()
            .all(|p| self.requires.iter().any(|q| q == p));
        covers && self.effect.rank() >= other.effect.rank()
    }

    /// The most conservative contract: assume it can throw for reasons we
    /// cannot state, and that it writes anything.
    pub const OPAQUE: Contract = Contract {
        requires: &[Precondition::Unexpressible],
        effect: Effect::Unknown,
    };

    /// `true` when every precondition is actually emitted as an obligation by
    /// the lifter.
    ///
    /// This is the invariant the verdict guard depends on, and it must be
    /// *seeded*, not merely *expressible*: the guard skips a call only because
    /// the obligations carry the burden instead. Declaring a condition
    /// expressible while the lifter does not emit it reinstates exactly the
    /// TRUE-by-vacuity bug this whole layer exists to remove — which is how
    /// `CharAtOutOfBounds` regressed the moment the two drifted apart.
    ///
    /// Keep in lockstep with the seeding loop in `lift.rs`.
    pub fn preconditions_all_seeded(&self) -> bool {
        self.requires.iter().all(|p| p.is_seeded())
    }
}


/// The contract for an external method, if we have one.
///
/// `None` means we know nothing and must stay conservative. A `Some` with
/// non-empty `requires` is the interesting case: the call *can* throw, but only
/// under a stated condition, so the lifter emits a `Check` the analysis may be
/// able to discharge — which is what lets a program using `s.contains(t)` still
/// be proved free of runtime exceptions.
///
/// Argument indices include the receiver at 0 for instance methods.
/// Replace a contract with the most conservative one, for metamorphic testing.
///
/// `AJAVE_PERTURB_CONTRACT=java/lang/String:length` makes `contract_of` return
/// `Contract::OPAQUE` for that signature — a strict move *up* the refinement
/// order. By the monotonicity property every consumer is supposed to have, that
/// may turn a TRUE into an UNKNOWN and must never change a verdict to a
/// different verdict.
///
/// This is what makes the order in `at_least_as_conservative_as` checkable
/// rather than merely stated: `tools/contract_monotonicity.py` perturbs each
/// contract in turn and looks for a flip. A flip means some consumer is not
/// monotone, which is the defect class behind #48 -- and one that no amount of
/// reading the table can reveal.
fn perturbed(class: &str, name: &str) -> bool {
    static SPEC: std::sync::OnceLock<Option<(String, String)>> = std::sync::OnceLock::new();
    let spec = SPEC.get_or_init(|| {
        std::env::var("AJAVE_PERTURB_CONTRACT").ok().and_then(|v| {
            let (c, n) = v.split_once(':')?;
            Some((c.to_string(), n.to_string()))
        })
    });
    matches!(spec, Some((c, n)) if c == class && n == name)
}

/// The contract for a method, always.
///
/// # Why a total function, and why `OPAQUE` is the default
///
/// `contract_of` returns `Option`, and that `None` conflates two different
/// things: "this method is specified to throw for some inputs" and "we have
/// never said anything about this method". Both leave the caller to invent a
/// default, which is how a third of the JDK surface came to be answered outside
/// the table at all.
///
/// Made total, the distinction is expressible -- a partial method gets a
/// contract *with* preconditions, an unknown one gets `OPAQUE` -- and coverage
/// stops being a number to chase: every method has a contract by construction,
/// and the refinement order governs all of them.
///
/// `OPAQUE` is the right default because it is the top of the order: assuming a
/// method may throw for reasons we cannot state, and may write anything, can
/// only cost precision. The unsafe default would be `TOTAL`, which is exactly
/// the mistake #48 catalogued 22 instances of.
pub fn contract_for(class: &str, name: &str, desc: &str) -> Contract {
    contract_of(class, name, desc).unwrap_or(Contract::OPAQUE)
}

pub fn contract_of(class: &str, name: &str, desc: &str) -> Option<Contract> {
    if perturbed(class, name) {
        return Some(Contract::OPAQUE);
    }
    // The signatures the JDK specifies as total, previously answered by a
    // separate match inside the BMC. Consulted first so that everything the
    // analyser asks about goes through this one function -- which is what makes
    // the refinement order enforceable and the monotonicity test non-vacuous.
    if is_total_jdk_signature(class, name, desc) {
        return Some(Contract::TOTAL);
    }
    // Argument-null preconditions, the single most common shape in the JDK.
    const NN1: &[Precondition] = &[Precondition::NonNull(1)];
    // Index-into-receiver, e.g. `charAt`.
    const IDX1: &[Precondition] = &[Precondition::IndexInRange { index: 1, seq: 0 }];
    // Regex and format methods throw for reasons we cannot state over arguments.
    const OPAQUE: &[Precondition] = &[Precondition::Unexpressible];

    let c = match (class, name) {
        // ── java.lang.String ────────────────────────────────────────────
        // The no-argument queries are total.
        ("java/lang/String", "length" | "isEmpty" | "hashCode" | "toString"
            | "intern" | "trim" | "toCharArray" | "toUpperCase" | "toLowerCase") => {
            Contract::TOTAL
        }
        // `equals` is specified null-tolerant; the others throw NPE on null.
        ("java/lang/String", "equals") => Contract::TOTAL,
        ("java/lang/String", "contains" | "startsWith" | "endsWith" | "concat"
            | "equalsIgnoreCase" | "compareTo" | "compareToIgnoreCase"
            | "indexOf" | "lastIndexOf" | "replace") => {
            Contract { requires: NN1, effect: Effect::Pure }
        }
        // Index-bounded accessors.
        ("java/lang/String", "charAt" | "codePointAt") => {
            Contract { requires: IDX1, effect: Effect::Pure }
        }
        ("java/lang/String", "substring") => Contract {
            requires: &[Precondition::RangeInBounds { start: 1, end: None, seq: 0 }],
            effect: Effect::Pure,
        },
        // PatternSyntaxException / IllegalFormatException are not conditions
        // over the argument values we track.
        ("java/lang/String", "matches" | "split" | "replaceAll" | "replaceFirst"
            | "format" | "join") => {
            Contract { requires: OPAQUE, effect: Effect::Pure }
        }

        // ── java.lang.Object ────────────────────────────────────────────
        // Monitor operations, listed before the class-level fallback below.
        //
        // `PURE_OWNERS` contains `java/lang/Object`, and a class-level entry is
        // exactly what this file warns against: `wait` blocks the calling
        // thread and *releases the monitor*, and `notify`/`notifyAll` move
        // other threads between wait sets. Treating them as pure let the
        // concurrency explorer step over a `wait()` as though it were free,
        // after which a thread that waits forever appeared to terminate and a
        // program that provably hangs was reported as deadlock-free — a wrong
        // TRUE. See benchmarks/ajave/concurrency/MissedSignalDeadlock.
        //
        // All three throw `IllegalMonitorStateException` unless the caller owns
        // the monitor, and `wait` also throws `InterruptedException`. That is
        // not expressible over the arguments, so it is `Unexpressible`.
        ("java/lang/Object", "wait" | "notify" | "notifyAll") => Contract {
            requires: &[Precondition::Unexpressible],
            effect: Effect::Unknown,
        },
        ("java/lang/Object", "<init>" | "getClass" | "hashCode" | "toString" | "equals") => {
            Contract::TOTAL
        }

        // ── StringBuilder / StringBuffer ────────────────────────────────
        ("java/lang/StringBuilder" | "java/lang/StringBuffer", "<init>") if desc == "()V" => {
            Contract::TOTAL_MUT
        }
        ("java/lang/StringBuilder" | "java/lang/StringBuffer", "<init>") => Contract {
            // `StringBuilder(int)` throws on a negative capacity;
            // `StringBuilder(String)` throws NPE on null.
            requires: if desc == "(I)V" {
                &[Precondition::NonNegative(1)]
            } else {
                NN1
            },
            effect: Effect::Receiver,
        },
        ("java/lang/StringBuilder" | "java/lang/StringBuffer", "length" | "toString") => {
            Contract::TOTAL
        }
        // `append` renders null as "null" for the reference overloads and is
        // total for the primitive ones.
        ("java/lang/StringBuilder" | "java/lang/StringBuffer", "append") => Contract::TOTAL_MUT,
        ("java/lang/StringBuilder" | "java/lang/StringBuffer", "charAt") => {
            Contract { requires: IDX1, effect: Effect::Pure }
        }

        // ── Boxing ──────────────────────────────────────────────────────
        ("java/lang/Integer" | "java/lang/Long" | "java/lang/Short" | "java/lang/Byte"
            | "java/lang/Float" | "java/lang/Double" | "java/lang/Character"
            | "java/lang/Boolean", "valueOf") => {
            if desc.starts_with("(Ljava/lang/String;)") {
                // Parsing: NumberFormatException is not a condition over a
                // value we model.
                Contract { requires: OPAQUE, effect: Effect::Pure }
            } else {
                Contract::TOTAL
            }
        }
        ("java/lang/Integer" | "java/lang/Long" | "java/lang/Short" | "java/lang/Byte"
            | "java/lang/Float" | "java/lang/Double" | "java/lang/Character"
            | "java/lang/Boolean",
            "intValue" | "longValue" | "shortValue" | "byteValue" | "floatValue"
            | "doubleValue" | "charValue" | "booleanValue" | "hashCode"
            | "toString" | "equals") => Contract::TOTAL,

        // ── Math ────────────────────────────────────────────────────────
        ("java/lang/Math" | "java/lang/StrictMath", n) => {
            if matches!(n, "addExact" | "subtractExact" | "multiplyExact") {
                // Overflow is expressible: widen both operands and check the
                // result stays in range.
                let width = if desc.starts_with("(JJ)") { 64 } else { 32 };
                let op = match n {
                    "addExact" => ajave_ir::BinOp::Add,
                    "subtractExact" => ajave_ir::BinOp::Sub,
                    _ => ajave_ir::BinOp::Mul,
                };
                return Some(Contract {
                    requires: Box::leak(Box::new([Precondition::NoOverflow {
                        a: 0, b: 1, op, width,
                    }])),
                    effect: Effect::Pure,
                });
            } else if matches!(n,
                "incrementExact" | "decrementExact" | "negateExact" | "absExact"
                    | "toIntExact"
            ) {
                // Single-operand overflow; not seeded yet.
                Contract { requires: OPAQUE, effect: Effect::Pure }
            } else if matches!(n, "floorDiv" | "floorMod" | "ceilDiv" | "ceilMod") {
                Contract { requires: &[Precondition::NonZero(2)], effect: Effect::Pure }
            } else if matches!(n,
                "abs" | "min" | "max" | "sqrt" | "cbrt" | "sin" | "cos" | "tan"
                    | "asin" | "acos" | "atan" | "atan2" | "exp" | "expm1"
                    | "log" | "log10" | "log1p" | "pow" | "floor" | "ceil"
                    | "rint" | "round" | "signum" | "hypot" | "random"
                    | "toRadians" | "toDegrees" | "ulp" | "copySign" | "fma"
            ) {
                Contract::TOTAL
            } else {
                return None;
            }
        }

        // ── System ──────────────────────────────────────────────────────
        ("java/lang/System", "currentTimeMillis" | "nanoTime" | "identityHashCode"
            | "lineSeparator") => Contract::TOTAL,

        // ── Enum ────────────────────────────────────────────────────────
        ("java/lang/Enum", "ordinal" | "name" | "toString" | "hashCode" | "equals") => {
            Contract::TOTAL
        }

        // `next()` on an exhausted iterator throws NoSuchElementException,
        // and `hasNext()` is total. We model an iterator as its collection, so
        // emptiness is `$$coll_size == 0`.
        ("java/util/Iterator" | "java/util/ListIterator", "next" | "previous") => {
            Contract { requires: &[Precondition::NonEmpty], effect: Effect::Receiver }
        }
        ("java/util/Iterator" | "java/util/ListIterator", "hasNext" | "hasPrevious") => {
            Contract::TOTAL
        }
        // Stack/Deque removal on an empty receiver throws.
        ("java/util/Stack", "pop" | "peek") => {
            Contract { requires: &[Precondition::NonEmpty], effect: Effect::Receiver }
        }
        ("java/util/ArrayDeque" | "java/util/LinkedList",
            "pop" | "removeFirst" | "removeLast" | "getFirst" | "getLast") => {
            Contract { requires: &[Precondition::NonEmpty], effect: Effect::Receiver }
        }

        // ── Collections ─────────────────────────────────────────────────
        // Now that element counts are tracked in `$$coll_size`, the bound on
        // an indexed access is expressible, so these stop being dead ends.
        ("java/util/List" | "java/util/ArrayList" | "java/util/LinkedList"
            | "java/util/AbstractList" | "java/util/Vector", "get") => {
            Contract { requires: IDX1, effect: Effect::Pure }
        }
        ("java/util/List" | "java/util/ArrayList" | "java/util/LinkedList"
            | "java/util/AbstractList" | "java/util/Vector", "size" | "isEmpty") => {
            Contract::TOTAL
        }
        // Appending cannot fail for the unbounded collections; the indexed
        // `add(int, E)` and `set(int, E)` overloads can.
        ("java/util/List" | "java/util/ArrayList" | "java/util/LinkedList"
            | "java/util/AbstractList" | "java/util/Vector", "add") => {
            if desc.starts_with("(I") {
                Contract { requires: IDX1, effect: Effect::Receiver }
            } else {
                Contract::TOTAL_MUT
            }
        }
        ("java/util/HashSet" | "java/util/LinkedHashSet" | "java/util/Set", "add"
            | "contains" | "size" | "isEmpty") => Contract::TOTAL_MUT,
        // Hash maps tolerate null keys; sorted maps do not, so they are absent.
        ("java/util/HashMap" | "java/util/LinkedHashMap", "put" | "get"
            | "containsKey" | "size" | "isEmpty") => Contract::TOTAL_MUT,

        // ── Output streams ──────────────────────────────────────────────
        // The constructors throw NPE on a null sink; printing is total and
        // renders null as "null". IOException is checked, so irrelevant here.
        ("java/io/PrintWriter" | "java/io/PrintStream", "<init>") => {
            Contract { requires: NN1, effect: Effect::Receiver }
        }
        ("java/io/PrintWriter" | "java/io/PrintStream",
            "println" | "print" | "write" | "flush" | "close" | "append") => {
            // `format`/`printf` are excluded: IllegalFormatException is not a
            // condition over a value we track.
            Contract::TOTAL_MUT
        }
        ("java/io/PrintWriter" | "java/io/PrintStream", "format" | "printf") => {
            Contract { requires: OPAQUE, effect: Effect::Receiver }
        }

        // ── CharSequence ────────────────────────────────────────────────
        ("java/lang/CharSequence", "length" | "toString") => Contract::TOTAL,
        ("java/lang/CharSequence", "charAt") => {
            Contract { requires: IDX1, effect: Effect::Pure }
        }

        // ── java.util.Objects ───────────────────────────────────────────
        ("java/util/Objects", "requireNonNull") => {
            Contract { requires: NN1, effect: Effect::Pure }
        }
        ("java/util/Objects", "equals" | "hashCode" | "toString" | "isNull" | "nonNull") => {
            Contract::TOTAL
        }

        // ── Threads ─────────────────────────────────────────────────────
        // `start()` runs the thread body, which we do not yet explore, so it
        // must not be treated as total: claiming no runtime exception while
        // never looking inside `run()` is a wrong TRUE. `Unexpressible` is the
        // honest classification until the concurrency engine lands — see
        // docs/strategies/concurrency.md.
        //
        // Thread was previously in PURE_OWNERS, which made the lifter erase
        // `start()` to a Havoc entirely — the same call-disappears-from-the-IR
        // shape as issue #49.
        ("java/lang/Thread", "start" | "run" | "join" | "interrupt" | "sleep") => {
            Contract { requires: OPAQUE, effect: Effect::Unknown }
        }
        // Queries that touch no shared state.
        ("java/lang/Thread", "currentThread" | "getName" | "getId" | "isAlive"
            | "isDaemon" | "getPriority") => Contract::TOTAL,

        // ── The nondet source ───────────────────────────────────────────
        (VERIFIER, _) => Contract::TOTAL,

        _ => return None,
    };
    Some(c)
}

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
    /// `size()` — read the synthetic `$$coll_size` field from the receiver.
    CollectionSize,
    /// `isEmpty()` — `$$coll_size == 0`.
    CollectionIsEmpty,
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
    // The scalar atomics were here as "rarely property-relevant", which was
    // true while nothing modelled them and is not any more: the concurrency
    // explorer models them, and `Pure` erases a call -- rewriting it to a
    // `Havoc` -- so `incrementAndGet()` never reached the interpreter and the
    // counter it updates was invisible. They are the whole point of a
    // concurrency engine, so the call has to survive into the IR.
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

    // Members of `PURE_OWNERS` classes that are *not* total. `Pure` erases the
    // call — the lifter rewrites it to a `Havoc`, or drops it entirely when the
    // return type is void — so no engine ever sees a call node, and neither the
    // NRE allowlist nor the verdict guard can fire. For a method that throws,
    // that is a silent wrong TRUE: `System.arraycopy` out of bounds simply
    // disappeared from the IR (issue #49).
    //
    // These must stay `Unmodelled` so the call survives into the IR and the
    // engines can reason about its exceptional behaviour.
    if pure_owner_member_may_throw(owner, name, desc) {
        return CallModel::Unmodelled;
    }

    if PURE_OWNERS.contains(&owner) {
        return CallModel::Pure(ret_ty(desc));
    }

    CallModel::Unmodelled
}

/// `true` for members of `PURE_OWNERS` classes that can raise a
/// `RuntimeException`, and so must not be modelled as pure.
///
/// Keyed on the descriptor where overloads differ in totality —
/// `Integer.valueOf(int)` is total, `Integer.valueOf(String)` throws
/// `NumberFormatException`.
fn pure_owner_member_may_throw(owner: &str, name: &str, desc: &str) -> bool {
    match owner {
        // Overflow (`*Exact`) and zero-divisor (`floorDiv`/`floorMod`) checks.
        "java/lang/Math" | "java/lang/StrictMath" => matches!(
            name,
            "addExact" | "subtractExact" | "multiplyExact" | "incrementExact"
                | "decrementExact" | "negateExact" | "absExact" | "toIntExact"
                | "floorDiv" | "floorMod" | "ceilDiv" | "ceilMod" | "divideExact"
        ),
        // Monitor operations. All three throw `IllegalMonitorStateException`
        // unless the caller owns the monitor, and `wait` also throws
        // `InterruptedException`.
        //
        // Keeping them out of `Pure` matters for a second reason beyond
        // throwing: `Pure` *erases* the call, and a void one disappears from
        // the IR entirely. A `wait()` that is not in the IR cannot block, so a
        // thread that waits forever appears to terminate and a program that
        // provably hangs is reported deadlock-free — the same shape as the
        // `System.arraycopy` disappearance in issue #49, which is why that
        // entry sits directly below.
        "java/lang/Object" => matches!(name, "wait" | "notify" | "notifyAll"),
        // IndexOutOfBounds / ArrayStore / NPE.
        "java/lang/System" => name == "arraycopy",
        // Boxing from a String parses, and parsing throws.
        "java/lang/Integer" | "java/lang/Long" | "java/lang/Short"
        | "java/lang/Byte" | "java/lang/Float" | "java/lang/Double" => {
            name == "valueOf" && desc.starts_with("(Ljava/lang/String;)")
        }
        // Bounds and comparator contracts.
        "java/util/Arrays" => matches!(
            name,
            "copyOfRange" | "fill" | "sort" | "binarySearch" | "asList" | "setAll"
        ),
        // `max`/`min` throw on an empty collection; `nCopies` on a negative count.
        "java/util/Collections" => matches!(
            name,
            "max" | "min" | "nCopies" | "unmodifiableList" | "unmodifiableMap"
                | "unmodifiableSet" | "sort" | "binarySearch"
        ),
        // Partial by contract: out-of-range index, empty receiver, null key.
        "java/util/List" | "java/util/ArrayList" | "java/util/LinkedList"
        | "java/util/AbstractList" => matches!(name, "get" | "set" | "remove" | "add"),
        "java/util/Map" | "java/util/HashMap" | "java/util/TreeMap"
        | "java/util/LinkedHashMap" | "java/util/AbstractMap" => {
            // Sorted maps throw on null/incomparable keys; the hash maps do not,
            // but `TreeMap` shares this owner set, so stay conservative.
            matches!(name, "put" | "get" | "remove")
        }
        "java/util/TreeSet" | "java/util/Set" => matches!(name, "add" | "first" | "last"),
        "java/util/Iterator" | "java/util/ListIterator" => {
            matches!(name, "next" | "previous" | "remove")
        }
        _ => false,
    }
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

        // Size queries read the tracked element count, which is what makes an
        // `i < size` bound provable rather than merely stated.
        "size" if desc == "()I" => Some(CallModel::CollectionSize),
        "isEmpty" if desc == "()Z" => Some(CallModel::CollectionIsEmpty),

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
        ExplicitThrow => Some("java/lang/RuntimeException"),
        // A deadlock throws nothing — the program hangs. There is no
        // exception class to look for on replay, which is one reason the
        // no-deadlock property is answered outside the obligation system.
        Deadlock => None,
    }
}

#[cfg(test)]
mod contract_order_tests {
    use super::*;

    #[test]
    fn more_preconditions_is_more_conservative() {
        let weak = Contract { requires: &[], effect: Effect::Pure };
        let strong = Contract {
            requires: &[Precondition::NonNull(1)],
            effect: Effect::Pure,
        };
        assert!(strong.at_least_as_conservative_as(&weak));
        assert!(!weak.at_least_as_conservative_as(&strong));
    }

    #[test]
    fn a_wider_effect_is_more_conservative() {
        let pure = Contract { requires: &[], effect: Effect::Pure };
        let recv = Contract { requires: &[], effect: Effect::Receiver };
        let unk = Contract { requires: &[], effect: Effect::Unknown };
        assert!(recv.at_least_as_conservative_as(&pure));
        assert!(unk.at_least_as_conservative_as(&recv));
        assert!(!pure.at_least_as_conservative_as(&recv));
    }

    #[test]
    fn opaque_is_the_top_of_the_order() {
        // Everything the table can express must sit below OPAQUE, or a
        // perturbation to it would not be a move *up* the order and the
        // metamorphic test would be checking the wrong thing.
        for (class, name, desc) in [
            ("java/lang/String", "length", "()I"),
            ("java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;"),
            ("java/lang/Object", "<init>", "()V"),
            ("java/lang/Math", "abs", "(I)I"),
        ] {
            if let Some(c) = contract_of(class, name, desc) {
                assert!(
                    Contract::OPAQUE.at_least_as_conservative_as(&c),
                    "{class}.{name} is not below OPAQUE"
                );
            }
        }
    }

    #[test]
    fn the_order_is_reflexive_and_transitive_where_it_should_be() {
        let a = Contract { requires: &[], effect: Effect::Pure };
        let b = Contract { requires: &[Precondition::NonNull(1)], effect: Effect::Receiver };
        let c = Contract::OPAQUE;
        assert!(a.at_least_as_conservative_as(&a));
        assert!(b.at_least_as_conservative_as(&a));
        assert!(c.at_least_as_conservative_as(&b) || c.requires.len() >= b.requires.len());
    }

    #[test]
    fn a_total_contract_is_the_bottom_and_is_what_licenses_a_discharge() {
        // `is_total` is the soundness commitment: it lets a havoced call be
        // treated as non-throwing. It must be exactly the bottom of the order.
        let total = Contract { requires: &[], effect: Effect::Pure };
        assert!(total.is_total());
        assert!(!Contract::OPAQUE.is_total());
    }
}

/// Signatures the JDK specifies as total: no input can make them throw.
///
/// # Why this lives here now
///
/// It was a `match` inside the BMC, consulted only after `contract_of` returned
/// `None` -- so a third of the JDK surface the analyser actually asks about was
/// answered *outside* the contract table. That made the refinement order in
/// `Contract::at_least_as_conservative_as` unenforceable over most of the
/// methods it exists to govern, and made the metamorphic monotonicity test
/// vacuous: perturbing `String.length` changed nothing, because nothing
/// consulted the contract for it.
///
/// Measured before the move: of 46 JDK signatures consulted across the smoke
/// set, 17 had a stated contract, 23 were answered here, and 6 fell through to
/// the default. Coverage was 36%.
///
/// Every entry is still a soundness commitment under the rules in CLAUDE.md --
/// keyed on the full `(class, name, desc)`, never a whole class, never a
/// partial function -- but now there is exactly one place that states them.
pub fn is_total_jdk_signature(class: &str, name: &str, desc: &str) -> bool {
    match class {
        // `Object`'s own implementations are total. (Overrides are not: a
        // subclass `equals`/`toString` can throw, but those have bodies we
        // inline, so they never reach this check as havoced calls.)
        "java/lang/Object" => matches!(
            (name, desc),
            ("<init>", "()V")
                | ("getClass", "()Ljava/lang/Class;")
                | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
        ),

        // Only the no-argument queries. Anything taking a `String`/`CharSequence`
        // throws NPE on null (`concat`, `contains`, `startsWith`, `replace`),
        // anything taking an index throws (`charAt`, `substring`), the regex
        // methods throw `PatternSyntaxException`, and `format` throws
        // `IllegalFormatException`.
        "java/lang/String" => matches!(
            (name, desc),
            ("length", "()I")
                | ("isEmpty", "()Z")
                | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("intern", "()Ljava/lang/String;")
                | ("trim", "()Ljava/lang/String;")
                | ("toCharArray", "()[C")
                | ("toUpperCase", "()Ljava/lang/String;")
                | ("toLowerCase", "()Ljava/lang/String;")
                // `equals` is null-tolerant by contract (returns false).
                | ("equals", "(Ljava/lang/Object;)Z")
        ),

        // Unboxing accessors are total. `valueOf` only for the *primitive*
        // overloads — the `String` ones throw `NumberFormatException`.
        "java/lang/Integer" => matches!(
            (name, desc),
            ("intValue", "()I") | ("longValue", "()J") | ("doubleValue", "()D")
                | ("floatValue", "()F") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(I)Ljava/lang/Integer;")
                | ("toString", "(I)Ljava/lang/String;")
                | ("compare", "(II)I")
        ),
        "java/lang/Long" => matches!(
            (name, desc),
            ("intValue", "()I") | ("longValue", "()J") | ("doubleValue", "()D")
                | ("floatValue", "()F") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(J)Ljava/lang/Long;")
                | ("toString", "(J)Ljava/lang/String;")
                | ("compare", "(JJ)I")
        ),
        "java/lang/Short" => matches!(
            (name, desc),
            ("shortValue", "()S") | ("intValue", "()I") | ("longValue", "()J")
                | ("doubleValue", "()D") | ("floatValue", "()F") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(S)Ljava/lang/Short;")
        ),
        "java/lang/Byte" => matches!(
            (name, desc),
            ("byteValue", "()B") | ("intValue", "()I") | ("longValue", "()J")
                | ("doubleValue", "()D") | ("floatValue", "()F") | ("shortValue", "()S")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(B)Ljava/lang/Byte;")
        ),
        // Float/Double parsing throws; the accessors and primitive boxing do not.
        "java/lang/Float" => matches!(
            (name, desc),
            ("floatValue", "()F") | ("doubleValue", "()D") | ("intValue", "()I")
                | ("longValue", "()J") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(F)Ljava/lang/Float;")
                | ("isNaN", "(F)Z") | ("isInfinite", "(F)Z")
        ),
        "java/lang/Double" => matches!(
            (name, desc),
            ("doubleValue", "()D") | ("floatValue", "()F") | ("intValue", "()I")
                | ("longValue", "()J") | ("shortValue", "()S") | ("byteValue", "()B")
                | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(D)Ljava/lang/Double;")
                | ("isNaN", "(D)Z") | ("isInfinite", "(D)Z")
        ),
        // `parseBoolean`/`valueOf(String)` are null-tolerant by contract here:
        // they return false rather than throwing.
        "java/lang/Boolean" => matches!(
            (name, desc),
            ("booleanValue", "()Z") | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(Z)Ljava/lang/Boolean;")
                | ("parseBoolean", "(Ljava/lang/String;)Z")
        ),
        "java/lang/Character" => matches!(
            (name, desc),
            ("charValue", "()C") | ("hashCode", "()I")
                | ("toString", "()Ljava/lang/String;")
                | ("equals", "(Ljava/lang/Object;)Z")
                | ("valueOf", "(C)Ljava/lang/Character;")
                // Classification predicates are total over the whole char range.
                | ("isDigit", "(C)Z") | ("isLetter", "(C)Z")
                | ("isLetterOrDigit", "(C)Z") | ("isWhitespace", "(C)Z")
                | ("isUpperCase", "(C)Z") | ("isLowerCase", "(C)Z")
                | ("isAlphabetic", "(I)Z") | ("isSpaceChar", "(C)Z")
                | ("toUpperCase", "(C)C") | ("toLowerCase", "(C)C")
        ),

        // Explicitly enumerated: the `*Exact` family throws `ArithmeticException`
        // on overflow, and `floorDiv`/`floorMod`/`ceilDiv` throw on a zero
        // divisor. The listed methods saturate to NaN/Infinity instead.
        "java/lang/Math" | "java/lang/StrictMath" => matches!(
            name,
            "abs" | "min" | "max" | "sqrt" | "cbrt" | "sin" | "cos" | "tan"
                | "asin" | "acos" | "atan" | "atan2" | "exp" | "expm1"
                | "log" | "log10" | "log1p" | "pow" | "floor" | "ceil"
                | "rint" | "round" | "signum" | "hypot" | "random"
                | "toRadians" | "toDegrees" | "ulp" | "nextUp" | "nextDown"
                | "nextAfter" | "copySign" | "IEEEremainder" | "sinh" | "cosh"
                | "tanh" | "fma" | "scalb" | "getExponent"
        ),

        // `arraycopy` throws `IndexOutOfBounds`/`ArrayStore`/NPE and `exit` can
        // raise `SecurityException`, so neither is listed.
        "java/lang/System" => matches!(
            (name, desc),
            ("currentTimeMillis", "()J") | ("nanoTime", "()J")
                | ("identityHashCode", "(Ljava/lang/Object;)I")
                | ("lineSeparator", "()Ljava/lang/String;")
        ),

        // The no-arg constructor and the primitive/String appends. The
        // capacity constructor throws `NegativeArraySizeException`, and the
        // `(char[], int, int)` append throws `IndexOutOfBoundsException`.
        "java/lang/StringBuilder" | "java/lang/StringBuffer" => {
            matches!((name, desc), ("<init>", "()V"))
                || matches!((name, desc),
                    ("length", "()I") | ("toString", "()Ljava/lang/String;"))
                || (name == "append"
                    && matches!(desc,
                        "(Ljava/lang/String;)Ljava/lang/StringBuilder;"
                        | "(Ljava/lang/String;)Ljava/lang/StringBuffer;"
                        | "(I)Ljava/lang/StringBuilder;" | "(I)Ljava/lang/StringBuffer;"
                        | "(J)Ljava/lang/StringBuilder;" | "(J)Ljava/lang/StringBuffer;"
                        | "(C)Ljava/lang/StringBuilder;" | "(C)Ljava/lang/StringBuffer;"
                        | "(Z)Ljava/lang/StringBuilder;" | "(Z)Ljava/lang/StringBuffer;"
                        | "(D)Ljava/lang/StringBuilder;" | "(D)Ljava/lang/StringBuffer;"
                        | "(F)Ljava/lang/StringBuilder;" | "(F)Ljava/lang/StringBuffer;"
                        | "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"
                        | "(Ljava/lang/Object;)Ljava/lang/StringBuffer;"))
        }

        // `print`/`println` swallow IOException and render null as "null".
        // `format`/`printf` throw `IllegalFormatException`, and `print(char[])`
        // throws NPE on a null array, so neither is listed.
        "java/io/PrintStream" | "java/io/PrintWriter" => {
            (matches!(name, "print" | "println")
                && matches!(desc,
                    "()V" | "(Ljava/lang/String;)V" | "(I)V" | "(J)V" | "(C)V"
                    | "(Z)V" | "(D)V" | "(F)V" | "(Ljava/lang/Object;)V"))
                || matches!((name, desc), ("flush", "()V"))
        }

        // `compareTo` can raise `ClassCastException` across enum types, so it
        // is excluded; the rest are total.
        "java/lang/Enum" => matches!(
            (name, desc),
            ("ordinal", "()I") | ("name", "()Ljava/lang/String;")
                | ("toString", "()Ljava/lang/String;") | ("hashCode", "()I")
                | ("equals", "(Ljava/lang/Object;)Z")
        ),

        // Only the total queries on hash-based collections. `get`, `next`,
        // `pop`, `peek` and the index-taking `add`/`remove` overloads are all
        // partial. Sorted collections are excluded entirely: `TreeMap`/`TreeSet`
        // throw NPE on a null key and `ClassCastException` on incomparable ones.
        "java/util/ArrayList" | "java/util/LinkedList" | "java/util/HashSet"
        | "java/util/HashMap" | "java/util/LinkedHashMap" | "java/util/LinkedHashSet" => {
            matches!((name, desc), ("<init>", "()V"))
                || matches!((name, desc), ("size", "()I") | ("isEmpty", "()Z") | ("clear", "()V"))
        }

        // `hasNext` is total; `next` throws `NoSuchElementException` when
        // exhausted and `remove` throws `IllegalStateException`.
        "java/util/Iterator" => matches!((name, desc), ("hasNext", "()Z")),

        _ => false,
    }

}
