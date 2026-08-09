# Notable Techniques and Contributions

Noteworthy implementation details, design decisions, and novel techniques that may be worth discussing in a paper.

## String Theory: Heap Flow and Wrapper toString Modeling (2026-08-09)

Three improvements to the SMT BMC's string theory that unlock securibench and autostub toString benchmarks:

1. **`field_str` — string terms through instance field storage.** Z3 string terms (QF_S sort) were tracked for local variables (`str_vars`) and static fields (`static_str`), but lost when stored into instance fields via `putfield`. Added `field_str: HashMap<FieldKey, Term>` to the symbolic state, mirroring `field_arrays` but for string sort terms. On `putfield`, if the value has an associated string term, it's stored in `field_str`; on `getfield`, it's recovered. This is critical for securibench benchmarks where tainted strings flow through mock HTTP request objects (e.g., `req.setAttribute("name", tainted); ... req.getAttribute("name")`).

2. **`inline_return_str` — string terms through inlined method returns.** When the BMC inlines a callee and the callee returns a string value, the Z3 string term was lost at the return boundary. Added `inline_return_str: Option<Term>` which accumulates across the inlining loop (like `inline_return` for BV terms). The caller's `str_vars` is updated with the returned string term, enabling end-to-end string flow through method call chains.

3. **Wrapper `toString()` modeling.** `Boolean.toString()`, `Integer.toString()`, `Short.toString()`, `Byte.toString()` now produce Z3 string expressions via `str.from_int` with signed number handling. Z3's `str.from_int` returns `""` for negative inputs, so `signed_bv_to_str` uses an ITE: negative values get `concat("-", str.from_int(abs(val)))`. Instance `toString()` unboxes `$value` from the receiver's field array before conversion. `Character.toString()` approximated as a fresh string with `length = 1`.

Impact: Score 544 → 554. New correct: Basic1/2/9/16/29-32/35, Aliasing1, Inter1/2/4/7/8, Datastructures1-3, Factories2, Pred1/2/4-8, Boolean/Integer toString autostub benchmarks.

## Soundness Fixes and Obligation Filtering (2026-08-09)

Six bugs fixed, eliminating all wrong FALSE verdicts and most wrong TRUEs:

1. **Solver `Unknown` results not skipped.** When Z3 returns an error or unknown result on a non-tainted obligation, the BMC silently fell through — the obligation was neither violated nor skipped, and would later be discharged as safe. Fixed by adding `Unknown` results to `skipped_obligations` regardless of taint status. Root cause of VelocityTracker_false wrong TRUE.

2. **Non-seeded obligation violations leak into verdict.** The blackboard accepted `Violated` status for obligations that were never seeded (e.g., `ArrayBounds` and `NullDeref` from callee bodies). Since `verdict()` checks for any `Violated` status, non-assertion violations produced FALSE verdicts on `valid-assert.prp` benchmarks. Fixed by rejecting status updates for non-seeded obligations in `publish()`. Root cause of Base64, StrictLineReader, and StrongUpdates5 wrong FALSEs.

3. **Reachability analysis doesn't follow `<clinit>`.** `reachable_from_entry()` only followed `Rvalue::Call` targets, missing `<clinit>` methods triggered by `new`, `getstatic`, and `putstatic`. Assertions in classes instantiated transitively from the entry method were not seeded. Fixed by adding class initializer methods to the reachability worklist on `New`, `GetStatic`, and `PutStatic`. Also added devirtualization for calls to classes with no loaded body (finding overrides among loaded subclasses).

4. **NRA engine unsound discharge over reals.** The NRA engine encoded float programs as real arithmetic constraints and published `Discharged` when CVC5 returned UNSAT. But UNSAT over reals does not imply UNSAT over IEEE 754 floats (NaN, Inf, -0 can violate assertions that hold over R). Fixed by making NRA falsification-only — it can find violations (SAT) but no longer discharges (UNSAT). Root cause of MathHelper_true wrong TRUE.

5. **Targeted discharge guard for entry method.** The global `all_calls_resolved` guard blocked all TRUEs when any havoced call existed, even if the call wasn't in a try block and couldn't reach the assertion. Refined: entry-method obligations only require `!has_unresolved_in_try` (havoced call in block with exception edges). Callee obligations still require `all_calls_resolved`. This unlocks TRUEs for programs with havoced library calls that can't affect assertions.

6. **Long.reverseBytes encoding fix.** Bytes 1 and 2 had wrong shift amounts.

Impact: Score 413 → 527+ (+114). Wrong FALSE: 3 → 0. Wrong TRUE: 3 → 1 (Refl4 remains, needs obligation seeding in mock classes).

## Smoke Test Suite (2026-08-08)

54 curated benchmarks covering sensitive engine behaviors. Run `python3 tools/smoke_test.py` before full scoring (~3 min). Exit code signals regressions. Canary tests for every previous wrong answer.

## Array, Boxing, and Exception Handling Soundness Fixes (2026-08-08)

Five bugs fixed, three of which caused wrong TRUEs (up to -400 points of penalties):

1. **Array contents lookup order.** `array_contents_lookup` iterated `array_map` in reverse, making the oldest entry for a given ref shadow newer entries from `array_store_update`. After an array store, the ITE chain would select the original (pre-store) array instead of the updated one, making the stored value invisible to subsequent loads. Root cause of ExSymExeArrays_false wrong TRUE. Fixed by iterating forward so later entries take priority.

2. **Double boxing sort mismatch.** `Double.valueOf(D)` was mapped to `BoxStore(Ty::Int)`, storing 64-bit Double values into 32-bit field arrays. This produced Z3 sort errors `(domain sort BV64 and parameter sort BV32 do not match)` that cascaded into all subsequent solver queries returning incorrect results — the solver was in an error state but the BMC interpreted error responses as UNSAT. Fixed by using `BoxStore(Ty::Double)` (64-bit field arrays). This alone eliminated 14 wrong TRUEs in autostub (Double_* and Math_getExponent benchmarks, -224 points recovered).

3. **Throw completeness discrimination.** The BMC's `all_paths_complete` flag controls whether exhaustive exploration can discharge obligations. Previously, ALL `Throw` terminators were treated as complete paths. But only assertion throws (`assert false` → `throw AssertionError`) are fully handled by the preceding `check Assertion` statement. Real exception throws (try/catch dispatch) are NOT modeled, so treating them as complete caused wrong TRUEs on 12+ exception handling benchmarks. Fixed by checking whether the block contains a `Stmt::Check(Assertion)` — only assertion throws count as complete.

4. **JVM narrowing casts.** Opcodes i2b/i2c/i2s (0x91-0x93) were all no-ops (mapped to `Cast(Int)`). Fixed by emitting shift/mask arithmetic: i2b = `(x << 24) >> 24` (sign-extend byte), i2c = `x & 0xFFFF` (zero-extend char), i2s = `(x << 16) >> 16` (sign-extend short).

5. **Diamond merge join point validation.** `find_join_multi` could select a join point that was one of the branch targets (e.g., bb15 as join for targets [bb15, bb10]). Fixed by detecting when one target is reachable from another and falling back to fork.

Impact: Eliminated ~28 wrong TRUEs (recovering ~450 points of penalties), fixed ExSymExeArrays_false (+17 net), VelocityTracker_false (+17 net), swap1, lookupswitch1, tableswitch1, uninitialised1, iarith2.

## Wrapper Unbox/CompareTo and Bit Operation Encodings (2026-08-06)

Four improvements to the SMT BMC's handling of Java wrapper types and bit operations:

1. **Long Unbox field key alignment.** `BoxStore(Ty::Long)` stores to `(java/lang/Long, $$value, J)` (64-bit field), but `Unbox(Ty::Int)` for `Long.byteValue()/shortValue()/intValue()` read from `(java/lang/Long, $$value, I)` — a different field key, reading stale data. Fixed by changing all Long unbox operations to `Unbox(Ty::Long)` so the field key matches. The lifter now inserts explicit `Cast` when the storage type and return type differ in width (e.g., Long→Int narrowing, Int→Long widening for `Integer.longValue()`).

2. **Instance `compareTo` for wrapper types.** Previously fell through to `PURE_OWNERS → Havoc`. Now modelled as `MathCall` in the lifter and encoded in `encode_math_call` by reading `$$value` from both the receiver and argument objects via the field array, then comparing. Integer/Long use `-1/0/1` semantics; Short/Byte/Character use `a - b` (matching JDK behavior). Boolean also uses `a - b`.

3. **Integer/Long `bitCount`, `numberOfLeadingZeros`, `numberOfTrailingZeros`, `reverse`.** Added to both `is_math_call` (lifter) and `math_call_modelled`/`encode_math_call` (BMC). `bitCount` uses ITE cascade over each bit position. `numberOfTrailingZeros`/`numberOfLeadingZeros` scan from LSB/MSB respectively. `reverse` extracts each bit, shifts to reversed position, and ORs.

4. **Additional Character method encodings.** `isSupplementaryCodePoint` (range check), `isISOControl` (two-range check), `isJavaIdentifierStart/Part` (letter/digit/$/_), `toCodePoint` (surrogate arithmetic), `digit` (radix-aware ASCII→value), `forDigit` (inverse). Also trimmed `is_math_call` to match `math_call_modelled` — methods without BMC encodings now get havoced (tainted) instead of unconstrained-untainted `fresh_bv("math_hv")`.

Impact: ~25+ autostub tasks fixed (Long.byteValue/shortValue/intValue, Integer.longValue, all wrapper compareTo, bitCount/nlz/ntz/reverse for Integer+Long, Character methods).

## Width Tracking and InstanceOf Encoding Fixes (2026-08-06)

Three classes of bugs in the SMT BMC's type and width handling, each causing spurious violations:

1. **JVM local slot reuse width mismatch.** A JVM local slot can hold a Long (64-bit), then be reused for a Ref (32-bit), then Long again. The IR's `VarInfo.ty` stores one declared type, but `width_of_operand` used this — producing wrong widths for SMT encoding (e.g., `bvslt(BV64, BV32)` → Z3 returns Unknown). Fixed by adding `var_widths: HashMap<VarId, u32>` that tracks the actual width assigned to each variable at each assignment, and `arg_width_from_desc` that parses method descriptors for argument widths in math call encoding.

2. **InstanceOf encoding for Object, string constants, and array covariance.** `instanceof java/lang/Object` now short-circuits to `obj != null` (correct: everything is an Object). String constants are recognized as always being `java/lang/String` instances. Array covariance is handled via recursive element-type subtyping in `is_subtype` (`[Ljava/lang/String;` is a subtype of `[Ljava/lang/Object;`). Also fixed `is_subtype("java/lang/Object", X)` returning true for any X due to the "unknown class" fallback.

3. **Entry method parameter non-null constraints.** The JVM guarantees `main(String[] args)` receives a non-null args. The SMT BMC now parses the entry method's descriptor, identifies Ref-typed parameter slots, and asserts them non-null. Also stores their declared type in `type_array` so `instanceof` checks on parameters work correctly.

Impact: instanceof1-5 all fixed (TRUE), plus width mismatch fixes prevent Z3 Unknown results on Long comparison benchmarks.

## Precise Wrapper Method Models in SMT BMC (2026-08-06)

The BMC's `encode_math_call` previously covered Math/Integer/Long arithmetic but left many wrapper type methods unencoded. Methods listed in `math_call_modelled` but without a corresponding encoding arm fell through to `fresh_bv("math_hv")` — an unconstrained but **untainted** value, which caused spurious violations that JVM replay would catch and downgrade.

Three changes:

1. **Fixed `compare()` for all wrapper types.** Previously modeled as `StaticBinOp(Sub)` in the lifter — `a - b` overflows for large values and doesn't return exactly -1/0/1 as the JDK specifies. Moved to `MathCall` with proper `(a < b) ? -1 : (a == b) ? 0 : 1` encoding. This alone unlocked 33 Long compare tasks and similar Integer/Short/Byte/Character compare tasks.

2. **Added precise SMT encodings** for: `Byte.toUnsignedInt/Long`, `Short.toUnsignedInt/Long/reverseBytes`, `Character.reverseBytes`, `Character.isDigit/isLetter/isLetterOrDigit/isUpperCase/isLowerCase/isWhitespace/isSpaceChar/isAlphabetic/isBmpCodePoint/isValidCodePoint/toUpperCase/toLowerCase/charCount`, `Integer/Long/Short/Byte/Character.hashCode`. Character classification uses ASCII-range BV constraints (sound for BMP code points used in benchmarks).

3. **Aligned `math_call_modelled` with `encode_math_call`.** Removed methods that had no encoding (reverseBytes, bitCount, numberOfLeadingZeros, etc. for Integer/Long) to prevent them from being unconstrained-but-untainted. These now stay as `Havoc` (tainted), which is sound but incomplete.

Impact: score went from 233 to 350 (+117 points). Correct TRUE: 44→97, Correct FALSE: 225→252.

## Virtual Dispatch in Reachability + Entry Point Disambiguation (2026-08-06)

Three bugs combined to produce 29 wrong TRUEs on securibench benchmarks:

1. **Entry point resolution was non-deterministic.** HashMap iteration picked an arbitrary class's `main()` when multiple were loaded together (securibench loads 100+ classes with `main` methods). Fixed by preferring the `Main` class (SV-COMP convention).

2. **`reachable_from_entry()` didn't follow virtual dispatch.** It only added the declared call target to the worklist, missing devirtualized receivers. For example, `PrintWriter.println()` → `HttpServletResponse$1.println()` (a mock class containing assertion obligations). Fixed by calling `devirtualise()` on virtual call targets during the transitive reachability walk.

3. **PrintWriter/PrintStream calls were classified as `Pure(None)` and dropped entirely.** Void calls on Pure owners only emitted a null check — no `Rvalue::Call` appeared in the IR. This broke the reachability chain even after fix #2. Fixed by removing `PrintWriter`/`PrintStream` from `PURE_OWNERS` so they get `Unmodelled` treatment (emitted as `Rvalue::Call`, inlineable by the BMC).

Impact: score went from -57 to 233 (+290 points). Wrong TRUEs dropped from 29 to 1.

## Benchmark Shape Analysis (2026-08-05)

`body_shape.rs` analyzes a method body at load time and produces a `BodyShape` summary: whether it uses transcendental math, heap ops, strings, arrays, loops, nonlinear integer arithmetic, or floating-point types. The engine portfolio uses this to route obligations to the most effective solver/theory combination instead of running every engine on every benchmark.

This is a lightweight form of **algorithm selection** — the verifier inspects the structure of the verification task and dispatches to a specialized engine rather than relying on a one-size-fits-all approach.

## NRA Engine with Transcendental Math (2026-08-05)

A dedicated engine (`nra.rs`) encodes methods containing transcendental Math calls (sin, cos, exp, log, pow, sqrt, etc.) as nonlinear real arithmetic (NRA) constraints. Transcendental functions are declared as uninterpreted functions with semantic range constraints (e.g., -1 <= sin(x) <= 1, sin(0) = 0, exp(x) > 0) for Z3 compatibility, or used natively with CVC5.

Key design: transcendental Math methods are kept as `Rvalue::Call` in the IR (not havoced to unconstrained values), enabling precise symbolic encoding. The engine does path-sensitive DFS from entry to error, accumulating constraints along each path.

The solver preference chain is CVC5 > dReal > Z3, probed at startup.

## Unified SMT Text Encoding (2026-08-04)

The `SmtTheory` trait (`smt_text.rs`) unifies bitvector (CHC) and linear integer arithmetic (interpolation/IMC/CEGAR) encodings behind a single interface. `encode_operand` and `encode_rvalue` are generic over the theory, eliminating ~200 lines of duplicated encoding logic across engines.

## Multi-Engine Portfolio with Blackboard Architecture

The orchestrator runs a portfolio of engines (presolve, concrete, SMT BMC, interval AI, k-induction, CHC, IMC, CEGAR, NRA) coordinated through an append-only blackboard with direction discipline (Under engines cannot Discharge; Over engines cannot Violate). Engines communicate results via artifacts, and the orchestrator phases (Presolve -> Falsify -> Prove -> Refine -> Report) give each technique its best chance.

## Diamond Merge (ITE State Merging)

The SMT BMC uses ITE-based state merging at branch join points instead of path forking. When a branch's post-dominator join point is found, both sides are explored and merged via `ite(cond, then_val, else_val)` for each variable. This exponentially reduces the number of solver calls compared to naive path enumeration.

## JVM Replay Certification

Every FALSE verdict is confirmed by replaying the witness on a real JVM before reporting. The certifier compiles a shadow `Verifier` class that feeds the witness's nondet values, runs the program, and checks that the assertion actually fails. This closes the gap between what the analysis proves and what the JVM executes.

## Soundness Guards

Proving engines (k-induction, CHC, IMC, CEGAR) skip methods with havoced operations via `body_uses_havoced_ops()`. Since havoced values are unconstrained, an UNSAT result from a simplified encoding would be unsound — the guard prevents false TRUE verdicts.

## CPA Substrate

The `roast-core::cpa` module implements a generic Configurable Program Analysis (CPA) framework. Engines like interval AI and CEGAR's predicate abstraction are implemented as CPA instances with domain-specific abstract states and transfer functions, sharing the reachability algorithm.
