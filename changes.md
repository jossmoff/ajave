# Notable Techniques and Contributions

Noteworthy implementation details, design decisions, and novel techniques that may be worth discussing in a paper.

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
