# ajave — concepts, definitions, and training material

Every entry has an **ELI5** (what you'd tell a smart person with no background),
an **Actually** (the real definition), and where relevant an **In ajave** (how it
lands in this codebase).

---

## Part 1 — The competition

### SV-COMP
**ELI5.** An annual bake-off where research teams point their bug-finding
programs at the same few thousand test programs and see who scores highest.
**Actually.** The International Competition on Software Verification, run by
Dirk Beyer (LMU Munich) and Jan Strejček (Masaryk), results announced at TACAS
each spring. Tracks for C, Java, and now SV-LIB, plus a separate witness
validation track.
**In ajave.** The Java track had 11 verifiers in 2026 against C's 61 — the
thinness of the field is the entire strategic opening.

### Java.Overall
**ELI5.** The single league table that decides who wins the Java track.
**Actually.** The meta-category aggregating all Java verification tasks. In 2026
it ran 1,731 tasks with a maximum score of 2,821; JBMC won on 1,561, GDart took
1,470, JLiSA 1,311.
**In ajave.** The winner captures ~55% of available points. That headroom is the
thing to attack.

### Scoring schema
**ELI5.** Correct answers earn points, wrong answers cost you a lot more than
they earn. Saying "I don't know" is free.
**Actually.** Correct TRUE is worth 2, correct FALSE 1, wrong TRUE −32, wrong
FALSE −16, unknown 0. Results also need their witness confirmed by a validator
to count fully.
**In ajave.** The asymmetry drives everything: never guess. A tool that is merely
*never wrong* closes a real part of the gap before proving anything clever.

### Verification task
**ELI5.** A program plus a question about it, and a sealed envelope with the
right answer.
**Actually.** A `.yml` task definition naming the input files, the property
file, and the `expected_verdict`. Ground truth ships in the repo, so you don't
need an oracle — you need a runner.

### Property file (`assert.prp`)
**ELI5.** A one-line statement of what "correct" means for this run.
**Actually.** For the Java assertion property, literally
`CHECK( init(Main.main()), LTL(G assert) )` — "starting from `Main.main`, an
assertion never fails". A second property covers runtime exceptions.

### `Verifier` stub API
**ELI5.** A fake random-number library the benchmark programs call, which
verifiers are expected to treat as "any value at all".
**Actually.** `org.sosy_lab.sv_benchmarks.Verifier` provides `nondetInt()`,
`assume(boolean)`, and friends. `assume` is implemented as
`Runtime.getRuntime().halt(1)` on failure — worth knowing for replay, since an
assumption violation exits 1 rather than throwing.
**In ajave.** Modelled directly in the lifter: `nondet*` becomes
`Rvalue::Nondet`, `assume` becomes `Stmt::Assume`.

### BenchExec
**ELI5.** The stopwatch and referee — it runs each tool in a sealed box with
fixed CPU, memory and time, so results are comparable.
**Actually.** The benchmarking framework used to execute the competition, with
cgroup-based resource isolation. Tools integrate via a small Python "tool-info
module" that knows how to invoke the binary and parse its verdict.

### fm-tools
**ELI5.** The registry where you declare your tool exists so it can be entered.
**Actually.** A GitLab repository of tool metadata — archive DOI, options,
representing jury member. Registration is a prerequisite for participation.

### Witness
**ELI5.** Showing your working. Not "there's a bug" but "here's the exact input
that triggers it".
**Actually.** A machine-readable artifact justifying a verdict. *Violation
witnesses* describe a path to the error; *correctness witnesses* carry
invariants. Java currently uses witness format 1.0.
**In ajave.** `ajave_ir::verdict::Witness` holds the nondeterministic value sequence. The
`UnderApprox` trait cannot be implemented without producing one — deliberately.

### Witness validation
**ELI5.** A second, independent program checks your homework before you get the
marks.
**Actually.** A separate competition track where validators confirm or refute
witnesses. Unconfirmed results score less or nothing.
**In ajave.** This is your home turf — wit4java and polywit are validators. Most
teams bolt witness generation on in November and bleed points; building it
alongside the engine is a structural advantage.

### Quantile plot
**ELI5.** A graph where reaching further right means solving more, and starting
further left means you got more things wrong.
**Actually.** Cumulative score against per-task runtime. The right end shows
total score, the left end shows accumulated penalty, and the length shows
correct work done.

---

## Part 2 — Core verification concepts

### Soundness vs completeness
**ELI5.** Sound = never lies when it says "safe". Complete = never misses a bug.
You essentially cannot have both, so you pick which way to be wrong.
**Actually.** A sound analysis never reports TRUE for an unsafe program; a
complete one never reports UNKNOWN for a safe one. Undecidability forces a
trade.
**In ajave.** Encoded as `ajave_core::artifact::Direction`.

### Over-approximation
**ELI5.** You draw a big generous circle around everything the program could
possibly do. If the bug isn't inside the circle, it can't happen.
**Actually.** The analysis computes a superset of reachable states. May prove
safety; any "bug" it finds may be spurious.
**In ajave.** Abstract interpretation and k-induction are `Over`. The blackboard
rejects any attempt by them to publish a violation.

### Under-approximation
**ELI5.** You actually run some real paths. Anything you see happen definitely
happens — but you haven't seen everything.
**Actually.** The analysis computes a subset of reachable states. May exhibit a
genuine bug; silence proves nothing.
**In ajave.** BMC and concolic execution are `Under` and can never discharge an
obligation.

### Proof obligation
**ELI5.** One specific thing that must not go wrong, at one specific place —
"this division must not be by zero, right here".
**Actually.** A safety condition attached to a program point. The task is TRUE
when all obligations are discharged, FALSE the moment one is violated.
**In ajave.** The central unit of work (`ajave_ir::Obligation`). Both SV-COMP Java
properties reduce to obligation reachability, so the core never needs to know
which property it's checking.

### Reachability
**ELI5.** Can the program ever actually get to this line, with values that make
things go wrong?
**Actually.** The fundamental question underlying safety verification: does
there exist an execution reaching a designated error state.

### Invariant
**ELI5.** Something that's always true at a particular point in the program, no
matter how you got there.
**Actually.** A predicate holding on every reachable state at a location.
*Inductive* invariants additionally survive every transition — which is what
makes them usable as proofs.

### Inductive invariant
**ELI5.** A fact that's true when you start, and stays true every time the
program takes a step. That combination is a proof by itself.
**Actually.** `Init ⇒ I` and `I ∧ T ⇒ I'`. The workhorse of unbounded safety
proof, and small enough to check independently.
**In ajave.** `InvStatus::Candidate` until `certify::InductiveCheck` promotes it
to `Inductive`. Only inductive invariants may discharge anything.

### Lattice / join / fixpoint
**ELI5.** A way of ranking "how much you know", with a rule for merging two
partial pictures, and a stopping condition for when merging stops teaching you
anything new.
**Actually.** A partially ordered set with least upper bounds. Analyses iterate
a monotone function until it stabilises — the least fixpoint.
**In ajave.** `cpa::Lattice` (`leq`, `join`, `is_bottom`).

### Belnap four-valued lattice
**ELI5.** Four answers instead of two: I don't know, true, false, and "two
sources told me contradictory things".
**Actually.** A bilattice with bottom (no information) and top (contradiction).
Contradiction is informative — it always means a bug in the tooling.
**In ajave.** `ajave_ir::verdict::Verdict`. `Contradiction` reports as UNKNOWN externally:
we'd rather score zero than emit a verdict we know is internally inconsistent.

---

## Part 3 — Techniques

### Bounded model checking (BMC)
**ELI5.** Unroll the program a fixed number of steps, turn the whole thing into
one giant logic puzzle, and ask a solver whether anything can go wrong within
that many steps.
**Actually.** Encode executions up to depth *k* as an SMT formula; SAT means a
bug with a concrete counterexample, UNSAT means no bug *within k*. Fundamentally
under-approximating.
**In ajave.** `ajave_engines::concrete` (the enumerate-don't-solve falsifier --
see `docs/strategies/concrete.md`). JBMC is real BMC, which is exactly why it can't
prove unbounded safety.

### k-induction
**ELI5.** Prove it holds for the first few steps, then prove that whenever it
held for the last few steps it holds for the next one. Together those give you
"always", from a bounded tool.
**Actually.** Base case = BMC to depth *k*. Step case = assume the property on
*k* consecutive states, prove it at *k+1*. Both discharging yields an unbounded
proof.
**In ajave.** The route from `Status::Bounded { k }` to `Status::Discharged`.

### Invariant injection (auxiliary invariants)
**ELI5.** k-induction usually gets stuck. You hand it a few extra facts you
proved cheaply elsewhere, and suddenly it goes through.
**Actually.** Strengthening the k-induction step case with externally computed
invariants. Most properties aren't k-inductive for any usable *k*; this is what
fixes that.
**In ajave.** Combination (A), the highest-leverage pairing available and one no
Java-track tool currently does.

### Abstract interpretation
**ELI5.** Instead of tracking exact values, track something coarser and cheaper
— like "this is somewhere between 0 and 10" — and reason with that.
**Actually.** Sound approximation of program semantics over an abstract domain
connected to the concrete one by a Galois connection. Fast, always terminates,
imprecise.
**In ajave.** The growth path for `ajave_engines::presolve`. JLiSA is an abstract
interpreter.

### Interval / nullness domains
**ELI5.** Two very cheap facts worth tracking: roughly how big is this number,
and can this reference be null.
**Actually.** Non-relational domains mapping each variable to a range or a
nullness lattice. Cheap enough to run on everything.
**In ajave.** Between them these discharge a large fraction of runtime-exception
obligations — array bounds, division by zero, null dereference — in under a
second. Free score nobody is collecting cleanly.

### Widening
**ELI5.** When a loop keeps making your estimate grow, stop chasing it and jump
straight to "could be anything upward". Otherwise you'd loop forever.
**Actually.** An operator forcing termination of fixpoint iteration over
infinite-height lattices, at the cost of precision. Usually paired with
*narrowing* to claw some back.

### Symbolic execution
**ELI5.** Run the program with "some unknown number" instead of real inputs, and
collect the conditions each branch requires.
**Actually.** Execution over symbolic values, accumulating a path condition per
path; solve it to get concrete inputs. Suffers path explosion.

### Concolic execution
**ELI5.** Run the program for real, but also keep track of the symbolic story,
so you can flip one decision and get a genuinely new test.
**Actually.** Concrete + symbolic execution combined; the concrete run keeps
things grounded when the symbolic reasoning can't cope.
**In ajave.** GDart is concolic — strong at falsification, structurally unable to
prove.

### Path explosion
**ELI5.** Every `if` doubles the number of stories you have to keep track of.
Twenty of them and you're dead.
**Actually.** Exponential growth in paths with branching. Mitigated by merging,
summarisation, and abstraction.

### Path merging / veritesting
**ELI5.** Instead of following two branches separately forever, glue them back
together after the `if` and carry one combined description.
**Actually.** Summarising bounded control-flow regions into a single formula.
Java Ranger extended this to dynamic dispatch and exceptional control flow.

### Craig interpolation
**ELI5.** When the solver proves something is impossible, squeeze out the single
"reason why" — the minimal fact that explains the impossibility.
**Actually.** Given UNSAT `A ∧ B`, an interpolant `I` with `A ⇒ I`, `I ∧ B`
unsat, over shared variables only. Extracted from the refutation proof.
**In ajave.** The engine that turns infeasible traces into reusable predicates.

### Interpolation-based model checking (IMC)
**ELI5.** Run BMC; when it comes back "no bug at this depth", harvest the reason
and use it to build a generous-but-safe description of reachable states. Repeat
until it stops growing — that's your proof.
**Actually.** McMillan's algorithm: iterate interpolants into an
over-approximate reachability sequence until it converges to a fixpoint.

### IC3 / PDR
**ELI5.** Instead of one big explanation, build a stack of small ones — a
separate set of facts for "within 1 step", "within 2 steps", and so on — and
push facts up the stack until they stop moving.
**Actually.** Property-Directed Reachability: incrementally strengthen
frame-wise inductive clause sets. The modern descendant of IMC, and the
technique most competition tools reach for via hardware model checkers.

### CEGAR
**ELI5.** Start with a deliberately blurry picture. If it shows a bug, check
whether the bug is real. If it isn't, un-blur exactly the part that fooled you,
and go again.
**Actually.** Counterexample-Guided Abstraction Refinement: abstract, model
check, check counterexample feasibility, refine on spurious ones.
**In ajave.** Lives in the `Cpa::prec` hook (dynamic precision adjustment), fed
by traces from the blackboard rather than hard-wired to one producer.

### Predicate abstraction
**ELI5.** Forget the actual values; just track the answers to a handful of
yes/no questions like "is x bigger than y".
**Actually.** Abstract states are truth assignments over a predicate set. The
predicate set is the *precision*, and CEGAR is how it grows.

### Lazy abstraction
**ELI5.** Don't use the same level of detail everywhere — be precise only on the
paths that actually need it.
**Actually.** Refining precision locally per program location rather than
globally. Ultimate and CPAchecker both do versions of this.

### Trace abstraction
**ELI5.** Treat the program as a set of possible word-sequences. Each time you
prove one family of executions safe, subtract it from the set. When nothing's
left, you're done.
**Actually.** Automata-based verification: infeasible traces become automata
subtracted from the program's language, iterated to emptiness. Ultimate
Automizer's core, and it won C.Overall in 2026.

### Constrained Horn Clauses (CHC)
**ELI5.** Rewrite "is this program safe" as a standard-format logic puzzle, then
hand it to somebody else's very good puzzle solver.
**Actually.** A fragment of first-order logic; program safety becomes CHC
satisfiability, with the solution being the invariants. Solvers: Golem,
Eldarica, Spacer.
**In ajave.** Tier 5 — cheap to build once the IR exists, and an
under-explored angle for Java specifically.

### SMT solving
**ELI5.** A program that answers "is there any assignment of values making all
these constraints true at once" for arithmetic, arrays and bitvectors.
**Actually.** Satisfiability Modulo Theories. Z3, cvc5, Bitwuzla. Bitvector-heavy
Java work suits Bitwuzla; keep it behind a trait so it can be swapped.

### DRAT / LRAT proofs
**ELI5.** The solver doesn't just say "impossible", it hands you a receipt that
a tiny, separately-trusted program can check.
**Actually.** Proof formats for SAT refutations. `cake_lpr` is a checker verified
in HOL4, so "this unrolling is UNSAT" can be discharged without trusting the
solver.
**In ajave.** How the highest-risk component gets pulled out of the trusted core.

### Program slicing
**ELI5.** Delete every line that can't possibly affect the thing you care about,
then verify what's left.
**Actually.** Computing the subprogram affecting a criterion via dependence
analysis. Symbiotic's signature move.

### Portfolio / strategy selection
**ELI5.** Keep several different tools in the bag and either run them all at
once or learn which one to reach for based on what the program looks like.
**Actually.** Parallel portfolio or feature-based algorithm selection. Less
elegant than any single technique, but it wins competitions — many tasks are
trivially decidable by *some* cheap method.

### Conditional model checking (CMC)
**ELI5.** A tool that gives up doesn't just say "dunno" — it says "I checked all
of this region, you only need to look at the rest".
**Actually.** Output a *condition* summarising the covered state space; the next
verifier analyses only the residual.
**In ajave.** `Artifact::Residual`, combination (C) — the least-exploited idea in
the competition and the most natural fit for a blackboard.

### Cooperative verification
**ELI5.** Tools helping each other with partial results instead of each starting
from scratch.
**Actually.** Beyer's programme of exchanging invariants, conditions and
residual programs between verifiers rather than only verdicts.
**In ajave.** The whole reason the blackboard exists.

---

## Part 4 — The architecture

### CPA (Configurable Program Analysis)
**ELI5.** One reusable search loop with five pluggable parts. Swap the parts and
the same loop becomes a completely different verification technique.
**Actually.** `(initial, transfer, merge, stop, prec)` after
Beyer/Henzinger/Théoduloz. `merge_sep`+`stop_sep` = explicit-state model
checking; `merge_join`+`stop_join` = abstract interpretation; predicate domain
with refining `prec` = lazy abstraction.
**In ajave.** `ajave_core::cpa`. The extensibility story: a new domain is a new `Cpa`
impl and nothing else changes.

### Transfer relation
**ELI5.** "Given what I know here, what do I know after this one instruction?"
**Actually.** The abstract post-operator over a CFG edge.

### merge / stop operators
**ELI5.** `merge` decides whether two partial pictures get glued together or
kept apart; `stop` decides whether you've already seen this situation and can
skip it.
**Actually.** `merge_sep` keeps states separate (path-sensitive); `merge_join`
joins them (path-insensitive). `stop_sep` checks subsumption against reached
states.

### Dynamic precision adjustment (`prec`)
**ELI5.** The knob that lets the analysis decide, mid-run, to look more closely
at something.
**Actually.** The CPA+ extension allowing precision to change during
exploration. Where CEGAR refinement hooks in.

### Blackboard architecture
**ELI5.** A shared noticeboard. Everyone pins up what they've learned, everyone
reads what's new since they last looked, and nobody needs to know who else is in
the room.
**Actually.** A shared knowledge store with independent contributors and a
scheduler. Contributors couple to the board, not to each other.
**In ajave.** `ajave_core::blackboard`. Append-only log plus per-engine cursors, so
engines can be added, removed or restarted without coordination.

### Artifact
**ELI5.** A piece of knowledge worth sharing — an invariant, a suspect path, a
witness — rather than just a final answer.
**Actually.** `Invariant`, `Precision`, `AbstractTrace`, `Condition`, `Status`.
A portfolio exchanging only verdicts discards nearly everything each engine
learned.

### Direction tag
**ELI5.** A label on every piece of knowledge saying which way it might be
wrong, so nobody draws a conclusion they aren't entitled to.
**Actually.** `Over` / `Under` / `Exact`. The blackboard rejects a discharge from
an `Under` producer and a violation from an `Over` one, at runtime, in addition
to the type-level rule in `ajave-ir/src/verdict.rs`.
**In ajave.** The single most safety-critical line of code in the system.

### Engine
**ELI5.** One strategy, doing a small slice of work each time it's called, so
the scheduler can share time out fairly.
**Actually.** A bounded-step state machine returning
`Advanced` / `Stalled` / `Exhausted`.

### Orchestrator
**ELI5.** The scheduler deciding who works next: hunt for bugs first because
that's cheap, then try to prove things, then go get more precise and retry.
**Actually.** The phase machine `Presolve → Falsify → Prove → Refine → Report`.
Falsify-first because a found bug ends the task immediately.

### Certifier
**ELI5.** A small, dumb, separately-written checker that refuses to take the
clever code's word for anything.
**Actually.** `JvmReplay` runs a violation witness on a real JVM;
`InductiveCheck` re-verifies invariants. Certificate checking gets most of the
assurance of a verified verifier for a fraction of the cost.

### Trusted computing base (TCB)
**ELI5.** The small set of parts that have to be right. Everything else can be
buggy without producing a wrong answer.
**Actually.** In ajave: the lifter, the memory model, and the transfer functions.
Strategy selection, scheduling and heuristics are soundness-irrelevant by
construction.

### Self-certifying falsification
**ELI5.** If you claim there's a bug and can show the exact input, running it
proves you right — nobody has to trust anything else about you.
**Actually.** A replayed violation witness is correct independently of whether
the IR, solver or semantics are right.
**In ajave.** Why stages 0–3 can ship before anything is trustworthy.

### Differential / metamorphic / mutation testing
**ELI5.** Three ways to catch yourself being wrong: compare against other tools,
change the program in ways that shouldn't matter and check the answer didn't,
and inject a known bug to check you find it.
**Actually.** Differential = disagreement with JBMC/GDart/JLiSA on published
per-task results. Metamorphic = semantics-preserving bytecode transforms.
Mutation = injected faults in known-safe tasks.

---

## Part 5 — The JVM frontend

### Bytecode / operand stack
**ELI5.** Java compiles to instructions for an imaginary machine that does
everything on a stack of plates instead of in named boxes.
**Actually.** A stack-based instruction set. `iadd` pops two, pushes their sum.
**In ajave.** Eliminated at lift time — invariant inference over a stack machine
is miserable, over registers it's routine.

### Constant pool
**ELI5.** A lookup table at the top of every class file holding all its strings,
numbers and names, so instructions can just reference an index.
**Actually.** A 1-based, gappy table (`long` and `double` consume two slots).
**In ajave.** `classfile::Cp`, with `Cp::Unusable` preserving the gaps so indices
line up.

### `Code` attribute / exception table
**ELI5.** The actual instructions of a method, plus a side table saying "if
something goes wrong between here and here, jump there".
**Actually.** Holds `max_stack`, `max_locals`, the bytecode, and handler ranges.
**In ajave.** A method with handlers currently lifts to a single `Diverge` block
— sound, useless, and clearly labelled as stage 4.

### `StackMapTable`
**ELI5.** Notes the compiler leaves saying what the stack looks like at each
jump target, so the JVM can verify quickly.
**Actually.** Frame types for bytecode verification. Gives you verified stack
heights for free instead of recomputing them.

### Descriptor
**ELI5.** A compact string spelling out a method's argument and return types.
**Actually.** `(I[Ljava/lang/String;)V` is "takes an int and a String array,
returns void".

### `<clinit>` / `<init>`
**ELI5.** The hidden setup methods — one that runs once when a class is first
touched, one that runs for each new object.
**Actually.** Static initialiser and constructor. Ordering semantics are subtle
and a classic source of frontend bugs.
**In ajave.** Deliberately modelled away, which is why the completeness check is
scoped to bodies reachable from `main`.

### `$assertionsDisabled`
**ELI5.** `assert` doesn't compile to anything simple — javac adds a hidden flag
and wraps every assert in a check of it.
**Actually.** A synthetic static field initialised in `<clinit>` via
`Class.desiredAssertionStatus()`. SV-COMP runs with `-ea`, so it's false.
**In ajave.** Pinned to `0` in the lifter — deliberately, rather than discovering
three weeks later that every task reports TRUE.

### Basic block / leader / CFG
**ELI5.** Chop the instructions into straight-line runs with no jumps in or out,
then draw arrows between the runs.
**Actually.** Leaders are the entry, every branch target, and every fallthrough
after a terminating instruction. Blocks are maximal runs from one leader to the
next.

### Three-address code / Jimple
**ELI5.** Rewrite everything as "x = y op z" with named variables, which is far
easier to reason about than a stack.
**Actually.** Soot's Jimple is the canonical JVM version. Produced by simulating
the operand stack abstractly and materialising entries into registers.
**In ajave.** `ajave_ir::Stmt`, with stack registers `s0..sn` spilled at block
boundaries as a parallel copy so entries reading each other can't clobber.

### SSA / phi node
**ELI5.** Give every assignment its own fresh variable name, and where two paths
meet, add a marker saying "the value here is whichever one we came from".
**Actually.** Static Single Assignment. Makes def-use chains explicit and helps
invariant generation considerably.
**In ajave.** Deliberately deferred — non-SSA is enough until loops arrive, and
deferring keeps the lifter debuggable while the frontend is the risky part.

### Class hierarchy analysis / devirtualisation
**ELI5.** Work out which classes extend which, so that when the program calls a
method through an interface you can narrow down what actually runs.
**Actually.** CHA computes the subtype relation; devirtualisation resolves
`invokevirtual`/`invokeinterface` to concrete targets where possible.
**In ajave.** Rust has no Soot or WALA, so this is hand-rolled. Budget for it.

### Havoc / nondeterminism
**ELI5.** "This could be anything." The safe thing to assume when you don't know.
**Actually.** Assigning an unconstrained fresh value. A sound over-approximation
of any unmodelled *pure* computation — but not of side effects, which is why
unmodelled calls must diverge rather than havoc.
**In ajave.** `Rvalue::Nondet`.

### Divergence (explicit unlifted regions)
**ELI5.** Instead of quietly skipping the bits you don't understand, plant a
loud marker saying "analysis stops here".
**Actually.** `Terminator::Diverge`. An unsound lifter costs −32 a task; a
partial one costs 0, and 0 is recoverable.

### Arena indices
**ELI5.** Refer to things by their number in a big list instead of by pointer.
Simpler, faster, and no lifetime headaches.
**Actually.** `VarId(u32)`, `BlockId(u32)` into flat vectors. Standard practice
in Rust compilers; avoids `Rc` and threaded lifetimes.

### Standard library modelling
**ELI5.** Don't try to analyse Java's own source code. Write your own short
descriptions of what `String` and friends do.
**Actually.** Hand-written models of `String`, `StringBuilder`, collections and
the exception hierarchy, instead of analysing `java.base` bytecode.
**In ajave.** Every tool that tried to be faithful to the JDK drowned. This is
where a large share of the remaining person-months go.
