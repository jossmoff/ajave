# Software development lifecycle

How this repository is actually meant to be worked in: labels, milestones,
the project board, what "done" means, and — because a process without its
reasoning attached rots into cargo-culted checkboxes — the decisions that
produced each piece of it.

## 1. Labels

Defined in `.github/labels.yml`, synced by `.github/workflows/labels.yml` on
every push to `main` that touches that file. Six families:

- **`type:*`** — what kind of change (`feature`, `fix`, `refactor`, `docs`,
  `test`, `ci`, `chore`). Drives `release-drafter`'s categorisation.
- **`tier:*`** — which layer of the engine portfolio, matching
  `docs/architecture.md` §6 exactly (0 presolve through 5 CHC). An issue
  about `ajave-engines/src/interval.rs` gets `tier:1-ai`; nothing else needs
  to guess which tier a change belongs to.
- **`area:*`** — which crate or subsystem. Maps directly onto
  `docs/crates.md`'s table, plus `witness` and `benchexec` for the two
  competition-integration concerns that don't live in a single crate.
- **`priority:*`** — `p0-soundness` (a wrong verdict is reachable — see §3),
  `p1-blocker` (blocks the current milestone), `p2-normal` (default),
  `p3-later` (not scheduled).
- **`direction:*`** — `over`/`under`/`exact`, mirroring
  `core::artifact::Direction`. Attached to any issue touching `ajave-core`
  or an `Engine`/`Cpa` implementation, so a reviewer knows what the change
  is and isn't entitled to conclude before reading a line of diff.
- **Meta labels** — `good-first-issue`, `help-wanted`, `needs-design-doc`
  (a strategy proposed but without its `docs/strategies/*.md` yet — see §4),
  `breaking`, `skip-changelog`, `dependencies`, `java8-compat`.

**Why six families instead of a flat list:** an issue like "interval domain
doesn't discharge X" needs `type:fix`, `tier:1-ai`, `area:engines`,
`direction:over`, and possibly `priority:p0-soundness` — five simultaneous
facts about one issue. A flat label list either forces picking one (losing
information) or lets labels multiply without structure. Families make the
label set self-documenting: seeing `tier:3-kinduction` without a matching
`docs/strategies/kinduction.md` is immediately legible as "in progress,
pre-design-doc", not a mystery requiring someone to remember context.

## 2. Milestones and the project board

Milestones are `docs/milestones-and-issues.md` M0–M7, created in GitHub
via `scripts/create-milestones.py` (wraps `gh issue create --milestone`).
Each milestone's due date is the calendar target in that file, not an
aspiration — if a milestone slips, move the date and say why in the
milestone description, don't quietly let issues pile up against a stale one.

**Project board** (GitHub Projects v2 — created once, manually, since it
needs a real project ID this repo can't provision for itself):

- **Views:** a board grouped by `tier:*` (shows the engine-portfolio
  progression at a glance — this is the view that answers "how close are we
  to combination A"), and a table grouped by milestone (the standard
  burn-down view).
- **Fields beyond the defaults:** `Tier` (single-select, mirrors the
  `tier:*` labels — redundant with labels deliberately, since a board field
  survives being displayed in views in a way a label list doesn't),
  `Direction` (single-select, same reasoning).
- **Automation:** `.github/workflows/labels.yml` keeps labels in sync;
  new-issue-to-project automation is a one-line `actions/add-to-project`
  step to add once the project URL exists — not included here since it
  requires that real URL, and a workflow referencing a placeholder is worse
  than no workflow.

## 3. Definition of done

Applies to every PR, enforced mechanically where possible rather than left
to review discipline:

| Check | Enforced by |
|---|---|
| Formatted | `cargo fmt --all -- --check` (CI: `fmt`) |
| Lints clean, workspace-wide | `cargo clippy --workspace --all-targets -D warnings` (CI: `clippy`) |
| Tests pass | `cargo test --workspace` (CI: `build-and-test`) |
| No unused dependencies | `cargo udeps` (CI: `unused-deps`) |
| Crate graph matches `docs/crates.md` | `scripts/check-boundaries.sh` (CI: `boundaries`) |
| Every strategy has a doc | `scripts/check-strategy-docs.sh` (CI: `strategy-docs`) |
| Java 8 sourcepath compilation still works | `scripts/check-java8.sh` (CI: `java8`) |
| Zero wrong verdicts against the real corpus | `scripts/run-corpus.sh` (CI: `corpus`) |

The last one is the one that actually matters most and is easiest to skip
locally because it's slow (a few minutes, not seconds). It runs on every
push to `main` regardless, and weekly regardless of pushes, and it opens a
`priority:p0-soundness` issue automatically on failure. **A soundness
regression is not a normal bug** — see §5's postmortems for why this gets
its own tier of urgency instead of living in the general issue backlog.

## 4. Adding a verification strategy

Unchanged from `docs/README.md`, repeated here because it's a process rule,
not just a docs-folder convention: `docs/strategies/<name>.md` exists
*before* the `Engine`/`Cpa` implementation, using the template in
`docs/README.md`. An issue proposing a strategy without its doc gets
`needs-design-doc` and doesn't get a PR opened against it. This forces the
direction (`Over`/`Under`/`Exact`) and the soundness argument to exist as
prose before they exist as code — which is exactly backwards from how the
concrete engine's heap-modelling gap was originally found (code first,
soundness argument reconstructed afterward, during a live debugging session
rather than a design review).

## 5. Decision log

The choices that produced the shape of this repository, in the order they
came up, including the two that turned out to be wrong the first time.

**Obligation-centric architecture, not program-centric.** The unit of
verification work is a single proof obligation (`ir::Obligation`), not a
whole-program verdict. Both SV-COMP Java properties (`assert`,
no-runtime-exception) reduce to "is this obligation's safety condition
reachable-false", so the core never needs to know which property it's
checking. Rejected alternative: a property-specific checker per
specification, which would have duplicated the reachability question twice
for no benefit.

**Blackboard, not verdict-only portfolio exchange.** Engines publish
artifacts (invariants, traces, witnesses — `core::artifact::Artifact`) to a
shared store rather than only reporting a final verdict. A portfolio that
only exchanges verdicts discards nearly everything each engine learned;
combinations A/B/C/D in `docs/architecture.md` §6 aren't possible without
this.

**Direction tags enforced twice, not once.** Every artifact carries
`Direction::{Over,Under,Exact}`, checked both at compile time
(`verdict::OverApprox`/`UnderApprox` traits) and at runtime
(`Blackboard::publish`'s rejection rule). Belt and braces was deliberate:
the runtime check exists because not every engine is required to go through
the trait-based path, and the type-level check exists because a runtime
check alone means a bug is caught in testing rather than prevented at
compile time. Both layers have each caught something the other didn't.

**Workspace split into six crates, not one.** Originally a single crate.
Split for isolation once the design stabilised enough that the boundaries
were real rather than aspirational — see `docs/crates.md` for the graph and
rationale. The split itself surfaced a latent bug: `Body::check_point`
briefly needed a `core`-crate type from the `ir` crate, which would have
forced a circular dependency. Caught by the split, not by review; this is
the argument for `scripts/check-boundaries.sh` existing as a permanent CI
check rather than a one-time cleanup.

**Compile Java source itself, not assume pre-built classfiles.** SV-COMP
task YAMLs list `.java` sourcepaths, not classfiles — confirmed by checking
how JBMC handles this (a wrapper script compiles before invoking the
binary). `ajave` does the compile step inline in `ajave-cli` rather than as
a separate wrapper, trading "javac's wall-clock time counts against our own
CPU budget" for "one binary, no separate script to keep in sync". Worth
revisiting if SV-COMP's resource accounting rules make the wrapper-script
split matter competitively — noted as an open question, not resolved.

**JVM replay for FALSE, not trust the engine.** A violation is only ever
reported after an independent replay against a real JVM — a deterministic
shadow `Verifier` stand-in, compiled and executed, not just re-run through
`ajave`'s own interpreter. This makes a confirmed `FALSE` correct
independently of whether `ajave`'s IR, lifter, or interpreter semantics are
right. The equivalent for `TRUE` (`InductiveCheck`, independently
re-verifying an interval invariant) is still stubbed — tracked as M4's
prerequisite, and it's the largest asymmetry in the certification story
right now: a `TRUE` currently rests entirely on the interval engine's own
fixpoint being correct.

**Postmortem: `stop_sep` ignored program location.** The default
subsumption check in the shared CPA fixpoint loop compared a new abstract
state against every previously reached state, regardless of where each one
sits in the program. An empty variable map (Top everywhere) made the very
first explored state look like it subsumed almost anything, silently
truncating exploration. Produced 12 confirmed wrong `TRUE` verdicts on the
`jbmc-regression` corpus — found by running against real tasks, not by any
of the four hand-picked stage examples, all of which passed throughout.
Fixed in `core::cpa`'s default `stop`, not in the interval domain, since the
bug was general to any `Cpa` implementation. Correctness went from
"51 correct, 12 wrong" to "32 correct, 0 wrong" — a worse headline number
and a strictly better tool. **This is the concrete reason `scripts/run-corpus.sh`
exists as a permanent, scheduled CI job rather than a one-off sanity check.**

**Postmortem: `Unknown` silently resolving to `0`.** The concrete engine's
untracked values (array lengths, field reads) defaulted to the numeric
value `0` in comparisons and arithmetic (`Value::Unknown.as_i64() == 0`),
so a bounds check like `idx < len` for an untracked `len` silently became
`idx < 0` — always false, including on an array literal's own construction.
Found by building and testing an example rather than by inspection. Fixed
by propagating `Unknown` through `eval_bin` instead of defaulting it, and by
making the `Check`-site logic distinguish "concretely false" from
"genuinely unknown" (only the former may report `Violated`). Net effect on
the corpus: 32 correct → 40 correct, 0 wrong → 0 wrong — again, found by
testing against something real, not by code review. **Reinforces the same
lesson as the `stop_sep` bug from a completely different subsystem:
soundness bugs in this codebase have so far always been found by running
against real tasks, never by reasoning about the code in the abstract.**

**Tool renamed `jvmv` → `ajave`.** Purely naming; the ajave-level metaphor
(light ajave = cheap fast passes, dark ajave = deep proof) happened to map
cleanly onto the tier system already in `docs/architecture.md` §6, which is
the actual justification beyond "it sounded fun" — a name that fights the
architecture's own vocabulary would have been a worse trade than a
duller name that matched it.
