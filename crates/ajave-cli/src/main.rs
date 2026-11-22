//! ajave driver.
//!
//! Usage:
//!   ajave [OPTIONS] <path>...
//!
//! Prints the lifted IR on `--ir`, the orchestrator schedule on `--trace`, and
//! always ends with a single line BenchExec parses as the verdict.

use std::path::{Path, PathBuf};

use ajave_core::engine::Engine;
use ajave_core::orchestrator::Orchestrator;
use ajave_frontend::classfile::ClassFile;
use ajave_frontend::lift;
use ajave_ir::verdict;
use ajave_ir::Program;
use clap::{ArgAction, Parser};
use log::{debug, info, warn};

#[derive(Parser)]
#[command(
    name = "ajave",
    about = "An SV-COMP Java verifier: compiles/loads a program, runs the engine portfolio, reports a certified verdict.",
    version
)]
struct Cli {
    /// Input files or directories (.java source or pre-compiled .class bytecode).
    /// BenchExec passes every entry of the task YAML's input_files as a separate argument.
    // Both `--build-info` and `--emit-shadow` are modes that consume no
    // program, so either one makes the inputs optional.
    #[arg(required_unless_present_any = ["build_info", "emit_shadow"])]
    inputs: Vec<PathBuf>,

    /// Report which build this is and exit, in particular whether the internal
    /// contract assertions are compiled in.
    ///
    /// Exists because a profile is a claim nobody checks. `debug_assert!` is
    /// compiled out of `release`, so the `MergePolicy` clauses that guard
    /// against losing an abstract state were enforced only under `cargo test`
    /// -- and a harness that means to exercise them has no way to tell a
    /// `release-checked` binary from a `release` one by looking at it. Now it
    /// can ask, and `just oracles` does before it runs.
    #[arg(long)]
    build_info: bool,

    /// Print the lifted IR for every loaded method before verification begins.
    #[arg(long)]
    ir: bool,

    /// Print the orchestrator round schedule and per-obligation statuses after verification.
    #[arg(long)]
    trace: bool,

    /// Increase log verbosity. Pass once for INFO (-v), twice for DEBUG (-vv), three times for TRACE (-vvv).
    /// The RUST_LOG environment variable overrides this flag when set.
    #[arg(short = 'v', long = "verbose", action = ArgAction::Count)]
    verbose: u8,

    /// Write a violation witness (SV-COMP format 2.0 YAML) to this path when
    /// the verdict is FALSE. BenchExec passes this via `--witness <path>`.
    #[arg(long = "witness")]
    witness: Option<PathBuf>,

    /// Skip JVM replay confirmation of violation witnesses. When set, a FALSE
    /// verdict is reported as soon as an engine finds one, without checking it
    /// on a real JVM first.
    #[arg(long = "no-replay")]
    no_replay: bool,

    /// Print the assumptions (nondet values) used in violation witnesses.
    #[arg(long = "show-witness")]
    show_witness: bool,

    /// Wall-clock budget for the whole verification, in seconds.
    ///
    /// Without it the process runs until something outside kills it, which is
    /// what the harness does — and that is the problem. An engine cannot yield
    /// to the next if it does not know a deadline exists. Measured over 20
    /// tasks that hit a 60s budget, `smt-bmc` held the process on 18 of 18, so
    /// `chc`, `k-induction`, `imc` and `cegar` never ran on precisely the
    /// tasks that needed another angle.
    ///
    /// Pass the same value the harness enforces. Engines are given a share of
    /// what remains rather than the whole of it.
    #[arg(long = "timeout", value_name = "SECS")]
    timeout: Option<u64>,

    /// Constrain nondet char to ASCII (0-127). Prevents witnesses with
    /// non-ASCII chars that our Character method encodings can't model.
    #[arg(long = "ascii-only")]
    ascii_only: bool,

    /// Run the IR interpreter on the entry method against a fixed nondet
    /// sequence, print how it terminated, and exit without verifying.
    ///
    /// For `tools/lifter_differential.py`: the same program and the same
    /// sequence are run on a real JVM through the shadow `Verifier`, and the
    /// two terminations compared. Takes a comma-separated list of raw i64
    /// values, matching the `-Dajave.seq=` encoding the replay harness already
    /// uses; an empty list means all-zero, which is the probe the concrete
    /// engine itself runs.
    ///
    /// Deliberately not a verification mode: it prints `INTERPRET <outcome>`
    /// and no verdict line, so nothing downstream can mistake an interpreter
    /// run for an answer about the program.
    #[arg(long = "interpret", value_name = "SEQ", num_args = 0..=1,
          default_missing_value = "")]
    interpret: Option<String>,

    /// Ask, per obligation, what *kind* of fact would discharge it, and exit.
    ///
    /// A census, not a verdict: prints one TSV row per obligation and no
    /// verdict line, for the same reason `--interpret` prints none.
    ///
    /// It exists because three capability directions were each estimated to be
    /// worth points and measured exactly zero. Every bucket in
    /// `tools/blocker_census.py` is named after what *blocks* a verdict, and
    /// removing the blocker leaves the obligation unprovable underneath — so
    /// the question that should have been asked first is what facts the corpus
    /// actually needs. Abduction answers it directly: given the obligation's
    /// error formula, what added hypothesis makes it unreachable?
    #[arg(long = "abduct-census")]
    abduct_census: bool,

    /// Per-obligation vocabulary cap for `--abduct-census`. The scalar grammar
    /// is quadratic in the variable count and the widest corpus method carries
    /// 112 variables, so this is what stops one body dominating a run.
    #[arg(long = "abduct-census-cap", default_value = "240")]
    abduct_census_cap: usize,

    /// Write the deterministic shadow `Verifier` sources into this directory
    /// and exit. The JVM half of `tools/lifter_differential.py` compiles them,
    /// so the harness feeds a real JVM through exactly the stub `JvmReplay`
    /// uses rather than a second copy of it.
    #[arg(long = "emit-shadow", value_name = "DIR")]
    emit_shadow: Option<PathBuf>,

    /// Step budget for `--interpret`. Separate from `--timeout`: the
    /// interpreter has no solver to yield to, and a differential wants the
    /// same bound on every task rather than a wall-clock one that varies with
    /// machine load.
    #[arg(long = "interpret-steps", default_value = "200000")]
    interpret_steps: u64,

    /// SV-COMP property to check. Defaults to `assert`.
    ///   assert              — valid-assert (assertion violations)
    ///   no-runtime-exception — uncaught RuntimeException
    /// SV-COMP property to check. Defaults to `assert`.
    ///   assert               — valid-assert (assertion violations)
    ///   no-runtime-exception — uncaught RuntimeException
    ///   no-deadlock          — CHECK( init(Main.main()), LTL(G !deadlock) )
    #[arg(long = "property", default_value = "assert")]
    property: String,
}

fn collect_by_ext(root: &Path, ext: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if root.is_file() {
        if root.extension().map(|x| x == ext).unwrap_or(false) {
            out.push(root.to_path_buf());
        }
        return out;
    }
    let Ok(entries) = std::fs::read_dir(root) else {
        return out;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            out.extend(collect_by_ext(&p, ext));
        } else if p.extension().map(|x| x == ext).unwrap_or(false) {
            out.push(p);
        }
    }
    out.sort();
    out
}

fn collect_classes(root: &Path) -> Vec<PathBuf> {
    collect_by_ext(root, "class")
}

/// SV-COMP Java tasks ship as `.java` source -- a task's own directory plus a
/// shared `../common/` (the `Verifier` stub). BenchExec passes every entry of
/// the task YAML's `input_files` as a separate argument, so `inputs` here is
/// the full list, not one path. If any `.java` file turns up among them, they
/// all get compiled together in a single `javac` invocation (so the task's
/// references to `Verifier` resolve) into a scratch directory, and that
/// directory is what actually gets lifted -- the rest of the pipeline never
/// knows source was involved at all.
///
/// Compiling rather than reading source directly matters for more than
/// convenience: a `FALSE` witness gets replayed by running the *compiled*
/// program, so analysing anything other than what javac actually produced
/// would open a gap between what's proven and what's certified. Returning the
/// classpath directory alongside the class files is what keeps that promise
/// -- replay needs to run against the exact same bytecode that was lifted.
/// Returns the classes, the classpath, and — when sources had to be compiled —
/// the scratch directory holding them. The caller must keep that alive for the
/// whole run: dropping it deletes the classpath out from under the analysis.
fn compile_if_needed(
    inputs: &[PathBuf],
) -> Result<
    (
        Vec<PathBuf>,
        String,
        Option<ajave_core::scratch::ScratchDir>,
    ),
    String,
> {
    let java_files: Vec<PathBuf> = inputs
        .iter()
        .flat_map(|p| collect_by_ext(p, "java"))
        .collect();
    if java_files.is_empty() {
        debug!("no .java files found; using pre-compiled .class files directly");
        let classes = inputs.iter().flat_map(|p| collect_classes(p)).collect();
        // No compile step: the classpath is whichever input directories were
        // given (or their parent, for a lone .class file).
        let cp = inputs
            .iter()
            .map(|p| {
                if p.is_dir() {
                    p.display().to_string()
                } else {
                    p.parent()
                        .map(|d| d.display().to_string())
                        .unwrap_or_else(|| ".".into())
                }
            })
            .collect::<Vec<_>>()
            .join(if cfg!(windows) { ";" } else { ":" });
        // Pre-compiled .class inputs: nothing temporary to own.
        return Ok((classes, cp, None));
    }

    // Unique per run and self-deleting. Named after the pid alone, this could
    // be a directory a previous run left behind — and `collect_classes` below
    // takes everything in it, so the verifier would analyse that run's classes
    // alongside these. See ajave_core::scratch (#66).
    let scratch = ajave_core::scratch::ScratchDir::new("ajave-build")
        .map_err(|e| format!("could not create build dir: {e}"))?;
    let out_dir = scratch.path().to_path_buf();
    info!(
        "compiling {} .java file(s) to {}",
        java_files.len(),
        out_dir.display()
    );

    let result = std::process::Command::new("javac")
        .arg("-nowarn")
        .arg("-d")
        .arg(&out_dir)
        .args(&java_files)
        .output()
        .map_err(|e| format!("failed to run javac: {e}"))?;

    if !result.status.success() {
        return Err(format!(
            "javac failed:\n{}",
            String::from_utf8_lossy(&result.stderr)
        ));
    }

    debug!("javac succeeded");
    let classes = collect_classes(&out_dir);
    // The classpath must remain valid for the whole run, so the directory
    // cannot be deleted when this function returns. Ownership goes to the
    // caller, which holds it until the process exits.
    Ok((classes, out_dir.display().to_string(), Some(scratch)))
}

// ---------------------------------------------------------------------------
// Engine portfolio construction
// ---------------------------------------------------------------------------

fn build_engine_portfolio(ascii_only: bool) -> Vec<Box<dyn Engine>> {
    let mut engines: Vec<Box<dyn Engine>> = vec![
        Box::new(ajave_engines::presolve::Presolve::new()),
        // Concurrency runs before the sequential engines.
        //
        // Every other engine analyses a threaded program as if `t.start()` did
        // nothing, so `concrete` reports JoinOrdersWrite's assertion as
        // violated and `smt-bmc` would prove a racy body safe. The blackboard
        // keeps the *first* status per obligation, so whichever engine gets
        // there first decides — the same first-writer-wins issue that voided
        // the float-nonlinear category (see changes.md, 2026-08-28).
        //
        // Running the concurrency engine first makes it authoritative for the
        // programs it can actually analyse, and it costs nothing elsewhere: it
        // refuses a program with no threads immediately.
        Box::new(ajave_engines::concurrency::ConcurrencyEngine::new()),
        Box::new(ajave_engines::concrete::Concrete::new()),
        // Concolic runs straight after concrete: it starts from the same
        // all-zero probe and only differs once a branch needs flipping, so
        // anything concrete can find it finds on its first iteration.
        Box::new(ajave_engines::concolic::Concolic::new()),
    ];
    // NRA before BMC: NRA handles transcendental math (sin, cos, exp, etc.)
    // via cvc5's native support. BMC havoces these calls and produces garbage
    // witnesses, so NRA must claim them first.
    engines.push(Box::new(ajave_engines::nra::NraEngine::new()));
    // Search-based float falsification, after NRA and before AI/BMC.
    //
    // SMT-LIB's FloatingPoint theory has no transcendentals, and this corpus is
    // full of them (173 uses of Math.sin alone), so no encoding can decide
    // those obligations. Java's Math.sin is also only specified to 1 ulp, so
    // there is no unique symbolic answer — concrete execution is the ground
    // truth. This engine searches for inputs and publishes only violations it
    // actually executed.
    engines.push(Box::new(ajave_engines::float_search::FloatSearch::new()));
    // AI before BMC: for float-loop bodies, the AI's widening analysis can
    // prove safety via interval fixpoint. BMC finds spurious violations on
    // bounded unrollings that fail JVM replay; AI discharges first to prevent
    // this. For non-float bodies, AI only publishes hints during init (no
    // discharge), so BMC is unaffected.
    engines.push(Box::new(ajave_engines::ai::AiEngine::new()));
    // Answers questions rather than deciding obligations. Placed before the
    // BMC so a question asked in one round is answered by the time the BMC
    // returns for it — the BMC posts queries, reports `Stalled`, and the
    // orchestrator's round loop brings it back once.
    //
    // This engine could not verify a program if its life depended on it. That
    // is the point: a specialised engine should be a resource the others can
    // use, not an alternative to them.
    // Only when asking is on. An answerer with nobody to answer reports
    // `Stalled` forever, which also stops `all_retired` ever becoming true and
    // keeps the round loop turning for nothing.
    if ajave_engines::smt_bmc::asking_enabled() {
        engines.push(Box::new(ajave_engines::ranges::Ranges::new()));
    }
    if let Some(factory) = ajave_core::smt_smtlib::SmtLibFactory::from_env() {
        // The *floor* under the BMC's path-length bound, which
        // `path_length_bound` raises in proportion to the entry body's size.
        // It began as a diagnostic — iterative deepening deliberately never
        // raises depth, so this was the only way to ask whether `max_depth`
        // was what truncated an exploration — and the answer was that a flat
        // bound caps the size of method traversable at all. See
        // `docs/large-block-encoding.md` and gh #126.
        let bmc_depth: u32 = std::env::var("AJAVE_BMC_DEPTH")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(200);
        let factory2 = ajave_core::smt_smtlib::SmtLibFactory::from_env();
        let mut bmc = ajave_engines::smt_bmc::SmtBmc::new(Box::new(factory), bmc_depth);
        bmc.ascii_only = ascii_only;
        engines.push(Box::new(bmc));
        // A second BMC pass with FloatingPoint arithmetic, after the cheap one.
        //
        // FPA decides float-guarded obligations that the bitvector encoding
        // cannot — `(a+b)+c != a+(b+c)` needs exact rounding — but it makes the
        // formulas hard enough that the solver returns `unknown` where it used
        // to return `unsat`, so running it on everything loses far more proofs
        // than it wins (-62 across the corpus, concentrated in
        // no-runtime-exception, which is overwhelmingly a proving problem).
        //
        // Running it second means it can only affect obligations the cheap pass
        // left open, so the cost is paid where it might help and nowhere else.
        if let Some(f3) = ajave_core::smt_smtlib::SmtLibFactory::from_env() {
            // Bounded per query: this pass is a bonus and must not be able to
            // spend the whole task budget. FPA formulas are the hard ones, so
            // an unbounded solver here starves the run rather than adding to it.
            let f3 = f3.with_query_timeout(5_000);
            let mut fpa = ajave_engines::smt_bmc::SmtBmc::new(Box::new(f3), bmc_depth);
            fpa.ascii_only = ascii_only;
            fpa.fp_arith = true;
            engines.push(Box::new(fpa));
        }
        if let Some(f2) = factory2 {
            // k-induction is a bonus pass: it runs after the BMC and can only
            // decide what the BMC left open, so an unbounded solver is a
            // hazard. Since it stopped requiring `Status::Bounded` it attempts
            // far more obligations, and `argv-tasks/ActiveCheck` went from
            // UNKNOWN to a timeout because it sat in one query past the whole
            // task budget -- the same failure `with_query_timeout` was added
            // for. z3 answers `unknown` at the bound rather than hanging,
            // which is the yield-and-move-on behaviour wanted here.
            engines.push(Box::new(ajave_engines::kinduction::KInduction::new(
                Box::new(f2.with_query_timeout(5_000)),
            )));
        }
    }
    // Synthesis after the BMC and before CHC.
    //
    // After, because its candidate pool is other engines' claims and the BMC's
    // are the richest; before CHC, because an inductive map is the hint a Horn
    // solver most wants and CHC cannot use one it has not been given yet.
    // Off unless AJAVE_HOUDINI=1 — see `houdini_engine::enabled`.
    {
        let h = ajave_engines::houdini_engine::HoudiniEngine::new();
        if h.available() {
            engines.push(Box::new(h));
        }
    }
    // CHC after BMC: BMC handles falsification; CHC proves safety for
    // recursive programs that BMC can't resolve (unbounded recursion).
    {
        let chc = ajave_engines::chc::ChcEngine::new();
        if chc.available() {
            engines.push(Box::new(chc));
        }
    }
    {
        let imc = ajave_engines::imc::ImcEngine::new();
        if imc.available() {
            engines.push(Box::new(imc));
        }
    }
    {
        let cegar = ajave_engines::cegar::CegarEngine::new();
        if cegar.available() {
            engines.push(Box::new(cegar));
        }
    }

    // `AJAVE_DISABLE=chc,imc` removes engines by id.
    //
    // For the ablation differential (`tools/engine_ablation.py`): dropping an
    // engine may lose answers, but it must never turn a TRUE into a FALSE or
    // the reverse. Two engines disagreeing about the same obligation means one
    // of them is wrong, and the portfolio can check that against itself without
    // any expected-verdict label -- which is a stronger oracle than the corpus,
    // and the one thing that looks *between* engines rather than inside one.
    if let Ok(list) = std::env::var("AJAVE_DISABLE") {
        let disabled: Vec<String> = list
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();
        if !disabled.is_empty() {
            let present: Vec<String> = engines.iter().map(|e| e.id().0.to_string()).collect();
            engines.retain(|e| {
                let keep = !disabled.iter().any(|d| d == e.id().0);
                if !keep {
                    info!("engine {} disabled by AJAVE_DISABLE", e.id().0);
                }
                keep
            });
            // A name that matched nothing used to be silently ignored, which
            // turns a mis-typed ablation into a full-portfolio run that reads
            // as "this engine was not needed". Three ablations in one session
            // were wrong this way: `smt-bmc`, `kinduction` and `ai` against a
            // portfolio that spells them `smt-bmc-fpa`, `k-induction` and
            // `interval-ai`.
            //
            // A warning, not a refusal, because an absent name is legitimate:
            // `imc` is not constructed at all without `AJAVE_SMTINTERPOL_JAR`,
            // so `engine_ablation.py` would die on a clean checkout. Stderr
            // rather than `info!`, so it is visible without `-v` -- the whole
            // failure was that nothing said anything.
            let unmatched: Vec<&String> =
                disabled.iter().filter(|d| !present.contains(d)).collect();
            if !unmatched.is_empty() {
                eprintln!(
                    "WARNING: AJAVE_DISABLE named {} engine(s) that are not in this \
                     portfolio and disabled nothing: {}",
                    unmatched.len(),
                    unmatched
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                eprintln!("         ids present in this run: {}", present.join(", "));
            }
        }
    }
    engines
}

// ---------------------------------------------------------------------------
// Violation confirmation via JVM replay
// ---------------------------------------------------------------------------

struct ViolationInfo {
    obligation_ref: ajave_core::artifact::ObligationRef,
    witness: ajave_ir::verdict::Witness,
    tagged: ajave_core::artifact::Tagged,
}

/// One `PROGRAM_SHAPE` line per run, summarising the entry body and the whole
/// reachable program. Paired with the orchestrator's existing
/// `timing step <engine> <ms>ms discharged=N violated=M` lines, this is enough
/// to answer "what does each engine cost, and pay, on programs like this one".
/// Ask what shape of fact each obligation needs, and print one row per
/// obligation.
///
/// # Why a census instead of another domain
///
/// On 2026-11-22 four capability directions were estimated and three measured
/// exactly zero: a raised loop-unroll cap converted 0 of 69 tasks, suppressing
/// refuted witnesses converted 0 of 79, forced FPA converted 1 of 8. The cause
/// generalises — every bucket in `tools/blocker_census.py` is named after what
/// *blocks* a verdict, so removing the blocker leaves whatever the obligation
/// actually needs still missing. `InsertionSort-FunSat01 [valid-assert]` is the
/// clean case: suppress its refuted witness, the obligation goes `Open`, and
/// nothing discharges it, because the assertion needs **sortedness**.
///
/// So this asks the corpus rather than guessing at it. The query is the
/// obligation's own error formula from `interpolation::encode_body_lia` — the
/// same encoding `imc`, `cegar` and `invariant_check` consume, so the census
/// measures the production encoding and not a second one written for it.
///
/// # What a row means, and what it does not
///
/// A row says *a fact of this shape is sufficient*. It does not say the fact is
/// true of the program, nor inductive, nor safe to publish: every abduct here
/// is stated over mathematical integers, and on a JVM `0 <= sum` is false the
/// moment the addition wraps. Turning one into a proof needs initiation and the
/// overflow-guarded preservation query of `docs/proposals/lia-faithfulness.md`
/// §3. This mode publishes nothing and asserts nothing.
fn run_abduct_census(prog: &Program, cap: usize) {
    use ajave_engines::abduct;
    use ajave_engines::interpolation::encode_body_lia;

    // Read the symbol names out of the declarations the encoder emitted rather
    // than rebuilding them from the naming convention. The convention is
    // deliberately inconsistent -- `ghost_len` is unprefixed where `arr0_1` is
    // prefixed, and `interpolation.rs` explains at length why -- so a second
    // copy of it here would be exactly the producer/consumer disagreement that
    // `Bounded { k }` cost us once already.
    fn declared(decls: &str, sort: &str) -> Vec<String> {
        let mut out = Vec::new();
        for line in decls.lines() {
            let l = line.trim();
            let Some(rest) = l.strip_prefix("(declare-fun ") else {
                continue;
            };
            let Some((name, tail)) = rest.split_once(' ') else {
                continue;
            };
            // Strip exactly one closing paren -- the one that closes
            // `declare-fun` -- not every trailing paren.
            //
            // `trim_end_matches(')')` was the first version and it is greedy,
            // so `() (Array Int Int))` reduced to `() (Array Int Int` and no
            // array sort ever matched. Every body therefore reported zero
            // arrays, the quantified grammar was never built, and the census
            // was on course to conclude that array facts are not what the
            // corpus needs -- from a run in which it had not once asked.
            let Some(ty) = tail.trim_end().strip_suffix(')') else {
                continue;
            };
            if ty.trim() == format!("() {sort}") {
                out.push(name.to_string());
            }
        }
        out
    }

    println!(
        "# abduct-census\tbudget_ms={}\tcap={cap}",
        std::env::var("AJAVE_ABDUCT_BUDGET_MS").unwrap_or_else(|_| "5000".into())
    );
    println!("method\toid\tkind\tshape\tms\tfact");

    let mut keys: Vec<_> = prog.bodies.keys().cloned().collect();
    keys.sort();
    let mut tally: std::collections::BTreeMap<&'static str, usize> = Default::default();

    for k in keys {
        let body = &prog.bodies[&k];
        if body.obligations.is_empty() {
            continue;
        }
        for ob in &body.obligations {
            let enc = encode_body_lia(body, &[ob.id], "");
            let errors: Vec<String> = enc
                .error_formulas
                .iter()
                .filter(|(id, _)| *id == ob.id)
                .map(|(_, f)| f.clone())
                .collect();
            if errors.is_empty() {
                continue;
            }
            // An obligation checked in several blocks has one clause per block,
            // and the obligation holds only if *none* of them is reachable --
            // `imc` disjoins them for the same reason. Taking the first would
            // ask about one path and report the answer as if it covered all.
            let error = if errors.len() == 1 {
                errors[0].clone()
            } else {
                format!("(or {})", errors.join(" "))
            };

            // Pre-state symbols only. The post-state copies (`v3p`,
            // `ghost_lenp`) exist so a transition relation can talk about the
            // successor; an invariant is a fact about *a* state, and offering
            // the primed copies as vocabulary would let the census report a
            // fact no invariant domain could ever express.
            let prestate = |v: Vec<String>| -> Vec<String> {
                v.into_iter().filter(|n| !n.ends_with('p')).collect()
            };
            let all_vars = prestate(declared(&enc.declarations, "Int"));
            let all_arrays: Vec<String> = prestate(declared(&enc.declarations, "(Array Int Int)"))
                .into_iter()
                // `ghost_len` holds lengths indexed by reference, not contents
                // indexed by position, so an element template over it would be
                // a category error.
                .filter(|n| n != "ghost_len")
                .collect();

            // Narrow the vocabulary to the symbols the obligation itself
            // mentions.
            //
            // The first census run offered every variable in the body, and the
            // widest method here carries 43 of them. A pairwise scalar grammar
            // over 43 variables is ~2600 productions, enumerative SyGuS does
            // not finish it inside any sane budget, and the census then reports
            // "no scalar fact suffices" for obligations a two-variable relation
            // would have discharged. A vocabulary that cannot be searched is
            // indistinguishable from a vocabulary that does not contain the
            // answer, which is the same failure as a gate that disables
            // nothing: the output is identical to the informative one.
            // Two different scopes, and the asymmetry is forced by the
            // encoding.
            //
            // **Integers come from the error formula alone.** A block clause
            // relates the whole state pre to post, giving every unchanged
            // variable its own `vip = vi` conjunct, so *every* variable in the
            // body appears in it. Narrowing the integer vocabulary on the
            // clause is therefore a no-op dressed as a filter: it returned all
            // 44 variables plus 44 length terms, 88 operands, ~7700 pairwise
            // productions, and a grammar that size is not searched inside any
            // budget. A vocabulary that cannot be searched is indistinguishable
            // from one that lacks the answer.
            //
            // **Arrays come from the clause as well.** An array is read where
            // the program reads it, which for a guarded assertion is the
            // predecessor's branch, not the error formula. There are few arrays
            // per body, so including the clause costs nothing here.
            let edges_here = incoming_edges(&enc, body, ob.id);
            let toks = |t: &str| -> std::collections::BTreeSet<String> {
                t.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                    .filter(|x| !x.is_empty())
                    .map(|x| x.to_string())
                    .collect()
            };
            let mentioned = toks(&error);
            let mut wide = mentioned.clone();
            for e in &edges_here {
                wide.extend(toks(&e.clause));
                for g in &e.ghost {
                    wide.extend(toks(g));
                }
            }
            let pick = |all: &[String], from: &std::collections::BTreeSet<String>| -> Vec<String> {
                all.iter().filter(|n| from.contains(*n)).cloned().collect()
            };

            // Integer *terms*, not variable names. An array length is
            // `(select ghost_len r)` in this encoding, so `i < a.length` --
            // the most common missing fact in an array-bounds obligation --
            // is not a relation between two variables and a name-only
            // vocabulary cannot state it.
            let mut terms = pick(&all_vars, &mentioned);
            if terms.len() < 2 {
                // Too narrow to state a relation. Widen to the clause's
                // variables, but capped: a partial vocabulary that is searched
                // beats a complete one that is not.
                terms = pick(&all_vars, &wide).into_iter().take(10).collect();
            }
            let refs: Vec<String> = terms.clone();
            for r in &refs {
                terms.push(format!("(select ghost_len {r})"));
            }
            let arrays = pick(&all_arrays, &wide);

            // `(set-logic ALL)` after the options and before the
            // declarations. Without it cvc5 writes four lines of advice to
            // stdout per query, which lands in the middle of the TSV this mode
            // exists to produce.
            let prelude = format!("(set-logic ALL)\n{}", enc.edge_preamble());

            // The post-state symbols, so an abduct that constrains the
            // successor can be told apart from one that states an invariant.
            // Without this screen the first census run reported 95% of rows as
            // "a fact exists outside the offered vocabulary", when what
            // existed was `v2p = 2147483648`.
            let poststate: Vec<String> = declared(&enc.declarations, "Int")
                .into_iter()
                .chain(declared(&enc.declarations, "(Array Int Int)"))
                .filter(|n| n.ends_with('p'))
                .collect();

            if std::env::var("AJAVE_ABDUCT_DEBUG").as_deref() == Ok("1") {
                eprintln!(
                    "abduct-census {}.{} oid={} error={}\n  terms={:?}\n  arrays={:?}",
                    k.class, k.name, ob.id.0, error, terms, arrays
                );
            }

            let vocab = abduct::Vocab {
                terms: &terms,
                arrays: &arrays,
                poststate: &poststate,
                cap,
            };
            let t0 = std::time::Instant::now();
            let v = classify_over_edges(&prelude, &error, &enc, &edges_here, &vocab);
            let ms = t0.elapsed().as_millis();
            match v {
                Ok(v) => {
                    *tally.entry(v.shape.tag()).or_default() += 1;
                    println!(
                        "{}.{}\t{}\t{:?}\t{}\t{ms}\t{}",
                        k.class,
                        k.name,
                        ob.id.0,
                        ob.kind,
                        v.shape.tag(),
                        v.fact.as_deref().unwrap_or("-")
                    );
                }
                Err(e) => {
                    *tally.entry("error").or_default() += 1;
                    println!(
                        "{}.{}\t{}\t{:?}\terror\t{ms}\t{}",
                        k.class,
                        k.name,
                        ob.id.0,
                        ob.kind,
                        e.replace('\n', " ")
                    );
                }
            }
        }
    }

    let total: usize = tally.values().sum();
    println!("# totals over {total} obligation(s)");
    for (tag, n) in &tally {
        let pct = if total > 0 {
            100.0 * *n as f64 / total as f64
        } else {
            0.0
        };
        println!("# {tag}\t{n}\t{pct:.1}%");
    }
}

/// Ask the census question across every edge into the obligation's block.
///
/// # Why not at the block the check is in
///
/// That was the first formulation and it is malformed for most of the corpus.
/// A Java `assert` compiles to a guarded jump into a failure block, so the
/// obligation's error clause in that block is `(= 0 0)` — unconditional, and
/// correctly so: once control is there the property has already failed, and
/// safety means the block is **unreachable**. Abduction requires the
/// hypothesis to be *consistent* with the premises, and the only ψ entailing
/// `¬true` is `false`, so cvc5 answers nothing. The census would then have
/// reported "no fact of any shape discharges this" for every assertion in the
/// corpus — a confident, wrong, and entirely self-consistent result.
///
/// It was caught only because `InsertionSort-FunSat01` is a case whose needed
/// fact is known independently (sortedness), which is the argument for keeping
/// a known-answer control in any census.
///
/// # The shape asked instead
///
/// For each edge `A → B` where `B` holds the check, find ψ over `A`'s state
/// with
///
/// ```text
/// ψ  ⊨  ¬( clause_{A→B}  ∧  ghost  ∧  error′ )
/// ```
///
/// which is exactly `interpolation::preservation_query` with the pre-state
/// assertion left unknown — abduction over the preservation query. The error
/// is primed because `B`'s entry state *is* the edge's post-state.
///
/// The overflow disjunct is included, matching `preservation_query`: a fact
/// sufficient only when the arithmetic does not wrap is not sufficient on a
/// JVM, and a census that quietly asked the easier question would overstate
/// every domain it measures.
///
/// # Aggregating across edges
///
/// Every incoming edge must be excluded, so the obligation needs the *hardest*
/// thing any edge needs — `max` over `Shape`, whose variant order is written
/// worst-last for this. Reporting the easiest edge would be the same
/// overstatement in a different place.
/// The edges whose target holds the obligation's check.
///
/// Shared by the vocabulary narrowing and the classifier so the two cannot
/// disagree about which edges the census is asking about — the producer and
/// consumer fault `Bounded { k }` cost us once already.
fn incoming_edges<'a>(
    enc: &'a ajave_engines::interpolation::LiaEncoding,
    body: &ajave_ir::Body,
    oid: ajave_ir::ObligationId,
) -> Vec<&'a ajave_engines::interpolation::EdgeClause> {
    let check_blocks: Vec<ajave_ir::BlockId> = body
        .blocks
        .iter()
        .filter(|b| {
            b.stmts
                .iter()
                .any(|st| matches!(st, ajave_ir::Stmt::Check(o) if *o == oid))
        })
        .map(|b| b.id)
        .collect();

    // Walk back through edges that carry no guard.
    //
    // A Java `assert` compiles to a guarded jump into a failure block, so the
    // edge *into* the check block is pure frame -- measured on
    // `InsertionSort-FunSat01` as
    // `(and (= arr5_2p arr5_2) (= ghost_lenp ghost_len) (= v0p v0) …)`. No
    // pre-state fact entails the negation of a frame, because a frame is
    // satisfiable from every pre-state, so asking there is vacuous and the
    // only abducts on offer are post-state contradictions. The guard that
    // decides the obligation sits further back, and that is the edge worth
    // asking about.
    //
    // Depth-bounded, and the bound is a real limit on the instrument rather
    // than a tuning constant: a guard more than this many unguarded edges
    // behind the check is simply not found, and the obligation is reported on
    // whatever edge the walk ended at. Breadth-first so the *nearest* guard
    // is the one used.
    const MAX_WALK: usize = 8;
    let mut frontier: Vec<ajave_ir::BlockId> = check_blocks;
    let mut seen: std::collections::BTreeSet<u32> = frontier.iter().map(|b| b.0).collect();
    let mut out: Vec<&ajave_engines::interpolation::EdgeClause> = Vec::new();

    for _ in 0..MAX_WALK {
        if frontier.is_empty() {
            break;
        }
        let mut next: Vec<ajave_ir::BlockId> = Vec::new();
        let mut progressed = false;
        for e in enc
            .edge_clauses
            .iter()
            .filter(|e| e.to.map(|t| frontier.contains(&t)).unwrap_or(false))
        {
            if ajave_engines::abduct::is_frame_only(&e.clause) && e.overflow.is_none() {
                // Nothing to contradict here; keep walking. An edge with an
                // overflow condition is *not* skipped even if its clause is a
                // frame: the overflow disjunct is a real constraint a fact can
                // be required to exclude.
                if seen.insert(e.from.0) {
                    next.push(e.from);
                    progressed = true;
                }
            } else {
                out.push(e);
            }
        }
        if !out.is_empty() || !progressed {
            break;
        }
        frontier = next;
    }
    out
}

fn classify_over_edges(
    prelude: &str,
    error: &str,
    enc: &ajave_engines::interpolation::LiaEncoding,
    incoming: &[&ajave_engines::interpolation::EdgeClause],
    vocab: &ajave_engines::abduct::Vocab<'_>,
) -> Result<ajave_engines::abduct::Verdict, String> {
    use ajave_engines::abduct;

    // Prime only the symbols that *have* a post-state copy.
    //
    // Not "every unprimed symbol": the `Encoder` mints per-block fresh binders
    // like `e8_f0` for intermediate values, and those are existential within
    // one clause with no successor copy. Priming them produced
    // `Symbol 'e8_f0p' not declared as a variable` on every `ArrayBounds`
    // obligation in the body — 8 of 42 rows, and loudly rather than silently
    // only because `abduce_with_grammar` was made to return `Err` on solver
    // errors rather than an empty answer.
    let declared_names: std::collections::BTreeSet<String> = enc
        .declarations
        .lines()
        .filter_map(|l| {
            l.trim()
                .strip_prefix("(declare-fun ")
                .and_then(|r| r.split_once(' '))
                .map(|(n, _)| n.to_string())
        })
        .collect();
    let has_post: Vec<String> = declared_names
        .iter()
        .filter(|n| !n.ends_with('p') && declared_names.contains(&format!("{n}p")))
        .cloned()
        .collect();
    let error_post = abduct::prime_formula(error, &has_post);

    if incoming.is_empty() {
        // The check sits in the entry block, so there is no edge to exclude and
        // the question is the block-local one after all: what fact about the
        // entry state rules the violation out?
        return abduct::classify(prelude, &[], &format!("(not {error})"), vocab);
    }

    let mut worst: Option<abduct::Verdict> = None;
    for e in incoming {
        let mut conj: Vec<String> = Vec::new();
        match &e.overflow {
            Some(ovf) => conj.push(format!("(or {} {ovf})", e.clause)),
            None => conj.push(e.clause.clone()),
        }
        conj.extend(e.ghost.iter().cloned());
        conj.push(error_post.clone());
        let goal = format!("(not (and {}))", conj.join(" "));
        match std::env::var("AJAVE_ABDUCT_DEBUG").as_deref() {
            Ok("1") => eprintln!("  edge {:?} -> {:?}  goal_len={}", e.from, e.to, goal.len()),
            Ok("2") => eprintln!("  edge {:?} -> {:?}  clause={}", e.from, e.to, e.clause),
            _ => {}
        }
        let v = abduct::classify(prelude, &[], &goal, vocab)?;
        let keep = match &worst {
            None => true,
            Some(w) => v.shape > w.shape,
        };
        if keep {
            worst = Some(v);
        }
    }
    Ok(worst.unwrap_or(abduct::Verdict {
        shape: abduct::Shape::Nothing,
        fact: None,
    }))
}

fn emit_program_shape(prog: &ajave_ir::Program, plan: &ajave_core::plan::Plan) {
    use ajave_engines::body_shape;
    let Some(entry) = &prog.entry else { return };
    let Some(entry_body) = prog.body(entry) else {
        return;
    };
    let entry_shape = body_shape::analyze(entry_body);

    // Whole-program rollup: an engine's cost is driven by everything it may be
    // asked to inline, not only by the entry body's own shape.
    let reachable = prog.reachable_from_entry();
    let mut blocks = 0usize;
    let mut any_loops = false;
    let mut any_float = false;
    let mut any_heap = false;
    let mut any_string = false;
    let mut any_transcendental = false;
    for key in &reachable {
        let Some(b) = prog.body(key) else { continue };
        let s = body_shape::analyze(b);
        blocks += s.num_blocks;
        any_loops |= s.has_loops;
        any_float |= s.has_float_types;
        any_heap |= s.has_heap_ops;
        any_string |= s.has_string_ops;
        any_transcendental |= s.has_transcendental_math;
    }

    info!(
        "PROGRAM_SHAPE property={:?} methods={} blocks={} entry_blocks={} entry_vars={} \
         loops={} float={} heap={} string={} transcendental={} nonlinear_int={}",
        plan.property,
        reachable.len(),
        blocks,
        entry_shape.num_blocks,
        entry_shape.num_vars,
        any_loops,
        any_float,
        any_heap,
        any_string,
        any_transcendental,
        entry_shape.has_nonlinear_int,
    );
}

fn collect_violations(orchestrator: &Orchestrator) -> Vec<ViolationInfo> {
    orchestrator
        .bb
        .statuses()
        .filter_map(|(obligation_ref, status)| match status {
            ajave_core::artifact::Status::Violated { by, witness } => Some(ViolationInfo {
                obligation_ref: obligation_ref.clone(),
                witness: witness.clone(),
                tagged: ajave_core::artifact::Tagged {
                    seq: 0,
                    producer: *by,
                    direction: ajave_core::artifact::Direction::Under,
                    approximated: orchestrator.bb.status_approximations(obligation_ref),
                    artifact: ajave_core::artifact::Artifact::Status(
                        obligation_ref.clone(),
                        ajave_core::artifact::Status::Violated {
                            by: *by,
                            witness: witness.clone(),
                        },
                    ),
                },
            }),
            _ => None,
        })
        .collect()
}

fn confirm_violations(
    violations: &[ViolationInfo],
    classpath: &str,
    program: &Program,
    trace: bool,
    contested: &[(ajave_core::artifact::ObligationRef, &'static str)],
) -> Option<(ajave_core::artifact::ObligationRef, verdict::Witness)> {
    let replay = ajave_core::certify::JvmReplay::new(classpath.to_string());
    let mut any_confirmed = false;
    let mut confirmed = None;

    for violation in violations {
        // A witness carrying a schedule cannot go to JvmReplay, which has no
        // way to force an interleaving. Route it to the interpreter-based
        // schedule replay instead, and say plainly which certifier ran — the
        // two are not equally strong evidence.
        if violation.witness.needs_schedule() {
            let entries =
                ajave_engines::concurrency::check_preconditions(program).unwrap_or_default();
            let ok = ajave_engines::concurrency::replay_schedule(
                program,
                &entries,
                &violation.obligation_ref,
                &violation.witness.schedule,
                &violation.witness.choices,
                Default::default(),
            );
            if trace || ok {
                eprintln!(
                    "schedule-replay: {} {} (interpreter, not a real JVM)",
                    if ok {
                        "confirmed"
                    } else {
                        "could not reproduce"
                    },
                    violation.obligation_ref
                );
            }
            if ok {
                any_confirmed = true;
                if confirmed.is_none() {
                    confirmed = Some((violation.obligation_ref.clone(), violation.witness.clone()));
                }
            }
            continue;
        }
        match ajave_core::certify::Certifier::certify(&replay, &violation.tagged, program) {
            ajave_core::certify::CertResult::Confirmed => {
                any_confirmed = true;
                // A violation the JVM reproduced, on an obligation some Over
                // engine proved safe, means two engines disagree about a fact
                // of this program and one of them is wrong. Before replay the
                // pair is legitimate -- a witness is a candidate, which is what
                // `proved_safe` exists to record -- so this is the first point
                // at which it is a contradiction rather than a race.
                //
                // Always reported, never silent: it needs no expected-verdict
                // label, so it holds on programs no benchmark covers.
                if contested
                    .iter()
                    .any(|(o, _)| o == &violation.obligation_ref)
                {
                    eprintln!(
                        "CONTRADICTION: {} was proved safe by an over-approximating \
                         engine and violated by a witness that reproduced on a real \
                         JVM. One of those engines is unsound.",
                        violation.obligation_ref
                    );
                }
                if confirmed.is_none() {
                    confirmed = Some((violation.obligation_ref.clone(), violation.witness.clone()));
                }
                if trace {
                    eprintln!("jvm-replay: confirmed {}", violation.obligation_ref);
                }
            }
            other => {
                if trace {
                    eprintln!("jvm-replay: {other:?} for {}", violation.obligation_ref);
                }
            }
        }
    }

    if !any_confirmed && !violations.is_empty() {
        eprintln!("downgrading FALSE to UNKNOWN: witness did not replay on a real JVM");
    }

    confirmed
}

// ---------------------------------------------------------------------------
// Witness emission
// ---------------------------------------------------------------------------

fn emit_witness_file(
    witness_path: &Path,
    obligation_ref: &ajave_core::artifact::ObligationRef,
    witness: &verdict::Witness,
    program: &Program,
    inputs: &[PathBuf],
) {
    let body = program.body(&obligation_ref.method);
    let obligation = body.map(|b| b.obligation(obligation_ref.id));
    let input_files: Vec<String> = inputs.iter().map(|p| p.display().to_string()).collect();
    let kind = obligation
        .map(|o| o.kind)
        .unwrap_or(ajave_ir::ObligationKind::Assertion);
    let spec = match kind {
        ajave_ir::ObligationKind::Assertion => "CHECK( init(Main.main()), LTL(G assert) )",
        _ => "CHECK(init(Main.main()), LTL(G ! uncaught(java.lang.RuntimeException)))",
    };
    let yaml = ajave_core::witness::emit_violation_yaml(
        witness,
        &ajave_core::witness::TaskInfo {
            input_files: &input_files,
            specification: spec,
        },
        &ajave_core::witness::ViolationInfo {
            kind,
            line: obligation.and_then(|o| o.line),
        },
    );
    match std::fs::write(witness_path, &yaml) {
        Ok(()) => info!("witness written to {}", witness_path.display()),
        Err(e) => warn!("failed to write witness: {e}"),
    }
}

fn print_witness(
    obligation_ref: &ajave_core::artifact::ObligationRef,
    witness: &verdict::Witness,
    program: &Program,
) {
    let body = program.body(&obligation_ref.method);
    let obligation = body.map(|b| b.obligation(obligation_ref.id));
    eprintln!(
        "--- witness for {}#{} ---",
        obligation_ref.method, obligation_ref.id.0
    );
    if let Some(obligation) = obligation {
        eprintln!(
            "  obligation: {:?}{}",
            obligation.kind,
            obligation
                .line
                .map(|l| format!(" (line {})", l))
                .unwrap_or_default()
        );
    }
    for (i, entry) in witness.entries.iter().enumerate() {
        eprintln!(
            "  {}(): {} = {}",
            entry.nondet_method,
            i,
            format_nondet_value(&entry.value)
        );
    }
    eprintln!("---");
}

fn print_unconfirmed_witness(witness: &verdict::Witness) {
    eprintln!("--- witness found but not confirmed by JVM replay ---");
    for (i, entry) in witness.entries.iter().enumerate() {
        eprintln!(
            "  {}(): {} = {}",
            entry.nondet_method,
            i,
            format_nondet_value(&entry.value)
        );
    }
    eprintln!("---");
}

fn format_nondet_value(value: &verdict::NondetValue) -> String {
    match value {
        verdict::NondetValue::Int(v) => format!("{v}"),
        verdict::NondetValue::Long(v) => format!("{v}L"),
        verdict::NondetValue::Bool(v) => format!("{v}"),
        verdict::NondetValue::Str(s) => format!("{s:?}"),
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

/// Whether the internal contract assertions are compiled into this binary.
///
/// `cfg!(debug_assertions)` is evaluated in *this* crate, and the flag is set
/// per profile rather than per crate, so it answers for the whole build.
fn contract_checks_on() -> bool {
    cfg!(debug_assertions)
}

/// Report-time certification of invariant-backed TRUE claims.
///
/// The TRUE half of the rule `certify.rs` states: "no artifact reaches the
/// reporter on an engine's authority alone." FALSE is replayed on a real JVM
/// just above; this re-checks the invariants a proof rests on.
///
/// Returns the obligations whose certificate did **not** confirm. A non-empty
/// result means TRUE must not be reported: the engine claimed an invariant
/// justifies the check and an independent pass could not agree.
///
/// Runs at report time rather than at publish time because the blackboard is
/// append-only — rejecting a discharge when its invariant is still a
/// `Candidate` would make promotion unreachable. This is also where
/// `JvmReplay` runs, for the same reason.
fn uncertified_invariant_proofs(
    bb: &ajave_core::blackboard::Blackboard,
    prog: &Program,
) -> Vec<ajave_core::artifact::ObligationRef> {
    let Some(solver) = which_solver() else {
        // No solver, so nothing can be certified. Every invariant-backed
        // proof is therefore unconfirmed, which is the conservative answer.
        warn!("certify-true: no solver available; no invariant proof can be checked");
        return bb
            .discharged_by_invariant()
            .into_iter()
            .map(|(o, _)| o)
            .collect();
    };
    let mut bad = Vec::new();
    for (oref, inv_id) in bb.discharged_by_invariant() {
        let Some(inv) = bb.invariant(inv_id) else {
            warn!("certify-true: {oref} names invariant {inv_id}, which does not exist");
            bad.push(oref);
            continue;
        };
        let Some(body) = prog.body(&oref.method) else {
            bad.push(oref);
            continue;
        };
        let r = ajave_engines::invariant_check::check_inductive(body, inv, oref.id, &solver);
        match r {
            ajave_core::certify::CertResult::Confirmed => {
                debug!("certify-true: {oref} confirmed by invariant {inv_id}");
            }
            other => {
                info!("certify-true: {oref} NOT confirmed ({other:?})");
                bad.push(oref);
            }
        }
    }
    bad
}

/// The SMT binary the certifier should use, honouring the same override the
/// engines do.
fn which_solver() -> Option<String> {
    let bin = std::env::var("AJAVE_SMT_SOLVER")
        .or_else(|_| std::env::var("ROAST_SMT_SOLVER"))
        .unwrap_or_else(|_| "z3".to_string());
    match std::process::Command::new(&bin).arg("--version").output() {
        Ok(o) if o.status.success() => Some(bin),
        _ => None,
    }
}

fn main() {
    let cli = Cli::parse();

    // Before anything else: this must work without inputs, and must not depend
    // on logging being initialised.
    if cli.build_info {
        println!(
            "ajave {}\ncontract_checks={}",
            env!("CARGO_PKG_VERSION"),
            if contract_checks_on() { "on" } else { "off" }
        );
        std::process::exit(0);
    }

    // Initialise logging. RUST_LOG takes absolute precedence (power-user override);
    // otherwise --verbose/-v controls the level (default: WARN, keeping stderr
    // clean during normal BenchExec runs).
    let default_level = match cli.verbose {
        0 => log::LevelFilter::Warn,
        1 => log::LevelFilter::Info,
        2 => log::LevelFilter::Debug,
        _ => log::LevelFilter::Trace,
    };
    let mut log_builder = env_logger::Builder::from_default_env();
    if std::env::var("RUST_LOG").is_err() {
        log_builder.filter_level(default_level);
    }
    log_builder.init();

    // Before anything is loaded: this mode consumes no program.
    if let Some(dir) = &cli.emit_shadow {
        for (rel, src) in ajave_core::certify::JvmReplay::shadow_sources() {
            let path = dir.join(rel);
            if let Some(parent) = path.parent() {
                if let Err(e) = std::fs::create_dir_all(parent) {
                    eprintln!("--emit-shadow: {}: {e}", parent.display());
                    std::process::exit(2);
                }
            }
            if let Err(e) = std::fs::write(&path, src) {
                eprintln!("--emit-shadow: {}: {e}", path.display());
                std::process::exit(2);
            }
            println!("{}", path.display());
        }
        return;
    }

    info!(
        "ajave starting, inputs={:?}, contract_checks={}",
        cli.inputs,
        if contract_checks_on() { "on" } else { "off" }
    );

    // `_scratch` must stay bound for the rest of main: it owns the compiled
    // classes, and dropping it early would delete the classpath mid-run.
    let (class_files, classpath, _scratch) = match compile_if_needed(&cli.inputs) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("{e}");
            println!("UNKNOWN");
            std::process::exit(0);
        }
    };
    if class_files.is_empty() {
        eprintln!("no .java or .class input found in: {:?}", cli.inputs);
        println!("UNKNOWN");
        std::process::exit(0);
    }

    // Load and lift class files.
    info!("loading {} class file(s)", class_files.len());
    let mut prog = Program::default();
    let mut load_errors = Vec::new();

    for path in &class_files {
        debug!("loading {}", path.display());
        match std::fs::read(path)
            .map_err(|e| e.to_string())
            .and_then(|b| ClassFile::parse(&b).map_err(|e| format!("{}: {e}", path.display())))
        {
            Ok(cf) => lift::lift_class(&cf, &mut prog),
            Err(e) => load_errors.push(e),
        }
    }

    prog.entry = prog
        .bodies
        .keys()
        .filter(|k| k.name == "main" && k.desc == "([Ljava/lang/String;)V")
        .min_by_key(|k| {
            // Prefer the "Main" class (SV-COMP convention), then shorter
            // class names (less likely to be a nested/test class).
            if k.class == "Main" {
                0
            } else {
                1 + k.class.len()
            }
        })
        .cloned();

    for e in &load_errors {
        warn!("{e}");
        eprintln!("warning: {e}");
    }

    // Reduce the IR before any engine sees it.
    //
    // Deliberately here rather than in an engine: the lifter materialises the
    // JVM operand stack into temporaries, so 35-47% of assignments are bare
    // copies and the widest corpus method carries 112 variables. Each is an
    // argument of every CHC block predicate and an entry in every BMC state,
    // and doing this per-engine is how the same work -- and the same bug --
    // gets written seven times.
    //
    // `Level::Normalise` only rewrites reads and is always on.
    // `Level::Optimise` removes statements and variables and is behind
    // `AJAVE_IR_OPT`, off until the configuration differential is clean on
    // both properties.
    {
        let level = ajave_opt::level_from_env();
        let stats = ajave_opt::reduce(&mut prog, level);
        info!(
            "ir-opt ({:?}): {} copies propagated, {} assignments and {} vars removed \
             across {} bodies",
            level,
            stats.copies_propagated,
            stats.assignments_removed,
            stats.vars_removed,
            stats.bodies
        );
    }

    if cli.ir {
        let mut keys: Vec<_> = prog.bodies.keys().cloned().collect();
        keys.sort();
        for k in keys {
            print!("{}", prog.bodies[&k].render());
        }
        println!();
    }

    // Abduction census, off the verification path entirely.
    //
    // Here, after lifting and IR reduction, for the reason given on
    // `--interpret`: a measurement is only evidence about the production
    // pipeline if it runs on the IR the production pipeline builds.
    if cli.abduct_census {
        run_abduct_census(&prog, cli.abduct_census_cap);
        return;
    }

    // Interpreter mode, off the verification path entirely.
    //
    // Placed after lifting and IR reduction so it runs on exactly the IR the
    // engines see — a differential against a real JVM is only evidence about
    // the production pipeline if it uses the production pipeline.
    if let Some(seq) = &cli.interpret {
        let choices: Vec<i64> = seq
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(|s| s.parse::<i64>())
            .collect::<Result<_, _>>()
            .unwrap_or_else(|e| {
                eprintln!("--interpret: could not parse the nondet sequence: {e}");
                std::process::exit(2);
            });
        let Some(entry) = prog.entry.clone() else {
            println!("INTERPRET NO-ENTRY");
            return;
        };
        let Some(body) = prog.body(&entry) else {
            println!("INTERPRET NO-ENTRY");
            return;
        };
        let outcome =
            ajave_engines::concrete::interpret(&prog, body, &choices, cli.interpret_steps);
        // No verdict line. BenchExec reads the last line of stdout, and a mode
        // that prints TRUE/FALSE/UNKNOWN from an under-approximating single
        // run would be a wrong answer waiting for a stray flag.
        println!("INTERPRET {outcome}");
        return;
    }

    let obligations = prog.obligations();
    info!(
        "loaded {} bodies, {} obligations",
        prog.bodies.len(),
        obligations.len()
    );

    // Run the engine portfolio.
    // The no-deadlock property is answered directly by the concurrency engine
    // rather than through the obligation system.
    //
    // Every other property is a condition at a program point, which is what an
    // `Obligation` is. A deadlock is a property of the *execution* — no thread
    // can proceed and not all have terminated — so there is no statement to
    // attach it to. Forcing it into the obligation model would mean seeding a
    // synthetic obligation against the entry method that no engine but this one
    // could ever discharge, which buys nothing and obscures what is being
    // claimed.
    // Parse the property once, here, rather than comparing the raw string at
    // each use. Two separate string comparisons decided behaviour below, and a
    // third place inferring the property differently is exactly how the corpus
    // tests came to check one property while asserting another (#54).
    let plan = ajave_core::plan::Property::parse(&cli.property)
        .map(ajave_core::plan::Plan::for_property)
        .unwrap_or_else(|| {
            eprintln!("unknown property: {}", cli.property);
            std::process::exit(2);
        });
    // The lifter and the BMC must agree on whether call preconditions exist:
    // one decides whether to emit those obligations, the other whether a call
    // may be treated as non-throwing *because* they were emitted.
    //
    // This was computed inside `Plan::for_property` for a decision record and
    // never actually stored, so the flag sat at its default of `true` for every
    // property -- including valid-assert, which does not consume NullDeref
    // obligations at all. The guard then treated a call as non-throwing while
    // nothing carried its burden, which is a wrong TRUE.
    ajave_models::SEED_CALL_PRECONDITIONS.store(
        plan.property.wants_call_preconditions(),
        std::sync::atomic::Ordering::Relaxed,
    );
    if cli.trace {
        eprint!("{}", plan.explain());
    }

    if plan.property == ajave_core::plan::Property::NoDeadlock {
        let verdict = match ajave_engines::concurrency::check_preconditions(&prog) {
            Err(why) => {
                info!("no-deadlock: {why}");
                verdict::Verdict::Unknown
            }
            // Exhaustive, not DPOR, for deadlock.
            //
            // DPOR's reduction is justified by reasoning over *enabled*
            // transitions: two independent enabled transitions commute, so one
            // order represents both. A deadlock is a state where nothing is
            // enabled, reached by threads blocking on each other — and the
            // interleaving that produces it can be exactly the one the
            // reduction discards, because the blocking transitions never
            // appeared in an enabled set to be compared.
            //
            // Measured here: DPOR explored 236 states of LockOrderInversion and
            // reported no deadlock, which is a wrong TRUE for this property.
            // Making DPOR deadlock-aware (tracking blocked transitions in the
            // backtrack computation) is the real fix; until then the property
            // uses the unreduced baseline, which is why that baseline is kept.
            Ok(entries) => match ajave_engines::concurrency::explore(
                &prog,
                &entries,
                // `from_env`, not `default`: the bounds are overridable so their
                // effect on a verdict can be measured rather than assumed.
                ajave_engines::concurrent_state::Bounds::from_env(),
                // Switchable so the two strategies can be compared directly; see the
                // equivalence test. AJAVE_DEADLOCK_EXHAUSTIVE=1 forces the
                // unreduced baseline.
                if std::env::var("AJAVE_DEADLOCK_EXHAUSTIVE")
                    .map(|v| v == "1")
                    .unwrap_or(false)
                {
                    ajave_engines::concurrency::Strategy::Exhaustive
                } else {
                    ajave_engines::concurrency::Strategy::Dpor
                },
            ) {
                ajave_engines::concurrency::Exploration::Deadlock { schedule } => {
                    if cli.trace {
                        eprintln!(
                            "no-deadlock: reachable under a {}-slice schedule",
                            schedule.len()
                        );
                    }
                    verdict::Verdict::False
                }
                // Exhaustive *and* no bound was hit, so the whole interleaving
                // space within the modelled fragment was covered.
                // Deadlock freedom is a property of the schedule, not of the
                // memory model: a race cannot create or remove a deadlock, so
                // this verdict does not need the DRF-SC precondition.
                ajave_engines::concurrency::Exploration::ExhaustiveNoViolation { .. } => {
                    verdict::Verdict::True
                }
                // A violation of some other property is not a deadlock.
                ajave_engines::concurrency::Exploration::Violation { .. } => verdict::Verdict::True,
                // A race is not a deadlock.
                ajave_engines::concurrency::Exploration::DataRace { .. } => verdict::Verdict::True,
                ajave_engines::concurrency::Exploration::Incomplete(why) => {
                    info!("no-deadlock: exploration incomplete — {why}");
                    verdict::Verdict::Unknown
                }
            },
        };
        println!("{verdict}");
        return;
    }

    if plan.property == ajave_core::plan::Property::NoDataRace {
        let verdict = match ajave_engines::concurrency::check_preconditions(&prog) {
            // A program that starts no threads has no races, trivially. Every
            // other refusal means we did not look.
            Err(ajave_engines::concurrency::Refusal::Sequential) => verdict::Verdict::True,
            Err(why) => {
                info!("no-data-race: {why}");
                verdict::Verdict::Unknown
            }
            Ok(entries) => match ajave_engines::concurrency::explore_for(
                &prog,
                &entries,
                ajave_engines::concurrent_state::Bounds::from_env(),
                ajave_engines::concurrency::Strategy::Dpor,
                true,
            ) {
                // A race is exhibited by a concrete interleaving, so finding
                // one needs no completeness argument.
                ajave_engines::concurrency::Exploration::DataRace { location, .. } => {
                    if cli.trace {
                        eprintln!("no-data-race: race on {location}");
                    }
                    verdict::Verdict::False
                }
                // Race *freedom* does need one: it is a claim about every
                // interleaving, so only an exhaustive search that hit no bound
                // can support it.
                ajave_engines::concurrency::Exploration::ExhaustiveNoViolation { .. } => {
                    verdict::Verdict::True
                }
                // The search stopped at a violation of a different property, so
                // it did not cover the space and cannot claim race freedom.
                ajave_engines::concurrency::Exploration::Violation { .. }
                | ajave_engines::concurrency::Exploration::Deadlock { .. } => {
                    info!("no-data-race: search stopped at another property's violation");
                    verdict::Verdict::Unknown
                }
                ajave_engines::concurrency::Exploration::Incomplete(why) => {
                    info!("no-data-race: exploration incomplete — {why}");
                    verdict::Verdict::Unknown
                }
            },
        };
        println!("{verdict}");
        return;
    }

    // The blackboard still takes a bool; the plan is the thing that decides it,
    // so there is one place that knows which obligation kinds a property
    // consumes. Widening this to the full Plan is tracked in #65.
    let assertion_only = plan.property != ajave_core::plan::Property::NoRuntimeException;
    let engines = build_engine_portfolio(cli.ascii_only);
    let mut orchestrator = Orchestrator::new(engines);
    orchestrator.assertion_only = assertion_only;
    // Time held back from the engines for what happens *after* `run` returns.
    //
    // JVM replay is the big term, and it is what turns a violation into a
    // point: a FALSE whose witness was never confirmed scores nothing. While
    // the round loop stopped early this was invisible, because the engines
    // never reached the deadline in the first place. An engine that resumes
    // will spend everything it is given, so the reserve becomes load-bearing
    // the moment resumption lands.
    //
    // Measured rather than guessed: `main: report tail Nms` below is logged on
    // every run at `-v`, and the reserve is set from the tail of that
    // distribution over the corpus, not from its mean. Overrunning by one
    // replay costs the whole task.
    const REPORT_RESERVE: std::time::Duration = std::time::Duration::from_millis(3_000);
    let run_started = std::time::Instant::now();
    orchestrator.deadline = cli.timeout.map(|s| {
        let end = std::time::Instant::now() + std::time::Duration::from_secs(s);
        end.checked_sub(REPORT_RESERVE).unwrap_or(end)
    });
    // Phase 0 of the cooperative-scheduling work: a machine-readable record of
    // what the portfolio was asked to solve, so per-engine cost and payoff can
    // be aggregated *by program shape* rather than by task name.
    //
    // Keyed on features rather than identity on purpose. A cost model fitted to
    // the corpus we score against is the overfitting CLAUDE.md warns about,
    // moved from the engines into the scheduler; one keyed on "bodies with
    // loops and floats and no heap" is a claim that can be checked on a program
    // nobody has seen. `tools/engine_census.py` does the aggregation.
    emit_program_shape(&prog, &plan);
    let verdict = orchestrator.run(&prog, 16);

    if cli.trace {
        for line in &orchestrator.trace {
            eprintln!("{line}");
        }
        for (obligation_ref, status) in orchestrator.bb.statuses() {
            eprintln!("  {obligation_ref} -> {status:?}");
        }
    }
    for r in &orchestrator.bb.rejections {
        eprintln!("blackboard rejected: {r}");
    }

    // Confirm violations via JVM replay.
    let report_started = std::time::Instant::now();
    let contested = orchestrator.bb.contested();
    let violations = collect_violations(&orchestrator);
    let confirmed_witness = if cli.no_replay {
        violations
            .first()
            .map(|v| (v.obligation_ref.clone(), v.witness.clone()))
    } else if !violations.is_empty() && verdict == verdict::Verdict::False {
        confirm_violations(&violations, &classpath, &prog, cli.trace, &contested)
    } else {
        None
    };

    // Determine final verdict.
    let verdict = if verdict == verdict::Verdict::False {
        if cli.no_replay || confirmed_witness.is_some() {
            verdict::Verdict::False
        } else if !violations.is_empty() {
            // Every violation was refuted on a real JVM. The claim is
            // withdrawn — but that is a statement about the *witness*, not
            // about the program, and the blackboard may still hold a proof
            // from an over-approximating engine that never depended on it.
            //
            // Falling straight to UNKNOWN discards that proof. It is how the
            // whole float-nonlinear-calculation category was being lost: NRA
            // solves over the reals, so its counterexamples routinely fail to
            // reproduce under IEEE-754, and each refuted candidate was vetoing
            // a TRUE the AI had legitimately established.
            //
            // Recomputing the verdict with the refuted violations excluded
            // asks the right question: with no surviving counterexample, is
            // every obligation discharged?
            let refuted: Vec<ajave_core::artifact::ObligationRef> = violations
                .iter()
                .map(|v| v.obligation_ref.clone())
                .collect();
            match orchestrator.bb.verdict_excluding(&refuted) {
                verdict::Verdict::True => {
                    if cli.trace {
                        eprintln!(
                            "all {} violation(s) refuted by replay; \
                             remaining obligations are discharged",
                            violations.len()
                        );
                    }
                    let bad = if ajave_core::blackboard::certify_true_enabled() {
                        uncertified_invariant_proofs(&orchestrator.bb, &prog)
                    } else {
                        Vec::new()
                    };
                    if bad.is_empty() {
                        verdict::Verdict::True
                    } else {
                        warn!(
                            "downgrading TRUE to UNKNOWN: {} invariant-backed \
                             proof(s) could not be certified",
                            bad.len()
                        );
                        verdict::Verdict::Unknown
                    }
                }
                _ => verdict::Verdict::Unknown,
            }
        } else {
            verdict
        }
    } else {
        verdict
    };

    // A body we could not fully lift means an over-approximating TRUE is not
    // ours to claim, whatever the engines concluded.
    let all_lifted = prog
        .reachable_from_entry()
        .iter()
        .all(|k| prog.body(k).map(|b| b.is_fully_lifted()).unwrap_or(true));
    let verdict = if verdict == verdict::Verdict::True && !all_lifted {
        eprintln!("downgrading TRUE to UNKNOWN: program contains unlifted regions");
        verdict::Verdict::Unknown
    } else {
        verdict
    };

    // The same reasoning for library calls whose exceptions we do not model.
    // `Math.addExact` throws on overflow and `"abc".charAt(5)` throws on a bad
    // index, but neither produces a `Check` in the IR — so the blackboard can
    // hold *zero* obligations and the verdict becomes TRUE by vacuity, without
    // any engine having reasoned about the program at all. Claiming "no
    // runtime exception" then asserts something we never examined.
    // Did the concurrency engine explore the program exhaustively? If so the
    // Thread lifecycle calls are no longer "unmodelled" — that engine modelled
    // them, over every interleaving within its bounds.
    //
    // The guard cannot simply be dropped for threaded programs: the interval AI
    // analyses a `run()` body as an ordinary root, under a sequential
    // assumption, so it would happily prove a racy body safe. The guard is what
    // stops that becoming a TRUE. It may only stand down when an engine that
    // actually reasons about interleavings has covered the program.
    let concurrency_covered = orchestrator
        .bb
        .since(0)
        .iter()
        .any(|t| t.producer == ajave_core::artifact::EngineId("concurrency"));

    let verdict = if verdict == verdict::Verdict::True && !assertion_only && !concurrency_covered {
        let offender = prog.reachable_from_entry().into_iter().find_map(|k| {
            prog.body(&k).and_then(|b| {
                ajave_engines::first_unmodelled_throwing_call(&prog, b)
                    .map(|t| (k.clone(), t.clone()))
            })
        });
        match offender {
            Some((k, call)) => {
                eprintln!(
                    "downgrading TRUE to UNKNOWN: {k} calls {}.{}{} whose exception \
                     behaviour is not modelled",
                    call.class, call.name, call.desc
                );
                verdict::Verdict::Unknown
            }
            None => verdict,
        }
    } else {
        verdict
    };

    // Emit witness file when the verdict is FALSE and --witness was given.
    if verdict == verdict::Verdict::False {
        if let Some(witness_path) = &cli.witness {
            if let Some((obligation_ref, witness)) = &confirmed_witness {
                emit_witness_file(witness_path, obligation_ref, witness, &prog, &cli.inputs);
            }
        }
    }

    // Print witness assumptions when --show-witness is set.
    if cli.show_witness {
        if let Some((obligation_ref, witness)) = &confirmed_witness {
            print_witness(obligation_ref, witness, &prog);
        } else if !violations.is_empty() {
            print_unconfirmed_witness(&violations[0].witness);
        }
    }

    // What the reserve has to cover. Logged unconditionally at `-v` so the
    // constant above can be set from a distribution over the corpus rather
    // than from one task, and so a growing tail shows up before it starts
    // eating the budget.
    info!(
        "main: report tail {}ms (engines {}ms)",
        report_started.elapsed().as_millis(),
        report_started
            .saturating_duration_since(run_started)
            .as_millis(),
    );
    info!("final verdict: {verdict}");
    println!("{verdict}");
}
