//! ajave driver.
//!
//! Usage:
//!   ajave [OPTIONS] <path>...
//!
//! Prints the lifted IR on `--ir`, the orchestrator schedule on `--trace`, and
//! always ends with a single line BenchExec parses as the verdict.

use std::path::{Path, PathBuf};

use clap::{ArgAction, Parser};
use log::{debug, info, warn};
use ajave_core::engine::Engine;
use ajave_core::orchestrator::Orchestrator;
use ajave_frontend::classfile::ClassFile;
use ajave_frontend::lift;
use ajave_ir::verdict;
use ajave_ir::Program;

#[derive(Parser)]
#[command(
    name = "ajave",
    about = "An SV-COMP Java verifier: compiles/loads a program, runs the engine portfolio, reports a certified verdict.",
    version
)]
struct Cli {
    /// Input files or directories (.java source or pre-compiled .class bytecode).
    /// BenchExec passes every entry of the task YAML's input_files as a separate argument.
    #[arg(required = true)]
    inputs: Vec<PathBuf>,

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

    /// Constrain nondet char to ASCII (0-127). Prevents witnesses with
    /// non-ASCII chars that our Character method encodings can't model.
    #[arg(long = "ascii-only")]
    ascii_only: bool,

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
) -> Result<(Vec<PathBuf>, String, Option<ajave_core::scratch::ScratchDir>), String> {
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
    ];
    // NRA before BMC: NRA handles transcendental math (sin, cos, exp, etc.)
    // via cvc5's native support. BMC havoces these calls and produces garbage
    // witnesses, so NRA must claim them first.
    engines.push(Box::new(ajave_engines::nra::NraEngine::new()));
    // AI before BMC: for float-loop bodies, the AI's widening analysis can
    // prove safety via interval fixpoint. BMC finds spurious violations on
    // bounded unrollings that fail JVM replay; AI discharges first to prevent
    // this. For non-float bodies, AI only publishes hints during init (no
    // discharge), so BMC is unaffected.
    engines.push(Box::new(ajave_engines::ai::AiEngine::new()));
    if let Some(factory) = ajave_core::smt_smtlib::SmtLibFactory::from_env() {
        let factory2 = ajave_core::smt_smtlib::SmtLibFactory::from_env();
        let mut bmc = ajave_engines::smt_bmc::SmtBmc::new(Box::new(factory), 200);
        bmc.ascii_only = ascii_only;
        engines.push(Box::new(bmc));
        if let Some(f2) = factory2 {
            engines.push(Box::new(ajave_engines::kinduction::KInduction::new(
                Box::new(f2),
            )));
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
            let entries = ajave_engines::concurrency::check_preconditions(program)
                .unwrap_or_default();
            let ok = ajave_engines::concurrency::replay_schedule(
                program,
                &entries,
                &violation.obligation_ref,
                &violation.witness.schedule,
                Default::default(),
            );
            if trace || ok {
                eprintln!(
                    "schedule-replay: {} {} (interpreter, not a real JVM)",
                    if ok { "confirmed" } else { "could not reproduce" },
                    violation.obligation_ref
                );
            }
            if ok {
                any_confirmed = true;
                if confirmed.is_none() {
                    confirmed = Some((
                        violation.obligation_ref.clone(),
                        violation.witness.clone(),
                    ));
                }
            }
            continue;
        }
        match ajave_core::certify::Certifier::certify(&replay, &violation.tagged, program) {
            ajave_core::certify::CertResult::Confirmed => {
                any_confirmed = true;
                if confirmed.is_none() {
                    confirmed = Some((
                        violation.obligation_ref.clone(),
                        violation.witness.clone(),
                    ));
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
        ajave_ir::ObligationKind::Assertion => {
            "CHECK( init(Main.main()), LTL(G assert) )"
        }
        _ => {
            "CHECK(init(Main.main()), LTL(G ! uncaught(java.lang.RuntimeException)))"
        }
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

fn main() {
    let cli = Cli::parse();

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

    info!("ajave starting, inputs={:?}", cli.inputs);

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
            if k.class == "Main" { 0 } else { 1 + k.class.len() }
        })
        .cloned();

    for e in &load_errors {
        warn!("{e}");
        eprintln!("warning: {e}");
    }

    if cli.ir {
        let mut keys: Vec<_> = prog.bodies.keys().cloned().collect();
        keys.sort();
        for k in keys {
            print!("{}", prog.bodies[&k].render());
        }
        println!();
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
                Default::default(),
                ajave_engines::concurrency::Strategy::Exhaustive,
            ) {
                ajave_engines::concurrency::Exploration::Deadlock { schedule } => {
                    if cli.trace {
                        eprintln!("no-deadlock: reachable under a {}-slice schedule", schedule.len());
                    }
                    verdict::Verdict::False
                }
                // Exhaustive *and* no bound was hit, so the whole interleaving
                // space within the modelled fragment was covered.
                ajave_engines::concurrency::Exploration::ExhaustiveNoViolation => {
                    verdict::Verdict::True
                }
                // A violation of some other property is not a deadlock.
                ajave_engines::concurrency::Exploration::Violation { .. } => {
                    verdict::Verdict::True
                }
                ajave_engines::concurrency::Exploration::Incomplete(why) => {
                    info!("no-deadlock: exploration incomplete — {why}");
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
    let violations = collect_violations(&orchestrator);
    let confirmed_witness = if cli.no_replay {
        violations.first().map(|v| (v.obligation_ref.clone(), v.witness.clone()))
    } else if !violations.is_empty() && verdict == verdict::Verdict::False {
        confirm_violations(&violations, &classpath, &prog, cli.trace)
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
            let refuted: Vec<ajave_core::artifact::ObligationRef> =
                violations.iter().map(|v| v.obligation_ref.clone()).collect();
            match orchestrator.bb.verdict_excluding(&refuted) {
                verdict::Verdict::True => {
                    if cli.trace {
                        eprintln!(
                            "all {} violation(s) refuted by replay; \
                             remaining obligations are discharged",
                            violations.len()
                        );
                    }
                    verdict::Verdict::True
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

    info!("final verdict: {verdict}");
    println!("{verdict}");
}
