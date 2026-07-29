//! roast driver.
//!
//! Usage:
//!   roast [OPTIONS] <path>...
//!
//! Prints the lifted IR on `--ir`, the orchestrator schedule on `--trace`, and
//! always ends with a single line BenchExec parses as the verdict.

use std::path::{Path, PathBuf};

use clap::{ArgAction, Parser};
use log::{debug, info, warn};
use roast_core::engine::Engine;
use roast_core::orchestrator::Orchestrator;
use roast_frontend::classfile::ClassFile;
use roast_frontend::lift;
use roast_ir::verdict;
use roast_ir::Program;

#[derive(Parser)]
#[command(
    name = "roast",
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
fn compile_if_needed(inputs: &[PathBuf]) -> Result<(Vec<PathBuf>, String), String> {
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
        return Ok((classes, cp));
    }

    let out_dir = std::env::temp_dir().join(format!("roast-build-{}", std::process::id()));
    info!(
        "compiling {} .java file(s) to {}",
        java_files.len(),
        out_dir.display()
    );
    std::fs::create_dir_all(&out_dir).map_err(|e| e.to_string())?;

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
    Ok((classes, out_dir.display().to_string()))
}

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

    info!("roast starting, inputs={:?}", cli.inputs);

    let (class_files, classpath) = match compile_if_needed(&cli.inputs) {
        Ok(r) => r,
        Err(e) => {
            // A build failure is not evidence of anything about the program's
            // safety. Report it plainly and stop, rather than lifting nothing
            // and silently producing a wrong verdict.
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
        .find(|k| k.name == "main" && k.desc == "([Ljava/lang/String;)V")
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

    let engine_list: Vec<Box<dyn Engine>> = vec![
        Box::new(roast_engines::presolve::Presolve::new()),
        Box::new(roast_engines::concrete::Concrete::new(2000)),
        Box::new(roast_engines::ai::AiEngine::new()),
    ];
    let mut orch = Orchestrator::new(engine_list);
    let v = orch.run(&prog, 16);

    if cli.trace {
        for line in &orch.trace {
            eprintln!("{line}");
        }
        for (oref, st) in orch.bb.statuses() {
            eprintln!("  {oref} -> {st:?}");
        }
    }
    for r in &orch.bb.rejections {
        eprintln!("blackboard rejected: {r}");
    }

    // Nothing published by an engine is final on its own authority. A
    // Violated status is provisional until `JvmReplay` confirms it against a
    // real JVM; one that can't be confirmed is downgraded rather than
    // reported, per the certify::JvmReplay module doc.
    let replay = roast_core::certify::JvmReplay::new(classpath);
    let violated: Vec<_> = orch
        .bb
        .statuses()
        .filter_map(|(oref, st)| match st {
            roast_core::artifact::Status::Violated { by, witness } => Some((
                oref.clone(),
                roast_core::artifact::Tagged {
                    seq: 0,
                    producer: *by,
                    direction: roast_core::artifact::Direction::Under,
                    artifact: roast_core::artifact::Artifact::Status(
                        oref.clone(),
                        roast_core::artifact::Status::Violated {
                            by: *by,
                            witness: witness.clone(),
                        },
                    ),
                },
            )),
            _ => None,
        })
        .collect();

    let mut any_confirmed = false;
    let mut any_unconfirmed = false;
    for (oref, tagged) in &violated {
        match roast_core::certify::Certifier::certify(&replay, tagged, &prog) {
            roast_core::certify::CertResult::Confirmed => {
                any_confirmed = true;
                if cli.trace {
                    eprintln!("jvm-replay: confirmed {oref}");
                }
            }
            other => {
                any_unconfirmed = true;
                if cli.trace {
                    eprintln!("jvm-replay: {other:?} for {oref}");
                }
            }
        }
    }

    let v = if v == verdict::Verdict::False {
        if any_confirmed {
            verdict::Verdict::False
        } else if any_unconfirmed {
            eprintln!("downgrading FALSE to UNKNOWN: witness did not replay on a real JVM");
            verdict::Verdict::Unknown
        } else {
            v
        }
    } else {
        v
    };

    // A body we could not fully lift means an over-approximating TRUE is not
    // ours to claim, whatever the engines concluded. Only bodies actually
    // reachable from the entry point matter.
    let all_lifted = prog
        .reachable_from_entry()
        .iter()
        .all(|k| prog.body(k).map(|b| b.is_fully_lifted()).unwrap_or(false));
    let v = if v == verdict::Verdict::True && !all_lifted {
        eprintln!("downgrading TRUE to UNKNOWN: program contains unlifted regions");
        verdict::Verdict::Unknown
    } else {
        v
    };

    info!("final verdict: {v}");
    println!("{v}");
}
