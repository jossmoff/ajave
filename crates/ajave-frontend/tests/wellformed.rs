//! Every body the lifter produces from `benchmarks/ajave/` must be well formed.
//!
//! # Why this test and not only the `debug_assert!`
//!
//! `lift_method_with_lambdas` ends with a `debug_assert!` on
//! `ajave_ir::validate`, so every debug-mode lift already checks itself. That
//! covers whatever programs happen to get lifted — in `cargo test`, almost
//! none, because the frontend had exactly one unit test. This test is what
//! supplies the programs: 170-odd hand-written Java files that between them
//! exercise floats, arrays, strings, exceptions, generics, lambdas, threads
//! and every obligation kind.
//!
//! A lifter defect is a *systematic* wrong answer across the whole portfolio,
//! where an engine defect is localised and usually caught by JVM replay. So
//! the cheapest useful thing to assert about the lifter is that its output is
//! structurally indexable at all — `Body::block`, `Body::var` and
//! `Body::obligation` index directly, and the historical defects in this area
//! (a callee's `BlockId` used to index the caller, an `ObligationId` treated
//! as global) are exactly range violations.
//!
//! # Why it compiles rather than reading `.class` files
//!
//! There are none in the tree, and there should not be: a replayed witness
//! runs the *compiled* program, so anything other than what javac actually
//! produced would open a gap between what is proven and what is certified.
//! Compiling here keeps this test looking at the same bytecode the engines do.
//!
//! Skipped, not failed, when `javac` is absent — this crate's other tests do
//! not need a JDK and should not start needing one.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn have_javac() -> bool {
    Command::new("javac")
        .arg("-version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Every directory holding a `Main.java`, i.e. one benchmark each.
fn benchmark_dirs(root: &Path) -> Vec<PathBuf> {
    let mut out = BTreeSet::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().map(|x| x == "java").unwrap_or(false) {
                out.insert(d.clone());
            }
        }
    }
    // `common/` is the shared `Verifier` stub, compiled once below rather than
    // lifted as a benchmark of its own.
    out.retain(|d| !d.components().any(|c| c.as_os_str() == "common"));
    out.into_iter().collect()
}

fn java_files(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.flatten()
                .map(|e| e.path())
                .filter(|p| p.extension().map(|x| x == "java").unwrap_or(false))
                .collect()
        })
        .unwrap_or_default();
    v.sort();
    v
}

fn class_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().map(|x| x == "class").unwrap_or(false) {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

#[test]
fn every_body_lifted_from_the_ajave_benchmarks_is_well_formed() {
    if !have_javac() {
        eprintln!("javac not found; skipping (this crate's other tests need no JDK)");
        return;
    }
    let root = workspace_root();
    // `AJAVE_WELLFORMED_DIR=benchmarks/sv-comp` points the same walk at the
    // competition corpus. Not the default: it is ~10x the work and needs its
    // own `common/`, so it belongs in a nightly job rather than `cargo test`.
    let rel = std::env::var("AJAVE_WELLFORMED_DIR").unwrap_or_else(|_| "benchmarks/ajave".into());
    let bench = root.join(&rel);
    let common = bench.join("common");
    let dirs = benchmark_dirs(&bench);
    let floor = if rel == "benchmarks/ajave" { 100 } else { 1 };
    assert!(
        dirs.len() > floor,
        "expected a benchmark suite, found {} benchmark dirs under {}",
        dirs.len(),
        bench.display()
    );

    let scratch = tempdir("ajave-wellformed");
    // The `Verifier` stub compiles once and goes on every benchmark's
    // classpath; recompiling it 175 times is most of the wall clock.
    let common_out = scratch.join("__common");
    std::fs::create_dir_all(&common_out).unwrap();
    let common_srcs = {
        let mut v = Vec::new();
        let mut stack = vec![common.clone()];
        while let Some(d) = stack.pop() {
            for e in std::fs::read_dir(&d).unwrap().flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else if p.extension().map(|x| x == "java").unwrap_or(false) {
                    v.push(p);
                }
            }
        }
        v.sort();
        v
    };
    let out = Command::new("javac")
        .arg("-nowarn")
        .arg("-d")
        .arg(&common_out)
        .args(&common_srcs)
        .output()
        .expect("javac");
    assert!(
        out.status.success(),
        "the shared Verifier stub does not compile: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let problems: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let bodies = AtomicUsize::new(0);
    let lifted_dirs = AtomicUsize::new(0);
    let next = AtomicUsize::new(0);

    // One javac per benchmark is unavoidable (175 identical `Main` classes
    // cannot share an invocation), so they run in parallel: ~0.45s each
    // serially is 80s, which is more than this test is worth.
    let workers = std::thread::available_parallelism()
        .map(|n| n.get().min(8))
        .unwrap_or(4);
    std::thread::scope(|s| {
        for w in 0..workers {
            let (problems, bodies, lifted_dirs, next) = (&problems, &bodies, &lifted_dirs, &next);
            let (dirs, scratch, common_out) = (&dirs, &scratch, &common_out);
            s.spawn(move || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= dirs.len() {
                    return;
                }
                let dir = &dirs[i];
                let out_dir = scratch.join(format!("w{w}_{i}"));
                std::fs::create_dir_all(&out_dir).unwrap();
                let srcs = java_files(dir);
                let r = Command::new("javac")
                    .arg("-nowarn")
                    .arg("-cp")
                    .arg(common_out)
                    .arg("-d")
                    .arg(&out_dir)
                    .args(&srcs)
                    .output()
                    .expect("javac");
                if !r.status.success() {
                    problems.lock().unwrap().push(format!(
                        "{}: does not compile: {}",
                        dir.display(),
                        String::from_utf8_lossy(&r.stderr).trim()
                    ));
                    return;
                }
                lifted_dirs.fetch_add(1, Ordering::Relaxed);
                let mut prog = ajave_ir::Program::default();
                for cf_path in class_files(&out_dir) {
                    let bytes = std::fs::read(&cf_path).unwrap();
                    match ajave_frontend::classfile::ClassFile::parse(&bytes) {
                        Ok(cf) => ajave_frontend::lift::lift_class(&cf, &mut prog),
                        Err(e) => problems.lock().unwrap().push(format!(
                            "{}: {} does not parse: {e}",
                            dir.display(),
                            cf_path.display()
                        )),
                    }
                }
                let mut keys: Vec<_> = prog.bodies.keys().cloned().collect();
                keys.sort();
                bodies.fetch_add(keys.len(), Ordering::Relaxed);
                for k in keys {
                    let body = &prog.bodies[&k];
                    let defects = ajave_ir::validate::defects(body);
                    if !defects.is_empty() {
                        let mut msg = format!("{}: {k}", dir.display());
                        for d in &defects {
                            msg.push_str(&format!("\n      {d}"));
                        }
                        problems.lock().unwrap().push(msg);
                    }
                }
                let _ = std::fs::remove_dir_all(&out_dir);
            });
        }
    });

    let problems = problems.into_inner().unwrap();
    eprintln!(
        "lifted {} bodies from {} of {} benchmarks",
        bodies.load(Ordering::Relaxed),
        lifted_dirs.load(Ordering::Relaxed),
        dirs.len()
    );
    let _ = std::fs::remove_dir_all(&scratch);
    assert!(
        bodies.load(Ordering::Relaxed) > dirs.len(),
        "lifted suspiciously few bodies; the suite or the harness is broken"
    );
    if !problems.is_empty() {
        let mut sorted = problems;
        sorted.sort();
        panic!(
            "{} ill-formed lift(s):\n  {}",
            sorted.len(),
            sorted.join("\n  ")
        );
    }
}

/// A unique self-made temp dir. `ajave_core::scratch::ScratchDir` is the
/// production answer, and this crate must not depend on `ajave-core` — the
/// dependency runs the other way (see `scripts/check-boundaries.sh`).
fn tempdir(prefix: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let p = std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&p).unwrap();
    p
}
