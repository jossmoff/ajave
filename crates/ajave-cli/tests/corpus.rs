//! Integration tests: run the ajave binary against every task in `tasks/` and
//! check the verdict against the task's own declared ground truth.
//!
//! # Why this is data-driven
//!
//! This file used to hold 114 hand-written tests, each calling the binary with
//! no `--property` flag and asserting a literal verdict. Two problems followed
//! from that, and 24 tests failed on a clean `main` because of them (#54):
//!
//! 1. **The property was implicit.** With no flag the binary runs its default,
//!    `--property assert`, while many of the asserted verdicts describe
//!    runtime-exception behaviour. `tasks/stage04_divzero` is
//!    `int y = 100 / nondetInt(); assert y != 12345;` and is declared FALSE —
//!    but under valid-assert the correct answer is TRUE, because
//!    `100/x == 12345` has no integer solution and `x == 0` throws before the
//!    assertion is reached. Both answers are right; the test asserted the one
//!    for the other property.
//!
//! 2. **The expectations were pinned to output, not to truth.** The old header
//!    said each test asserts "the verdict ajave *currently* produces". That
//!    makes every genuine improvement look like a failure —
//!    `jbmc-regression/array1` moved UNKNOWN -> TRUE, which is *correct* per
//!    SV-COMP, and was recorded as a regression.
//!
//! # What replaces it
//!
//! Every task under `tasks/` carries a `.yml` declaring its expected verdict.
//! That is the ground truth, so this harness reads it rather than restating it.
//!
//! All 114 declare `assert.prp`, but their expected verdicts plainly cover
//! uncaught exceptions as well as failed assertions — `ModuloZero1` has no
//! reachable assertion failure at all and is declared FALSE. So this corpus
//! uses "assert" to mean *the program misbehaves*, which spans both SV-COMP
//! properties. Rather than re-adjudicate 114 ground truths, each task is run
//! under **both** properties and the results combined:
//!
//! * `expected: false` — at least one property must be violated.
//! * `expected: true`  — neither property may be violated, and both must be
//!   proved. Requiring both is deliberately conservative: if NRE is UNKNOWN we
//!   do not know whether an exception escapes, so the task is scored "unproven"
//!   rather than passed. A regression gate must never produce a false pass.
//!
//! # What fails the build
//!
//! * **A wrong verdict** — the combined answer is the opposite of the declared
//!   one. Always a failure; this is the −16/−32 case.
//! * **A regression** — a task that was previously proved is no longer proved.
//!   Baselines live in `tasks/corpus-expectations.txt`; regenerate with
//!   `UPDATE_CORPUS=1 cargo test --release -p ajave-cli --test corpus`.
//!
//! An UNKNOWN that was already UNKNOWN is not a failure. Precision we never had
//! is not a regression, and treating it as one is what made the old suite noisy
//! enough to ignore.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};

/// Per-task timeout. Above the corpus's slowest passing task with headroom, so
/// a timeout here means something hung rather than that the machine was busy.
const TIMEOUT_SECS: u64 = 90;

/// Parallel workers. Below core count on purpose: each ajave spawns a solver
/// child, and oversubscribing turns slow tasks into timeouts, which would read
/// as regressions that are really just contention (#64).
const JOBS: usize = 6;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// One task: its directory name, resolved inputs, and declared verdict.
struct Task {
    name: String,
    inputs: Vec<PathBuf>,
    expect_true: bool,
}

/// Minimal reader for the two fields we need. The task files are generated and
/// uniform — a flat `input_files` list and a single `expected_verdict` — so a
/// line scanner is enough and keeps a YAML crate out of the dev-dependencies.
///
/// `root` is the workspace root; the task's name is its path relative to
/// `tasks/`, not its directory name. `ArithmeticException1` exists both at the
/// top level and under `jbmc-regression/`, and keying on the bare name silently
/// collapsed the two into one baseline entry.
fn read_task(root: &Path, yml: &Path) -> Option<Task> {
    let text = std::fs::read_to_string(yml).ok()?;
    let dir = yml.parent()?;

    let mut inputs = Vec::new();
    let mut expect: Option<bool> = None;
    let mut in_inputs = false;

    for line in text.lines() {
        let t = line.trim();
        if t.starts_with("input_files:") {
            in_inputs = true;
            continue;
        }
        if in_inputs {
            if let Some(rest) = t.strip_prefix("- ") {
                inputs.push(dir.join(rest.trim()));
                continue;
            }
            if !t.is_empty() && !t.starts_with('#') {
                in_inputs = false;
            }
        }
        if let Some(rest) = t.strip_prefix("expected_verdict:") {
            expect = match rest.trim() {
                "true" => Some(true),
                "false" => Some(false),
                _ => None,
            };
        }
    }

    let name = dir
        .strip_prefix(root.join("tasks"))
        .unwrap_or(dir)
        .to_string_lossy()
        .into_owned();

    Some(Task {
        name,
        inputs,
        expect_true: expect?,
    })
}

fn find_tasks(root: &Path) -> Vec<Task> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "yml") {
                out.push(p);
            }
        }
    }
    let mut ymls = Vec::new();
    walk(&root.join("tasks"), &mut ymls);
    ymls.sort();
    ymls.iter().filter_map(|y| read_task(root, y)).collect()
}

/// Kill an entire process group, so a timed-out run takes its solver and JVM
/// with it. A negative PID addresses the group; `process_group(0)` above made
/// the child its own leader, so this cannot reach anything we did not start.
///
/// Shells out to `kill` rather than pulling in `libc` for one call.
#[cfg(unix)]
fn kill_group(pid: u32) {
    let _ = std::process::Command::new("/bin/kill")
        .arg("-9")
        .arg(format!("-{pid}"))
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();
}

#[cfg(not(unix))]
fn kill_group(_pid: u32) {}

/// Run one property. Returns the last non-empty stdout line, or `TIMEOUT`.
fn run(property: &str, inputs: &[PathBuf]) -> String {
    let binary = env!("CARGO_BIN_EXE_ajave");
    let mut cmd = Command::new(binary);
    cmd.arg("--property").arg(property).args(inputs);

    // No portable timeout on Command, so bound it by polling below.
    //
    // `process_group(0)` matters as much as the timeout. ajave spawns a solver
    // (z3/cvc5) and a real JVM for witness replay, and `Child::kill` signals
    // only the direct child — the grandchildren survive, holding memory. With
    // 228 runs and a handful of timeouts that leak compounded until the machine
    // ran out of memory and froze. Putting each run in its own process group
    // lets `kill_group` reach every descendant.
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }
    let child = cmd
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn();
    let Ok(mut child) = child else {
        return "SPAWN-FAILED".into();
    };

    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                if start.elapsed().as_secs() > TIMEOUT_SECS {
                    kill_group(child.id());
                    let _ = child.kill();
                    let _ = child.wait();
                    return "TIMEOUT".into();
                }
                std::thread::sleep(std::time::Duration::from_millis(50));
            }
            Err(_) => return "ERROR".into(),
        }
    }

    let pid = child.id();
    let out = match child.wait_with_output() {
        Ok(o) => o,
        Err(_) => {
            kill_group(pid);
            return "ERROR".into();
        }
    };
    // Belt and braces: ajave exiting does not guarantee its solver did.
    kill_group(pid);
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .rfind(|l| !l.trim().is_empty())
        .unwrap_or("(no output)")
        .trim()
        .to_string()
}

/// How a task came out, once both properties are combined.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Outcome {
    /// Matches the declared verdict.
    Correct,
    /// Neither property settled it. Not a failure.
    Unproven,
    /// The opposite of the declared verdict. Always a failure.
    Wrong,
}

impl Outcome {
    fn as_str(self) -> &'static str {
        match self {
            Outcome::Correct => "correct",
            Outcome::Unproven => "unproven",
            Outcome::Wrong => "WRONG",
        }
    }
}

fn combine(expect_true: bool, va: &str, nre: &str) -> Outcome {
    let any_false = va == "FALSE" || nre == "FALSE";
    if expect_true {
        if any_false {
            Outcome::Wrong
        } else if va == "TRUE" && nre == "TRUE" {
            Outcome::Correct
        } else {
            Outcome::Unproven
        }
    } else if any_false {
        Outcome::Correct
    } else if va == "TRUE" && nre == "TRUE" {
        // Both properties proved safe on a task declared to misbehave.
        Outcome::Wrong
    } else {
        Outcome::Unproven
    }
}

fn baseline_path(root: &Path) -> PathBuf {
    root.join("tasks/corpus-expectations.txt")
}

fn read_baseline(root: &Path) -> BTreeMap<String, String> {
    let Ok(text) = std::fs::read_to_string(baseline_path(root)) else {
        return BTreeMap::new();
    };
    text.lines()
        .filter(|l| !l.trim_start().starts_with('#') && !l.trim().is_empty())
        .filter_map(|l| {
            let mut it = l.split_whitespace();
            Some((it.next()?.to_string(), it.next()?.to_string()))
        })
        .collect()
}

#[test]
fn corpus_verdicts_match_declared_ground_truth() {
    let root = workspace_root();
    let tasks = find_tasks(&root);
    assert!(
        tasks.len() > 100,
        "expected the full task corpus, found {} — has tasks/ moved?",
        tasks.len()
    );

    let queue = Arc::new(Mutex::new(tasks.into_iter().collect::<Vec<_>>()));
    let results = Arc::new(Mutex::new(Vec::<(String, Outcome, String, String)>::new()));

    let mut handles = Vec::new();
    for _ in 0..JOBS {
        let queue = Arc::clone(&queue);
        let results = Arc::clone(&results);
        handles.push(std::thread::spawn(move || loop {
            let task = { queue.lock().unwrap().pop() };
            let Some(task) = task else { break };
            let va = run("assert", &task.inputs);
            let nre = run("no-runtime-exception", &task.inputs);
            let outcome = combine(task.expect_true, &va, &nre);
            results
                .lock()
                .unwrap()
                .push((task.name, outcome, va, nre));
        }));
    }
    for h in handles {
        h.join().expect("worker panicked");
    }

    let mut results = Arc::try_unwrap(results).unwrap().into_inner().unwrap();
    results.sort_by(|a, b| a.0.cmp(&b.0));

    if std::env::var("UPDATE_CORPUS").is_ok() {
        let mut out = String::from(
            "# Corpus baseline: the outcome ajave achieves on each task today.\n\
             # Generated by: UPDATE_CORPUS=1 cargo test --release -p ajave-cli --test corpus\n\
             #\n\
             # A task moving correct -> unproven fails the build. Improving a task to\n\
             # correct is expected to update this file in the same commit.\n\
             # Format: <task> <outcome> <valid-assert> <no-runtime-exception>\n",
        );
        for (name, outcome, va, nre) in &results {
            out.push_str(&format!("{name}\t{}\t{va}\t{nre}\n", outcome.as_str()));
        }
        std::fs::write(baseline_path(&root), out).expect("write baseline");
        eprintln!("baseline updated with {} tasks", results.len());
        return;
    }

    let baseline = read_baseline(&root);

    let wrong: Vec<_> = results
        .iter()
        .filter(|(_, o, _, _)| *o == Outcome::Wrong)
        .collect();

    let regressed: Vec<_> = results
        .iter()
        .filter(|(name, o, _, _)| {
            *o != Outcome::Correct && baseline.get(name).map(String::as_str) == Some("correct")
        })
        .collect();

    let correct = results
        .iter()
        .filter(|(_, o, _, _)| *o == Outcome::Correct)
        .count();
    eprintln!(
        "corpus: {} tasks — {} correct, {} unproven, {} wrong",
        results.len(),
        correct,
        results.len() - correct - wrong.len(),
        wrong.len()
    );

    let mut failures = String::new();
    if !wrong.is_empty() {
        failures.push_str(&format!("\n{} WRONG verdict(s):\n", wrong.len()));
        for (name, _, va, nre) in &wrong {
            failures.push_str(&format!("  {name}: valid-assert={va} nre={nre}\n"));
        }
        failures.push_str(
            "A wrong verdict costs -16 (TRUE) or -32 (FALSE) at competition. \
             Fix the analysis, never the expectation.\n",
        );
    }
    if !regressed.is_empty() {
        failures.push_str(&format!(
            "\n{} task(s) regressed from correct:\n",
            regressed.len()
        ));
        for (name, o, va, nre) in &regressed {
            failures.push_str(&format!(
                "  {name}: now {} (valid-assert={va} nre={nre})\n",
                o.as_str()
            ));
        }
    }
    assert!(failures.is_empty(), "{failures}");
}

#[cfg(test)]
mod combine_tests {
    use super::*;

    #[test]
    fn a_task_declared_false_passes_when_either_property_is_violated() {
        // stage04_divzero: the assertion cannot fail, but the division throws.
        assert_eq!(combine(false, "TRUE", "FALSE"), Outcome::Correct);
        // stage00_const: the assertion itself fails.
        assert_eq!(combine(false, "FALSE", "TRUE"), Outcome::Correct);
    }

    #[test]
    fn proving_both_properties_safe_on_a_false_task_is_wrong() {
        assert_eq!(combine(false, "TRUE", "TRUE"), Outcome::Wrong);
    }

    #[test]
    fn violating_either_property_on_a_true_task_is_wrong() {
        assert_eq!(combine(true, "FALSE", "TRUE"), Outcome::Wrong);
        assert_eq!(combine(true, "TRUE", "FALSE"), Outcome::Wrong);
    }

    #[test]
    fn a_true_task_needs_both_properties_proved() {
        assert_eq!(combine(true, "TRUE", "TRUE"), Outcome::Correct);
        // An UNKNOWN on either side leaves the program's behaviour open, so
        // this must not pass — a gate that guesses here would hide a real bug.
        assert_eq!(combine(true, "TRUE", "UNKNOWN"), Outcome::Unproven);
        assert_eq!(combine(true, "UNKNOWN", "TRUE"), Outcome::Unproven);
    }

    #[test]
    fn timeouts_are_unproven_never_wrong() {
        assert_eq!(combine(true, "TIMEOUT", "TIMEOUT"), Outcome::Unproven);
        assert_eq!(combine(false, "TIMEOUT", "TIMEOUT"), Outcome::Unproven);
    }
}
