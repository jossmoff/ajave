//! Profiling for the SMT layer: what the encoder emitted, and what the solver
//! did with it.
//!
//! ## Why this is its own thing
//!
//! Verification tools are normally measured end to end — program in, verdict
//! and wall-clock out. That number confounds four separable costs: lifting,
//! encoding, solving, and certification. When a benchmark is slow or comes back
//! UNKNOWN, the end-to-end number cannot say which of them to look at.
//!
//! The encoder deserves separate measurement in particular, because **its
//! output size is a floor on total cost that no solver improvement can
//! remove**. A solver parses and builds terms before it reasons about any of
//! them, so an encoder that emits a formula twice as large pays for it twice
//! over even when the formula is trivially decidable. That cost is invisible to
//! solver benchmarking (SMT-COMP and friends take the formula as their input)
//! and invisible to end-to-end verification benchmarking (which cannot
//! attribute it). It is visible here.
//!
//! The classic instance is Flanagan & Saxe, *Avoiding exponential explosion*
//! (POPL 2001): a verification-condition generator that substitutes an
//! expression into a variable map, rather than naming it, emits a formula
//! exponential in the size of the source fragment. roast's text encoders did
//! exactly that until recently, and nothing in the test suite could see it —
//! the verdicts were still correct, just slower to reach, until they weren't
//! reachable at all.
//!
//! ## What is recorded
//!
//! Two channels, because roast has two ways of talking to a solver:
//!
//! * **Incremental** (`smt_bmc`, `kinduction`): the `Solver` trait over a
//!   long-lived subprocess. `SmtLib` funnels every byte through one `send`, so
//!   the counters there are exact.
//! * **Batch** (`chc`, `imc`, `cegar`): a whole script assembled as text and
//!   handed to a fresh solver process. Recorded by the engine at the call.
//!
//! Both land in the same [`SmtProfile`], keyed by engine, so a report can put
//! them side by side.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// One engine's SMT activity.
///
/// Counters are cumulative across every solver instance the engine created, so
/// an engine that spawns a fresh process per query still reports one row.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct EngineSmtStats {
    /// Which solver binary served this engine, when known.
    pub solver: String,

    // ── What the encoder produced ───────────────────────────────────────
    /// Bytes of SMT-LIB text handed to the solver. The direct measure of
    /// encoding size, and the quantity that bounds parse cost from below.
    pub bytes_emitted: u64,
    /// SMT-LIB commands emitted (`declare-const`, `define-const`, `assert`, …).
    /// With `SmtLib`'s one-`define-const`-per-term encoding this is close to a
    /// term count, so `bytes_emitted / commands` is the average term size.
    pub commands: u64,
    /// `assert` commands specifically — the constraint count, as opposed to
    /// the definitions that build up the terms being asserted.
    pub asserts: u64,
    /// Time spent inside the encoder, excluding anything spent waiting on the
    /// solver. Measured as total time minus solver time.
    pub encode_time: Duration,

    // ── What the solver did ─────────────────────────────────────────────
    pub check_sat_calls: u64,
    /// Wall time blocked on a solver response. Includes the solver's own
    /// parsing of everything buffered since the last response, which is
    /// precisely the cost a large encoding imposes.
    pub solver_time: Duration,
    /// Slowest single query, for spotting one pathological obligation hiding
    /// inside an otherwise cheap benchmark.
    pub slowest_query: Duration,
    pub sat: u64,
    pub unsat: u64,
    pub unknown: u64,
    /// Model extraction (`get-value`) round trips.
    pub model_queries: u64,
    /// Incremental-stack operations, as a proxy for how much the engine is
    /// reusing solver state rather than rebuilding it.
    pub pushes: u64,
    pub pops: u64,
    /// Solver processes spawned. High counts against low `check_sat_calls`
    /// means process startup is dominating.
    pub instances: u64,
}

impl EngineSmtStats {
    /// Total observed time attributable to this engine's SMT work.
    pub fn total_time(&self) -> Duration {
        self.encode_time + self.solver_time
    }

    /// Share of SMT time spent waiting on the solver rather than encoding.
    ///
    /// A low fraction with a large `bytes_emitted` is the signature of an
    /// encoder that is the bottleneck in its own right.
    pub fn solver_fraction(&self) -> f64 {
        let total = self.total_time().as_secs_f64();
        if total <= 0.0 {
            return 0.0;
        }
        self.solver_time.as_secs_f64() / total
    }

    /// Mean bytes per emitted command — the average size of a term or
    /// constraint. Grows when the encoder inlines rather than names.
    pub fn bytes_per_command(&self) -> f64 {
        if self.commands == 0 {
            return 0.0;
        }
        self.bytes_emitted as f64 / self.commands as f64
    }

    fn merge(&mut self, other: &EngineSmtStats) {
        if self.solver.is_empty() {
            self.solver = other.solver.clone();
        }
        self.bytes_emitted += other.bytes_emitted;
        self.commands += other.commands;
        self.asserts += other.asserts;
        self.encode_time += other.encode_time;
        self.check_sat_calls += other.check_sat_calls;
        self.solver_time += other.solver_time;
        self.slowest_query = self.slowest_query.max(other.slowest_query);
        self.sat += other.sat;
        self.unsat += other.unsat;
        self.unknown += other.unknown;
        self.model_queries += other.model_queries;
        self.pushes += other.pushes;
        self.pops += other.pops;
        self.instances += other.instances;
    }
}

/// Everything recorded during one roast run.
#[derive(Clone, Debug, Default)]
pub struct SmtProfile {
    by_engine: BTreeMap<String, EngineSmtStats>,
}

impl SmtProfile {
    pub fn record(&mut self, engine: &str, stats: &EngineSmtStats) {
        self.by_engine
            .entry(engine.to_string())
            .or_default()
            .merge(stats);
    }

    pub fn engines(&self) -> impl Iterator<Item = (&String, &EngineSmtStats)> {
        self.by_engine.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.by_engine.is_empty()
    }

    pub fn get(&self, engine: &str) -> Option<&EngineSmtStats> {
        self.by_engine.get(engine)
    }

    /// Summed across engines.
    pub fn totals(&self) -> EngineSmtStats {
        let mut out = EngineSmtStats::default();
        for s in self.by_engine.values() {
            out.merge(s);
        }
        out
    }

    /// Human-readable report.
    pub fn render_table(&self) -> String {
        if self.is_empty() {
            return "smt profile: no SMT activity recorded\n".to_string();
        }
        let mut out = String::new();
        out.push_str(&format!(
            "{:<14} {:>10} {:>8} {:>7} {:>9} {:>9} {:>7} {:>6} {:>6} {:>7}\n",
            "engine",
            "bytes",
            "cmds",
            "B/cmd",
            "encode s",
            "solve s",
            "checks",
            "sat",
            "unsat",
            "unkn"
        ));
        out.push_str(&"-".repeat(94));
        out.push('\n');
        for (name, s) in &self.by_engine {
            out.push_str(&format!(
                "{:<14} {:>10} {:>8} {:>7.1} {:>9.3} {:>9.3} {:>7} {:>6} {:>6} {:>7}\n",
                name,
                s.bytes_emitted,
                s.commands,
                s.bytes_per_command(),
                s.encode_time.as_secs_f64(),
                s.solver_time.as_secs_f64(),
                s.check_sat_calls,
                s.sat,
                s.unsat,
                s.unknown,
            ));
        }
        let t = self.totals();
        out.push_str(&"-".repeat(94));
        out.push('\n');
        out.push_str(&format!(
            "{:<14} {:>10} {:>8} {:>7.1} {:>9.3} {:>9.3} {:>7} {:>6} {:>6} {:>7}\n",
            "total",
            t.bytes_emitted,
            t.commands,
            t.bytes_per_command(),
            t.encode_time.as_secs_f64(),
            t.solver_time.as_secs_f64(),
            t.check_sat_calls,
            t.sat,
            t.unsat,
            t.unknown,
        ));
        out.push_str(&format!(
            "\n{:.0}% of SMT time spent in the solver; slowest single query {:.3}s\n",
            t.solver_fraction() * 100.0,
            t.slowest_query.as_secs_f64()
        ));
        out
    }

    /// Machine-readable output for the scaling harness.
    ///
    /// Hand-rolled rather than pulling in serde: the schema is a dozen integers
    /// and `roast-core` has no serialisation dependency today, which is worth
    /// more than the convenience.
    pub fn to_json(&self) -> String {
        let mut out = String::from("{\n  \"engines\": {\n");
        let n = self.by_engine.len();
        for (i, (name, s)) in self.by_engine.iter().enumerate() {
            out.push_str(&format!("    {}: {}", json_str(name), engine_json(s)));
            out.push_str(if i + 1 < n { ",\n" } else { "\n" });
        }
        out.push_str("  },\n");
        out.push_str(&format!("  \"total\": {}\n", engine_json(&self.totals())));
        out.push_str("}\n");
        out
    }
}

fn engine_json(s: &EngineSmtStats) -> String {
    format!(
        "{{\"solver\": {}, \"bytes_emitted\": {}, \"commands\": {}, \"asserts\": {}, \
         \"encode_seconds\": {:.6}, \"solver_seconds\": {:.6}, \"slowest_query_seconds\": {:.6}, \
         \"check_sat_calls\": {}, \"sat\": {}, \"unsat\": {}, \"unknown\": {}, \
         \"model_queries\": {}, \"pushes\": {}, \"pops\": {}, \"instances\": {}}}",
        json_str(&s.solver),
        s.bytes_emitted,
        s.commands,
        s.asserts,
        s.encode_time.as_secs_f64(),
        s.solver_time.as_secs_f64(),
        s.slowest_query.as_secs_f64(),
        s.check_sat_calls,
        s.sat,
        s.unsat,
        s.unknown,
        s.model_queries,
        s.pushes,
        s.pops,
        s.instances,
    )
}

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Handle shared between the profiled solver instances and the reporter.
///
/// `Arc<Mutex<..>>` because `SolverFactory` is `Send` and an engine may hold a
/// solver while the CLI holds the profile. Contention is irrelevant: the lock
/// is taken once per SMT command, which is orders of magnitude cheaper than the
/// I/O it is accounting for.
pub type ProfileHandle = Arc<Mutex<SmtProfile>>;

pub fn new_handle() -> ProfileHandle {
    Arc::new(Mutex::new(SmtProfile::default()))
}

/// Accumulates one solver instance's activity, flushing into the shared profile
/// when dropped.
///
/// Per-instance rather than locking the shared profile on every command, so the
/// hot path is an uncontended field increment.
#[derive(Debug)]
pub struct InstanceRecorder {
    engine: String,
    handle: Option<ProfileHandle>,
    stats: EngineSmtStats,
}

impl InstanceRecorder {
    pub fn new(engine: &str, solver: &str, handle: Option<ProfileHandle>) -> Self {
        let mut stats = EngineSmtStats {
            solver: solver.to_string(),
            ..Default::default()
        };
        if handle.is_some() {
            stats.instances = 1;
        }
        InstanceRecorder {
            engine: engine.to_string(),
            handle,
            stats,
        }
    }

    /// Whether anything is listening. Lets callers skip work when profiling is
    /// off.
    pub fn active(&self) -> bool {
        self.handle.is_some()
    }

    pub fn note_command(&mut self, text: &str) {
        if self.handle.is_none() {
            return;
        }
        // +1 for the newline `send` appends.
        self.stats.bytes_emitted += text.len() as u64 + 1;
        self.stats.commands += 1;
        if text.starts_with("(assert") {
            self.stats.asserts += 1;
        } else if text.starts_with("(push") {
            self.stats.pushes += 1;
        } else if text.starts_with("(pop") {
            self.stats.pops += 1;
        }
    }

    pub fn note_check_sat(&mut self, elapsed: Duration, response: &str) {
        if self.handle.is_none() {
            return;
        }
        self.stats.check_sat_calls += 1;
        self.stats.solver_time += elapsed;
        self.stats.slowest_query = self.stats.slowest_query.max(elapsed);
        match response {
            "sat" => self.stats.sat += 1,
            "unsat" => self.stats.unsat += 1,
            _ => self.stats.unknown += 1,
        }
    }

    pub fn note_model_query(&mut self, elapsed: Duration) {
        if self.handle.is_none() {
            return;
        }
        self.stats.model_queries += 1;
        self.stats.solver_time += elapsed;
    }

    /// Time spent in the engine itself, not blocked on the solver.
    pub fn note_encode_time(&mut self, elapsed: Duration) {
        if self.handle.is_none() {
            return;
        }
        self.stats.encode_time += elapsed;
    }

    /// Which engine this instance belongs to. Set after construction because
    /// the factory does not know who asked for the solver.
    pub fn set_engine(&mut self, engine: &str) {
        self.engine = engine.to_string();
    }
}

impl Drop for InstanceRecorder {
    fn drop(&mut self) {
        let Some(handle) = &self.handle else { return };
        if let Ok(mut profile) = handle.lock() {
            profile.record(&self.engine, &self.stats);
        }
    }
}

/// Record a whole batch script in one go — the shape the text encoders use.
pub fn record_batch(
    handle: &Option<ProfileHandle>,
    engine: &str,
    solver: &str,
    script: &str,
    encode_time: Duration,
    solver_time: Duration,
    response: &str,
) {
    let Some(handle) = handle else { return };
    let mut stats = EngineSmtStats {
        solver: solver.to_string(),
        bytes_emitted: script.len() as u64,
        commands: script.lines().filter(|l| l.starts_with('(')).count() as u64,
        asserts: script.lines().filter(|l| l.starts_with("(assert")).count() as u64,
        encode_time,
        check_sat_calls: 1,
        solver_time,
        slowest_query: solver_time,
        instances: 1,
        ..Default::default()
    };
    match response {
        "sat" => stats.sat = 1,
        "unsat" => stats.unsat = 1,
        _ => stats.unknown = 1,
    }
    if let Ok(mut profile) = handle.lock() {
        profile.record(engine, &stats);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stats(bytes: u64, cmds: u64) -> EngineSmtStats {
        EngineSmtStats {
            solver: "z3".into(),
            bytes_emitted: bytes,
            commands: cmds,
            encode_time: Duration::from_millis(10),
            solver_time: Duration::from_millis(30),
            check_sat_calls: 1,
            unsat: 1,
            ..Default::default()
        }
    }

    #[test]
    fn merging_accumulates_and_keeps_the_worst_query() {
        let mut p = SmtProfile::default();
        let mut a = stats(100, 10);
        a.slowest_query = Duration::from_millis(5);
        let mut b = stats(50, 5);
        b.slowest_query = Duration::from_millis(20);
        p.record("chc", &a);
        p.record("chc", &b);

        let s = p.get("chc").unwrap();
        assert_eq!(s.bytes_emitted, 150);
        assert_eq!(s.commands, 15);
        assert_eq!(s.check_sat_calls, 2);
        assert_eq!(
            s.slowest_query,
            Duration::from_millis(20),
            "the worst query is a max, not a sum"
        );
    }

    #[test]
    fn engines_are_reported_separately_and_summed() {
        let mut p = SmtProfile::default();
        p.record("chc", &stats(100, 10));
        p.record("smt-bmc", &stats(400, 40));

        assert_eq!(p.engines().count(), 2);
        let t = p.totals();
        assert_eq!(t.bytes_emitted, 500);
        assert_eq!(t.commands, 50);
    }

    #[test]
    fn bytes_per_command_exposes_an_inlining_encoder() {
        // The signature of substituting rather than naming: few commands,
        // each enormous.
        let inlining = stats(1_000_000, 4);
        let naming = stats(4_000, 100);
        assert!(inlining.bytes_per_command() > naming.bytes_per_command() * 100.0);
    }

    #[test]
    fn solver_fraction_is_bounded_and_zero_safe() {
        let s = stats(100, 10);
        assert!((s.solver_fraction() - 0.75).abs() < 1e-9);
        assert_eq!(EngineSmtStats::default().solver_fraction(), 0.0);
    }

    #[test]
    fn an_instance_recorder_flushes_on_drop() {
        let handle = new_handle();
        {
            let mut rec = InstanceRecorder::new("smt-bmc", "z3", Some(handle.clone()));
            rec.note_command("(assert (= x #x00000001))");
            rec.note_command("(push 1)");
            rec.note_check_sat(Duration::from_millis(7), "unsat");
        }
        let p = handle.lock().unwrap();
        let s = p.get("smt-bmc").unwrap();
        assert_eq!(s.commands, 2);
        assert_eq!(s.asserts, 1);
        assert_eq!(s.pushes, 1);
        assert_eq!(s.unsat, 1);
        assert_eq!(s.instances, 1);
        assert_eq!(s.bytes_emitted, 25 + 1 + 8 + 1);
    }

    #[test]
    fn recording_is_inert_when_profiling_is_off() {
        // The solver name is still filled in (it costs nothing), but no counter
        // moves, so the instrumentation is free when nobody is listening.
        let mut rec = InstanceRecorder::new("smt-bmc", "z3", None);
        rec.note_command("(assert true)");
        rec.note_check_sat(Duration::from_secs(1), "sat");
        rec.note_model_query(Duration::from_secs(1));
        rec.note_encode_time(Duration::from_secs(1));
        assert_eq!(
            rec.stats,
            EngineSmtStats {
                solver: "z3".into(),
                ..Default::default()
            }
        );
        assert!(!rec.active());
    }

    #[test]
    fn json_is_parseable_and_escapes_names() {
        let mut p = SmtProfile::default();
        p.record("smt\"bmc", &stats(10, 2));
        let js = p.to_json();
        assert!(js.contains("\\\"bmc"), "engine name must be escaped: {js}");
        assert!(js.contains("\"bytes_emitted\": 10"));
        assert!(js.contains("\"total\""));
    }

    #[test]
    fn an_empty_profile_renders_without_panicking() {
        let p = SmtProfile::default();
        assert!(p.render_table().contains("no SMT activity"));
        assert!(p.to_json().contains("\"engines\""));
    }
}
