//! Independent checking of things we do not trust.
//!
//! The rule: no artifact reaches the reporter on an engine's authority alone.
//! FALSE is replayed on a real JVM; TRUE rests on invariants re-checked by a
//! separate, small, boring pass. Full verification of the verifier is a
//! multi-year project. Certificate checking gets most of the assurance now.

use crate::artifact::*;
use log::{debug, warn};
use roast_ir::{ObligationKind, Program};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CertResult {
    /// Independently confirmed.
    Confirmed,
    /// Independently contradicted. This is always a bug in us, and it is far
    /// better to find it here than in the competition results table.
    Refuted,
    /// The certifier could not decide; the artifact stays uncertified and the
    /// obligation cannot reach a final status on the strength of it.
    Inconclusive,
}

pub trait Certifier {
    fn name(&self) -> &'static str;
    fn certify(&self, artifact: &Tagged, prog: &Program) -> CertResult;
}

/// Replays a violation witness on a real JVM and checks that the expected
/// exception actually fires.
///
/// This is the payoff of the whole design: a confirmed FALSE is correct
/// *independently of whether our IR, our solver or our semantics are right*.
/// The mechanism is a shadow `Verifier` class -- same package, same method
/// signatures as the real one, but deterministic: it pops values from the
/// recorded witness sequence instead of calling `Random`. Placed earlier on
/// the classpath than the task's own copy, it shadows it, so `Main` runs
/// completely unmodified against inputs we chose instead of random ones.
///
/// Scoped to `Int`/`Long`/`Boolean` nondet, which is everything the concrete
/// engine's witnesses currently contain (see `engines::concrete`). A witness
/// touching `nondetFloat`/`nondetDouble`/`nondetString` returns `Inconclusive`
/// rather than guessing at a replay -- the honest answer, not a wrong one.
pub struct JvmReplay {
    pub java: String,
    pub javac: String,
    pub classpath: String,
}

impl JvmReplay {
    pub fn new(classpath: impl Into<String>) -> Self {
        JvmReplay {
            java: "java".into(),
            javac: "javac".into(),
            classpath: classpath.into(),
        }
    }

    const SHADOW_SRC: &'static str = r#"
package org.sosy_lab.sv_benchmarks;

public final class Verifier {
    private static final int[] SEQ;
    private static int idx = 0;
    private static int strIdx = 0;
    static {
        String s = System.getProperty("roast.seq", "");
        if (s.isEmpty()) {
            SEQ = new int[0];
        } else {
            String[] parts = s.split(",");
            SEQ = new int[parts.length];
            for (int i = 0; i < parts.length; i++) SEQ[i] = Integer.parseInt(parts[i].trim());
        }
    }
    private static int next() {
        return idx < SEQ.length ? SEQ[idx++] : 0;
    }
    public static void assume(boolean condition) {
        if (!condition) Runtime.getRuntime().halt(1);
    }
    public static boolean nondetBoolean() { return next() != 0; }
    public static byte nondetByte() { return (byte) next(); }
    public static char nondetChar() { return (char) next(); }
    public static short nondetShort() { return (short) next(); }
    public static int nondetInt() { return next(); }
    public static long nondetLong() { return next(); }
    public static float nondetFloat() { return next(); }
    public static double nondetDouble() { return next(); }
    public static String nondetString() {
        String val = System.getProperty("roast.str." + strIdx, "");
        strIdx++;
        return val;
    }
}
"#;

    /// Compile the shadow class into a temp directory, returning its path for
    /// use as the front of the classpath. Cached per-process would be nicer;
    /// kept simple since replay runs are few and this is a one-off tool.
    fn build_shadow(&self) -> Result<std::path::PathBuf, String> {
        let dir = std::env::temp_dir().join(format!("roast-shadow-{}", std::process::id()));
        debug!("jvm-replay: building shadow Verifier in {}", dir.display());
        let pkg_dir = dir.join("org/sosy_lab/sv_benchmarks");
        std::fs::create_dir_all(&pkg_dir).map_err(|e| e.to_string())?;
        let src = pkg_dir.join("Verifier.java");
        std::fs::write(&src, Self::SHADOW_SRC).map_err(|e| e.to_string())?;

        let out = std::process::Command::new(&self.javac)
            .arg("-d")
            .arg(&dir)
            .arg(&src)
            .output()
            .map_err(|e| format!("failed to run {}: {e}", self.javac))?;
        if !out.status.success() {
            return Err(format!(
                "shadow Verifier failed to compile: {}",
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        Ok(dir)
    }
}

impl Certifier for JvmReplay {
    fn name(&self) -> &'static str {
        "jvm-replay"
    }

    fn certify(&self, artifact: &Tagged, prog: &Program) -> CertResult {
        let Artifact::Status(oref, Status::Violated { witness, .. }) = &artifact.artifact else {
            return CertResult::Inconclusive;
        };
        let Some(body) = prog.body(&oref.method) else {
            return CertResult::Inconclusive;
        };
        let ob = body.obligation(oref.id);

        debug!("jvm-replay: certifying violation at {oref:?}");

        let shadow_dir = match self.build_shadow() {
            Ok(d) => d,
            Err(e) => {
                warn!("jvm-replay: {e}");
                return CertResult::Inconclusive;
            }
        };

        let cp = format!(
            "{}{}{}",
            shadow_dir.display(),
            if cfg!(windows) { ";" } else { ":" },
            self.classpath
        );
        let seq: Vec<String> = witness
            .nondet_sequence
            .iter()
            .map(|v| v.to_string())
            .collect();

        let mut cmd = std::process::Command::new(&self.java);
        cmd.args(["-ea", "-cp", &cp]);
        cmd.arg(format!("-Droast.seq={}", seq.join(",")));

        // Pass string nondet values as individual system properties so the
        // shadow Verifier uses the exact strings from the witness.
        let mut str_idx = 0usize;
        for entry in &witness.entries {
            if let roast_ir::verdict::NondetValue::Str(s) = &entry.value {
                cmd.arg(format!("-Droast.str.{str_idx}={s}"));
                str_idx += 1;
            }
        }

        cmd.arg("Main");
        let out = cmd.output();

        let out = match out {
            Ok(o) => o,
            Err(e) => {
                warn!("jvm-replay: failed to run {}: {e}", self.java);
                return CertResult::Inconclusive;
            }
        };

        let stderr = String::from_utf8_lossy(&out.stderr);
        let expected = match ob.kind {
            ObligationKind::Assertion => "AssertionError",
            _ => roast_models::exception_class(ob.kind)
                .and_then(|c| c.rsplit('/').next())
                .unwrap_or("Exception"),
        };

        // A halted-via-assume run exits 1 with no exception text -- that is
        // a real outcome of the JVM's own `Runtime.halt`, not our replay
        // failing, and it means this witness didn't actually reach the bug
        // (a stale trace, or an interpreter/JVM divergence). Refuted, not
        // Inconclusive: we have a definite answer, and it disagrees with us.
        let result = if !out.status.success() && stderr.contains(expected) {
            CertResult::Confirmed
        } else {
            CertResult::Refuted
        };
        debug!("jvm-replay: {oref:?} -> {result:?}");
        result
    }
}
