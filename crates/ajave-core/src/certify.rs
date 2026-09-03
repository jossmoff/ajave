//! Independent checking of things we do not trust.
//!
//! The rule: no artifact reaches the reporter on an engine's authority alone.
//! FALSE is replayed on a real JVM; TRUE rests on invariants re-checked by a
//! separate, small, boring pass. Full verification of the verifier is a
//! multi-year project. Certificate checking gets most of the assurance now.

use crate::artifact::*;
use log::{debug, warn};
use ajave_ir::{ObligationKind, Program};

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
/// Supports `Int`/`Long`/`Boolean`/`Float`/`Double` nondet via bit-pattern
/// reinterpretation (`intBitsToFloat`, `longBitsToDouble`). String nondet
/// uses system properties (`ajave.str.N`).
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
    private static final long[] SEQ;
    private static int idx = 0;
    private static int strIdx = 0;
    static {
        String s = System.getProperty("ajave.seq", "");
        if (s.isEmpty()) {
            SEQ = new long[0];
        } else {
            String[] parts = s.split(",");
            SEQ = new long[parts.length];
            for (int i = 0; i < parts.length; i++) SEQ[i] = Long.parseLong(parts[i].trim());
        }
    }
    private static long next() {
        return idx < SEQ.length ? SEQ[idx++] : 0;
    }
    public static void assume(boolean condition) {
        if (!condition) Runtime.getRuntime().halt(1);
    }
    public static boolean nondetBoolean() { return next() != 0; }
    public static byte nondetByte() { return (byte) next(); }
    public static char nondetChar() { return (char) next(); }
    public static short nondetShort() { return (short) next(); }
    public static int nondetInt() { return (int) next(); }
    public static long nondetLong() { return next(); }
    public static float nondetFloat() { return Float.intBitsToFloat((int) next()); }
    public static double nondetDouble() { return Double.longBitsToDouble(next()); }
    public static String nondetString() {
        String val = System.getProperty("ajave.str." + strIdx, "");
        strIdx++;
        return val;
    }
    public static <T> T nondetObject(Class<T> type, ObjectFactory<T> factory) {
        // Try the factory; if null, try again with different nondet values.
        // The witness may not include factory-internal nondets, so we retry
        // a few times and fall back to reflection if still null.
        for (int attempt = 0; attempt < 8; attempt++) {
            T obj = factory.createObject();
            if (obj != null) return obj;
        }
        try { return type.getDeclaredConstructor().newInstance(); }
        catch (Exception e) { return null; }
    }
}
"#;

    const SHADOW_FACTORY_SRC: &'static str = r#"
package org.sosy_lab.sv_benchmarks;
public interface ObjectFactory<T> { T createObject(); }
"#;

    /// Compile the shadow class into a temp directory, returning its path for
    /// use as the front of the classpath. Cached per-process would be nicer;
    /// kept simple since replay runs are few and this is a one-off tool.
    fn build_shadow(
        &self,
    ) -> Result<(std::path::PathBuf, crate::scratch::ScratchDir), String> {
        // Unique per call and self-deleting. Naming it after the pid alone
        // meant a run could inherit a previous run's directory, and this one
        // goes at the front of the replay classpath — stale classes here flip a
        // witness between confirmed and refuted (#66).
        let scratch = crate::scratch::ScratchDir::new("ajave-shadow")
            .map_err(|e| format!("could not create shadow dir: {e}"))?;
        let dir = scratch.path().to_path_buf();
        debug!("jvm-replay: building shadow Verifier in {}", dir.display());
        let pkg_dir = dir.join("org/sosy_lab/sv_benchmarks");
        std::fs::create_dir_all(&pkg_dir).map_err(|e| e.to_string())?;
        let src = pkg_dir.join("Verifier.java");
        std::fs::write(&src, Self::SHADOW_SRC).map_err(|e| e.to_string())?;
        let factory_src = pkg_dir.join("ObjectFactory.java");
        std::fs::write(&factory_src, Self::SHADOW_FACTORY_SRC).map_err(|e| e.to_string())?;

        let out = std::process::Command::new(&self.javac)
            .arg("-d")
            .arg(&dir)
            .arg(&src)
            .arg(&factory_src)
            .output()
            .map_err(|e| format!("failed to run {}: {e}", self.javac))?;
        if !out.status.success() {
            return Err(format!(
                "shadow Verifier failed to compile: {}",
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        // The caller uses this as a classpath entry, so the guard has to
        // outlive the function; leaking it here would reinstate the bug.
        Ok((dir, scratch))
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

        // A witness that names a thread schedule cannot be certified here. We
        // can hand a stock JVM the nondet values via system properties, but we
        // cannot make it take a particular interleaving — so a run that fails
        // to reproduce tells us nothing about the witness, only that we got a
        // different schedule.
        //
        // Refuting on that basis would be wrong (the violation may be real),
        // and confirming would be worse (we would not have checked it). This
        // is genuinely Inconclusive until a schedule-aware certifier exists;
        // see docs/strategies/concurrency.md.
        if witness.needs_schedule() {
            debug!(
                "jvm-replay: {oref:?} carries a {}-slice schedule; \
                 cannot certify without schedule control",
                witness.schedule.len()
            );
            return CertResult::Inconclusive;
        }

        debug!("jvm-replay: certifying violation at {oref:?}");

        // `_shadow_guard` deletes the directory when this function returns.
        // Binding it to `_` instead would drop it immediately and remove the
        // classpath entry out from under the JVM.
        let (shadow_dir, _shadow_guard) = match self.build_shadow() {
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
        // Build the integer sequence for JVM replay, excluding string entries.
        // The shadow Verifier uses separate counters: `idx` for int/long/etc
        // (via next()) and `strIdx` for strings (via system properties).
        // String entries occupy a slot in nondet_sequence but the shadow
        // Verifier does NOT call next() for nondetString(), so we must skip them.
        let seq: Vec<String> = witness
            .entries
            .iter()
            .zip(witness.nondet_sequence.iter())
            .filter(|(e, _)| !matches!(e.value, ajave_ir::verdict::NondetValue::Str(_)))
            .map(|(_, v)| v.to_string())
            .collect();

        let mut cmd = std::process::Command::new(&self.java);
        // Assertions on **only** when certifying an assertion.
        //
        // `assert e;` evaluates `e` only with `-ea`. For no-runtime-exception
        // the property is evaluated with assertions disabled, so running the
        // replay with `-ea` executes code the property does not include — and
        // an exception thrown while evaluating an assert expression is then
        // read as a runtime exception the program can throw.
        //
        // That is exactly how `apachecli_eqchk` became a wrong FALSE (#86):
        // its harness ends `assert outSPF.equals(outJR);`, `outSPF` is null
        // when parsing fails, and evaluating the condition throws NPE. With
        // assertions disabled the condition is never evaluated and nothing is
        // thrown, which is why the task's expected verdict is true.
        if matches!(ob.kind, ObligationKind::Assertion) {
            cmd.arg("-ea");
        } else {
            cmd.arg("-da");
        }
        cmd.args(["-cp", &cp]);
        cmd.arg(format!("-Dajave.seq={}", seq.join(",")));

        // Pass string nondet values as individual system properties so the
        // shadow Verifier uses the exact strings from the witness.
        let mut str_idx = 0usize;
        for entry in &witness.entries {
            if let ajave_ir::verdict::NondetValue::Str(s) = &entry.value {
                cmd.arg(format!("-Dajave.str.{str_idx}={s}"));
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

        // Which exception names count as confirming this obligation?
        //
        // Demanding the single class `exception_class` predicts is too strict,
        // and refuses witnesses that crash the JVM exactly as intended:
        //
        //  * `String.charAt(i)` out of range throws
        //    `StringIndexOutOfBoundsException`, not `ArrayIndexOutOfBounds` —
        //    and the contract-seeded bounds checks use the `ArrayBounds` kind
        //    for both.
        //  * `ExplicitThrow` is seeded for any `athrow` of a known
        //    RuntimeException subclass, so the program raises
        //    `IllegalStateException` or `IllegalArgumentException` while we
        //    predicted the literal name `RuntimeException`.
        //
        // For the runtime-exception property what matters is that *some*
        // uncaught RuntimeException escaped `main`, which is precisely the
        // property under test. Accepting the family rather than one member
        // keeps that faithful while staying strict for assertions, where
        // `AssertionError` is the only correct outcome.
        let accepted: &[&str] = match ob.kind {
            ObligationKind::Assertion => &["AssertionError"],
            ObligationKind::ArrayBounds => &[
                "ArrayIndexOutOfBoundsException",
                "StringIndexOutOfBoundsException",
                "IndexOutOfBoundsException",
            ],
            ObligationKind::NullDeref => &["NullPointerException"],
            ObligationKind::DivByZero => &["ArithmeticException"],
            ObligationKind::NegArraySize => &[
                "NegativeArraySizeException",
                // `new StringBuilder(-1)` reports this instead.
                "IllegalArgumentException",
            ],
            ObligationKind::ClassCast => &["ClassCastException"],
            // A deadlock produces no exception — the program hangs — so no
            // stderr text can confirm it. `JvmReplay` cannot certify one at
            // all; the no-deadlock property is answered by the concurrency
            // engine directly.
            ObligationKind::Deadlock => &[],
            // Any RuntimeException subclass the program chose to raise.
            ObligationKind::ExplicitThrow => &[
                "RuntimeException",
                "IllegalStateException",
                "IllegalArgumentException",
                "UnsupportedOperationException",
                "NoSuchElementException",
                "ConcurrentModificationException",
                "NumberFormatException",
                "ArithmeticException",
                "IndexOutOfBoundsException",
                "NullPointerException",
            ],
        };

        // A halted-via-assume run exits 1 with no exception text -- that is
        // a real outcome of the JVM's own `Runtime.halt`, not our replay
        // failing, and it means this witness didn't actually reach the bug
        // (a stale trace, or an interpreter/JVM divergence). Refuted, not
        // Inconclusive: we have a definite answer, and it disagrees with us.
        let result = if !out.status.success()
            && accepted.iter().any(|e| stderr.contains(e))
        {
            CertResult::Confirmed
        } else {
            CertResult::Refuted
        };
        if result == CertResult::Confirmed {
            // Log the evidence for a *confirmation* too, not just a refusal.
            // A confirmation is what publishes FALSE and is therefore the one
            // that can cost -32; having diagnostics only for the harmless half
            // is backwards.
            let tail: String = stderr
                .lines()
                .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with("at "))
                .take(12)
                .collect::<Vec<_>>()
                .join(" ⏎ ");
            debug!(
                "jvm-replay: CONFIRMED kind={:?} exit={:?} MATCHED={:?} stderr={}",
                ob.kind,
                out.status.code(),
                accepted.iter().find(|e| stderr.contains(**e)),
                if tail.is_empty() { "(empty)" } else { &tail }
            );
        }
        if result == CertResult::Refuted {
            // What the JVM actually did, not merely that we disagreed with it.
            // Without this a refutation is indistinguishable from a bad
            // witness, a too-strict matcher, and a genuinely spurious
            // violation -- and those want three different fixes.
            let tail: String = stderr
                .lines()
                .filter(|l| !l.trim().is_empty())
                .take(2)
                .collect::<Vec<_>>()
                .join(" | ");
            debug!(
                "jvm-replay: REFUTED kind={:?} exit={:?} seq=[{}] strs={} entries={} \
                 stderr={}",
                ob.kind,
                out.status.code(),
                seq.join(","),
                str_idx,
                witness.entries.len(),
                if tail.is_empty() { "(empty)" } else { &tail }
            );
        }
        debug!("jvm-replay: {oref:?} -> {result:?}");
        result
    }
}
