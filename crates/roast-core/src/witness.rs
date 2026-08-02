//! SV-COMP witness format 2.0 emitter.
//!
//! Produces YAML violation witnesses that external validators can check.
//! Each `Verifier.nondet*()` call in the witness is encoded as an assumption
//! waypoint specifying the return value, so a validator can replay the
//! execution and confirm the violation independently.
//!
//! String values are emitted as Java string literals (`\result == "hello"`)
//! so validators that understand Java expressions can parse them directly.

use roast_ir::verdict::{NondetEntry, NondetValue, Witness};
use roast_ir::ObligationKind;

/// Information about the task being verified, needed for witness metadata.
pub struct TaskInfo<'a> {
    pub input_files: &'a [String],
    pub specification: &'a str,
}

/// Information about the violated obligation.
pub struct ViolationInfo {
    pub kind: ObligationKind,
    pub line: Option<u16>,
}

/// Emit a violation witness in SV-COMP witness format 2.0 (YAML).
///
/// Returns the YAML content as a string. The caller writes it to a file.
pub fn emit_violation_yaml(
    witness: &Witness,
    task: &TaskInfo<'_>,
    violation: &ViolationInfo,
) -> String {
    let mut out = String::new();

    let uuid = make_uuid(witness);
    let timestamp = iso8601_now();

    out.push_str("- entry_type: violation_sequence\n");
    out.push_str("  metadata:\n");
    out.push_str("    format_version: \"2.0\"\n");
    out.push_str(&format!("    uuid: \"{uuid}\"\n"));
    out.push_str(&format!("    creation_time: \"{timestamp}\"\n"));
    out.push_str("    producer:\n");
    out.push_str("      name: \"roast\"\n");
    out.push_str(&format!(
        "      version: \"{}\"\n",
        env!("CARGO_PKG_VERSION")
    ));
    out.push_str("    task:\n");
    out.push_str("      input_files:\n");
    for f in task.input_files {
        out.push_str(&format!("        - \"{f}\"\n"));
    }
    out.push_str(&format!(
        "      specification: \"{}\"\n",
        yaml_escape(task.specification)
    ));
    out.push_str("      data_model: LP64\n");
    out.push_str("      language: Java\n");

    out.push_str("  content:\n");

    if witness.entries.is_empty() {
        // No nondet calls — the violation is on a fixed path.
        // Emit a single target waypoint at the violation line.
        out.push_str("    - segment:\n");
        emit_target_waypoint(&mut out, &violation);
    } else {
        out.push_str("    - segment:\n");
        for entry in &witness.entries {
            emit_assumption_waypoint(&mut out, entry);
        }
        emit_target_waypoint(&mut out, &violation);
    }

    out
}

fn emit_assumption_waypoint(out: &mut String, entry: &NondetEntry) {
    let constraint = format_constraint(entry);
    out.push_str("        - waypoint:\n");
    out.push_str("            type: assumption\n");
    out.push_str("            constraint:\n");
    out.push_str(&format!(
        "              value: \"{}\"\n",
        yaml_escape(&constraint)
    ));
    out.push_str("              format: java_expression\n");
    if let Some(line) = entry.line {
        out.push_str("            location:\n");
        out.push_str(&format!("              line: {line}\n"));
    }
    out.push_str("            action: follow\n");
}

fn emit_target_waypoint(out: &mut String, violation: &ViolationInfo) {
    out.push_str("        - waypoint:\n");
    out.push_str("            type: target\n");
    if let Some(line) = violation.line {
        out.push_str("            location:\n");
        out.push_str(&format!("              line: {line}\n"));
    }
    out.push_str("            action: follow\n");
}

/// Format the constraint for a nondet entry as a Java expression.
fn format_constraint(entry: &NondetEntry) -> String {
    match &entry.value {
        NondetValue::Int(v) => format!("\\result == {v}"),
        NondetValue::Long(v) => format!("\\result == {v}L"),
        NondetValue::Bool(v) => {
            if *v {
                "\\result == true".to_string()
            } else {
                "\\result == false".to_string()
            }
        }
        NondetValue::Str(s) => format!("\\result == {}", java_string_literal(s)),
    }
}

/// Encode a string as a Java string literal, escaping special characters.
fn java_string_literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_ascii_graphic() || c == ' ' => out.push(c),
            c => {
                // Unicode escape for non-ASCII.
                for unit in c.encode_utf16(&mut [0u16; 2]) {
                    out.push_str(&format!("\\u{unit:04x}"));
                }
            }
        }
    }
    out.push('"');
    out
}

/// Produce a deterministic UUID-like identifier from the witness content.
/// Not a real UUID v4, but unique enough for witness identification.
fn make_uuid(witness: &Witness) -> String {
    let mut h: u64 = 0xcbf29ce484222325;
    for &v in &witness.nondet_sequence {
        h ^= v as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    for entry in &witness.entries {
        if let NondetValue::Str(s) = &entry.value {
            for b in s.bytes() {
                h ^= b as u64;
                h = h.wrapping_mul(0x100000001b3);
            }
        }
    }
    let a = (h >> 32) as u32;
    let b = (h & 0xffff) as u16;
    let c = ((h >> 16) & 0x0fff) as u16 | 0x4000; // version 4
    let d = ((h >> 48) & 0x3f) as u8 | 0x80; // variant 1
    let e = (h & 0xff) as u8;
    let f = h.wrapping_mul(0x517cc1b727220a95);
    format!(
        "{a:08x}-{b:04x}-{c:04x}-{d:02x}{e:02x}-{f:012x}",
        f = f & 0xffffffffffff
    )
}

fn yaml_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// ISO 8601 timestamp without external dependencies.
fn iso8601_now() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    // Manual UTC breakdown — avoids a chrono/time dependency.
    let days = secs / 86400;
    let day_secs = secs % 86400;
    let h = day_secs / 3600;
    let m = (day_secs % 3600) / 60;
    let s = day_secs % 60;
    // Days since 1970-01-01 -> y/m/d (civil calendar).
    let (y, mo, d) = days_to_ymd(days as i64);
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{m:02}:{s:02}+00:00")
}

fn days_to_ymd(days: i64) -> (i64, u32, u32) {
    // Algorithm from Howard Hinnant (public domain).
    let z = days + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as u32;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y, m, d)
}
