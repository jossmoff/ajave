//! Answer "is this exact signature total?" for the allowlist validator.
//!
//! `tools/validate_jdk_allowlist.py` used to answer that question by scraping
//! `smt_bmc/explore.rs` for the class and descriptor strings. Two things were
//! wrong with that, and `CLAUDE.md` had already named the first:
//!
//! - A source-text check cannot distinguish overloads reliably. It looked in a
//!   2600-byte window after the class name, so an unrelated arm's descriptor
//!   could satisfy it.
//! - The table it was reading had *moved*. Everything is answered by
//!   `contract_of` now, and what remains in `explore.rs` is the test module —
//!   so the harness was matching its own test fixtures and reporting them as
//!   allowlist entries. It printed 27 "reachable wrong TRUEs" that did not
//!   exist, which is how a gate stops being read.
//!
//! Querying the real function removes the whole class of problem: there is one
//! declaration of what an external method does, and this asks it.
//!
//! Usage: `contract_query <class> <name> <desc>` — prints `total` or `partial`.
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        eprintln!("usage: contract_query <class> <name> <desc>");
        std::process::exit(2);
    }
    let c = ajave_models::contract_for(&args[0], &args[1], &args[2]);
    println!("{}", if c.is_total() { "total" } else { "partial" });
}
