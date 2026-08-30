//! Unique temporary directories that delete themselves.
//!
//! # Why this exists
//!
//! Two temp directories were named after the process id alone —
//! `ajave-build-{pid}` for compiled benchmark classes and `ajave-shadow-{pid}`
//! for the replay `Verifier` — created with `create_dir_all`, and never
//! removed. Three properties combined into a correctness bug:
//!
//! 1. **The OS reuses pids.** A later run can be handed the pid of an earlier
//!    one.
//! 2. **`create_dir_all` succeeds on an existing directory** and leaves its
//!    contents alone.
//! 3. **Nothing ever deleted them**, so every run left one behind.
//!
//! A run that inherited a stale directory therefore compiled its own sources
//! *alongside* another task's leftover `.class` files, and `collect_classes`
//! returned the union — so the verifier analysed a program that was never
//! submitted. For the shadow directory the effect is worse in kind: it sits at
//! the *front* of the replay classpath, so stale classes there can flip a
//! witness between confirmed and refuted.
//!
//! Observed as `objects14` returning FALSE on 4 of 10 identical runs and
//! UNKNOWN on the other 6, which stopped the moment the stale directories were
//! swept (#66). A verifier whose answer depends on what a previous run left in
//! `/tmp` cannot be trusted, and no score delta measured across such runs means
//! anything.
//!
//! A `ScratchDir` is unique by construction and removes itself on drop.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Distinguishes directories created within the same process in the same
/// nanosecond — the clock is not guaranteed to advance between two calls.
static COUNTER: AtomicU64 = AtomicU64::new(0);

/// A temporary directory that is unique to this run and deleted on drop.
///
/// Deliberately not `Clone`: two owners would mean two drops, and the second
/// would delete a directory the first may still be using.
#[derive(Debug)]
pub struct ScratchDir {
    path: PathBuf,
    keep: bool,
}

impl ScratchDir {
    /// Create a new directory under the system temp dir with the given prefix.
    ///
    /// Uses `create_dir`, which **fails** if the path exists, rather than
    /// `create_dir_all`, which does not. That is the point: inheriting an
    /// existing directory is the bug this type prevents, so a collision must
    /// retry with a fresh name rather than silently reuse.
    pub fn new(prefix: &str) -> std::io::Result<ScratchDir> {
        let base = std::env::temp_dir();
        let pid = std::process::id();
        let mut last_err = None;
        for _ in 0..64 {
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = base.join(format!("{prefix}-{pid}-{nanos:x}-{n:x}"));
            match std::fs::create_dir(&path) {
                Ok(()) => {
                    return Ok(ScratchDir {
                        path,
                        keep: keep_scratch(),
                    })
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    last_err = Some(e);
                    continue;
                }
                Err(e) => return Err(e),
            }
        }
        Err(last_err.unwrap_or_else(|| {
            std::io::Error::other("could not create a unique scratch directory")
        }))
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Keep the directory instead of deleting it. For debugging a failed run.
    pub fn keep(&mut self) {
        self.keep = true;
    }
}

/// `AJAVE_KEEP_SCRATCH=1` preserves scratch directories for inspection.
/// Off by default — leaking them is what caused the bug above.
fn keep_scratch() -> bool {
    std::env::var("AJAVE_KEEP_SCRATCH")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false)
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        if self.keep {
            return;
        }
        // Best effort: a failure here must not mask the real result, and the
        // unique name means a leftover cannot be picked up by a later run.
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_directory_is_distinct() {
        let a = ScratchDir::new("ajave-test").unwrap();
        let b = ScratchDir::new("ajave-test").unwrap();
        assert_ne!(
            a.path(),
            b.path(),
            "two scratch dirs in one process shared a path; a pid-only name did \
             exactly this and let one run read another's classes"
        );
        assert!(a.path().is_dir() && b.path().is_dir());
    }

    #[test]
    fn directory_is_removed_on_drop() {
        let path = {
            let d = ScratchDir::new("ajave-test").unwrap();
            d.path().to_path_buf()
        };
        assert!(
            !path.exists(),
            "scratch dir outlived its owner; leaked dirs are what a later run \
             with a recycled pid picked up"
        );
    }

    #[test]
    fn keep_suppresses_removal() {
        let path = {
            let mut d = ScratchDir::new("ajave-test").unwrap();
            d.keep();
            d.path().to_path_buf()
        };
        assert!(path.exists());
        let _ = std::fs::remove_dir_all(&path);
    }

    #[test]
    fn a_new_directory_is_empty() {
        // The whole failure was inheriting another run's contents.
        let d = ScratchDir::new("ajave-test").unwrap();
        assert_eq!(std::fs::read_dir(d.path()).unwrap().count(), 0);
    }
}
