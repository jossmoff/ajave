#!/usr/bin/env bash
# Asserts the crate dependency graph matches docs/architecture.md's isolation
# claims. This is not style enforcement -- it's the thing that would have
# caught, at commit time, an accidental `ajave-ir -> ajave-core` dependency
# (exactly the circular edge `Body::check_point` introduced during the
# original single-crate -> workspace split, before it was moved out).
#
# Run locally with `./scripts/check-boundaries.sh`; wired into CI as the
# `boundaries` job.
set -euo pipefail
cd "$(dirname "$0")/.."

# Bash 3.2 (macOS's default) has no associative arrays, and a check that only
# runs in CI is one nobody runs before pushing. A case statement is portable.
allowed_for() {
  case "$1" in
    ajave-ir)       echo "" ;;
    ajave-models)   echo "ajave-ir" ;;
    ajave-frontend) echo "ajave-ir ajave-models" ;;
    ajave-core)     echo "ajave-ir ajave-models" ;;
    ajave-engines)  echo "ajave-ir ajave-models ajave-core" ;;
    # IR reduction. Sits beside the frontend rather than under it: it rewrites
    # a `Body` and needs library contracts to know which calls are pure, but it
    # must not see the blackboard, or a reduction could depend on what an
    # engine has published and stop being a function of the program alone.
    ajave-opt)      echo "ajave-ir ajave-models" ;;
    ajave)          echo "ajave-ir ajave-models ajave-frontend ajave-core ajave-engines ajave-opt" ;;
    *)              echo "__MISSING__" ;;
  esac
}

fail=0
for dir in crates/*/; do
  toml="$dir/Cargo.toml"
  name=$(grep -m1 '^name = ' "$toml" | sed -E 's/name = "(.*)"/\1/')
  actual=$( (grep -oE '^ajave[a-z-]* = \{ path' "$toml" || true) | sed -E 's/ = .*//' | sort)
  expected=$(allowed_for "$name" | tr ' ' '\n' | sed '/^$/d' | sort)

  if [ "$actual" != "$expected" ]; then
    echo "boundary violation in $name:"
    echo "  expected deps: [$(allowed_for "$name")]"
    echo "  actual deps:   [$(echo "$actual" | tr '\n' ' ')]"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "crate graph matches docs/architecture.md"
else
  echo
  echo "If this dependency is intentional, update both Cargo.toml and the"
  echo "allowed_for map in this script (and explain why in docs/architecture.md --"
  echo "the whole point of this check is that the graph and the docs never"
  echo "silently drift apart)."
  exit 1
fi
