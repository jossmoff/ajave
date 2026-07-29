#!/usr/bin/env bash
# Asserts the crate dependency graph matches docs/architecture.md's isolation
# claims. This is not style enforcement -- it's the thing that would have
# caught, at commit time, an accidental `roast-ir -> roast-core` dependency
# (exactly the circular edge `Body::check_point` introduced during the
# original single-crate -> workspace split, before it was moved out).
#
# Run locally with `./scripts/check-boundaries.sh`; wired into CI as the
# `boundaries` job.
set -euo pipefail
cd "$(dirname "$0")/.."

declare -A ALLOWED=(
  [roast-ir]=""
  [roast-models]="roast-ir"
  [roast-frontend]="roast-ir roast-models"
  [roast-core]="roast-ir roast-models"
  [roast-engines]="roast-ir roast-models roast-core"
  [roast]="roast-ir roast-frontend roast-core roast-engines"
)

fail=0
for dir in crates/*/; do
  toml="$dir/Cargo.toml"
  name=$(grep -m1 '^name = ' "$toml" | sed -E 's/name = "(.*)"/\1/')
  actual=$( (grep -oE '^roast[a-z-]* = \{ path' "$toml" || true) | sed -E 's/ = .*//' | sort)
  expected=$(echo "${ALLOWED[$name]-__MISSING__}" | tr ' ' '\n' | sed '/^$/d' | sort)

  if [ "$actual" != "$expected" ]; then
    echo "boundary violation in $name:"
    echo "  expected deps: [${ALLOWED[$name]-<crate not registered in this script>}]"
    echo "  actual deps:   [$(echo "$actual" | tr '\n' ' ')]"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "crate graph matches docs/architecture.md"
else
  echo
  echo "If this dependency is intentional, update both Cargo.toml and the"
  echo "ALLOWED map in this script (and explain why in docs/architecture.md --"
  echo "the whole point of this check is that the graph and the docs never"
  echo "silently drift apart)."
  exit 1
fi
