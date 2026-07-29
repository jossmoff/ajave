#!/usr/bin/env bash
# Every module in roast-engines/src (excluding lib.rs) is a strategy, and every
# strategy needs docs/strategies/<name>.md before it's real -- see
# docs/README.md's "Adding a new strategy" section. This is what enforces
# that rule instead of leaving it as a convention someone eventually forgets.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0
for src in crates/roast-engines/src/*.rs; do
  name=$(basename "$src" .rs)
  [ "$name" = "lib" ] && continue
  doc="docs/strategies/${name}.md"
  if [ ! -f "$doc" ]; then
    echo "missing $doc for crates/roast-engines/src/${name}.rs"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "every strategy in roast-engines/src/ has a doc"
else
  exit 1
fi
