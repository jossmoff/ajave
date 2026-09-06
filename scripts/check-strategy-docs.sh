#!/usr/bin/env bash
# Every engine registered in the portfolio needs docs/strategies/<name>.md --
# see docs/README.md's "Adding a new strategy" section. This enforces the rule
# instead of leaving it a convention someone eventually forgets.
#
# The source of truth is the registration list in ajave-cli/src/main.rs, not
# the set of files in ajave-engines/src. Most modules there are shared
# machinery rather than strategies -- `smt_encode`, `smt_text`, `liveness`,
# `body_analysis`, `vclock` -- and demanding a strategy doc for a helper is how
# the previous version of this check ended up meaningless.
#
# It also read `crates/roast-engines`, a path that stopped existing at the
# 2026-08-25 rename, so it exited 1 on every run for weeks. A check nobody can
# pass is a check nobody reads.
set -euo pipefail
cd "$(dirname "$0")/.."

MAIN=crates/ajave-cli/src/main.rs

# Engines whose doc is still owed. Every entry is a known gap, not a licence:
# adding to this list needs a reason, and the list is meant to shrink.
KNOWN_GAPS="nra float_search ranges kinduction imc cegar"

fail=0
registered=$(grep -oE 'ajave_engines::[a-z_]+::[A-Za-z]+::new' "$MAIN" \
             | sed -E 's/ajave_engines::([a-z_]+)::.*/\1/' | sort -u)

for name in $registered; do
  doc="docs/strategies/${name}.md"
  [ -f "$doc" ] && continue
  if echo " $KNOWN_GAPS " | grep -q " $name "; then
    echo "known gap: $doc (engine is registered, doc is owed)"
    continue
  fi
  echo "MISSING $doc for the registered engine '$name'"
  fail=1
done

# A gap that has been filled must leave the list, or the list stops meaning
# anything.
for name in $KNOWN_GAPS; do
  if [ -f "docs/strategies/${name}.md" ]; then
    echo "stale KNOWN_GAPS entry: docs/strategies/${name}.md now exists; remove '$name' from the list in $0"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "every registered engine has a strategy doc, or is a recorded gap"
else
  exit 1
fi
