#!/usr/bin/env bash
# Every verification *strategy* in roast-engines needs docs/strategies/<name>.md
# before it's real -- see docs/README.md's "Adding a new strategy" section. This
# is what enforces that rule instead of leaving it as a convention someone
# eventually forgets.
#
# A strategy is a module that implements `Engine` or `Cpa`, not simply a file in
# the crate. Globbing `src/*.rs` (the old rule) got this wrong in both
# directions: it demanded docs for shared helpers like `smt_text` and
# `body_analysis`, which are not techniques, and it silently skipped `smt_bmc/`
# because a directory module does not match `*.rs` -- so the one engine that
# *did* have a doc was the one never checked.
set -euo pipefail
cd "$(dirname "$0")/.."

src_dir="crates/roast-engines/src"

# A module is a strategy iff its root file implements Engine or Cpa. Handles
# both `foo.rs` and `foo/mod.rs`.
is_strategy() {
  grep -qE '^[[:space:]]*impl([[:space:]]*<[^>]*>)?[[:space:]]+(roast_core::(engine::|cpa::)?)?(Engine|Cpa)[[:space:]]+for[[:space:]]' "$1"
}

strategies=()
for entry in "$src_dir"/*; do
  name=$(basename "$entry" .rs)
  [ "$name" = "lib" ] && continue

  if [ -f "$entry" ]; then
    root="$entry"
  elif [ -d "$entry" ]; then
    root="$entry/mod.rs"
    [ -f "$root" ] || continue
  else
    continue
  fi

  if is_strategy "$root"; then
    strategies+=("$name")
  fi
done

if [ "${#strategies[@]}" -eq 0 ]; then
  echo "no strategies found under $src_dir -- has the Engine/Cpa trait been renamed?"
  exit 1
fi

fail=0
for name in "${strategies[@]}"; do
  doc="docs/strategies/${name}.md"
  if [ ! -f "$doc" ]; then
    echo "missing $doc for the strategy in $src_dir/${name}"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "every strategy in $src_dir has a doc (${#strategies[@]} checked: ${strategies[*]})"
else
  echo
  echo "Only modules implementing Engine or Cpa are checked. A shared helper"
  echo "needs no strategy doc; if this fired on one, it is not a helper."
  exit 1
fi
