#!/usr/bin/env bash
# Kill anything this project leaked and remove its temp directories.
#
# Run after an interrupted benchmark run, or any time the machine feels slow.
# A leaked solver or JVM holds hundreds of megabytes and keeps running
# indefinitely; enough of them exhausted this machine's memory and froze it.
#
#   tools/cleanup.sh          # report and clean
#   tools/cleanup.sh --dry    # report only
set -uo pipefail
DRY=0; [ "${1:-}" = "--dry" ] && DRY=1

echo "load: $(sysctl -n vm.loadavg 2>/dev/null || uptime)"

found=0
report_and_kill() {
  local label="$1" pattern="$2"
  local pids
  pids=$(pgrep -f "$pattern" 2>/dev/null || true)
  [ -z "$pids" ] && return
  local n; n=$(echo "$pids" | wc -w | tr -d ' ')
  echo "  $label: $n"
  found=$((found + n))
  [ "$DRY" = "1" ] && return
  # shellcheck disable=SC2086
  kill -9 $pids 2>/dev/null || true
}

# Only patterns unique to this project — never a bare "java" or "z3", which
# would kill the user's own work.
report_and_kill "ajave JVM replays" "ajave-shadow|ajave-build"
report_and_kill "ajave processes"   "target/release/ajave"
report_and_kill "benchmark runners" "tools/bench.py|smoke_test.py|score_full.py"

dirs=$( { ls -d "${TMPDIR:-/tmp}"/ajave-* /tmp/ajave-* ; } 2>/dev/null | sort -u )
if [ -n "$dirs" ]; then
  n=$(echo "$dirs" | wc -l | tr -d ' ')
  echo "  temp dirs: $n"
  [ "$DRY" = "0" ] && echo "$dirs" | xargs rm -rf 2>/dev/null
fi

if [ "$found" = "0" ] && [ -z "$dirs" ]; then
  echo "  nothing to clean"
elif [ "$DRY" = "1" ]; then
  echo "(dry run — nothing killed)"
else
  echo "cleaned"
fi
