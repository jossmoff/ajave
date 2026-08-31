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

# Orphaned solvers and JVMs: parent gone (ppid 1), so nothing owns them.
#
# A bare "z3"/"java" pattern is too wide -- it would match your own work -- but
# an *orphaned* one is ours by construction: a live run still owns its children,
# and nothing else here spawns them. Killing the harness from outside (pkill on
# the wrapper) bypasses procguard's signal handlers, which is exactly how five
# z3 processes ended up spinning at 99% CPU each with no parent.
orphans=$(ps -A -o pid=,ppid=,command= | awk '$2==1 && ($3~/z3$/ || $3~/cvc5$/ || $0~/ajave-shadow|ajave-build/){print $1}')
if [ -n "$orphans" ]; then
  n=$(echo "$orphans" | wc -w | tr -d ' ')
  echo "  orphaned solvers/JVMs: $n"
  found=$((found + n))
  [ "$DRY" = "0" ] && echo "$orphans" | xargs kill -9 2>/dev/null
fi

# Only the directories a run actually creates. A blanket ajave-* glob also
# matched /tmp/ajave-runs, this harness's own log directory, and deleted it.
dirs=$( { ls -d "${TMPDIR:-/tmp}"/ajave-build-* "${TMPDIR:-/tmp}"/ajave-shadow-* \
                /tmp/ajave-build-* /tmp/ajave-shadow-* ; } 2>/dev/null | sort -u )
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
