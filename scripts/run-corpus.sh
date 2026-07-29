#!/usr/bin/env bash
# Runs roast against a task corpus and checks for soundness regressions.
#
# A soundness regression is a wrong verdict: TRUE when the expected is false,
# or FALSE when the expected is true. UNKNOWN is never wrong -- only incomplete.
# Exits 1 if any wrong verdicts are found.
#
# Usage:
#   ./scripts/run-corpus.sh [CORPUS_DIR]
#
# CORPUS_DIR defaults to tasks/. To run against the full jbmc-regression set:
#   ./scripts/run-corpus.sh /path/to/sv-benchmarks/java/jbmc-regression
set -euo pipefail
cd "$(dirname "$0")/.."

ROAST="${ROAST:-./target/release/roast}"
if [ ! -x "$ROAST" ]; then
  ROAST="./target/debug/roast"
fi
if [ ! -x "$ROAST" ]; then
  echo "roast binary not found; run 'cargo build' first" >&2
  exit 1
fi

CORPUS_DIR="${1:-tasks}"

# Python resolves YAML input_files relative to each task YAML's directory,
# printing lines: "<expected_verdict> <abs_path1> <abs_path2> ..."
TASK_LIST=$(python3 - "$CORPUS_DIR" <<'PYEOF'
import os, sys, yaml

corpus = sys.argv[1]
for root, dirs, files in os.walk(corpus):
    dirs.sort()
    for fname in sorted(files):
        if not fname.endswith('.yml'):
            continue
        yml_path = os.path.join(root, fname)
        try:
            with open(yml_path) as f:
                d = yaml.safe_load(f)
        except Exception:
            continue
        props = d.get('properties', [])
        expected = None
        for p in props:
            if 'expected_verdict' in p:
                expected = str(p['expected_verdict']).lower()
                break
        if expected is None:
            continue
        input_files = d.get('input_files', [])
        abs_inputs = []
        for rel in input_files:
            abs_p = os.path.normpath(os.path.join(root, rel))
            if os.path.exists(abs_p):
                abs_inputs.append(abs_p)
        if not abs_inputs:
            continue
        print(expected + ' ' + ' '.join(abs_inputs))
PYEOF
)

if [ -z "$TASK_LIST" ]; then
  echo "no tasks found under $CORPUS_DIR" >&2
  exit 1
fi

total=0
correct=0
wrong=0
unknown=0
wrong_out=""

while IFS= read -r line; do
  [ -z "$line" ] && continue
  expected="${line%% *}"
  rest="${line#* }"

  # Split rest into an array of paths (space-separated from python output).
  # Use eval carefully: paths come from our own Python, not user input.
  IFS=' ' read -r -a paths <<< "$rest"

  verdict=$(timeout 30 "$ROAST" "${paths[@]}" 2>/dev/null || echo "TIMEOUT")

  total=$((total + 1))
  case "$verdict/$expected" in
    FALSE/false|TRUE/true)
      correct=$((correct + 1)) ;;
    TRUE/false|FALSE/true)
      wrong=$((wrong + 1))
      wrong_out="$wrong_out\n  WRONG  expected=$expected got=$verdict  ${paths[0]}" ;;
    *)
      unknown=$((unknown + 1)) ;;
  esac
done <<< "$TASK_LIST"

echo "corpus: $total tasks, $correct correct, $unknown unknown/timeout, $wrong wrong"

if [ "$wrong" -gt 0 ]; then
  echo ""
  echo "SOUNDNESS REGRESSIONS (wrong verdicts):"
  printf "%b\n" "$wrong_out"
  exit 1
fi

echo "no wrong verdicts -- corpus clean"
