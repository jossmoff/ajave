#!/usr/bin/env bash
# Thin wrapper so CI can call a single script.
# All logic lives in run-corpus.py.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/run-corpus.py "$@"
