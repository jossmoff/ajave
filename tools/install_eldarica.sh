#!/usr/bin/env bash
# Install the Eldarica Horn solver for the `chc-eldarica` engine.
#
# Eldarica is a second Horn backend, not a faster one: it solves constrained
# Horn clauses by CEGAR over predicate abstraction, where z3's Spacer uses
# IC3/PDR. Each finds invariants the other does not, and the portfolio runs
# whichever is available -- `chc-eldarica` only ever sees obligations
# `chc-spacer` could not discharge, so having both costs nothing when the
# first succeeds.
#
# Installs a *native* build where one exists (no JVM, so no startup tax against
# the per-task budget), falling back to the JVM distribution otherwise.
#
# Everything lands under one directory and nothing is put on your PATH; the
# engine finds it via ROAST_ELDARICA or the default location below.
set -euo pipefail

VERSION="${ELDARICA_VERSION:-2.3}"
PREFIX="${ELDARICA_PREFIX:-$HOME/.local/share/ajave/eldarica}"
BASE="https://github.com/uuverifiers/eldarica/releases/download/v${VERSION}"

case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)  ASSET="eldarica-arm64-osx.gz";        NATIVE=1 ;;
    Linux/x86_64)  ASSET="eldarica-x86-linux-static.gz"; NATIVE=1 ;;
    *)             ASSET="eldarica-bin-${VERSION}.zip";  NATIVE=0 ;;
esac

mkdir -p "$PREFIX"
cd "$PREFIX"
echo "Installing Eldarica $VERSION ($ASSET) into $PREFIX"

if [ "$NATIVE" = "1" ]; then
    curl -fsSL "$BASE/$ASSET" -o eldarica.gz
    gunzip -f eldarica.gz
    chmod +x eldarica
    BIN="$PREFIX/eldarica"
else
    # The JVM distribution needs a `java` on PATH.
    command -v java >/dev/null || { echo "no java on PATH, needed for the JVM build" >&2; exit 1; }
    curl -fsSL "$BASE/$ASSET" -o eldarica.zip
    unzip -qo eldarica.zip
    BIN="$PREFIX/eldarica-${VERSION}/eld"
    chmod +x "$BIN"
fi

echo "Checking it runs..."
printf '(set-logic HORN)\n(declare-fun p (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (p x))))\n(assert (forall ((x Int)) (=> (and (p x) (> x 0)) false)))\n(check-sat)\n' > "$PREFIX/smoke.smt2"
if OUT=$("$BIN" "$PREFIX/smoke.smt2" 2>&1) && echo "$OUT" | grep -qE '^(sat|unsat|unknown)$'; then
    echo "  ok: $(echo "$OUT" | grep -E '^(sat|unsat|unknown)$' | head -1)"
else
    echo "  FAILED to get a verdict:" >&2
    echo "$OUT" | head -20 >&2
    exit 1
fi

echo
echo "Installed: $BIN"
echo "ajave finds it automatically at the default location, or set:"
echo "  export ROAST_ELDARICA=$BIN"
