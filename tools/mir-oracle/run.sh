#!/bin/sh
# Build and run the `rustc_public` MIR oracle over the corpora the gate uses.
#
# This is the one place in the repository that needs a nightly toolchain with the
# `rustc-dev` component, so it is kept out of `scripts/gate.sh`'s main build and
# invoked as its own gate. It exits:
#
#   0  every function shape agreed
#   1  a shape disagreed -- the text parser and rustc's typed MIR are out of step
#   2  the oracle could not run (no nightly, no rustc-dev) -- *not* evidence
#
# Exit 2 is deliberately distinct: a missing toolchain must never be reported as
# a parser failure, nor as a pass.
set -eu
cd "$(dirname "$0")/../.."

# The oracle links rustc internals, so it must be built *by* the nightly that
# provides them. `DISCHARGE_RUSTC` is the same variable the frontend itself reads,
# so one setting points both sides at one compiler.
RUSTC_BIN="${DISCHARGE_RUSTC:-}"
if [ -z "$RUSTC_BIN" ]; then
  if command -v rustup >/dev/null 2>&1; then
    RUSTC_BIN="$(rustup which --toolchain nightly rustc 2>/dev/null || true)"
  fi
fi
if [ -z "$RUSTC_BIN" ]; then
  echo "mir-oracle: no nightly rustc found; set DISCHARGE_RUSTC" >&2
  exit 2
fi

if ! "$RUSTC_BIN" -vV 2>/dev/null | grep -q nightly; then
  echo "mir-oracle: $RUSTC_BIN is not a nightly; rustc_private needs one" >&2
  exit 2
fi

# `RUSTC` here is what cargo *builds with*; `DISCHARGE_RUSTC` is what the frontend
# *runs*. Both must be the nightly, and they are, because `rustc-dev` is a
# property of the toolchain.
cd tools/mir-oracle
RUSTC="$RUSTC_BIN" cargo build -q 2>&1 || {
  echo "mir-oracle: build failed (is the 'rustc-dev' component installed?)" >&2
  exit 2
}
cd ../..

status=0
for corpus in examples/mir_targets/actuator.rs examples/mir_targets/realistic.rs; do
  DISCHARGE_RUSTC="$RUSTC_BIN" ./tools/mir-oracle/target/debug/mir-oracle "$corpus" || status=$?
done
exit "$status"
