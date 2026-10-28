#!/bin/sh
# Run every gate the README claims, and fail loudly on the first one that does not hold.
#
# Each of these was a separate command quoted in a summary, which is how a gate quietly
# stops being run. One script means "the gates are green" is a single, re-runnable claim.
#
# Usage: scripts/gate.sh
set -eu
cd "$(dirname "$0")/.."

fail() { echo "GATE FAILED: $1" >&2; exit 1; }

echo "== 1/8 clippy (all targets, std) =="
cargo clippy --features std --all-targets -- -D warnings || fail "clippy"

echo "== 2/8 tests (std), with a count that fails on failure =="
sh scripts/test-count.sh || fail "tests"

echo "== 3/8 no_std bare-metal build =="
cargo build -q --no-default-features --target thumbv7em-none-eabihf || fail "bare-metal build"

echo "== 4/8 zero dependencies =="
deps=$(cargo tree --features std | wc -l)
[ "$deps" -eq 1 ] || fail "crate has dependencies: cargo tree lists $deps lines"

echo "== 5/8 z3 differential oracle =="
# This one needs the oracle. If `z3` is absent it exits 2 and says so; that is a failure
# here too, because "the oracle did not run" is not evidence about the exporter.
cargo run -q --features std --example z3diff || fail "z3 differential oracle"

echo "== 6/8 kani differential oracle (skipped if kani is absent) =="
# Kani is an oracle, not a dependency, and installing it is a large download plus a nightly
# toolchain plus CBMC. Unlike z3 it is genuinely optional for a normal build, so an absent
# Kani is *reported and skipped* here rather than failed -- the CI job that installs Kani is
# what makes it a hard gate. When Kani is present, it must pass.
if cargo kani --version >/dev/null 2>&1; then
  cargo run -q --features std --example kanidiff || fail "kani differential oracle"
else
  echo "   (kani not installed; skipped -- 'cargo install --locked kani-verifier && cargo kani setup')"
fi

echo "== 7/8 MIR frontend, on real rustc MIR (skipped if no nightly is named) =="
# The MIR frontend shells out to `rustc --emit=mir`, which needs nightly. It takes the
# compiler from DISCHARGE_RUSTC rather than RUSTC so that pointing it at a nightly does
# not disturb the cargo that is building these tests. Without a nightly named, the
# frontend's tests skip themselves -- so this gate says so rather than passing in silence,
# exactly like Kani and Verus below.
if [ -n "${DISCHARGE_RUSTC:-}" ]; then
  cargo run -q --features std --example mir_demo || fail "MIR demo"
else
  echo "   (DISCHARGE_RUSTC not set; skipped -- set it to 'rustup which --toolchain nightly rustc')"
fi

echo "== 8/8 verus differential oracle (skipped if verus is absent) =="
# Same rule as Kani. Verus ships a self-contained bundle, so a run that wants this gate
# unpacks a release and points VERUS_BIN at the driver.
if command -v "${VERUS_BIN:-verus}" >/dev/null 2>&1; then
  cargo run -q --features std --example verusdiff || fail "verus differential oracle"
else
  echo "   (verus not installed; skipped -- set VERUS_BIN to the Verus release driver)"
fi

echo "ALL GATES GREEN"
