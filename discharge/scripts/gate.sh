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

echo "== 1/5 clippy (all targets, std) =="
cargo clippy --features std --all-targets -- -D warnings || fail "clippy"

echo "== 2/5 tests (std), with a count that fails on failure =="
sh scripts/test-count.sh || fail "tests"

echo "== 3/5 no_std bare-metal build =="
cargo build -q --no-default-features --target thumbv7em-none-eabihf || fail "bare-metal build"

echo "== 4/5 zero dependencies =="
deps=$(cargo tree --features std | wc -l)
[ "$deps" -eq 1 ] || fail "crate has dependencies: cargo tree lists $deps lines"

echo "== 5/5 z3 differential oracle =="
# This one needs the oracle. If `z3` is absent it exits 2 and says so; that is a failure
# here too, because "the oracle did not run" is not evidence about the exporter.
cargo run -q --features std --example z3diff || fail "z3 differential oracle"

echo "ALL GATES GREEN"
