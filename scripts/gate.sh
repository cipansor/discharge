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
cargo clippy --workspace --features std --all-targets -- -D warnings || fail "clippy"

echo "== 2/8 tests (std), with a count that fails on failure =="
sh scripts/test-count.sh || fail "tests"

echo "== 3/8 no_std bare-metal build =="
# Both crates must build for the target a flight computer actually is. The parent is
# built without its `std` feature; the arithmetic crate has no features at all, so its
# default build *is* the bare-metal one.
cargo build -q --no-default-features --target thumbv7em-none-eabihf || fail "bare-metal build"
cargo build -q -p discharge-arithmetic --target thumbv7em-none-eabihf \
  || fail "bare-metal build of discharge-arithmetic"

echo "== 4/8 no external dependencies =="
# The property is not "the tree has one line" any more -- the arithmetic primitives were
# split into a sibling crate in this repository, so `discharge` legitimately depends on
# `discharge-arithmetic`. The property that must not change is that *nothing from outside
# the repository* is linked: no registry crate, no git crate, nothing from crates.io.
#
# `discharge-arithmetic` must still be a leaf: one line, itself, no dependencies at all.
arith_deps=$(cargo tree -p discharge-arithmetic -e normal | wc -l)
[ "$arith_deps" -eq 1 ] || fail "discharge-arithmetic has dependencies: cargo tree lists $arith_deps lines"

# `discharge` may depend on exactly the one sibling, and it must be a *path* dependency.
discharge_deps=$(cargo tree -p discharge -e normal | wc -l)
[ "$discharge_deps" -eq 2 ] || fail "discharge has dependencies beyond the in-repo sibling: cargo tree lists $discharge_deps lines"
cargo tree -p discharge -e normal --prefix none | tail -n +2 | grep -q 'discharge-arithmetic v0.1.0 (' \
  || fail "the one dependency of discharge is not the in-repo discharge-arithmetic path crate"
# A registry or git dependency would print a `(https://...)` or `(registry+...)` suffix.
if cargo tree -p discharge -e normal --prefix none | tail -n +2 | grep -qE '\((https?://|git\+|registry\+)'; then
  fail "an external (registry or git) dependency has appeared in the tree"
fi

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
