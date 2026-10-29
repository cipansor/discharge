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

echo "== 1/12 clippy (all targets, std) =="
cargo clippy --workspace --features std --all-targets -- -D warnings || fail "clippy"

echo "== 2/12 tests (std), with a count that fails on failure =="
sh scripts/test-count.sh || fail "tests"

echo "== 3/12 ferrocene: the qualified compiler builds the crate (skipped if absent) =="
# Ferrocene is the *qualified* Rust toolchain (ISO 26262 ASIL D, IEC 61508 SIL 3, EN 50128,
# IEC 62304), so it is the one compiler whose word carries weight for a safety-critical
# claim. The crate's own README says it has no qualification evidence; building the same
# `no_std` crate with the qualified toolchain is the honest half of that claim that can be
# checked. It is *not* a dependency and adds nothing to the tree: like Kani, Verus, Lean and
# Coq it is a subprocess.
#
# Ferrocene is commercial -- a subscription plus a customer-portal token -- and its release
# archives "require authentication through the customer portal, and don't allow programmatic
# access" (Ferrocene User Manual 3.2.1), so a public CI job cannot install it. The script
# resolves the toolchain from `FERROCENE_RUSTC` or CriticalUp and exits 2 when there is
# none, which is reported and skipped here rather than failed, exactly like Kani and Verus.
# Exit 1 is a real build failure and fails the gate; the two must not be conflated, which is
# why the script keeps them distinct.
code=0
sh tools/ferrocene/run.sh || code=$?
if [ "$code" -eq 0 ]; then
  :
elif [ "$code" -eq 2 ]; then
  echo "   (no Ferrocene toolchain; skipped -- set FERROCENE_RUSTC, or install via CriticalUp"
  echo "    and run 'criticalup auth set'; see tools/ferrocene/README.md)"
else
  fail "ferrocene build (exit $code)"
fi

echo "== 4/12 no_std bare-metal build =="
# Both crates must build for the target a flight computer actually is. The parent is
# built without its `std` feature; the arithmetic crate has no features at all, so its
# default build *is* the bare-metal one.
cargo build -q --no-default-features --target thumbv7em-none-eabihf || fail "bare-metal build"
cargo build -q -p discharge-arithmetic --target thumbv7em-none-eabihf \
  || fail "bare-metal build of discharge-arithmetic"

echo "== 5/12 no external dependencies =="
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

echo "== 6/12 z3 differential oracle =="
# This one needs the oracle. If `z3` is absent it exits 2 and says so; that is a failure
# here too, because "the oracle did not run" is not evidence about the exporter.
cargo run -q --features std --example z3diff || fail "z3 differential oracle"

echo "== 7/12 kani differential oracle (skipped if kani is absent) =="
# Kani is an oracle, not a dependency, and installing it is a large download plus a nightly
# toolchain plus CBMC. Unlike z3 it is genuinely optional for a normal build, so an absent
# Kani is *reported and skipped* here rather than failed -- the CI job that installs Kani is
# what makes it a hard gate. When Kani is present, it must pass.
if cargo kani --version >/dev/null 2>&1; then
  cargo run -q --features std --example kanidiff || fail "kani differential oracle"
else
  echo "   (kani not installed; skipped -- 'cargo install --locked kani-verifier && cargo kani setup')"
fi

echo "== 8/12 MIR frontend, on real rustc MIR (skipped if no nightly is named) =="
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

echo "== 9/12 verus differential oracle (skipped if verus is absent) =="
# Same rule as Kani. Verus ships a self-contained bundle, so a run that wants this gate
# unpacks a release and points VERUS_BIN at the driver.
if command -v "${VERUS_BIN:-verus}" >/dev/null 2>&1; then
  cargo run -q --features std --example verusdiff || fail "verus differential oracle"
else
  echo "   (verus not installed; skipped -- set VERUS_BIN to the Verus release driver)"
fi

echo "== 10/12 rustc_public MIR oracle (skipped if no nightly/rustc-dev) =="
# The frontend reads *textual* MIR, so a rustc release that reprints the dump can
# break the parser and nothing else would notice. This gate asks `rustc_public`
# for the same programs' typed MIR and compares the per-function shape -- block
# count and panic inventory -- so a printer change is caught. It needs a nightly
# with `rustc-dev` *and* `llvm-tools-preview`; `run.sh` exits 2 only when those
# are genuinely absent, which is reported and skipped here rather than failed,
# exactly like Kani and Verus. Exit 3 means the components are present and the
# oracle still would not build -- a real failure, so it fails the gate.
code=0
sh tools/mir-oracle/run.sh || code=$?
if [ "$code" -eq 0 ]; then
  :
elif [ "$code" -eq 2 ]; then
  echo "   (nightly lacks rustc-dev/llvm-tools-preview; skipped --"
  echo "    'rustup component add rustc-dev llvm-tools-preview --toolchain nightly')"
else
  # 1 is a shape disagreement; 3 is a build failure with the components present.
  # Neither is a missing toolchain, so both fail the gate.
  fail "rustc_public MIR oracle (exit $code)"
fi

echo "== 11/12 lean differential oracle (skipped if lean is absent) =="
# Lean is the strongest of the four backends here: `bv_decide` bit-blasts and then replays
# the SAT refutation as a Lean proof term the kernel checks, so agreement is with a
# machine-checked theorem rather than with a solver's word. It is still an oracle, not a
# dependency -- `lean` is a subprocess and the crate builds with zero dependencies -- so an
# absent Lean is reported and skipped, exactly like Kani and Verus. `LEAN_BIN` names the
# binary when elan's `~/.elan/bin` is not on PATH.
if cargo run -q --features std --example leandiff -- 64; then
  :
else
  code=$?
  if [ "$code" -eq 2 ]; then
    echo "   (no lean on PATH; skipped -- install with elan, or set LEAN_BIN)"
  else
    fail "lean differential oracle"
  fi
fi

echo "== 12/12 coq differential oracle (skipped if coqc is absent) =="
# Coq checks a different thing from the other three: not "does the engine decide this the
# same way" but "does the engine's arithmetic, transcribed into `Z` with explicit masks,
# evaluate to the same truth value on every point of the 8-bit domain". It enumerates, so it
# is the slowest oracle and takes a selected subset of the corpus (see `SELECTED` in
# examples/coqdiff.rs). Absent `coqc` is reported and skipped, like Kani and Verus.
if cargo run -q --features std --example coqdiff; then
  :
else
  code=$?
  if [ "$code" -eq 2 ]; then
    echo "   (no coqc on PATH; skipped -- install Coq, or set COQC_BIN)"
  else
    fail "coq differential oracle"
  fi
fi

echo "ALL GATES GREEN"
