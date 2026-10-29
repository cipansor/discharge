#!/bin/sh
# Build both crates with Ferrocene, the *qualified* Rust toolchain, for the bare-metal
# target this repository actually ships to.
#
# Ferrocene is qualified to ISO 26262 ASIL D, IEC 61508 SIL 3, EN 50128 and IEC 62304, so
# it is the one compiler whose word carries weight for a safety-critical claim. The crate's
# README states plainly that it has no qualification evidence of its own; the honest half of
# that claim that *can* be checked is that the qualified compiler accepts the same sources
# and produces the same artifact shape. That is what this script checks.
#
# It is an *oracle*, not a dependency, exactly like Kani, Verus, Lean, Coq and z3: Ferrocene
# is invoked as a subprocess and adds nothing to the dependency tree, so `scripts/gate.sh`'s
# zero-external-dependency check still holds when this runs.
#
# Exit status, the same convention `tools/mir-oracle/run.sh` uses:
#
#   0  both crates built with the qualified toolchain
#   1  a build failed -- a real failure
#   2  no Ferrocene toolchain was found, so nothing was checked -- *not* evidence
#
# Exit 2 is deliberately distinct. Ferrocene is commercial: a subscription plus a
# customer-portal token, and its release archives "require authentication through the
# customer portal, and don't allow programmatic access" (Ferrocene User Manual 3.2.1). A
# public CI job therefore cannot install it, so "absent" must be reported and skipped rather
# than failed -- and must never be confused with "present and passing".
#
# Usage:
#   FERROCENE_RUSTC=/path/to/ferrocene/bin/rustc sh tools/ferrocene/run.sh
# or, with CriticalUp installed and authenticated:
#   sh tools/ferrocene/run.sh
set -eu
cd "$(dirname "$0")/../.."

# The target the crate's `no_std` build ships to. It is a target Ferrocene itself qualifies
# (User Manual 15, `thumbv7em-none-eabihf`), so a qualified build is a real build here and
# not a host-only formality.
TARGET=thumbv7em-none-eabihf

# Resolve the qualified `rustc`. `FERROCENE_RUSTC` wins, the same shape as
# `DISCHARGE_RUSTC` for the MIR frontend and `COQC_BIN` for the Coq oracle.
RUSTC_BIN="${FERROCENE_RUSTC:-}"
if [ -z "$RUSTC_BIN" ] && command -v criticalup >/dev/null 2>&1; then
  # CriticalUp discovers `criticalup.toml` by scanning the working directory and then its
  # parents, so it must be asked from the directory that holds the manifest -- this one --
  # and the absolute path it prints is then usable from the repository root.
  RUSTC_BIN="$(cd tools/ferrocene && criticalup which rustc 2>/dev/null || true)"
fi
if [ -z "$RUSTC_BIN" ]; then
  echo "ferrocene: no Ferrocene toolchain found" >&2
  echo "ferrocene: set FERROCENE_RUSTC, or install via CriticalUp and authenticate:" >&2
  echo "ferrocene:   curl --proto '=https' --tlsv1.2 -LsSf https://github.com/ferrocene/criticalup/releases/latest/download/criticalup-installer.sh | sh" >&2
  echo "ferrocene:   criticalup auth set   # paste a customer-portal token" >&2
  exit 2
fi

# A path that is set but not runnable is the same "no evidence" situation as an absent one:
# the archives ship their own `rust-std`, and a half-installed toolchain cannot build.
if ! version="$("$RUSTC_BIN" --version 2>&1)"; then
  echo "ferrocene: cannot run $RUSTC_BIN: $version" >&2
  exit 2
fi

# `RUSTC` is what cargo *builds with*; the sources are unchanged and no feature is added.
# The parent is built without `std`, the arithmetic sibling has no features at all, so both
# builds are the bare-metal ones a flight computer would link.
RUSTC="$RUSTC_BIN" cargo build -q --no-default-features --target "$TARGET" || {
  echo "ferrocene: build of discharge for $TARGET failed" >&2
  exit 1
}
RUSTC="$RUSTC_BIN" cargo build -q -p discharge-arithmetic --target "$TARGET" || {
  echo "ferrocene: build of discharge-arithmetic for $TARGET failed" >&2
  exit 1
}

echo "ferrocene: built discharge and discharge-arithmetic for $TARGET with $version"
