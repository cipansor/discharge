#!/bin/sh
# Build and run the `rustc_public` MIR oracle over the corpora the gate uses.
#
# This is the one place in the repository that needs a nightly toolchain with the
# `rustc-dev` component, so it is kept out of `scripts/gate.sh`'s main build and
# invoked as its own gate. It exits:
#
#   0  every function shape agreed
#   1  a shape disagreed -- the text parser and rustc's typed MIR are out of step
#   2  the oracle could not run: the toolchain lacks a component it needs
#      (no nightly, or a missing rustc-dev / llvm-tools-preview) -- *not* evidence
#   3  the oracle could not be *built* -- a real failure, and deliberately not 2
#
# Exit 2 is deliberately distinct: a missing toolchain must never be reported as
# a parser failure, nor as a pass. Exit 3 exists for the mirror-image reason. A
# build failure and a missing component both surface as a failing `cargo build`,
# so mapping every build failure to 2 let a compile error in the oracle be
# reported as "toolchain missing" -- and the local gate, which skips on 2, then
# reported success without having built the oracle at all. The components are
# probed for directly below, so 2 means "genuinely absent" and any build failure
# that survives the probe is 3.
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

if ! version="$("$RUSTC_BIN" -vV 2>&1)"; then
  echo "mir-oracle: cannot run $RUSTC_BIN: $version" >&2
  echo "            this is usually the missing 'llvm-tools-preview' component, which ships" >&2
  echo "            the libLLVM rustc needs to start: rustup component add llvm-tools-preview --toolchain nightly" >&2
  exit 2
fi

if ! printf '%s' "$version" | grep -q nightly; then
  echo "mir-oracle: $RUSTC_BIN is not a nightly; rustc_private needs one" >&2
  exit 2
fi

# The sysroot and host of the compiler we are about to build with, so the
# component probe below checks *this* toolchain rather than whichever one
# `rustup` calls `nightly`.
sysroot="$("$RUSTC_BIN" --print sysroot)"
host="$(printf '%s' "$version" | sed -n 's/^host: //p')"
libdir="$sysroot/lib/rustlib/$host/lib"

# The two components the oracle needs, probed by their artifacts rather than by
# `rustup component list` (which answers for a *named* toolchain, and
# `DISCHARGE_RUSTC` may point at one that is not named `nightly`):
#
#   rustc-dev            -> librustc_driver-*.so
#   llvm-tools-preview   -> libLLVM-*
#
# Both live in the same `rustlib/<host>/lib` directory, which is also the
# directory cargo puts on the build script's `LD_LIBRARY_PATH` and rustc passes
# to the linker as `-L`.
components_present() {
  [ -e "$libdir"/librustc_driver-*.so ] && [ -e "$libdir"/libLLVM-* ]
}

# `RUSTC` here is what cargo *builds with*; `DISCHARGE_RUSTC` is what the frontend
# *runs*. Both must be the nightly, and they are, because `rustc-dev` is a
# property of the toolchain.
#
# `llvm-tools-preview` must be installed as well: it ships the `libLLVM` that
# `rustc` needs to start, and without it the oracle's `build.rs` cannot read the
# sysroot and the link fails with `unable to find library -lLLVM-...`. That reads
# like a broken toolchain, so name the component here instead.
cd tools/mir-oracle
RUSTC="$RUSTC_BIN" cargo build -q 2>&1 || {
  # A build failure is *either* a missing component *or* a real error in the
  # oracle, and the two must not be conflated. Probe for the components directly:
  # if they are present, the failure is real and is reported as 3, so the gate
  # fails rather than skipping. `2` must mean "genuinely absent".
  if components_present; then
    echo "mir-oracle: build failed, but rustc-dev and llvm-tools-preview are present" >&2
    echo "            on $RUSTC_BIN -- this is a real failure in the oracle, not a" >&2
    echo "            missing component" >&2
    exit 3
  fi
  echo "mir-oracle: build failed, and $libdir is missing one of the components" >&2
  echo "            the oracle needs. Install both on the nightly:" >&2
  echo "              rustup component add rustc-dev llvm-tools-preview --toolchain nightly" >&2
  exit 2
}
cd ../..

status=0
for corpus in examples/mir_targets/actuator.rs examples/mir_targets/realistic.rs; do
  DISCHARGE_RUSTC="$RUSTC_BIN" ./tools/mir-oracle/target/debug/mir-oracle "$corpus" || status=$?
done
exit "$status"
