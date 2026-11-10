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

echo "== 1/17 clippy (all targets, std; and the no_std lib) =="
cargo clippy --workspace --features std --all-targets -- -D warnings || fail "clippy (std)"
# `--features std` compiles only the host half. Every `#[cfg(not(feature = "std"))]` item --
# the bare-metal arena, the `static mut` discipline, the whole shipped engine -- is *not*
# compiled by the line above, so a lint in that half would never be seen. Only `--lib` is
# linted here: the integration tests are `std`-only by construction and do not build without
# the feature, which is the point of the gate rather than a gap in it. This is the half that
# goes to a microcontroller, so it is the half that most deserves the lint.
cargo clippy --no-default-features --lib -- -D warnings || fail "clippy (no_std)"

echo "== 2/17 tests (std), with a count that fails on failure =="
sh scripts/test-count.sh || fail "tests"

echo "== 3/17 ferrocene: the qualified compiler builds the crate (skipped if absent) =="
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

echo "== 4/17 no_std bare-metal build =="
# Both crates must build for the target a flight computer actually is. The parent is
# built without its `std` feature; the arithmetic crate has no features at all, so its
# default build *is* the bare-metal one.
cargo build -q --no-default-features --target thumbv7em-none-eabihf || fail "bare-metal build"
cargo build -q -p discharge-arithmetic --target thumbv7em-none-eabihf \
  || fail "bare-metal build of discharge-arithmetic"
# `examples/bare_metal.rs` is the crate's own claim on the target: it is `no_std`, it
# calls the decision procedure, and building it is what proves the prover is code in the
# artifact rather than a host-side tool. A `lib` example (see `[[example]]` in Cargo.toml)
# because a bare-metal target has no `main` to give it.
cargo build -q --no-default-features --target thumbv7em-none-eabihf --example bare_metal \
  || fail "bare-metal build of examples/bare_metal.rs"

echo "== 5/17 no external dependencies =="
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

echo "== 6/17 z3 differential oracle =="
# This one needs the oracle. If `z3` is absent it exits 2 and says so; that is a failure
# here too, because "the oracle did not run" is not evidence about the exporter.
cargo run -q --features std --example z3diff || fail "z3 differential oracle"

echo "== 7/17 kani differential oracle (skipped if kani is absent) =="
# Kani is an oracle, not a dependency, and installing it is a large download plus a nightly
# toolchain plus CBMC. Unlike z3 it is genuinely optional for a normal build, so an absent
# Kani is *reported and skipped* here rather than failed -- the CI job that installs Kani is
# what makes it a hard gate. When Kani is present, it must pass.
if cargo kani --version >/dev/null 2>&1; then
  cargo run -q --features std --example kanidiff || fail "kani differential oracle"
else
  echo "   (kani not installed; skipped -- 'cargo install --locked kani-verifier && cargo kani setup')"
fi

echo "== 8/17 MIR frontend, on real rustc MIR =="
# The MIR frontend shells out to `rustc --emit=mir`. That is a *stable* flag: `-Zunpretty=mir`
# is the nightly-only spelling, and the frontend deliberately does not use it, so a stable
# `rustc` runs the whole `tests/mir.rs` suite (verified on 1.85, the MSRV, and on current
# stable). That makes this gate runnable everywhere rather than only where a nightly happens
# to be installed, which is the point: the "stable is enough" claim is only worth anything if
# something checks it on a stable compiler.
#
# It takes the compiler from DISCHARGE_RUSTC rather than RUSTC so that naming a *different*
# rustc -- a nightly, or the oracle's toolchain -- does not disturb the cargo that is building
# these tests. Falling back to `rustc` on PATH is what lets the gate run with no setup at all;
# it used to skip in that case, which left the stable claim unpinned. It skips only when no
# `rustc` can be found at all, and says so, exactly like Kani and Verus below.
if [ -z "${DISCHARGE_RUSTC:-}" ]; then
  if command -v rustc >/dev/null 2>&1; then
    DISCHARGE_RUSTC="$(command -v rustc)"
    export DISCHARGE_RUSTC
    echo "   (DISCHARGE_RUSTC not set; using the rustc on PATH: $DISCHARGE_RUSTC)"
  fi
fi
if [ -n "${DISCHARGE_RUSTC:-}" ]; then
  cargo run -q --features std --example mir_demo || fail "MIR demo"
else
  echo "   (no rustc on PATH and DISCHARGE_RUSTC unset; skipped -- the frontend needs a rustc)"
fi

echo "== 9/17 verus differential oracle (skipped if verus is absent) =="
# Same rule as Kani. Verus ships a self-contained bundle, so a run that wants this gate
# unpacks a release and points VERUS_BIN at the driver.
if command -v "${VERUS_BIN:-verus}" >/dev/null 2>&1; then
  cargo run -q --features std --example verusdiff || fail "verus differential oracle"
else
  echo "   (verus not installed; skipped -- set VERUS_BIN to the Verus release driver)"
fi

echo "== 10/17 rustc_public MIR oracle (skipped if no nightly/rustc-dev) =="
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

echo "== 11/17 lean differential oracle (skipped if lean is absent) =="
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

echo "== 12/17 coq differential oracle (skipped if coqc is absent) =="
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

echo "== 13/17 minimum supported Rust version (skipped if the toolchain is absent) =="
# `rust-version` in Cargo.toml is a claim, and a claim nothing checks is a claim that rots.
# This gate builds the crates with the *oldest* compiler the manifests promise to support,
# so raising the floor without meaning to -- or leaning on a feature newer than it -- fails
# here rather than in a downstream user's build. Edition 2024 is what fixes the floor at
# 1.85 (cargo refuses the edition on anything older), which is why one number covers both.
#
# It is a skip when the toolchain is absent, with the same convention as Kani and Ferrocene:
# a missing compiler is *not* evidence that the floor holds, so it is reported as a skip
# rather than folded into a pass. `DISCHARGE_MSRV` overrides the version, so the check can
# be pointed at a newer floor without editing the script.
MSRV="${DISCHARGE_MSRV:-1.85}"
if rustup run "$MSRV" rustc --version >/dev/null 2>&1; then
  cargo "+$MSRV" check -q --workspace --features std --all-targets \
    || fail "MSRV build with $MSRV"
  # The bare-metal half is the one that matters for the `no_std` claim, but it needs the
  # target installed *for this toolchain*, which a fresh install does not have. A missing
  # target is an absent check, not a failed one, so it is reported and skipped -- the same
  # distinction the Ferrocene and Kani gates draw, so "did not run" is never read as "passed".
  if rustup target list --toolchain "$MSRV" --installed 2>/dev/null | grep -qx thumbv7em-none-eabihf; then
    cargo "+$MSRV" check -q --no-default-features --target thumbv7em-none-eabihf \
      || fail "MSRV no_std build with $MSRV"
  else
    echo "   (the $MSRV toolchain has no thumbv7em-none-eabihf target; the no_std half was"
    echo "    skipped -- add it with 'rustup target add thumbv7em-none-eabihf --toolchain $MSRV')"
    echo "   This is reported, not passed: the no_std floor was not checked."
  fi
  # `check` only proves the crates *compile* on the floor; it says nothing about whether the
  # MIR frontend still *works* there, because the frontend reads rustc's textual MIR and that
  # text is not stable across toolchains. A `const` that folds to a literal prints inline on
  # current stable and as a CTFE brace-block on 1.85, so a parser that only knew the inline
  # shape passed every gate above and dropped the item on the floor -- the tests were green on
  # 1.99 and red on the compiler the manifest promises to support. Running the frontend's own
  # suite against the floor rustc is what makes the floor a checked claim rather than a build.
  if MSRV_RUSTC="$(rustup run "$MSRV" which rustc 2>/dev/null)"; then
    DISCHARGE_RUSTC="$MSRV_RUSTC" cargo "+$MSRV" test -q --features std --test mir \
      || fail "MIR frontend on the MSRV ($MSRV)"
  fi
else
  echo "   (no $MSRV toolchain; skipped -- install it with 'rustup toolchain install $MSRV')"
  echo "   This is reported, not passed: the floor was not checked."
fi

echo "== 14/17 documentation builds with no warnings =="
# The crate `#![deny(missing_docs)]`, so every public item is documented -- but a
# `missing_docs` deny says nothing about whether those doc comments *build*. Two kinds of
# rot slip past it: an intra-doc link to an item that was renamed or made private (the link
# resolves to nothing and rustdoc warns), and a link to a private item from a public one.
# Both shipped here until this gate: four warnings, none of which any other gate sees,
# because `cargo test` and `cargo clippy` do not run rustdoc.
#
# `-D warnings` makes any warning a failure, so the doc surface is held to the same standard
# as the code. `--no-deps` keeps a dependency's docs from being built (there are none, but
# the flag makes the intent explicit), and `--document-private-items` is deliberately *not*
# passed: the point is the *public* surface, the one a reader sees, and a private-item link
# from a public item is exactly the warning this is meant to catch.
#
# Both crates are checked, one command each. `discharge-arithmetic` takes no `--features std`
# -- it has no features, and naming one there would be a build error. It had the same class
# of warning this gate exists for (`prove.rs` linked its private `forall_pair_bounded` from
# three public items), which a parent-only gate would have left.
#
# `discharge` is built three ways, because the doc surface *differs* between feature sets and
# docs.rs publishes the default one. `--no-default-features` is the `no_std` build; `--features
# std` adds the whole `mir` frontend; `--all-features` is the union that
# `[package.metadata.docs.rs]` requests. A link to a `#[cfg(feature = "std")]` item resolves
# in the last two and *not* in the first -- which is exactly how `smtscript` shipped an
# unresolved link to `Query::to_smtlib2_string` that only the default build could see.
RUSTDOCFLAGS="-D warnings" cargo doc -q -p discharge --no-deps \
  || fail "rustdoc warnings (discharge, no_std)"
RUSTDOCFLAGS="-D warnings" cargo doc -q -p discharge --no-deps --features std \
  || fail "rustdoc warnings (discharge, std)"
RUSTDOCFLAGS="-D warnings" cargo doc -q -p discharge --no-deps --all-features \
  || fail "rustdoc warnings (discharge, all features)"
RUSTDOCFLAGS="-D warnings" cargo doc -q -p discharge-arithmetic --no-deps \
  || fail "rustdoc warnings (discharge-arithmetic)"

echo "== 15/17 the tree ships no build artifacts =="
# `scripts/gate.sh` runs the oracles, and the oracles run `rustc`, which leaves
# `lib<name>.rlib` next to the source it compiled. A `git add -A` then commits them. This
# happened twice: a cleanup commit untracked six root `.rlib`s, and the next `git add -A`
# put them straight back. A `.gitignore` does not help a file that is already tracked --
# ignore rules are consulted only for untracked paths -- so the recurrence needs a check,
# not a pattern. A tracked artifact is dead weight in every clone and, worse, makes the
# zero-dependency claim harder to audit than it should be.
#
# Only tracked files are inspected, and only when `git` is present and this is a work tree,
# so the gate still runs from a tarball export. `.gitignore` and `Cargo.lock` are tracked on
# purpose (a binary crate's lock is a build input, and here it pins the sibling path dep),
# so the pattern is specific to compiled output.
if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  artifacts=$(git ls-files | grep -E '(^|/)(target/|\.sweep/)|\.rlib$|\.rmeta$|\.d$|\.o$|\.bc$|__pycache__' || true)
  if [ -n "$artifacts" ]; then
    echo "$artifacts" >&2
    fail "build artifacts are tracked (see the list above; untrack them with 'git rm --cached')"
  fi
else
  echo "   (not a git work tree, or no git; skipped -- the artifact check needs an index)"
fi

echo "== 16/17 the unsafe surface is pinned and justified =="
# `SECURITY.md` tells a reporter that "the unsafe code" is in scope and names *two*
# blocks. That number was wrong in the other direction once -- it claimed three when there
# were two, and it named only `smt.rs` while `sat.rs` held the second. A count in prose is
# a claim like any other, and this one is security-relevant, so it is checked rather than
# trusted.
#
# Two things are enforced. First, the number of `unsafe { ... }` blocks in `src/` must be
# exactly two, so adding one is a deliberate act that updates this gate and `SECURITY.md`
# together -- an unnoticed `unsafe` in a verifier is exactly the surface a reporter should
# have been told about. Second, every block must be preceded by a `// SAFETY:` comment: the
# crate forbids `unsafe_op_in_unsafe_fn` and documents the arena discipline in prose, and a
# block whose justification is not written down is a block nobody can review.
#
# `discharge-arithmetic` is not checked here because it is `#![forbid(unsafe_code)]` -- it
# cannot have one -- which is the stronger statement.
unsafe_blocks=$(grep -rc 'unsafe {' src/ --include='*.rs' | awk -F: '{s+=$NF} END {print s+0}')
[ "$unsafe_blocks" -eq 2 ] || fail "expected exactly 2 'unsafe' blocks in src/, found $unsafe_blocks (update SECURITY.md and this gate together if that is deliberate)"
# Every `unsafe {` must have a `// SAFETY:` in the *contiguous comment block* directly above
# it -- not a fixed number of lines, because the justifications here run to several lines.
# A blank line or any code ends the run, so a `SAFETY:` from an unrelated earlier block does
# not count.
unjustified=$(find src -name '*.rs' | sort | xargs awk '
  /^[[:space:]]*\/\// { if (index($0, "SAFETY:") > 0) seen = 1; next }
  /^[[:space:]]*$/    { seen = 0; next }
  { if (index($0, "unsafe {") > 0 && !seen) print FILENAME ":" FNR; seen = 0 }
')
if [ -n "$unjustified" ]; then
  echo "$unjustified" >&2
  fail "an 'unsafe' block has no '// SAFETY:' justification in the comment block above it"
fi

echo "== 17/17 the build-time path verifies at compile time and costs nothing =="
# The crate's headline claim is a prover that compiles *into* the artifact. This gate
# checks the other shape a safety build often wants, and the one Kani and Verus actually
# have: the checker runs while the crate is built and the shipped binary carries none of
# it. `discharge` supports that through its `std`-only `mir` frontend as a
# `[build-dependencies]` entry -- a build script is a separate compilation unit, so the
# decision procedure is compiled for the host and never linked into the crate's own rlib.
#
# The claim is exactly the kind this repository refuses to leave in prose: "zero cost" and
# "verified at compile time" are both checkable, and both rot silently if only asserted.
# `tools/build-verify/run.sh` builds a scratch crate three ways and requires (1) a good
# contract to build *and* the verifier to report `verified` (a build script that did
# nothing would otherwise pass), (2) a broken contract to fail the build on its named
# obligation, and (3) the resulting rlib to carry zero `discharge` symbols. Exit 2 means
# no cargo, which is reported and skipped like the other toolchain gates; exit 1 is a real
# failure.
code=0
sh tools/build-verify/run.sh || code=$?
if [ "$code" -eq 0 ]; then
  :
elif [ "$code" -eq 2 ]; then
  echo "   (no cargo on PATH; skipped -- the build-time path needs a toolchain)"
else
  fail "build-time verification / zero-cost artifact (exit $code)"
fi

echo "ALL GATES GREEN"
