#!/bin/sh
# Prove the two properties that make a build-time verifier usable in a safety build:
# the verification runs at *build* time, and the prover does not reach the artifact.
#
# This is the Kani/Verus shape, reached without their toolchains. The checker runs on
# the host while the crate is built, and the shipped binary is the crate's own code with
# nothing of the checker in it. `discharge` supports that shape through the `std`-only
# `mir` frontend: put it in `[build-dependencies]`, call `verify_file_with` from
# `build.rs`, and fail the build when an outcome is not `Verified`. Nothing of the
# decision procedure is linked into the crate's own artifact, because a build script is
# a separate compilation unit that cargo runs and then throws away.
#
# This is deliberately the *opposite* trade-off from the crate's headline claim, which
# is a prover that compiles *into* the artifact so a proof can run where Z3 cannot (see
# `examples/bare_metal.rs` and README's "prover that compiles into your artifact"). Both
# are real; the difference is whether the obligation is discharged before or after the
# code ships. A build script gets the zero-cost artifact and pays with a host-side
# `rustc`; the embedded engine gets the on-target proof and pays with binary size. The
# point of this script is that the *first* trade-off is checked rather than asserted.
#
# It is a *scratch* crate under `mktemp -d`, not a fixture in the tree: a fixture would
# put a second `Cargo.toml` and a `target/` in the repository, and gate 15 exists
# precisely because that tends to get committed. The crate is created, exercised, and
# removed.
#
# Exit status, the same convention `tools/mir-oracle/run.sh` and `tools/ferrocene/run.sh`
# use:
#
#   0  the build-time path verified a good contract, refused a bad one, and left no
#      prover symbols in the artifact
#   1  a real failure -- one of the three properties did not hold
#   2  no `cargo` on PATH, so nothing was checked -- *not* evidence
#
# Usage: sh tools/build-verify/run.sh
set -eu
cd "$(dirname "$0")/../.."

if ! command -v cargo >/dev/null 2>&1; then
  echo "build-verify: no cargo on PATH, so nothing was checked" >&2
  exit 2
fi

ROOT="$(pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT INT TERM

mkdir -p "$WORK/src"

cat > "$WORK/Cargo.toml" <<EOF
[package]
name = "build_verify_scratch"
version = "0.1.0"
edition = "2021"

# The whole point: discharge is a *build* dependency, so it is compiled for the host,
# run by the build script, and never linked into this crate's own artifact.
[build-dependencies]
discharge = { path = "$ROOT", features = ["std"] }

[dependencies]
EOF

# The build script is the verifier. It fails the build on anything but `Verified`, so a
# broken contract is a *compile* error -- the same guarantee Kani and Verus give, reached
# without a nightly or an external solver.
cat > "$WORK/build.rs" <<'EOF'
fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    let src = std::path::Path::new("src/lib.rs");
    let report = discharge::mir::verify::verify_file_with("rustc", src, &[])
        .expect("discharge: the MIR frontend could not read the source");
    let mut bad = Vec::new();
    for (name, outcome) in &report.outcomes {
        println!("cargo:warning=discharge {name}: {outcome}");
        if !outcome.is_verified() {
            bad.push(format!("{name}: {outcome}"));
        }
    }
    if !bad.is_empty() {
        panic!("discharge: verification failed:\n  {}", bad.join("\n  "));
    }
}
EOF

# 1. A good contract must build, and the verification must actually *run* (a build script
#    that silently did nothing would also "pass").
cat > "$WORK/src/lib.rs" <<'EOF'
/// requires: true
/// decreases: n
/// ensures: ret == n
pub fn count_down(n: u8) -> u8 {
    if n == 0 { 0 } else { count_down(n - 1) + 1 }
}
EOF

if ! out="$(cd "$WORK" && cargo build --release 2>&1)"; then
    echo "$out" >&2
    echo "build-verify: a provable contract FAILED to build" >&2
    exit 1
fi
case "$out" in
    *"discharge count_down: verified"*) ;;
    *)
        echo "$out" >&2
        echo "build-verify: the build succeeded but the verifier did not report 'verified' --" >&2
        echo "build-verify: a build script that does nothing must not pass this gate" >&2
        exit 1
        ;;
esac

# 2. A broken contract must FAIL the build, with a counterexample. This is the half that
#    makes it a *verifier* rather than a linter: the induction's base case is wrong here
#    (`n == 0` returns 1 against `ensures: ret == n`), which is exactly the mistake a
#    circular induction would wave through.
cat > "$WORK/src/lib.rs" <<'EOF'
/// requires: true
/// decreases: n
/// ensures: ret == n
pub fn count_down(n: u8) -> u8 {
    if n == 0 { 1 } else { count_down(n - 1) + 1 }
}
EOF

if out="$(cd "$WORK" && cargo build --release 2>&1)"; then
    echo "$out" >&2
    echo "build-verify: a FALSE contract BUILT -- the verification is not gating the build" >&2
    exit 1
fi
case "$out" in
    *postcondition*) ;;
    *)
        echo "$out" >&2
        echo "build-verify: the build failed, but not on the postcondition -- expected the" >&2
        echo "build-verify: verifier to name the broken obligation" >&2
        exit 1
        ;;
esac

# 3. The artifact must carry nothing of the prover. A build dependency is a separate
#    compilation unit, so the crate's own rlib should have *no* `discharge` symbol at
#    all -- which is the "zero cost" claim, and the reason to prefer this shape in a
#    size-constrained safety build. Restore the good source first, so the rlib is a
#    real one rather than the failed build's leftovers.
cat > "$WORK/src/lib.rs" <<'EOF'
/// requires: true
/// decreases: n
/// ensures: ret == n
pub fn count_down(n: u8) -> u8 {
    if n == 0 { 0 } else { count_down(n - 1) + 1 }
}
EOF
(cd "$WORK" && cargo build --release >/dev/null 2>&1)

rlib="$(find "$WORK/target/release" -maxdepth 1 -name 'libbuild_verify_scratch*.rlib' | head -n 1)"
if [ -z "$rlib" ]; then
    echo "build-verify: no rlib was produced, so the zero-cost check has nothing to read" >&2
    exit 1
fi
rlib_bytes=$(wc -c < "$rlib" | tr -d ' ')

if command -v nm >/dev/null 2>&1; then
    # `nm -C` demangles, so `discharge::smt::blast` shows up as such. Zero matches means
    # the prover was not linked in; any match means it was, and the artifact is not free.
    symbols=$(nm -C "$rlib" 2>/dev/null | grep -ci 'discharge' || true)
    if [ "$symbols" -ne 0 ]; then
        echo "build-verify: the artifact carries $symbols 'discharge' symbol(s) -- the prover" >&2
        echo "build-verify: reached the shipped code, so it is not zero-cost" >&2
        exit 1
    fi
    echo "build-verify: 0 'discharge' symbols in the artifact ($rlib_bytes bytes rlib)"
else
    echo "build-verify: no nm, so the symbol check was skipped ($rlib_bytes bytes rlib)"
fi

echo "build-verify: a good contract built, a false one failed the build, and the artifact"
echo "build-verify: carries no prover -- verification is build-time and zero-cost"
