#!/bin/sh
# Check the comparison directory's *claims*, not just its prose.
#
# `examples/comparison/` is the evidence behind the README's comparison table, and
# until now nothing ran it: the fixtures were verified by hand, once, and the prose
# was the only record. That is the failure mode this repository names explicitly --
# a one-off verification is not a gate, and only a gate survives the next change.
#
# What is checked here, all of it re-runnable:
#
#   1. `discharge` decides the positive fixture and *refuses* each bug fixture. The
#      bug files carry the same contracts as the positive one, so a refusal is
#      evidence about the defect rather than about a weaker contract.
#   2. The degenerate implementations are refused. `sat_add` returning `u16::MAX`
#      for every input, and `clamp` returning `lo` for every input, satisfy the
#      bounds-only contracts the first version of this directory shipped; they must
#      fail the full contracts. This is the check that the contracts state the whole
#      function, and it is the one the earlier version could not have passed.
#   3. Coq and Lean each prove the positive fixture and reject both teeth. Coq
#      stops at the first failed proof, so the teeth are one theorem per file and
#      each exit code is checked on its own.
#   4. The teeth are mutation-clean: correcting the defect makes the file compile.
#      A proof script is a test, and a test that fails while the defect is present
#      has proved nothing until the defect is removed and it passes.
#
# The external provers (Kani, Verus, Prusti, SPARK) are exercised by CI as their own
# jobs, where their toolchains are installed; re-running them here on every local
# gate run would cost minutes for no extra signal. This script covers what is cheap
# and hermetic: `discharge` itself, Coq, and Lean.
#
# Exit status, the same convention `tools/mir-oracle/run.sh`, `tools/ferrocene/run.sh`
# and `tools/build-verify/run.sh` use:
#
#   0  every claim above held
#   1  a claim did not hold (a real failure -- do not treat this as "tool absent")
#   2  a needed tool is absent (reported and skipped by `gate.sh`)
set -u

cd "$(dirname "$0")/../.." || exit 1

fail() { echo "comparison: $1" >&2; exit 1; }
need() { command -v "$1" >/dev/null 2>&1; }

have_coqc=1; need coqc || have_coqc=0
have_lean=1; need lean || have_lean=0
if [ "$have_coqc" -eq 0 ] && [ "$have_lean" -eq 0 ]; then
  echo "comparison: neither coqc nor lean is installed; skipped" >&2
  exit 2
fi

# `discharge` needs the nightly named for its MIR frontend, as the README says.
if [ -z "${DISCHARGE_RUSTC:-}" ]; then
  if need rustup; then
    DISCHARGE_RUSTC="$(rustup which --toolchain nightly-2026-08-21 rustc 2>/dev/null || true)"
  fi
fi
if [ -z "${DISCHARGE_RUSTC:-}" ]; then
  echo "comparison: no nightly rustc for the MIR frontend; set DISCHARGE_RUSTC" >&2
  exit 2
fi
export DISCHARGE_RUSTC

mir() { cargo run -q --features std --example mir_coverage -- "$1" 2>/dev/null; }

echo "comparison: discharge decides the positive fixture"
mir examples/comparison/target.rs | grep -q "decided 3 of 3" \
  || fail "positive fixture did not decide 3 of 3"

echo "comparison: discharge refuses each bug fixture"
for b in bugs/target.rs bugs/clamp.rs bugs/loop.rs; do
  mir "examples/comparison/$b" | grep -q "decided 0 of 1" \
    || fail "discharge accepted the defect in $b"
done

echo "comparison: the contracts refuse the degenerate implementations"
# `u16::MAX` for every input satisfies `ret >= a && ret >= b`; `lo` for every input
# satisfies `lo <= ret <= hi`. Both must fail the full contracts.
degen_sat="$(mktemp)"; degen_clamp="$(mktemp)"
cat > "$degen_sat" <<'EOF'
/// requires: true
/// ensures: ret >= a
/// ensures: ret >= b
/// ensures: a <= 65535u16 - b || ret == 65535u16
/// ensures: a > 65535u16 - b || ret == a + b
pub fn sat_add(a: u16, b: u16) -> u16 { 65535u16 }
EOF
cat > "$degen_clamp" <<'EOF'
/// requires: lo <= hi
/// ensures: !(x < lo) || ret == lo
/// ensures: !(lo <= x && x > hi) || ret == hi
/// ensures: !(lo <= x && x <= hi) || ret == x
pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 { lo }
EOF
mir "$degen_sat"   | grep -q "decided 0 of 1" || fail "degenerate sat_add (always u16::MAX) was accepted"
mir "$degen_clamp" | grep -q "decided 0 of 1" || fail "degenerate clamp (always lo) was accepted"
rm -f "$degen_sat" "$degen_clamp"

if [ "$have_coqc" -eq 1 ]; then
  echo "comparison: Coq proves the fixture and rejects both teeth"
  coqc -Q examples/comparison/coq "" examples/comparison/coq/model.v >/dev/null 2>&1 \
    || fail "coq: model.v did not compile"
  coqc -Q examples/comparison/coq "" examples/comparison/coq/example.v >/dev/null 2>&1 \
    || fail "coq: example.v did not compile"
  for t in teeth_sat_add teeth_sum_to; do
    if coqc -Q examples/comparison/coq "" "examples/comparison/bugs/coq/$t.v" >/dev/null 2>&1; then
      fail "coq: $t.v was accepted (the false theorem proved)"
    fi
  done
  # Mutation: correct the defect, and the file must compile. This is what makes the
  # rejection evidence about the defect and not about the shape of the script.
  mut="$(mktemp -d)"
  cp examples/comparison/coq/model.v "$mut/"
  ( cd "$mut" && coqc model.v >/dev/null 2>&1 ) || fail "coq: mutation harness could not build model.v"
  sed 's/then add_eng a b else MAX/then MAX else add_eng a b/' \
    examples/comparison/bugs/coq/teeth_sat_add.v > "$mut/teeth_sat_add.v"
  ( cd "$mut" && coqc -Q . "" teeth_sat_add.v >/dev/null 2>&1 ) \
    || fail "coq: teeth_sat_add.v still failed after the defect was corrected (script-shaped rejection)"
  sed 's/S (S (sum_to_buggy k))/S (sum_to_buggy k)/' \
    examples/comparison/bugs/coq/teeth_sum_to.v > "$mut/teeth_sum_to.v"
  ( cd "$mut" && coqc -Q . "" teeth_sum_to.v >/dev/null 2>&1 ) \
    || fail "coq: teeth_sum_to.v still failed after the defect was corrected (script-shaped rejection)"
  rm -rf "$mut"
fi

if [ "$have_lean" -eq 1 ]; then
  echo "comparison: Lean proves the fixture and rejects both teeth"
  lean -o examples/comparison/lean/model.olean examples/comparison/lean/model.lean >/dev/null 2>&1 \
    || fail "lean: model.lean did not compile"
  LEAN_PATH=examples/comparison/lean lean examples/comparison/lean/example.lean >/dev/null 2>&1 \
    || fail "lean: example.lean did not compile"
  for t in teeth_sat_add teeth_sum_to; do
    if LEAN_PATH=examples/comparison/lean lean "examples/comparison/bugs/lean/$t.lean" >/dev/null 2>&1; then
      fail "lean: $t.lean was accepted (the false theorem proved)"
    fi
  done
  mut="$(mktemp -d)"
  cp examples/comparison/lean/model.lean "$mut/"
  ( cd "$mut" && lean -o model.olean model.lean >/dev/null 2>&1 ) || fail "lean: mutation harness could not build model.olean"
  sed 's/then addEng a b else MAX/then MAX else addEng a b/' \
    examples/comparison/bugs/lean/teeth_sat_add.lean > "$mut/teeth_sat_add.lean"
  ( cd "$mut" && LEAN_PATH="$mut" lean teeth_sat_add.lean >/dev/null 2>&1 ) \
    || fail "lean: teeth_sat_add.lean still failed after the defect was corrected (script-shaped rejection)"
  sed 's/sumToBuggy n + 2/sumToBuggy n + 1/' \
    examples/comparison/bugs/lean/teeth_sum_to.lean > "$mut/teeth_sum_to.lean"
  ( cd "$mut" && LEAN_PATH="$mut" lean teeth_sum_to.lean >/dev/null 2>&1 ) \
    || fail "lean: teeth_sum_to.lean still failed after the defect was corrected (script-shaped rejection)"
  rm -rf "$mut"
fi

# The .olean this script writes is an ignored build artifact, but remove it so a run
# leaves the tree exactly as it found it.
rm -f examples/comparison/lean/model.olean

echo "comparison: every claim held"
exit 0
