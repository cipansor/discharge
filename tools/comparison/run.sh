#!/bin/sh
# Check the comparison directory's *claims*, not just its prose.
#
# `examples/comparison/` is the evidence behind the README's comparison table, and
# until now nothing ran it: the fixtures were verified by hand, once, and the prose
# was the only record. That is the failure mode this repository names explicitly --
# a one-off verification is not a gate, and only a gate survives the next change.
#
# The `verif` half is `examples/comparison_check.rs`, a driver that asserts the
# per-function `FnOutcome` of each fixture. It is a driver and not a scrape of
# `mir_coverage`'s `decided N of M` line on purpose: that line counts only
# `Verified`, so `Failed`, `Incomplete` and `Skipped` all leave it at zero, and a
# fixture whose contract became *unreadable* would still read `decided 0 of 1`.
# The old version of this script asserted that line, so it would have called a lost
# proof a caught defect -- the "teeth have to isolate the guard they claim to test"
# rule, violated by the gate that enforces it. The driver now requires `Failed`
# with the expected obligation kind, and rejects `Skipped`, `Incomplete` and driver
# errors outright.
#
# The Coq and Lean halves each prove the positive fixture and reject both teeth, and
# each rejection is mutation-checked: correcting the defect makes the file compile,
# so a rejection cannot be an artifact of the script's shape. Coq stops at the first
# failed proof, so the teeth are one theorem per file and each exit code is checked
# on its own.
#
# Both Coq *and* Lean are required. An earlier version skipped whichever was absent
# and still reported success, so a machine with only one of them would report "every
# claim held" without having checked one of the two proof suites. A gate that reports
# success for work it did not do is the thing this file exists to prevent, so a
# missing prover is exit 2 (a skip, reported by `gate.sh`) and never exit 0.
#
# The external provers (Kani, Verus, Prusti, SPARK) are exercised by CI as their own
# jobs, where their toolchains are installed; re-running them here on every local
# gate run would cost minutes for no extra signal.
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

missing=""
need coqc || missing="$missing coqc"
need lean || missing="$missing lean"

# `verif` needs the nightly named for its MIR frontend, as the README says.
if [ -z "${VERIF_RUSTC:-}" ]; then
  if need rustup; then
    VERIF_RUSTC="$(rustup which --toolchain nightly-2026-08-21 rustc 2>/dev/null || true)"
  fi
fi
[ -n "${VERIF_RUSTC:-}" ] || missing="$missing nightly-rustc"

if [ -n "$missing" ]; then
  echo "comparison: required tool(s) absent:$missing -- skipped" >&2
  exit 2
fi
export VERIF_RUSTC

echo "comparison: verif on the fixtures (per-function outcome, not a count)"
cargo run -q --features std --example comparison_check || fail "verif fixtures (see the driver output above)"

# Coq: the fixture proves, each tooth is refused, and each tooth compiles once its
# defect is corrected. `-Q dir ""` maps the directory to the empty logical prefix so
# `Require Import model` resolves without a build system.
coq_check() {
  coqc -Q examples/comparison/coq "" "$1" >/dev/null 2>&1
}

echo "comparison: Coq proves the fixture and rejects both teeth"
coq_check examples/comparison/coq/model.v || fail "coq: model.v did not compile"
coq_check examples/comparison/coq/example.v || fail "coq: example.v did not compile"
for t in teeth_sat_add teeth_sum_to; do
  if coq_check "examples/comparison/bugs/coq/$t.v"; then
    fail "coq: $t.v was accepted (the false theorem proved)"
  fi
done

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

# The .olean this script writes is an ignored build artifact; remove it so a run
# leaves the tree exactly as it found it.
rm -f examples/comparison/lean/model.olean

echo "comparison: every claim held"
exit 0
