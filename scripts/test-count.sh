#!/bin/sh
# Print the exact number of test cases that pass -- but only when everything passed.
#
# This exists because I got the number wrong three commits in a row, by the same twelve,
# while every other figure in those messages was measured. A recalled count is a claim; a
# computed one is evidence. Quote this script's output, do not remember a number.
#
# It also has to *fail* when a test fails. The first version counted only lines matching
# `test result: ok`, so a suite with a failing test printed a smaller number and exited 0:
# a failed run and a smaller passing run were indistinguishable, and the caller was told
# nothing was wrong. A count that survives a failure is worse than no count, because it
# gets quoted. So a failure, a compile error, or a binary that never ran is a hard error
# here, and the count is printed only when the whole run is green.
set -e
cd "$(dirname "$0")/.."

out=$(cargo test --features std 2>&1) || {
  echo "test-count: cargo test FAILED; not printing a count" >&2
  printf '%s\n' "$out" | grep -E '^(test result: FAILED|error(\[|:)|failures:)' >&2 || true
  exit 1
}

# `cargo test` can exit 0 while a harness reported failures in rare cases, so also require
# that no line reports a failure. `test result: ok` never contains "FAILED".
if printf '%s\n' "$out" | grep -qE '^test result: FAILED'; then
  echo "test-count: a test binary reported FAILED; not printing a count" >&2
  printf '%s\n' "$out" | grep -E '^test result: FAILED' >&2
  exit 1
fi

n=$(printf '%s\n' "$out" \
  | grep -E '^test result: ok' \
  | grep -oE 'ok\. [0-9]+' \
  | grep -oE '[0-9]+' \
  | awk '{ s += $1 } END { printf "%d", s }')

# A green run with zero tests is a broken harness, not a clean bill of health.
if [ -z "$n" ] || [ "$n" -eq 0 ]; then
  echo "test-count: no passing tests were reported; the harness did not run" >&2
  exit 1
fi

printf '%s\n' "$n"
