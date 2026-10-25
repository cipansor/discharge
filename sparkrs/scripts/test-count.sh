#!/bin/sh
# Print the exact number of test cases that pass.
#
# This exists because I got the number wrong three commits in a row, by the same twelve,
# while every other figure in those messages was measured. A recalled count is a claim; a
# computed one is evidence. Quote this script's output, do not remember a number.
set -e
cd "$(dirname "$0")/.."
cargo test --features std 2>&1 \
  | grep -E '^test result: ok' \
  | grep -oE 'ok\. [0-9]+' \
  | grep -oE '[0-9]+' \
  | awk '{ n += $1 } END { printf "%d\n", n }'
