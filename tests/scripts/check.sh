#!/bin/sh
# Build the printer and compare its output with prettier's, on the corpus
# and on a run of random programs.
#
# Usage:  sh scripts/check.sh [fuzz-count] [seed]
#
# `PRETTIER` may point at an installed prettier module.
set -e
cd "$(dirname "$0")/.."
lake build dump fuzz >/dev/null
./.lake/build/bin/dump > /tmp/dump.txt
node scripts/check-prettier.mjs /tmp/dump.txt | tail -1
./.lake/build/bin/fuzz "${1:-400}" "${2:-1}" > /tmp/fuzz.txt
node scripts/diff-prettier.mjs /tmp/fuzz.txt 0 | tail -1
# The same programs, written inside nested blocks: a layout decision
# depends on the width that is left on the line, so printing them at
# several indentations exercises the decisions at several widths.
for nesting in 1 2 3; do
  ./.lake/build/bin/fuzz "${1:-400}" "${2:-1}" 4 3 "$nesting" > /tmp/fuzz-$nesting.txt
  node scripts/diff-prettier.mjs /tmp/fuzz-$nesting.txt 0 | tail -1
done
# Random programs built around JSX elements, which the generator above
# writes only now and then, at the same several indentations.
for nesting in 0 1 2 3; do
  ./.lake/build/bin/fuzz "${1:-400}" "${2:-1}" 3 3 "$nesting" jsx > /tmp/fuzz-jsx-$nesting.txt
  node scripts/diff-prettier.mjs /tmp/fuzz-jsx-$nesting.txt 0 | tail -1
done
# The same samples printed for a very wide line, which holds each of them
# on as few lines as it can.  Prettier has to break that text the way the
# printer breaks it at eighty columns, and the two texts have to mean the
# same: a run of whitespace a line break swallows is one the printer has
# to write `{" "}`, which neither comparison above can see.
./.lake/build/bin/dump 100000 > /tmp/dump-wide.txt
node scripts/check-reflow.mjs /tmp/dump-wide.txt /tmp/dump.txt 0 | tail -1
node scripts/check-semantics.mjs /tmp/dump-wide.txt /tmp/dump.txt 0 | tail -1
for nesting in 0 2; do
  ./.lake/build/bin/fuzz "${1:-400}" "${2:-1}" 3 3 "$nesting" jsx 100000 > /tmp/fuzz-jsx-wide-$nesting.txt
  node scripts/check-reflow.mjs /tmp/fuzz-jsx-wide-$nesting.txt /tmp/fuzz-jsx-$nesting.txt 0 | tail -1
  node scripts/check-semantics.mjs /tmp/fuzz-jsx-wide-$nesting.txt /tmp/fuzz-jsx-$nesting.txt 0 | tail -1
done
