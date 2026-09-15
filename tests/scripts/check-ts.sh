#!/bin/sh
# Build the TypeScript printer and compare its output with prettier's, on
# the TypeScript corpus, on the JavaScript corpus read as TypeScript, and
# on runs of random programs.
#
# Usage:  sh scripts/check-ts.sh [fuzz-count] [seed]
#
# `PRETTIER` may point at an installed prettier module.
set -e
cd "$(dirname "$0")/.."
lake build dumpts dumpjsts fuzzts fuzztsgen >/dev/null

# The TypeScript corpus: every sample printed, and prettier asked to
# return it unchanged.
./.lake/build/bin/dumpts > /tmp/dump-ts.txt
./.lake/build/bin/dumpts 80 guard > /tmp/dump-ts-guarded.txt
./.lake/build/bin/dumpts 100000 guard > /tmp/dump-ts-wide.txt
printf 'corpus:            '
node scripts/check-prettier-ts.mjs /tmp/dump-ts.txt /tmp/dump-ts-guarded.txt | tail -1
# The same samples printed with the parentheses that make TypeScript read
# the text back as the tree it was printed from.  Prettier drops those
# parentheses, so it has to give the text above back.  This is what says
# that the printer agrees with prettier even where a text prettier leaves
# alone would prove nothing, because TypeScript reads it as another tree.
printf 'corpus, guarded:   '
node scripts/check-guard-ts.mjs /tmp/dump-ts-guarded.txt /tmp/dump-ts.txt 0 | tail -1
# The same samples printed a second time for a very wide line, so that
# each of them stands on as few lines as it can.  Prettier has to make the
# layout decisions itself, from a text that carries none of them, and give
# the eighty column text back; this says more than reformatting a text
# prettier already agrees with.
printf 'corpus, reflowed:  '
node scripts/check-guard-ts.mjs /tmp/dump-ts-wide.txt /tmp/dump-ts.txt 0 | tail -1

# The JavaScript corpus, printed by the TypeScript printer: every
# JavaScript program is a TypeScript program, so the text has to be one
# prettier returns unchanged when it reads it as TypeScript.  A few
# samples are JavaScript the TypeScript grammar does not accept at all
# (a decorated class expression, `for (let.x = 1; ; )`, a private name in
# an optional chain, a JSX element in the head of a `for`); they are
# counted on their own.
./.lake/build/bin/dumpjsts > /tmp/dump-jsts.txt
printf 'JavaScript corpus: '
node scripts/check-prettier-ts.mjs /tmp/dump-jsts.txt | tail -1

# Random TypeScript programs, at four indentations: a layout decision
# depends on the width that is left on the line, so printing the same
# programs inside nested namespaces exercises the decisions at several
# widths.
for nesting in 0 1 2 3; do
  ./.lake/build/bin/fuzztsgen "${1:-200}" "${2:-1}" 3 3 "$nesting" > /tmp/fuzz-ts-$nesting.txt
  ./.lake/build/bin/fuzztsgen "${1:-200}" "${2:-1}" 3 3 "$nesting" 80 guard \
    > /tmp/fuzz-ts-guarded-$nesting.txt
  ./.lake/build/bin/fuzztsgen "${1:-200}" "${2:-1}" 3 3 "$nesting" 100000 guard \
    > /tmp/fuzz-ts-wide-$nesting.txt
  printf 'random, nesting %s:          ' "$nesting"
  node scripts/diff-prettier-ts.mjs /tmp/fuzz-ts-$nesting.txt 0 \
    /tmp/fuzz-ts-guarded-$nesting.txt | tail -1
  printf 'random, nesting %s, guarded: ' "$nesting"
  node scripts/check-guard-ts.mjs /tmp/fuzz-ts-guarded-$nesting.txt \
    /tmp/fuzz-ts-$nesting.txt 0 | tail -1
  printf 'random, nesting %s, reflow:  ' "$nesting"
  node scripts/check-guard-ts.mjs /tmp/fuzz-ts-wide-$nesting.txt \
    /tmp/fuzz-ts-$nesting.txt 0 | tail -1
done

# Random JavaScript programs printed by the TypeScript printer, at the
# same several indentations.
for nesting in 0 1 2; do
  ./.lake/build/bin/fuzzts "${1:-200}" "${2:-1}" 4 3 "$nesting" > /tmp/fuzz-jsts-$nesting.txt
  printf 'random JavaScript, nesting %s: ' "$nesting"
  node scripts/diff-prettier-ts.mjs /tmp/fuzz-jsts-$nesting.txt 0 | tail -1
done
