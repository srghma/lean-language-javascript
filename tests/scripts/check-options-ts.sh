#!/bin/sh
# Compare the TypeScript printer with prettier under configurations other
# than prettier's default one.
#
# Usage:  sh scripts/check-options-ts.sh [fuzz-count] [seed]
#
# For every configuration below, the TypeScript corpus, the JavaScript
# corpus read as TypeScript, and a run of random TypeScript programs are
# printed with that configuration and handed to prettier with the same
# configuration.  The settings are spelled the way prettier's own
# configuration spells them, and are passed unchanged both to the dump
# programs and to the comparison scripts.
#
# `PRETTIER` may point at an installed prettier module.
set -e
cd "$(dirname "$0")/.."
lake build dumpts dumpjsts fuzztsgen >/dev/null

COUNT="${1:-100}"
SEED="${2:-1}"

# One configuration to a line.  The empty line is prettier's default
# style, which `scripts/check-ts.sh` checks in full; it is here so that
# the harness itself is checked against a configuration known to match.
CONFIGS='
semi=false
singleQuote=true
jsxSingleQuote=true
quoteProps=consistent
quoteProps=preserve
trailingComma=none
trailingComma=es5
bracketSpacing=false
bracketSameLine=true
singleAttributePerLine=true
arrowParens=avoid
tabWidth=4
tabWidth=8
useTabs=true
useTabs=true tabWidth=4
printWidth=40
printWidth=120
experimentalOperatorPosition=start
experimentalTernaries=true
experimentalTernaries=true tabWidth=4
experimentalTernaries=true useTabs=true
experimentalTernaries=true printWidth=40
endOfLine=crlf
endOfLine=cr
semi=false singleQuote=true trailingComma=none bracketSpacing=false arrowParens=avoid tabWidth=4
'

echo "$CONFIGS" | while IFS= read -r config; do
  [ -z "$config" ] && continue
  echo "=== $config"
  ./.lake/build/bin/dumpts $config > /tmp/dump-ts-opt.txt
  ./.lake/build/bin/dumpts guard $config > /tmp/dump-ts-opt-guarded.txt
  printf 'corpus:            '
  node scripts/check-prettier-ts.mjs /tmp/dump-ts-opt.txt /tmp/dump-ts-opt-guarded.txt \
    $config | tail -1
  printf 'corpus, guarded:   '
  node scripts/check-guard-ts.mjs /tmp/dump-ts-opt-guarded.txt /tmp/dump-ts-opt.txt 0 \
    $config | tail -1
  ./.lake/build/bin/dumpjsts $config > /tmp/dump-jsts-opt.txt
  printf 'JavaScript corpus: '
  node scripts/check-prettier-ts.mjs /tmp/dump-jsts-opt.txt $config | tail -1
  ./.lake/build/bin/fuzztsgen "$COUNT" "$SEED" 3 3 0 $config > /tmp/fuzz-ts-opt.txt
  ./.lake/build/bin/fuzztsgen "$COUNT" "$SEED" 3 3 0 guard $config \
    > /tmp/fuzz-ts-opt-guarded.txt
  printf 'random:            '
  node scripts/diff-prettier-ts.mjs /tmp/fuzz-ts-opt.txt 0 /tmp/fuzz-ts-opt-guarded.txt \
    $config | tail -1
  printf 'random, guarded:   '
  node scripts/check-guard-ts.mjs /tmp/fuzz-ts-opt-guarded.txt /tmp/fuzz-ts-opt.txt 0 \
    $config | tail -1
  # The same samples printed for a very wide line, which prettier then has
  # to break the way the printer breaks them at eighty columns, under the
  # same configuration: prettier makes every decision the option changes
  # itself, from a text that carries none of them.  A configuration that
  # sets a width of its own is left out, since the wide print is asked for
  # by a width argument.
  case "$config" in
    *printWidth*) ;;
    *)
      ./.lake/build/bin/dumpts 100000 guard $config > /tmp/dump-ts-opt-wide.txt
      printf 'corpus, reflowed:  '
      node scripts/check-guard-ts.mjs /tmp/dump-ts-opt-wide.txt /tmp/dump-ts-opt.txt 0 \
        $config | tail -1
      ./.lake/build/bin/fuzztsgen "$COUNT" "$SEED" 3 3 0 100000 guard $config \
        > /tmp/fuzz-ts-opt-wide.txt
      printf 'random, reflowed:  '
      node scripts/check-guard-ts.mjs /tmp/fuzz-ts-opt-wide.txt /tmp/fuzz-ts-opt.txt 0 \
        $config | tail -1
      ;;
  esac
done
