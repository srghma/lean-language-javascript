#!/bin/sh
# Compare the printer with prettier under configurations other than
# prettier's default one.
#
# Usage:  sh scripts/check-options.sh [fuzz-count] [seed]
#
# For every configuration below, the corpus and a run of random programs
# -- the general ones and the ones built around JSX -- are printed with
# that configuration and handed to prettier with the same configuration.
# The settings are spelled the way prettier's own configuration spells
# them, and are passed unchanged both to the dump programs and to the
# comparison scripts.
#
# `PRETTIER` may point at an installed prettier module.
set -e
cd "$(dirname "$0")/.."
lake build dump fuzz >/dev/null

COUNT="${1:-200}"
SEED="${2:-1}"

# One configuration to a line.  The empty line is prettier's default
# style, which `scripts/check.sh` checks in full; it is here so that the
# harness itself is checked against a configuration known to match.
CONFIGS='
semi=false
singleQuote=true
jsxSingleQuote=true
singleQuote=true jsxSingleQuote=true
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
  ./.lake/build/bin/dump $config > /tmp/dump-opt.txt
  node scripts/check-prettier.mjs /tmp/dump-opt.txt $config | tail -1
  ./.lake/build/bin/fuzz "$COUNT" "$SEED" 4 3 0 "" $config > /tmp/fuzz-opt.txt
  node scripts/diff-prettier.mjs /tmp/fuzz-opt.txt 3 $config | tail -1
  ./.lake/build/bin/fuzz "$COUNT" "$SEED" 3 3 1 jsx $config > /tmp/fuzz-opt-jsx.txt
  node scripts/diff-prettier.mjs /tmp/fuzz-opt-jsx.txt 3 $config | tail -1
  # The same samples printed for a very wide line, which prettier then has
  # to break the way the printer breaks them at eighty columns -- under
  # the same configuration, so that prettier makes every decision the
  # option changes itself, from a text that carries none of them.  A
  # configuration that sets the width of its own is left out: the wide
  # print is asked for by a width argument, which would contradict it.
  case "$config" in
    *printWidth*) ;;
    *)
      ./.lake/build/bin/dump 100000 $config > /tmp/dump-opt-wide.txt
      printf 'reflow:    '
      node scripts/check-reflow.mjs /tmp/dump-opt-wide.txt /tmp/dump-opt.txt 3 $config | tail -1
      printf 'semantics: '
      node scripts/check-semantics.mjs /tmp/dump-opt-wide.txt /tmp/dump-opt.txt 3 $config | tail -1
      ./.lake/build/bin/fuzz "$COUNT" "$SEED" 3 3 1 jsx 100000 $config \
        > /tmp/fuzz-opt-jsx-wide.txt
      printf 'reflow:    '
      node scripts/check-reflow.mjs /tmp/fuzz-opt-jsx-wide.txt /tmp/fuzz-opt-jsx.txt 3 \
        $config | tail -1
      printf 'semantics: '
      node scripts/check-semantics.mjs /tmp/fuzz-opt-jsx-wide.txt /tmp/fuzz-opt-jsx.txt 3 \
        $config | tail -1
      ;;
  esac
done
