#!/bin/sh
# A wider sweep under non-default options than `scripts/check-options.sh`
# runs: random JavaScript programs, general and JSX, compared with
# prettier over a range of seeds and nesting levels, for every
# configuration listed below.
#
# Usage:  sh scripts/sweep-options.sh [count] [first-seed] [last-seed]
#
# `PRETTIER` may point at an installed prettier module.
set -e
cd "$(dirname "$0")/.."
lake build fuzz >/dev/null

count="${1:-100}"
first="${2:-100}"
last="${3:-104}"

# One configuration to a line.  These are the settings that change a
# layout decision rather than only its spelling, together with a few
# combinations of them.
CONFIGS='
semi=false
singleQuote=true
quoteProps=consistent
quoteProps=preserve
trailingComma=none
trailingComma=es5
bracketSpacing=false
bracketSameLine=true
singleAttributePerLine=true
arrowParens=avoid
tabWidth=4
useTabs=true
printWidth=40
printWidth=60
experimentalOperatorPosition=start
experimentalTernaries=true
experimentalTernaries=true printWidth=40
experimentalTernaries=true arrowParens=avoid tabWidth=4
semi=false arrowParens=avoid trailingComma=none
semi=false experimentalTernaries=true printWidth=60
'

seed="$first"
while [ "$seed" -le "$last" ]; do
  echo "$CONFIGS" | while IFS= read -r config; do
    [ -z "$config" ] && continue
    for nesting in 0 2; do
      printf 'seed %s nesting %s  %s: ' "$seed" "$nesting" "$config"
      ./.lake/build/bin/fuzz "$count" "$seed" 4 3 "$nesting" "" $config > /tmp/swo.txt
      node scripts/diff-prettier.mjs /tmp/swo.txt 2 $config | tail -1
      printf 'seed %s nesting %s  %s (jsx): ' "$seed" "$nesting" "$config"
      ./.lake/build/bin/fuzz "$count" "$seed" 3 3 "$nesting" jsx $config > /tmp/swo-jsx.txt
      node scripts/diff-prettier.mjs /tmp/swo-jsx.txt 2 $config | tail -1
    done
  done
  seed=$((seed + 1))
done
