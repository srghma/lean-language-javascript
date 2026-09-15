#!/bin/sh
# A wider sweep of random TypeScript programs under non-default options
# than `scripts/check-options-ts.sh` runs: the comparison with prettier,
# and the guarded one, over a range of seeds and nesting levels, for
# every configuration listed below.
#
# Usage:  sh scripts/sweep-options-ts.sh [count] [first-seed] [last-seed]
#
# `PRETTIER` may point at an installed prettier module.
set -e
cd "$(dirname "$0")/.."
lake build fuzztsgen >/dev/null

count="${1:-100}"
first="${2:-100}"
last="${3:-104}"

# One configuration to a line: the settings that change a layout decision
# rather than only its spelling, and a few combinations of them.
CONFIGS='
semi=false
singleQuote=true
quoteProps=consistent
quoteProps=preserve
trailingComma=none
trailingComma=es5
bracketSpacing=false
arrowParens=avoid
tabWidth=4
useTabs=true
printWidth=40
printWidth=60
experimentalOperatorPosition=start
experimentalTernaries=true
experimentalTernaries=true printWidth=40
semi=false arrowParens=avoid trailingComma=none tabWidth=4
'

seed="$first"
while [ "$seed" -le "$last" ]; do
  echo "$CONFIGS" | while IFS= read -r config; do
    [ -z "$config" ] && continue
    for nesting in 0 2; do
      ./.lake/build/bin/fuzztsgen "$count" "$seed" 3 3 "$nesting" $config > /tmp/swots.txt
      ./.lake/build/bin/fuzztsgen "$count" "$seed" 3 3 "$nesting" guard $config \
        > /tmp/swots-g.txt
      printf 'seed %s nesting %s  %s: ' "$seed" "$nesting" "$config"
      node scripts/diff-prettier-ts.mjs /tmp/swots.txt 2 /tmp/swots-g.txt $config | tail -1
      printf 'seed %s nesting %s  %s (guarded): ' "$seed" "$nesting" "$config"
      node scripts/check-guard-ts.mjs /tmp/swots-g.txt /tmp/swots.txt 2 $config | tail -1
    done
  done
  seed=$((seed + 1))
done
