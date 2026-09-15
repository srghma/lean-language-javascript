#!/bin/sh
# A wider sweep of random TypeScript programs than `scripts/check-ts.sh`
# runs: the same three comparisons with prettier, over a range of seeds,
# tree depths and nesting levels.
#
# Usage:  sh scripts/sweep-ts.sh [count] [first-seed] [last-seed]
set -e
cd "$(dirname "$0")/.."
lake build fuzztsgen fuzzts >/dev/null
count="${1:-200}"
first="${2:-100}"
last="${3:-110}"
seed="$first"
while [ "$seed" -le "$last" ]; do
  for depth in 2 3 4; do
    for nesting in 0 1 2 3; do
      ./.lake/build/bin/fuzztsgen "$count" "$seed" "$depth" 3 "$nesting" > /tmp/sw.txt
      ./.lake/build/bin/fuzztsgen "$count" "$seed" "$depth" 3 "$nesting" 80 guard > /tmp/sw-g.txt
      ./.lake/build/bin/fuzztsgen "$count" "$seed" "$depth" 3 "$nesting" 100000 guard > /tmp/sw-w.txt
      printf 'seed %s depth %s nesting %s: ' "$seed" "$depth" "$nesting"
      node scripts/diff-prettier-ts.mjs /tmp/sw.txt 0 /tmp/sw-g.txt | tail -1
      printf '  guarded: '
      node scripts/check-guard-ts.mjs /tmp/sw-g.txt /tmp/sw.txt 0 | tail -1
      printf '  reflow:  '
      node scripts/check-guard-ts.mjs /tmp/sw-w.txt /tmp/sw.txt 0 | tail -1
    done
  done
  seed=$((seed + 1))
done
