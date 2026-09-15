#!/bin/sh
# Build the scratch samples of `Tests/Scratch.lean` and show how prettier
# would have written them.
#
# Usage:  sh scripts/scratch.sh
set -e
cd "$(dirname "$0")/.."
lake build scratch >/dev/null
./.lake/build/bin/scratch > /tmp/scratch.txt
node scripts/check-prettier.mjs /tmp/scratch.txt
