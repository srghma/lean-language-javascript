#!/bin/sh
# Build the scratch samples of `Tests/Ts/Scratch.lean` and show how prettier
# would have written them, reading the text as TypeScript.
#
# Usage:  sh scripts/scratch-ts.sh
set -e
cd "$(dirname "$0")/.."
lake build scratchts >/dev/null
./.lake/build/bin/scratchts > /tmp/scratch-ts.txt
node scripts/check-prettier-ts.mjs /tmp/scratch-ts.txt
