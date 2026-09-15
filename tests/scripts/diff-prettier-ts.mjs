// Show a compact diff between the MiniTsAST printer's output and prettier's,
// reading the text as TypeScript.
//
// Usage:  node scripts/diff-prettier-ts.mjs <dump-file> [max-cases] [guarded-dump]
//
// Reads the same dump format as `scripts/check-prettier.mjs` (each sample
// preceded by a line `===CASE <name>`) and, for every sample prettier would
// have written differently, prints only the differing lines with a little
// context.  This makes the failures of a large fuzz run readable.
//
// A third argument names the same samples printed with the parentheses
// that make TypeScript read the text back as the tree it was printed from
// (`dumpts 80 guard`, `fuzztsgen … 80 guard`).  A sample whose text
// TypeScript reads as another tree is one this comparison cannot judge:
// prettier rewrites it, but so would it rewrite its own output for that
// tree.  Where the guarded text is given, such a sample is recognised —
// prettier turns the guarded text into ours — and counted on its own
// rather than as a difference.  `scripts/check-guard-ts.mjs` is the
// comparison that judges those samples.

import { readFileSync } from "node:fs";
import { readOptions, readCases } from "./options.mjs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

// Prettier keeps an object literal spread over several lines when the
// source it reads has a line break right after the `{`.  The printer here
// prints from a syntax tree, which holds no such information, so the
// comparison turns that off with `objectWrap: "collapse"`; every other
// option is prettier's default (two space indentation, eighty columns).
const { options, rest } = readOptions(process.argv.slice(2), {
  parser: "typescript",
  objectWrap: "collapse",
});

const file = rest[0] ?? "/tmp/dump.txt";
const maxCases = Number(rest[1] ?? "10");
const guardedFile = rest[2];

/** Split a dump file into its samples, in the order they are written. */
function parseDump(path) {
  const cases = [];
  cases.push(...readCases(readFileSync(path, "utf8")));
  return cases;
}

const cases = parseDump(file);
const guarded = guardedFile ? parseDump(guardedFile) : null;
if (guarded && guarded.length !== cases.length) {
  console.log(
    `the two dumps hold different numbers of samples: ${cases.length} and ${guarded.length}`,
  );
  process.exit(1);
}

let bad = 0;
let rejected = 0;
let reread = 0;
let shown = 0;
for (let i = 0; i < cases.length; i++) {
  const c = cases[i];
  const src = c.text;
  let out;
  try {
    out = await prettier.format(src, options);
  } catch (e) {
    // The TypeScript grammar is not a superset of the JavaScript one: a
    // decorated class expression, a JSX element in the head of a `for`,
    // `for (let.x = 1; ; )` and a private name in an optional chain are
    // all JavaScript that TypeScript does not accept.  A text prettier
    // cannot read says nothing either way, so such a sample is counted
    // on its own rather than as a difference; its name is always shown.
    // So is a text prettier cannot read back because of the ambiguities
    // the guarded text settles.
    if (guarded && (await formatsToOurs(guarded[i].text, src))) {
      reread++;
      continue;
    }
    rejected++;
    console.log(`--- ${c.name}: NOT TYPESCRIPT: ${e.message.split("\n")[0]}`);
    continue;
  }
  if (out === src) continue;
  if (guarded && (await formatsToOurs(guarded[i].text, src))) {
    reread++;
    continue;
  }
  bad++;
  if (shown++ >= maxCases) continue;
  const a = src.split("\n");
  const b = out.split("\n");
  // First and last differing line index.
  let lo = 0;
  while (lo < a.length && lo < b.length && a[lo] === b[lo]) lo++;
  let ai = a.length - 1;
  let bi = b.length - 1;
  while (ai > lo && bi > lo && a[ai] === b[bi]) {
    ai--;
    bi--;
  }
  const ctx = 2;
  console.log(`--- ${c.name}: DIFFERS (lines ${lo + 1}..)`);
  for (let i = Math.max(0, lo - ctx); i < lo; i++) console.log(`   ${a[i]}`);
  for (let i = lo; i <= ai; i++) console.log(`  -${a[i]}`);
  for (let i = lo; i <= bi; i++) console.log(`  +${b[i]}`);
  for (let i = ai + 1; i <= Math.min(a.length - 1, ai + ctx); i++)
    console.log(`   ${a[i]}`);
}

/** Whether prettier writes `ours` for the tree the guarded text holds. */
async function formatsToOurs(guardedText, ours) {
  try {
    return (await prettier.format(guardedText, options)) === ours;
  } catch {
    return false;
  }
}

console.log(
  `${cases.length - bad - rejected - reread}/${cases.length - rejected - reread}` +
    ` samples match prettier` +
    (rejected ? ` (${rejected} not accepted by the TypeScript grammar)` : "") +
    (reread ? ` (${reread} read back as another tree, see check-guard-ts.mjs)` : ""),
);
