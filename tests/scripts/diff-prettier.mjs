// Show a compact diff between the MiniAST printer's output and prettier's.
//
// Usage:  node scripts/diff-prettier.mjs <dump-file> [max-cases]
//
// Reads the same dump format as `scripts/check-prettier.mjs` (each sample
// preceded by a line `===CASE <name>`) and, for every sample prettier would
// have written differently, prints only the differing lines with a little
// context.  This makes the failures of a large fuzz run readable.

import { readFileSync } from "node:fs";
import { readOptions, readCases } from "./options.mjs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

// Prettier keeps an object literal spread over several lines when the
// source it reads has a line break right after the `{`.  The printer here
// prints from a syntax tree, which holds no such information, so the
// comparison turns that off with `objectWrap: "collapse"`; every other
// option is prettier's default (two space indentation, eighty columns).
const { options, rest } = readOptions(process.argv.slice(2), {
  parser: "babel",
  objectWrap: "collapse",
});


const file = rest[0] ?? "/tmp/dump.txt";
const maxCases = Number(rest[1] ?? "10");
const text = readFileSync(file, "utf8");

const cases = readCases(text);

let bad = 0;
let shown = 0;
for (const c of cases) {
  // the text of the sample as the printer wrote it, its line terminator
  // included: an empty program prints as nothing at all
  const src = c.text;
  let out;
  try {
    out = await prettier.format(src, options);
  } catch (e) {
    bad++;
    if (shown++ < maxCases)
      console.log(`--- ${c.name}: PARSE ERROR: ${e.message.split("\n")[0]}`);
    continue;
  }
  if (out === src) continue;
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
console.log(`${cases.length - bad}/${cases.length} samples match prettier`);
