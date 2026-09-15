// Check that prettier writes the printer's text for the tree the printer
// means, where the text itself is not read back as that tree.
//
// Usage:  node scripts/check-guard-ts.mjs <guarded-dump> <normal-dump> [max-cases]
//
// TypeScript reads an instantiation expression, `f<T>`, as a pair of
// comparisons wherever the token after it does not rule that reading out:
// `f<T> + []` is `f < T > +[]`, and `f<T>!` is not a program at all.
// Prettier writes no parentheses around such an expression, and neither
// does the printer, so the text of a sample which holds one is not always
// read back as the tree it was printed from — and then reformatting that
// text says nothing about whether the printer agrees with prettier.
//
// Both files here hold the same samples in the dump format (each preceded
// by a line `===CASE <name>`): the first printed with parentheses around
// every instantiation expression, which is a text TypeScript does read
// back as the intended tree, the second printed in the ordinary style.
// Prettier drops the redundant parentheses, so handing it the guarded text
// must give the ordinary text back.  Where it does not, the printer and
// prettier really disagree.

import { readFileSync } from "node:fs";
import { readOptions, readCases } from "./options.mjs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

const { options, rest } = readOptions(process.argv.slice(2), {
  parser: "typescript",
  objectWrap: "collapse",
});

// The line terminator the dumps were written with, which is also the one
// prettier writes under this configuration: the samples are compared with
// the terminator their own `endOfLine` asks for.
const eol =
  options.endOfLine === "crlf" ? "\r\n" : options.endOfLine === "cr" ? "\r" : "\n";

const guardedFile = rest[0] ?? "/tmp/dump-ts-guarded.txt";
const normalFile = rest[1] ?? "/tmp/dump-ts.txt";
const maxCases = Number(rest[2] ?? "10");

/** Split a dump file into its samples, in the order they are written. */
function parseDump(file) {
  const cases = [];
  cases.push(
    ...readCases(readFileSync(file, "utf8")).map(({ name, text }) => ({
      name,
      text: text.replace(/\s*$/, ""),
    })),
  );
  return cases;
}

const guarded = parseDump(guardedFile);
const normal = parseDump(normalFile);
if (guarded.length !== normal.length) {
  console.log(
    `the two dumps hold different numbers of samples: ${guarded.length} and ${normal.length}`,
  );
  process.exit(1);
}

let bad = 0;
let rejected = 0;
let shown = 0;
for (let i = 0; i < guarded.length; i++) {
  const { name } = normal[i];
  const src = guarded[i].text === "" ? "" : guarded[i].text + eol;
  const want = normal[i].text === "" ? "" : normal[i].text + eol;
  let out;
  try {
    out = await prettier.format(src, options);
  } catch (e) {
    // The guarded text may still be one the TypeScript grammar rejects:
    // the JavaScript corpus holds a few samples TypeScript does not
    // accept at all.  Such a sample is counted on its own.
    rejected++;
    if (shown++ < maxCases)
      console.log(`--- ${name}: NOT TYPESCRIPT: ${e.message.split("\n")[0]}`);
    continue;
  }
  if (out === want) continue;
  bad++;
  if (shown++ >= maxCases) continue;
  const a = want.split("\n");
  const b = out.split("\n");
  let lo = 0;
  while (lo < a.length && lo < b.length && a[lo] === b[lo]) lo++;
  let ai = a.length - 1;
  let bi = b.length - 1;
  while (ai > lo && bi > lo && a[ai] === b[bi]) {
    ai--;
    bi--;
  }
  const ctx = 2;
  console.log(`--- ${name}: DIFFERS (lines ${lo + 1}..)`);
  for (let i = Math.max(0, lo - ctx); i < lo; i++) console.log(`   ${a[i]}`);
  for (let i = lo; i <= ai; i++) console.log(`  -${a[i]}`);
  for (let i = lo; i <= bi; i++) console.log(`  +${b[i]}`);
  for (let i = ai + 1; i <= Math.min(a.length - 1, ai + ctx); i++)
    console.log(`   ${a[i]}`);
}
console.log(
  `${guarded.length - bad - rejected}/${guarded.length - rejected} samples match prettier` +
    (rejected ? ` (${rejected} not accepted by the TypeScript grammar)` : ""),
);
