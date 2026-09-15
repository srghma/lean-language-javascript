// Compare the MiniAST printer's output with prettier's.
//
// Usage:  node scripts/check-prettier.mjs <dump-file>
//
// The dump file holds the printer's output for every sample of
// `Tests/Corpus.lean`, each preceded by a line `===CASE <name>`.  For every
// sample the script reformats the printed source with prettier (default
// options, which are two space indentation and an eighty column width) and
// reports the samples prettier would have written differently.
//
// Prettier is not a dependency of the Lean build; install it with
// `npm install prettier` and run this script by hand when the printer
// changes.

import { readFileSync } from "node:fs";
import { readOptions, readCases } from "./options.mjs";
// Resolve prettier from the directory it was installed in (`PRETTIER` may
// point at the module, e.g. /path/to/node_modules/prettier/index.mjs).
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
const text = readFileSync(file, "utf8");

const cases = readCases(text);

let bad = 0;
for (const c of cases) {
  // the text of the sample as the printer wrote it, its line terminator
  // included: an empty program prints as nothing at all
  const src = c.text;
  let out;
  try {
    out = await prettier.format(src, options);
  } catch (e) {
    console.log(`--- ${c.name}: PARSE ERROR: ${e.message.split("\n")[0]}`);
    bad++;
    continue;
  }
  if (out !== src) {
    bad++;
    console.log(`--- ${c.name}: DIFFERS`);
    console.log("ours:");
    console.log(src.replace(/^/gm, "  | "));
    console.log("prettier:");
    console.log(out.replace(/^/gm, "  | "));
  }
}
console.log(`${cases.length - bad}/${cases.length} samples match prettier`);
