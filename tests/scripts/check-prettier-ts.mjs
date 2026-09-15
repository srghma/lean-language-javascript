// Compare the MiniTsAST printer's output with prettier's.
//
// Usage:  node scripts/check-prettier-ts.mjs <dump-file> [guarded-dump]
//
// The dump file holds the printer's output for every sample of
// `Tests/Ts/Corpus*.lean`, each preceded by a line `===CASE <name>`.  For
// every sample the script reformats the printed source with prettier
// (`parser: "typescript"`, prettier's default options) and reports the
// samples prettier would have written differently.
//
// A second argument names the same samples printed with the parentheses
// that make TypeScript read the text back as the tree it was printed from
// (`dumpts 80 guard`).  A sample whose text TypeScript reads as another
// tree is one this comparison cannot judge: prettier rewrites it, but so
// would it rewrite its own output for that tree.  Where the guarded text
// is given, such a sample is recognised — prettier turns the guarded text
// into ours — and counted on its own.  `scripts/check-guard-ts.mjs` is
// the comparison that judges those samples.
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

const file = rest[0] ?? "/tmp/dump-ts.txt";
const guardedFile = rest[1];

/** Split a dump file into its samples, in the order they are written. */
function parseDump(path) {
  return readCases(readFileSync(path, "utf8"));
}

/** Whether prettier writes `ours` for the tree the guarded text holds. */
async function formatsToOurs(guardedText, ours) {
  try {
    return (await prettier.format(guardedText, options)) === ours;
  } catch {
    return false;
  }
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
    // all JavaScript that TypeScript does not accept.  Such a sample is
    // counted on its own rather than as a difference.
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
  console.log(`--- ${c.name}: DIFFERS`);
  console.log("ours:");
  console.log(src.replace(/^/gm, "  | "));
  console.log("prettier:");
  console.log(out.replace(/^/gm, "  | "));
}
console.log(
  `${cases.length - bad - rejected - reread}/${cases.length - rejected - reread}` +
    ` samples match prettier` +
    (rejected ? ` (${rejected} not accepted by the TypeScript grammar)` : "") +
    (reread ? ` (${reread} read back as another tree, see check-guard-ts.mjs)` : ""),
);
