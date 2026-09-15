// Check that prettier breaks the printer's own wide output the way the
// printer breaks it at eighty columns.
//
// Usage:  node scripts/check-reflow.mjs <wide-dump> <normal-dump> [max-cases]
//
// Both files hold the same samples in the dump format (each sample preceded
// by a line `===CASE <name>`): the first printed for a very wide line, so
// that every sample stands on as few lines as it can, the second printed
// for prettier's eighty columns.  Handing the wide text to prettier must
// give the eighty column text back.
//
// This is a stronger check than reformatting the eighty column text, which
// prettier returns unchanged as soon as it is a fixed point of prettier:
// here prettier has to make the layout decisions itself, from text that
// carries none of them.  For JSX it also checks that the line breaks the
// printer writes do not change what the element means, since the wide text
// holds the children on one line, where no whitespace can be lost.
//
// The wide text cannot say whether a run of whitespace between two
// children was written `{" "}` or as a plain space: the printer writes a
// plain space wherever the line holds, as prettier does.  The two are the
// same run of whitespace, but prettier writes the first back as `{" "}`
// where the line breaks and the second as a line break alone, so a `{" "}`
// at the end of a line is left out of the comparison here.  What it stands
// for is checked instead by `scripts/check-semantics.mjs`, which compares
// what the two texts mean.
//
// Prettier is not idempotent on JSX: a line break written between two
// children which no whitespace separates is one a parser reads back as
// whitespace, and prettier lays that out as a line break of its own, so a
// second pass may break an element the first pass left alone.  The printer
// writes the layout prettier settles on, so prettier is run here until its
// output stops changing.

import { readFileSync } from "node:fs";
import { readOptions, readCases } from "./options.mjs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

const { options, rest } = readOptions(process.argv.slice(2), {
  parser: "babel",
  objectWrap: "collapse",
});

const wideFile = rest[0] ?? "/tmp/dump-wide.txt";
const normalFile = rest[1] ?? "/tmp/dump.txt";
const maxCases = Number(rest[2] ?? "10");

/** Split a dump file into its samples, in the order they are written; a
name may stand for more than one sample, so they are kept as a list. */
function parseDump(file) {
  return readCases(readFileSync(file, "utf8")).map(({ name, text }) => ({
    name,
    text: text.replace(/\s*$/, ""),
  }));
}

const wide = parseDump(wideFile);
const normal = parseDump(normalFile);

let bad = 0;
let shown = 0;
let total = 0;
for (const [index, { name, text: wideText }] of wide.entries()) {
  const want = normal[index]?.text;
  if (want === undefined) continue;
  total += 1;
  let got;
  try {
    got = wideText + "\n";
    for (let pass = 0; pass < 6; pass++) {
      const next = await prettier.format(got, options);
      if (next === got) break;
      got = next;
    }
    got = got.replace(/\s*$/, "");
  } catch (e) {
    got = `<<parse error: ${e.message.split("\n")[0]}>>`;
  }
  const ignoreJsxWhitespace = (text) => text.replaceAll(/\{" "\}$/gm, "");
  if (got === want || ignoreJsxWhitespace(got) === ignoreJsxWhitespace(want)) continue;
  bad += 1;
  if (shown < maxCases) {
    shown += 1;
    console.log(`--- ${name}`);
    console.log("--- printed at eighty columns:");
    console.log(want);
    console.log("--- prettier, from the wide text, run to a fixed point:");
    console.log(got);
    console.log("--- the wide text:");
    console.log(wideText);
  }
}
console.log(`${total - bad}/${total} samples reflow the way the printer breaks them`);
process.exitCode = bad === 0 ? 0 : 1;
