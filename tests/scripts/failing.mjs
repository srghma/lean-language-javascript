// List the names of the samples the printer writes differently from prettier.
//
// Usage:  node scripts/failing.mjs <dump-file>
//
// Reads the dump format of `scripts/check-prettier.mjs` and prints one name
// per line, so that two runs can be compared with `diff`.

import { readFileSync } from "node:fs";
import { readCases } from "./options.mjs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

// Prettier keeps an object literal spread over several lines when the
// source it reads has a line break right after the `{`.  The printer here
// prints from a syntax tree, which holds no such information, so the
// comparison turns that off with `objectWrap: "collapse"`; every other
// option is prettier's default (two space indentation, eighty columns).
const options = { parser: "babel", objectWrap: "collapse" };


const text = readFileSync(process.argv[2] ?? "/tmp/dump.txt", "utf8");
const cases = readCases(text);

for (const c of cases) {
  const body = c.lines.join("\n").replace(/\s*$/, "");
  // an empty program prints as nothing at all, not as a blank line
  const src = body === "" ? "" : body + "\n";
  let out;
  try {
    out = await prettier.format(src, options);
  } catch {
    console.log(`${c.name} PARSE-ERROR`);
    continue;
  }
  if (out !== src) console.log(c.name);
}
