// Print how prettier formats a piece of JavaScript.
//
// Usage:  node scripts/format.mjs <file>        (or read from stdin)
//
// The options are the ones the conformance scripts compare against:
// prettier's defaults, plus `objectWrap: "collapse"` (see the note in
// scripts/check-prettier.mjs).

import { readFileSync } from "node:fs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

const options = { parser: "babel", objectWrap: "collapse" };

const file = process.argv[2];
const src = readFileSync(file ?? 0, "utf8");
process.stdout.write(await prettier.format(src, options));
