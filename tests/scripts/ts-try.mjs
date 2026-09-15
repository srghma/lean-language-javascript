// Print a TypeScript source as prettier formats it (default options).
import prettier from "prettier";
import { readFileSync } from "node:fs";
const src = readFileSync(process.argv[2], "utf8");
try {
  process.stdout.write(
    await prettier.format(src, { parser: "typescript", objectWrap: "collapse" }),
  );
} catch (e) {
  console.log("ERR", e.message.split("\n")[0]);
}
