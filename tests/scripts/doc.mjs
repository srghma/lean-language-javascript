import prettier from "prettier";
import fs from "fs";
const code = fs.readFileSync(process.argv[2], "utf8");
const doc = await prettier.__debug.printToDoc(code, { parser: "typescript" });
console.log(await prettier.__debug.formatDoc(doc, { parser: "babel" }));
