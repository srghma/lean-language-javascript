// Check that the line breaks the printer writes inside JSX do not change
// what the JSX means.
//
// Usage:  node scripts/check-semantics.mjs <wide-dump> <normal-dump> [max-cases]
//
// Both files hold the same samples in the dump format (each sample preceded
// by a line `===CASE <name>`): the first printed for a very wide line, the
// second for prettier's eighty columns.  The wide text holds the children
// of every element on one line, where no line break can swallow whitespace,
// so it says what the element means; the eighty column text has to mean the
// same.
//
// This is what the other two harnesses cannot see.  A run of whitespace a
// line break swallows has to be written `{" "}`, and an element printed
// without the `{" "}` it needs is still a text prettier returns unchanged —
// it is simply a different element.  Here the two prints of the same tree
// are read back and compared, so a lost (or invented) space is a failure.
//
// Both texts are parsed and every JSX element in them is reduced to a
// signature: its name, its attributes, and the sequence its children
// denote, with the whitespace rules a JSX parser applies (a line break and
// the indentation around it are dropped; a run of spaces within a line
// stands).  The signatures have to agree, element for element.

import { readFileSync } from "node:fs";
import { readOptions, readCases } from "./options.mjs";
const prettier = await import(process.env.PRETTIER ?? "prettier");

// The comparison here parses both texts rather than formatting them, so
// prettier's options do not enter it; the settings are read all the same,
// so that this script takes the same arguments as the others.
const { rest } = readOptions(process.argv.slice(2));

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

const namedEntities = {
  amp: "&",
  lt: "<",
  gt: ">",
  quot: '"',
  apos: "'",
  nbsp: "\u00a0",
};

/** The characters a piece of JSX source denotes. */
function decodeEntities(text) {
  return text.replaceAll(/&(#x[0-9a-fA-F]+|#[0-9]+|[a-zA-Z]+);/g, (whole, body) => {
    if (body.startsWith("#x") || body.startsWith("#X")) {
      return String.fromCodePoint(Number.parseInt(body.slice(2), 16));
    }
    if (body.startsWith("#")) return String.fromCodePoint(Number.parseInt(body.slice(1), 10));
    const named = namedEntities[body];
    return named ?? whole;
  });
}

/** The text a JSX text child denotes: the rules a JSX parser applies to the
 * lines of the text, which drop a line break together with the indentation
 * around it, and keep a run of spaces within a line. */
function jsxTextMeaning(raw) {
  const lines = decodeEntities(raw).split(/\r\n|\n|\r/);
  let lastNonEmpty = 0;
  for (const [i, line] of lines.entries()) if (/[^ \t]/.test(line)) lastNonEmpty = i;
  let out = "";
  for (const [i, line] of lines.entries()) {
    let trimmed = line.replaceAll("\t", " ");
    if (i !== 0) trimmed = trimmed.replace(/^ +/, "");
    if (i !== lines.length - 1) trimmed = trimmed.replace(/ +$/, "");
    if (trimmed !== "") {
      if (i !== lastNonEmpty) trimmed += " ";
      out += trimmed;
    }
  }
  return out;
}

/** The name of an element or of an attribute. */
function nameOf(node) {
  switch (node.type) {
    case "JSXIdentifier":
      return node.name;
    case "JSXNamespacedName":
      return `${node.namespace.name}:${node.name.name}`;
    case "JSXMemberExpression":
      return `${nameOf(node.object)}.${nameOf(node.property)}`;
    default:
      return `<${node.type}>`;
  }
}

/** Whether the expression written in a `{ }` is the string a run of
 * whitespace is written as. */
function isWhitespaceString(expr) {
  return expr.type === "StringLiteral" && /^ +$/.test(expr.value);
}

/** The signature of the children of an element: the text they denote, with
 * the substitutions and the nested elements standing between the runs of
 * text as markers. */
function childrenSignature(children) {
  const items = [];
  const pushText = (text) => {
    if (text === "") return;
    if (typeof items.at(-1) === "string") items[items.length - 1] += text;
    else items.push(text);
  };
  for (const child of children) {
    switch (child.type) {
      case "JSXText":
        pushText(jsxTextMeaning(child.extra?.raw ?? child.value));
        break;
      case "JSXExpressionContainer":
        if (isWhitespaceString(child.expression)) pushText(child.expression.value);
        else if (child.expression.type === "JSXEmptyExpression") items.push("{}");
        else items.push("{expr}");
        break;
      case "JSXSpreadChild":
        items.push("{...}");
        break;
      case "JSXElement":
      case "JSXFragment":
        items.push("<node>");
        break;
      default:
        items.push(`<${child.type}>`);
    }
  }
  return items;
}

/** The signature of one attribute. */
function attributeSignature(attr) {
  if (attr.type === "JSXSpreadAttribute") return "{...}";
  const name = nameOf(attr.name);
  const value = attr.value;
  if (value == null) return name;
  switch (value.type) {
    case "StringLiteral":
      return `${name}=${JSON.stringify(decodeEntities(value.extra?.raw?.slice(1, -1) ?? value.value))}`;
    case "JSXExpressionContainer":
      return `${name}={expr}`;
    default:
      return `${name}=<node>`;
  }
}

/** The signature of a JSX element or fragment. */
function elementSignature(node) {
  if (node.type === "JSXFragment") {
    return JSON.stringify(["<>", [], childrenSignature(node.children)]);
  }
  const opening = node.openingElement;
  return JSON.stringify([
    nameOf(opening.name),
    opening.attributes.map(attributeSignature),
    opening.selfClosing ? null : childrenSignature(node.children),
  ]);
}

/** The signatures of every JSX element of a program, in the order they are
 * written. */
function signatures(ast) {
  const out = [];
  const walk = (node) => {
    if (Array.isArray(node)) {
      for (const item of node) walk(item);
      return;
    }
    if (node === null || typeof node !== "object") return;
    if (node.type === "JSXElement" || node.type === "JSXFragment") out.push(elementSignature(node));
    for (const [key, value] of Object.entries(node)) {
      if (key === "loc" || key === "extra" || key === "tokens" || key === "comments") continue;
      walk(value);
    }
  };
  walk(ast);
  return out;
}

const wide = parseDump(wideFile);
const normal = parseDump(normalFile);

let bad = 0;
let shown = 0;
let total = 0;
for (const [index, { name, text: wideText }] of wide.entries()) {
  const narrowText = normal[index]?.text;
  if (narrowText === undefined) continue;
  total += 1;
  let wideSigs;
  let narrowSigs;
  try {
    wideSigs = signatures((await prettier.__debug.parse(wideText, { parser: "babel" })).ast);
    narrowSigs = signatures((await prettier.__debug.parse(narrowText, { parser: "babel" })).ast);
  } catch (e) {
    wideSigs = [`<<parse error: ${e.message.split("\n")[0]}>>`];
    narrowSigs = [];
  }
  if (wideSigs.length === narrowSigs.length && wideSigs.every((s, i) => s === narrowSigs[i])) {
    continue;
  }
  bad += 1;
  if (shown < maxCases) {
    shown += 1;
    console.log(`--- ${name}`);
    const n = Math.max(wideSigs.length, narrowSigs.length);
    for (let i = 0; i < n; i++) {
      if (wideSigs[i] === narrowSigs[i]) continue;
      console.log(`  wide:   ${wideSigs[i]}`);
      console.log(`  narrow: ${narrowSigs[i]}`);
    }
    console.log("--- printed at eighty columns:");
    console.log(narrowText);
    console.log("--- the wide text:");
    console.log(wideText);
  }
}
console.log(`${total - bad}/${total} samples mean the same at both widths`);
process.exitCode = bad === 0 ? 0 : 1;
