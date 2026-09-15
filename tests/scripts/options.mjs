// Read prettier's options from the command line.
//
// Every comparison script takes its options the way the dump programs take
// them: as arguments of the shape `name=value`, spelled the way prettier's
// own configuration spells them (`semi=false`, `trailingComma=es5`,
// `tabWidth=4`, `quoteProps=consistent`, …).  Handing the same arguments to
// a dump program and to a comparison script compares the printer with
// prettier under one and the same configuration.
//
// Arguments that are not settings are returned as they are, so that the
// positional arguments of each script keep working.

/** Turn the text of a setting into the value prettier expects. */
function optionValue(text) {
  if (text === "true") return true;
  if (text === "false") return false;
  if (/^[0-9]+$/.test(text)) return Number(text);
  return text;
}

/**
 * Split `argv` into prettier's options and the remaining arguments.
 * `defaults` are the options every comparison uses: the parser, and
 * `objectWrap: "collapse"`, since the printer prints from a syntax tree,
 * which does not record whether the source had a line break after a `{`.
 */
export function readOptions(argv, defaults = {}) {
  const options = { ...defaults };
  const rest = [];
  for (const arg of argv) {
    const m = /^([A-Za-z][A-Za-z0-9]*)=(.*)$/.exec(arg);
    if (m) options[m[1]] = optionValue(m[2]);
    else rest.push(arg);
  }
  return { options, rest };
}

/** The options as a one line description, for a report. */
export function describeOptions(options) {
  const skip = new Set(["parser", "objectWrap"]);
  const shown = Object.entries(options).filter(([k]) => !skip.has(k));
  return shown.length === 0
    ? "default options"
    : shown.map(([k, v]) => `${k}=${v}`).join(" ");
}

/**
 * Split a dump file into its samples.
 *
 * A dump holds the printer's output for every sample, each preceded by a
 * line `===CASE <name>`.  The text of a sample is taken as it stands,
 * line terminators included, so that a dump written under `endOfLine`
 * other than `lf` is compared as it was printed; the marker lines
 * themselves always end with a line feed.
 */
export function readCases(text) {
  const marks = [...text.matchAll(/^===CASE (.*)\n/gm)];
  return marks.map((m, i) => ({
    name: m[1],
    text: text.slice(
      m.index + m[0].length,
      i + 1 < marks.length ? marks[i + 1].index : text.length,
    ),
  }));
}
