/-
A synthetic JavaScript source of arbitrary size, used by the benchmark
(`lake exe bench`) and by the large input test of the test suite.
-/

namespace LanguageJavaScriptBench.Sample

/-- One chunk of the synthetic input: a mixture of the constructs the lexer
has to deal with (identifiers, keywords, numbers, strings, comments,
regular expressions).  `NN` is replaced by the number of the chunk. -/
def chunk : String :=
  "// a line comment\n" ++
  "/* a block comment */\n" ++
  "function f_NN(a, b) {\n" ++
  "  var x = a + b * 12.5e3 - 0x1f;\n" ++
  "  var s = 'a string with \\' escapes';\n" ++
  "  var t = \"another string\";\n" ++
  "  if (x > 10 && !s) { x += 1; } else { x -= 1; }\n" ++
  "  for (var i = 0; i < 10; i++) { x = x / 2; }\n" ++
  "  return { p: x, q: [1, 2, 3], r: function () { return s.replace(/ab+c/g, ''); } };\n" ++
  "}\n"

/-- `n` copies of `chunk`, each defining a differently named function. -/
def source (n : Nat) : String :=
  String.join ((List.range n).map (fun i => chunk.replace "NN" (toString i)))

end LanguageJavaScriptBench.Sample
