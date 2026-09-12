/-
Tests for the `BrujinAST` optimizer using `lean-spec`.
-/
import Spec
import LanguageJavascriptBrujin.AST
import LanguageJavascriptBrujin.Optimizer
import LanguageJavascriptBrujin.OfMini

namespace LanguageJavascriptTests.Brujin.Optimizer

open Spec
open Spec.Assert
open Language.JavaScript.BrujinAST

/-- Read source, optimize it, and print the result. -/
def brujinOpt (src : String) : String :=
  match parseIndexed src with
  | .ok p => printProgram (optimizeProgram p)
  | .error e => "ERROR: " ++ e

def foldingCases : List (String × String × String) :=
  [ ("arithmetic, and only when it is exact",
      brujinOpt "console.log(1 + 2 * 3, 10 - 4, 7 / 2, 8 / 2, 7 % 3, 2 * 3);",
      "console.log(7, 6, 7 / 2, 4, 1, 6);\n")
  , ("string concatenation, also with a number",
      brujinOpt "console.log(\"a\" + \"b\", \"n = \" + 5, 5 + \"!\");",
      "console.log(\"ab\", \"n = 5\", \"5!\");\n")
  , ("comparison and equality",
      brujinOpt
        "console.log(1 < 2, 2 <= 1, \"a\" < \"b\", 1 === 1, 1 === \"1\", 1 !== 2, null === null);",
      "console.log(true, false, true, true, false, true, true);\n")
  , ("the unary operators, and typeof",
      brujinOpt ("console.log(!0, !\"\", !\"x\", -(3), typeof 1, typeof \"s\", typeof true, "
        ++ "typeof null, typeof (() => 1));"),
      ("console.log(\n  true,\n  true,\n  false,\n  -3,\n  \"number\",\n  \"string\",\n"
        ++ "  \"boolean\",\n  \"object\",\n  \"function\",\n);\n"))
  , ("the bitwise operators, on 32 bit words",
      brujinOpt "console.log(~5, 6 & 3, 6 | 3, 6 ^ 3, 1 << 4, -8 >> 1, -1 >>> 28);",
      "console.log(-6, 2, 7, 5, 16, -4, 15);\n")
  , ("an exponent is an ordinary integer, so it is folded",
      brujinOpt "console.log(1e3 + 1);", "console.log(1001);\n")
  , ("what is not folded",
      brujinOpt "console.log(0.5 + 1, 9007199254740991 + 1, 1 / 0);",
      "console.log(0.5 + 1, 9007199254740991 + 1, 1 / 0);\n")
  , ("?? keeps the left hand side unless it is null",
      brujinOpt "f(null ?? g(), 1 ?? h(), \"\" ?? h(), x ?? k());",
      "f(g(), 1, \"\", x ?? k());\n")
  , ("the short circuiting operators, the ternary and the comma",
      brujinOpt "f(true && g(), false && g(), 0 || h(), 1 || h(), true ? a : b, (1, k()));",
      "f(g(), false, h(), 1, a, k());\n")
  ]

def regexCases : List (String × String × String) :=
  [ ("a test on a literal subject is computed",
      brujinOpt "console.log(/a+/.test(\"xaaay\"), /^b/.test(\"abc\"));",
      "console.log(true, false);\n")
  , ("a replace, with and without the g flag",
      brujinOpt "console.log(\"a1a2\".replace(/a/g, \"X\"), \"a1a2\".replace(/a/, \"X\"));",
      "console.log(\"X1X2\", \"X1a2\");\n")
  , ("a replaceAll is folded only for a global literal",
      brujinOpt "console.log(\"a1a2\".replaceAll(/a/g, \"X\"), \"a1a2\".replaceAll(/a/, \"X\"));",
      "console.log(\"X1X2\", \"a1a2\".replaceAll(/a/, \"X\"));\n")
  , ("a class, a repetition and a Perl class",
      brujinOpt "console.log(/^[a-c]{2}\\d$/.test(\"ab1\"), /^[a-c]{2}\\d$/.test(\"abc\"));",
      "console.log(true, false);\n")
  , ("the i and s flags",
      brujinOpt "console.log(/AB/i.test(\"xab\"), /a.c/s.test(\"a\\nc\"), /a.c/.test(\"a\\nc\"));",
      "console.log(true, true, false);\n")
  , ("what is not folded: a pattern or a flag the library does not model",
      brujinOpt "console.log(/(?=a)b/.test(\"ab\"), /a/m.test(\"a\"), /a/y.test(\"a\"));",
      "console.log(/(?=a)b/.test(\"ab\"), /a/m.test(\"a\"), /a/y.test(\"a\"));\n")
  , ("a replacement mentioning a capture group is not folded",
      brujinOpt "console.log(\"a\".replace(/a/, \"$&!\"));",
      "console.log(\"a\".replace(/a/, \"$&!\"));\n")
  , ("and neither is a call whose subject or argument is not a literal",
      brujinOpt "console.log(x.test(\"a\"), /a/.test(y));",
      "console.log(x.test(\"a\"), /a/.test(y));\n")
  , ("a subject which is not ASCII is left alone",
      brujinOpt "console.log(/é/.test(\"é\"));", "console.log(/é/.test(\"é\"));\n")
  ]

def statementCases : List (String × String × String) :=
  [ ("an if with a true condition",
      brujinOpt "if (true) { f(); } else { g(); }", "f();\n")
  , ("an if with a false condition",
      brujinOpt "if (false) { f(); } else { g(); }", "g();\n")
  , ("a block of one statement", brujinOpt "{ f(); }", "f();\n")
  , ("a block of several statements",
      brujinOpt "{ f(); g(); }", "{\n  f();\n  g();\n}\n")
  , ("a branch that returns makes the rest of the block unreachable",
      brujinOpt "function f() { if (2 > 1) { return 3 * 3; } g(); }",
      "function _c0() {\n  return 9;\n}\n")
  , ("a while that never runs, and a do-while that runs once",
      brujinOpt "while (false) { f(); } do { f(); } while (false);",
      "do {\n  f();\n} while (false);\n")
  , ("an if with nothing in it and a condition without effect",
      brujinOpt "if (x) { }", "")
  , ("an if whose condition has an effect keeps the condition",
      brujinOpt "if (f()) { }", "f();\n")
  , ("statements after a return",
      brujinOpt "function f() { return 1; g(); }", "function _c0() {\n  return 1;\n}\n")
  , ("statements after a break",
      brujinOpt "while (x) { g(); break; h(); }",
      "while (x) {\n  g();\n  break;\n}\n")
  , ("expression statements without effect, and an empty block",
      brujinOpt "1 + 1; x; {} f();", "f();\n")
  , ("a statement with an effect stays",
      brujinOpt "f(); x.y; delete x.y;", "f();\nx.y;\ndelete x.y;\n")
  ]

def bindingCases : List (String × String × String) :=
  [ ("a chain of unused consts",
      brujinOpt "function f() { const a = 1; const b = a + 1; return 2; }",
      "function _c0() {\n  return 2;\n}\n")
  , ("an unused let, next to a const that is used",
      brujinOpt "function f() { let unused = 0; const used = g(); return used; }",
      "function _c0() {\n  const _c1 = g();\n  return _c1;\n}\n")
  , ("an unused function declaration",
      brujinOpt "function f() { function helper() { return 1; } return 2; }",
      "function _c0() {\n  return 2;\n}\n")
  , ("an unused class declaration",
      brujinOpt "function f() { class C { m() {} } return 2; }",
      "function _c0() {\n  return 2;\n}\n")
  , ("an unused class whose static block runs code is kept",
      brujinOpt "function f() { class C { static { g(); } } return 2; }",
      ("function _c0() {\n  class _c1 {\n    static {\n      g();\n    }\n  }\n"
        ++ "  return 2;\n}\n"))
  , ("an unused class whose static field has an effect is kept",
      brujinOpt "function f() { class C { static x = g(); } return 2; }",
      "function _c0() {\n  class _c1 {\n    static x = g();\n  }\n  return 2;\n}\n")
  , ("but an unused class whose instance field has one is dropped",
      brujinOpt "function f() { class C { x = g(); } return 2; }",
      "function _c0() {\n  return 2;\n}\n")
  , ("an unused decorated class is kept: the decorator runs",
      brujinOpt "function f() { @dec class C {} return 2; }",
      "function _c0() {\n  @dec class _c1 {}\n  return 2;\n}\n")
  , ("a binding that is assigned to is used",
      brujinOpt "function f() { let x = 1; x = 2; return x; }",
      "function _c0() {\n  let _m0 = 1;\n  _m0 = 2;\n  return _m0;\n}\n")
  , ("a binding a closure captures is used",
      brujinOpt "function f() { const a = 1; return () => a; }",
      "function _c0() {\n  const _c1 = 1;\n  return () => _c1;\n}\n")
  , ("an initializer with an effect keeps the binding",
      brujinOpt "function f() { const a = g(); return 1; }",
      "function _c0() {\n  const _c1 = g();\n  return 1;\n}\n")
  , ("a top level binding is never deleted",
      brujinOpt "1 + 1; x; {} const top = 1;", "const _c0 = 1;\n")
  , ("an exported binding is used",
      brujinOpt "function f() { const a = 1; return a; } export { f };",
      "function _c0() {\n  const _c1 = 1;\n  return _c1;\n}\nexport { _c0 as f };\n")
  ]

def spec : Spec := do
  describe "BrujinAST Optimizer Folding" do
    for (label, actual, expected) in foldingCases do
      it label do
        shouldEqual actual expected

  describe "BrujinAST Optimizer Regular Expressions" do
    for (label, actual, expected) in regexCases do
      it label do
        shouldEqual actual expected

  describe "BrujinAST Optimizer Statements" do
    for (label, actual, expected) in statementCases do
      it label do
        shouldEqual actual expected

  describe "BrujinAST Optimizer Bindings" do
    for (label, actual, expected) in bindingCases do
      it label do
        shouldEqual actual expected

end LanguageJavascriptTests.Brujin.Optimizer
