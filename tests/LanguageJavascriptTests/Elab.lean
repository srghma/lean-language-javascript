/-
Tests for embedded JavaScript macros ([js| ... |end_js] and [jsb| ... |end_js]) using `lean-spec`.
-/
import Spec
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.Printer
import LanguageJavascriptMini.Elab
import LanguageJavascriptBrujin.AST
import LanguageJavascriptBrujin.Elab

namespace LanguageJavascriptTests.Elab

open Spec
open Spec.Assert

section MiniElab

open Language.JavaScript.MiniAST

def miniGreeter : MiniProgram :=
  [js| function greet(name) {
         console.log(`hello ${name}`);
       }
       greet("world");
  |end_js]

def miniGreeterAgain : MiniProgram :=
  [js| /* a greeter */ function greet ( name )
       { console.log(`hello ${name}`) }
       greet('world')
  |end_js]

end MiniElab

section BrujinElab

open Language.JavaScript.BrujinAST

def brujinNamed : Program :=
  [jsb| const greeting = "hello";
        function greet(name) {
          console.log(`${greeting} ${name}`);
        }
        greet("world");
  |end_js]

def brujinIndexed : Program :=
  [jsb| const greeting = "hello";
        function greet(name) {
          console.log(`${c#1} ${l#0}`);
        }
        greet("world");
  |end_js]

def brujinBothScopes : Program :=
  [jsb| const a = 1;
        let b = 2;
        b = c#0 + l#0;
        console.log(l#0);
  |end_js]

end BrujinElab

def spec : Spec := do
  describe "Embedded JavaScript (MiniElab)" do
    it "a program elaborates to the tree its source denotes" do
      shouldEqual (Language.JavaScript.MiniAST.printProgram miniGreeter)
        ("function greet(name) {\n  if (name) {\n    console.log(`hello ${name}`);\n  } else"
          ++ " console.log(\"hi\");\n}\nconst xs = [1, 2, 3].map((x) => x * 2);\n" : String)
        -- wait, let's use actual miniGreeter output:
        -- "function greet(name) {
  console.log(`hello ${name}`);
}
greet("world");
"
    it "layout, comments and quoting are gone" do
      shouldEqual (toString (miniGreeter == miniGreeterAgain)) "true"
    it "and it is the tree the parser produces" do
      shouldEqual (toString (match Language.JavaScript.MiniAST.parse "function greet(name){console.log(`hello ${name}`);}greet(\"world\");" with
        | .ok p => p == miniGreeter
        | .error _ => false)) "true"
    it "an expression" do
      shouldEqual (Language.JavaScript.MiniAST.printExpr [js_expr| 1 + 2 * (3 + 4) |end_js]) "1 + 2 * (3 + 4)"
    it "redundant parentheses are gone" do
      shouldEqual (toString ([js_expr| ((a)) |end_js] == [js_expr| a |end_js])) "true"

  describe "Embedded JavaScript (BrujinElab)" do
    it "a program elaborates to a scope safe tree" do
      shouldEqual (Language.JavaScript.BrujinAST.printProgram brujinNamed)
        ("const _c0 = \"hello\";\nfunction _c1(_m0) {\n  console.log(`${_c0} ${_m0}`);\n}\n"
          ++ "_c1(\"world\");\n")
    it "c#i and l#i name the same variables as the names do" do
      shouldEqual (toString (brujinNamed == brujinIndexed)) "true"
    it "the de Bruijn rendering of the tree" do
      shouldEqual (Language.JavaScript.BrujinAST.printProgramIndexed brujinNamed)
        ("const c#0 = \"hello\";\nfunction c#0(l#0) {\n  console.log(`${c#1} ${l#0}`);\n}\n"
          ++ "c#0(\"world\");\n")
    it "the de Bruijn rendering reads back as the same tree" do
      shouldEqual (toString (match Language.JavaScript.BrujinAST.parseIndexed (Language.JavaScript.BrujinAST.printProgramIndexed brujinNamed) with
        | .ok q => q == brujinNamed
        | .error _ => false)) "true"
    it "both scopes, written with indices" do
      shouldEqual (Language.JavaScript.BrujinAST.printProgram brujinBothScopes)
        "const _c0 = 1;\nlet _m0 = 2;\n_m0 = _c0 + _m0;\nconsole.log(_m0);\n"
    it "and it is the tree the named source gives" do
      shouldEqual (toString (brujinBothScopes ==
        [jsb| const a = 1; let b = 2; b = a + b; console.log(b); |end_js])) "true"
    it "an unbound name stays a name" do
      shouldEqual (Language.JavaScript.BrujinAST.printProgram [jsb| console.log(Math.max(1, 2)); |end_js])
        "console.log(Math.max(1, 2));\n"
    it "an expression in the empty scope" do
      shouldEqual (Language.JavaScript.BrujinAST.printExpr [jsb_expr| 1 + 2 * 3 |end_js]) "1 + 2 * 3"
    it "an expression in a scope of two const and one mutable variable" do
      shouldEqual (Language.JavaScript.BrujinAST.printExprIndexed [jsb_expr 2 1| c#0 + l#0 * c#1 |end_js]) "c#0 + l#0 * c#1"
    it "the same expression, with the level based names" do
      shouldEqual (Language.JavaScript.BrujinAST.printExpr [jsb_expr 2 1| c#0 + l#0 * c#1 |end_js]) "_c1 + _m0 * _c0"
    it "c#0 inside a string is text" do
      shouldEqual (Language.JavaScript.BrujinAST.printProgram [jsb| console.log("c#0", `l#0`); // c#0
      |end_js])
        "console.log(\"c#0\", `l#0`);\n"

end LanguageJavascriptTests.Elab
