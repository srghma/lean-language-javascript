/-
Tests for the deterministic AST: `MiniAST`, `MiniASTPrinter`,
the conversions to and from the annotated AST, and the `[js| ... |end_js]`
syntax of `MiniASTElab`.

There is no Haskell counterpart for these — the deterministic AST is an
addition to the port — so the expected values were written here.
-/
import Spec
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.Printer
import LanguageJavascriptMini.OfFull
import LanguageJavascriptMini.ToFull
import LanguageJavascriptMini.Elab

namespace LanguageJavascriptTests.Mini.AST

open Spec
open Spec.Assert
open Language.JavaScript.MiniAST

/-- Parse and print in the canonical style. -/
def miniPrint (src : String) : String :=
  match parse src with
  | .ok p => printProgram p
  | .error e => "ERROR: " ++ e

/-- Do two sources describe the same program? -/
def miniSame (a b : String) : String :=
  match parse a, parse b with
  | .ok p, .ok q => toString (p == q)
  | _, _ => "parse error"

/-- Is printing a fixed point: does the printed program parse back to the
same tree? -/
def miniStable (src : String) : String :=
  match parse src with
  | .ok p => toString (match parse (printProgram p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

/-- Does the trip through the annotated AST preserve the tree? -/
def miniViaAST (src : String) : String :=
  match parse src with
  | .ok p => toString (match ofAST (toAST p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

/-- Does the *source* produced from the annotated AST still mean the same? -/
def miniViaASTSource (src : String) : String :=
  match parse src with
  | .ok p =>
      toString (match parse (renderViaAST p) with | .ok q => q == p | .error _ => false)
  | .error e => "ERROR: " ++ e

/-! ## The printed layout -/

def printCases : List (String × String × String) :=
  [ ("var x = 1", miniPrint "var x = 1", "var x = 1;\n")
    -- the layout of the input is not preserved
  , ("import  def  from 'mod'", miniPrint "import  def  from 'mod'", "import def from \"mod\";\n")
  , ("function f(a,b){return a+b*2}", miniPrint "function f(a,b){return a+b*2}", "function f(a, b) {\n  return a + b * 2;\n}\n")
  , ("if(x){f(1,2)}else{f(3,4)}", miniPrint "if(x){f(1,2)}else{f(3,4)}", "if (x) {\n  f(1, 2);\n} else {\n  f(3, 4);\n}\n")
  , ("if (a) b(); else c();", miniPrint "if (a) b(); else c();", "if (a) b();\nelse c();\n")
  , ("const o={a:1,'b b':2,[c]:3};", miniPrint "const o={a:1,'b b':2,[c]:3};", "const o = { a: 1, \"b b\": 2, [c]: 3 };\n")
    -- a construct which does not fit into 80 columns is broken, one entry
    -- per line, with a trailing comma
  , ("long object literal", miniPrint "const big={alpha:1,beta:2,gamma:3,delta:4,epsilon:5,zeta:66666,eta:77777,theta:8};", "const big = {\n  alpha: 1,\n  beta: 2,\n  gamma: 3,\n  delta: 4,\n  epsilon: 5,\n  zeta: 66666,\n  eta: 77777,\n  theta: 8,\n};\n")
  , ("let arr=[1,,2,];", miniPrint "let arr=[1,,2,];", "let arr = [1, , 2];\n")
  , ("class", miniPrint "class A extends B{constructor(x){super(x)}static c(){}*g(){yield 1}get v(){return 1}}", "class A extends B {\n  constructor(x) {\n    super(x);\n  }\n  static c() {}\n  *g() {\n    yield 1;\n  }\n  get v() {\n    return 1;\n  }\n}\n")
  , ("try{a()}catch(e){b()}finally{c()}", miniPrint "try{a()}catch(e){b()}finally{c()}", "try {\n  a();\n} catch (e) {\n  b();\n} finally {\n  c();\n}\n")
  , ("switch(x){case 1:a();break;default:b()}", miniPrint "switch(x){case 1:a();break;default:b()}", "switch (x) {\n  case 1:\n    a();\n    break;\n  default:\n    b();\n}\n")
  , ("for(let i=0;i<10;i++)console.log(i);", miniPrint "for(let i=0;i<10;i++)console.log(i);", "for (let i = 0; i < 10; i++) console.log(i);\n")
  , ("for(;;);", miniPrint "for(;;);", "for (;;);\n")
  , ("do{x++}while(x<3);", miniPrint "do{x++}while(x<3);", "do {\n  x++;\n} while (x < 3);\n")
  , ("label:while(1){break label}", miniPrint "label:while(1){break label}", "label: while (1) {\n  break label;\n}\n")
    -- parentheses are not stored; they are put back where they are needed
  , ("x=(a+b)*c;y=a+(b*c);z=-(-1);", miniPrint "x=(a+b)*c;y=a+(b*c);z=-(-1);", "x = (a + b) * c;\ny = a + b * c;\nz = -(-1);\n")
  , ("let g=x=>({y:1});(function(){})();", miniPrint "let g=x=>({y:1});(function(){})();", "let g = (x) => ({ y: 1 });\n(function () {})();\n")
    -- literals are normalised
  , ("literals", miniPrint "let s=`a${b}c`;let r=/ab+/gi;let n=0XFF;let m=1.50;let q=.5e+07;", "let s = `a${b}c`;\nlet r = /ab+/gi;\nlet n = 0xff;\nlet m = 1.5;\nlet q = 0.5e7;\n")
  , ("quotes", miniPrint "x = 'it\'s';y=\"say \"hi\"\";z='\\u0041\\n';", "x = \"it's\";\ny = 'say \"hi\"';\nz = \"A\\n\";\n")
  , ("export {a as b} from 'm';export const x=1;", miniPrint "export {a as b} from 'm';export const x=1;", "export { a as b } from \"m\";\nexport const x = 1;\n")
  , ("f(...args);function g(a,...rest){}", miniPrint "f(...args);function g(a,...rest){}", "f(...args);\nfunction g(a, ...rest) {}\n")
  , ("a.b.c(1)[2].d;new Foo;new a.b(1);", miniPrint "a.b.c(1)[2].d;new Foo;new a.b(1);", "a.b.c(1)[2].d;\nnew Foo();\nnew a.b(1);\n")
    -- an empty program prints as nothing
  , ("(empty)", miniPrint "", "")
  ]

/-! ## Determinism

Sources that differ only in what the deterministic AST does not record give
equal trees. -/

def determinismCases : List (String × String × String) :=
  [ ("whitespace", miniSame "var  x   =  1 ;" "var x = 1;", "true")
  , ("comments", miniSame "var x = 1; // note\n/* here */ var y = 2;" "var x = 1;\nvar y = 2;", "true")
  , ("line breaks", miniSame "if (a) {\n  b();\n}" "if(a){b()}", "true")
  , ("automatic semicolon", miniSame "var x = 1" "var x = 1;", "true")
  , ("stray semicolons", miniSame "var x = 1;;;" "var x = 1;", "true")
  , ("quotes", miniSame "x = 'a'" "x = \"a\"", "true")
  , ("escapes", miniSame "x = '\\u0041'" "x = 'A'", "true")
  , ("number spelling", miniSame "x = 1.50" "x = 1.5", "true")
  , ("hex case", miniSame "x = 0XFF" "x = 0xff", "true")
  , ("redundant parentheses", miniSame "x = (((1)));" "x = 1;", "true")
  , ("new without arguments", miniSame "new Foo" "new Foo()", "true")
    -- but a real difference is still a difference
  , ("different parentheses", miniSame "x = (a+b)*c" "x = a+b*c", "false")
  , ("different names", miniSame "var x = 1" "var y = 1", "false")
  , ("different strings", miniSame "x = 'a'" "x = 'b'", "false")
  ]

/-! ## Round trips -/

def roundTripSources : List String :=
  [ "var x = 1, y = 2;"
  , "function f(a, b) { return a + b * 2; }"
  , "if (x) { f(1, 2) } else { g() }"
  , "const o = { a: 1, 'b b': 2, [c]: 3, m() { return 1 }, get v() { return 2 } };"
  , "let arr = [1, , 2, [3, [4]]];"
  , "class A extends B { constructor(x) { super(x) } static c() {} *g() { yield 1 } }"
  , "try { a() } catch (e) { b() } finally { c() }"
  , "try { a() } finally { c() }"
  , "switch (x) { case 1: a(); break; default: b() }"
  , "for (let i = 0; i < 10; i++) console.log(i);"
  , "for (const k in o) g(k);"
  , "for (var v of xs) { h(v) }"
  , "do { x++ } while (x < 3);"
  , "while (a) { b() }"
  , "with (o) { p }"
  , "label: while (1) { break label; continue }"
  , "x = (a + b) * c; y = a ? b : c; z = -(-1); w = typeof x === 'string';"
  , "let g = (x) => ({ y: 1 }); let h = (a, b) => a + b;"
  , "let s = `a${b}c${d}e`; let r = /ab+/gi;"
  , "import def from 'mod'; import * as ns from 'p'; import { a, b as c } from 'q';"
  , "import 'side-effect';"
  , "export { a as b } from 'm'; export { c }; export function f() {}"
  , "f(...args); function g(a, ...rest) {}"
  , "a.b.c(1)[2].d; new Foo; new a.b(1); (1).toString();"
  , "throw new Error('x');"
  , "var x = function () { return 1 }; var y = function* () { yield 1 };"
  , "async function f() { await g() }"
  ]

/-! ## Literals -/

def literalCases : List (String × String × String) :=
  [ ("normalizeNumber 1.50", normalizeNumber "1.50", "1.5")
  , ("normalizeNumber 1.00", normalizeNumber "1.00", "1.0")
  , ("normalizeNumber .5", normalizeNumber ".5", "0.5")
  , ("normalizeNumber 1.", normalizeNumber "1.", "1")
  , ("normalizeNumber 1E+07", normalizeNumber "1E+07", "1e7")
  , ("normalizeNumber 1e-07", normalizeNumber "1e-07", "1e-7")
  , ("normalizeNumber 1e0", normalizeNumber "1e0", "1")
  , ("normalizeNumber 0XFF", normalizeNumber "0XFF", "0xff")
  , ("decode 'a\\nb'", decodeStringLiteral "'a\\nb'", "a\nb")
  , ("decode '\\u0041'", decodeStringLiteral "'\\u0041'", "A")
  , ("decode '\\x41'", decodeStringLiteral "'\\x41'", "A")
  , ("decode '\\u{1F600}'", decodeStringLiteral "'\\u{1F600}'", "😀")
  , ("decode surrogate pair", decodeStringLiteral "'\\ud83d\\ude00'", "😀")
  , ("encode a\\nb", encodeStringLiteral "a\nb", "\"a\\nb\"")
  , ("encode with double quotes", encodeStringLiteral "say \"hi\"", "'say \"hi\"'")
  , ("encode with single quotes", encodeStringLiteral "it's", "\"it's\"")
  , ("encode both quotes", encodeStringLiteral "'\"", "\"\'\\\"\"")
  ]

/-! ## The `[js| ... |end_js]` syntax

The fragment is parsed while this file is elaborated; the value below is the
tree, not the text. -/

def embedded : MiniProgram :=
  [js| function greet(name) {
         if (name) { console.log(`hello ${name}`) } else console.log('hi');
       }
       const xs = [1, 2, 3].map(x => x * 2);
  |end_js]

def embeddedExpr : MiniExpr := [js_expr| a + b * (c - d) |end_js]

def spec : Spec := do
  describe "MiniAST Print Layout" do
    for (label, actual, expected) in printCases do
      it label do
        shouldEqual actual expected

  describe "MiniAST Determinism" do
    for (label, actual, expected) in determinismCases do
      it label do
        shouldEqual actual expected

  describe "MiniAST Round Trip" do
    for s in roundTripSources do
      it ("print: " ++ s) do
        shouldEqual (miniStable s) "true"
      it ("toAST: " ++ s) do
        shouldEqual (miniViaAST s) "true"
      it ("render: " ++ s) do
        shouldEqual (miniViaASTSource s) "true"

  describe "MiniAST Literals" do
    for (label, actual, expected) in literalCases do
      it label do
        shouldEqual actual expected

  describe "MiniAST Elab" do
    it "[js| ... |end_js] prints in the canonical style" do
      shouldEqual (printProgram embedded)
        ("function greet(name) {\n  if (name) {\n    console.log(`hello ${name}`);\n  } else"
          ++ " console.log(\"hi\");\n}\nconst xs = [1, 2, 3].map((x) => x * 2);\n")
    it "[js| ... |end_js] agrees with the parser" do
      shouldEqual (toString (match parse "function greet(name) { if (name) { console.log(`hello ${name}`) } else console.log('hi'); } const xs = [1,2,3].map(x => x*2);" with
        | .ok p => p == embedded
        | .error _ => false)) "true"
    it "[js_expr| ... |end_js]" do
      shouldEqual (printExpr embeddedExpr) "a + b * (c - d)"

end LanguageJavascriptTests.Mini.AST
