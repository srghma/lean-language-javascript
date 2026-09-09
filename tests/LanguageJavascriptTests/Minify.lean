/-
Tests for the minifier.

The uploaded Haskell sources contain the minifier itself but no test module
for it, so these cases were written for the Lean port; each expected result
follows from the rules of `LanguageJavaScript.Process.Minify` (semicolons
forced between statements and dropped at the end of a block, redundant
blocks and empty statements removed, adjacent `var`/`const` declarations
merged, string concatenation of literals folded, and the whitespace which
the syntax requires kept).
-/
import LanguageJavascriptTests.Utils

namespace Test.Language.Javascript

def testMinify : List Test :=
  -- expressions and simple statements
  [ shouldBe "a = 1" (minifyProg "a = 1") "a=1"
  , shouldBe "a  ?  b  :  c" (minifyExpr "a  ?  b  :  c") "a?b:c"
  , shouldBe "delete x" (minifyProg "delete x") "delete x"
  , shouldBe "x = y instanceof z" (minifyProg "x = y instanceof z") "x=y instanceof z"
  , shouldBe "throw new Error('x')" (minifyProg "throw new Error('x')") "throw new Error('x')"
  -- string concatenation is folded, and double quotes are normalised
  , shouldBe "x = 'a' + 'b'" (minifyProg "x = 'a' + 'b'") "x='ab'"
  , shouldBe "x = \"a\" + \"b\"" (minifyProg "x = \"a\" + \"b\"") "x='ab'"
  -- declarations
  , shouldBe "var x = 1;\nvar y = 2;" (minifyProg "var x = 1;\nvar y = 2;") "var x=1,y=2"
  , shouldBe "var x = 1 ; { var y = 2 ; }" (minifyProg "var x = 1 ; { var y = 2 ; }")
      "var x=1;var y=2"
  , shouldBe "const a = 1 ; const b = 2 ;" (minifyProg "const a = 1 ; const b = 2 ;")
      "const a=1,b=2"
  -- redundant blocks and empty statements disappear
  , shouldBe "{ }" (minifyProg "{ }") ""
  , shouldBe ";;;" (minifyProg ";;;") ""
  -- control structures
  , shouldBe "if (a) { b(); } else { c(); }" (minifyProg "if (a) { b(); } else { c(); }")
      "if(a){b()}else c()"
  , shouldBe "if (x) { } else { y() }" (minifyProg "if (x) { } else { y() }") "if(x){}else y()"
  , shouldBe "while (a) { b() ; }" (minifyProg "while (a) { b() ; }") "while(a)b()"
  , shouldBe "do { x() } while (a);" (minifyProg "do { x() } while (a);") "do{x()}while(a)"
  , shouldBe "for (i = 0; i < 10; i++) { x(); }" (minifyProg "for (i = 0; i < 10; i++) { x(); }")
      "for(i=0;i<10;i++)x()"
  , shouldBe "for (var k in o) { f(k) }" (minifyProg "for (var k in o) { f(k) }")
      "for(var k in o)f(k)"
  , shouldBe "switch (a) { case 1: b(); break; default: c(); }"
      (minifyProg "switch (a) { case 1: b(); break; default: c(); }")
      "switch(a){case 1:b();break;default:c()}"
  , shouldBe "try { a() } catch (e) { b() } finally { c() }"
      (minifyProg "try { a() } catch (e) { b() } finally { c() }")
      "try{a()}catch(e){b()}finally{c()}"
  , shouldBe "label : for (;;) { break label }" (minifyProg "label : for (;;) { break label }")
      "label:for(;;)break label"
  -- functions and classes
  , shouldBe "function f (a, b) { return a + b; }"
      (minifyProg "function f (a, b) { return a + b; }") "function f(a,b){return a+b}"
  , shouldBe "x = function (a) { return a }" (minifyProg "x = function (a) { return a }")
      "x=function(a){return a}"
  , shouldBe "function a(){}\nfunction b(){}" (minifyProg "function a(){}\nfunction b(){}")
      "function a(){}\nfunction b(){}"
  , shouldBe "class Foo extends Bar { static a () { return 1 } ; b (x) {} }"
      (minifyProg "class Foo extends Bar { static a () { return 1 } ; b (x) {} }")
      "class Foo extends Bar{static a(){return 1}b(x){}}"
  -- objects
  , shouldBe "a = { b : 1, c : 2, }" (minifyProg "a = { b : 1, c : 2, }") "a={b:1,c:2}"
  -- modules
  , shouldBe "import def from 'mod';\nexport { a as b };\nexport const x = 1 ;"
      (minifyModule "import def from 'mod';\nexport { a as b };\nexport const x = 1 ;")
      "import def from'mod'export{a as b}export const x=1"
  ]

#guard allPass testMinify

end Test.Language.Javascript
