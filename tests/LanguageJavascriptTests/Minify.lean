/-
Tests for the minifier.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascript.Minify

namespace LanguageJavascriptTests.Minify

open Spec
open Spec.Assert
open Language.JavaScript.Parser
open Language.JavaScript.Pretty
open Language.JavaScript.Process

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def minifyProg (str : String) : String := renderToString (minifyJS (readJs str))

def minifyModule (str : String) : String := renderToString (minifyJS (readJsModule str))

def minifyExpr (str : String) : String :=
  match parseExpressionAST str with
  | .ok ast => renderToString (minifyJS ast)
  | .error e => e

def itProg (input expected : String) : Spec :=
  it (escapeLabel input) do shouldEqual (minifyProg input) expected

def itExpr (input expected : String) : Spec :=
  it (escapeLabel input) do shouldEqual (minifyExpr input) expected

def itModule (input expected : String) : Spec :=
  it (escapeLabel input) do shouldEqual (minifyModule input) expected

def spec : Spec := do
  describe "Minify" do
    -- expressions and simple statements
    itProg "a = 1" "a=1"
    itExpr "a  ?  b  :  c" "a?b:c"
    itProg "delete x" "delete x"
    itProg "x = y instanceof z" "x=y instanceof z"
    itProg "throw new Error('x')" "throw new Error('x')"
    -- string concatenation is folded, and double quotes are normalised
    itProg "x = 'a' + 'b'" "x='ab'"
    itProg "x = \"a\" + \"b\"" "x='ab'"
    -- declarations
    itProg "var x = 1;\nvar y = 2;" "var x=1,y=2"
    itProg "var x = 1 ; { var y = 2 ; }" "var x=1;var y=2"
    itProg "const a = 1 ; const b = 2 ;" "const a=1,b=2"
    -- redundant blocks and empty statements disappear
    itProg "{ }" ""
    itProg ";;;" ""
    -- control structures
    itProg "if (a) { b(); } else { c(); }" "if(a){b()}else c()"
    itProg "if (x) { } else { y() }" "if(x){}else y()"
    itProg "while (a) { b() ; }" "while(a)b()"
    itProg "do { x() } while (a);" "do{x()}while(a)"
    itProg "for (i = 0; i < 10; i++) { x(); }" "for(i=0;i<10;i++)x()"
    itProg "for (var k in o) { f(k) }" "for(var k in o)f(k)"
    itProg "switch (a) { case 1: b(); break; default: c(); }" "switch(a){case 1:b();break;default:c()}"
    itProg "try { a() } catch (e) { b() } finally { c() }" "try{a()}catch(e){b()}finally{c()}"
    itProg "label : for (;;) { break label }" "label:for(;;)break label"
    -- functions and classes
    itProg "function f (a, b) { return a + b; }" "function f(a,b){return a+b}"
    itProg "x = function (a) { return a }" "x=function(a){return a}"
    itProg "function a(){}\nfunction b(){}" "function a(){}\nfunction b(){}"
    itProg "class Foo extends Bar { static a () { return 1 } ; b (x) {} }" "class Foo extends Bar{static a(){return 1}b(x){}}"
    -- objects
    itProg "a = { b : 1, c : 2, }" "a={b:1,c:2}"
    -- statement lists: blocks are spliced, empty statements dropped,
    -- neighbouring declarations merged
    itProg "var a=1;;var b=2;" "var a=1,b=2"
    itProg "{ var a = 1; var b = 2; }" "var a=1,b=2"
    itProg "x(); { y(); z(); } w();" "x();y();z();w()"
    itProg "{ ; }" ";"
    itProg "{ { a(); } }" "a()"
    itProg "{ ; a(); ; }" ";a();;"
    itProg "if (a) { ; } else { ; }" "if(a){}else{}"
    itProg "function a(){} ; function b(){}" "function a(){}\nfunction b(){}"
    itProg "const a = 1; ; const b = 2;" "const a=1,b=2"
    itProg "var a = 1; { } var b = 2;" "var a=1,b=2"
    itProg "{ a(); }" "a()"
    itProg "{ a(); b(); }" "a();b()"
    itProg "while (a) { ; }" "while(a){}"
    itProg "for (;;) { { x(); } }" "for(;;)x()"
    itProg "var a=1,b=2; var c=3;" "var a=1,b=2,c=3"
    itProg "switch(a){case 1: { b(); c(); } }" "switch(a){case 1:b();c()}"
    itProg "try { ; } catch (e) { { f(); } }" "try{}catch(e){f()}"
    itProg "label: { a(); b(); }" "label:{a();b()}"
    itProg "if (a) b(); else { }" "if(a){b()}else;"
    itProg "x(); ;" "x()"
    itProg "{ var a = 1; }" "var a=1"
    itProg "{ }; x();" "x()"
    itProg "const a=1; var b=2; const c=3;" "const a=1;var b=2;const c=3"
    itProg "function f(){ var a=1; var b=2; ; }" "function f(){var a=1,b=2}"
    -- modules
    itModule "import def from 'mod';\nexport { a as b };\nexport const x = 1 ;" "import def from'mod'export{a as b}export const x=1"

end LanguageJavascriptTests.Minify
