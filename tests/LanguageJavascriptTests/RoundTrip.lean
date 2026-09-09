/-
Port of the Haskell test module `RoundTrip`.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.Printer

namespace LanguageJavascriptTests.RoundTrip

open Spec
open Spec.Assert
open LanguageJavaScript.Parser
open LanguageJavaScript.Pretty

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def programCases : List String :=
  -- multi comment
  [ "/*a*/\n//foo\nnull"
  , "/*a*/x"
  , "/*a*/null"
  , "/*b*/false"
  , "true/*c*/"
  , "/*c*/true"
  , "/*d*/0x1234fF"
  , "/*e*/1.0e4"
  , "/*x*/011"
  , "/*f*/\"hello\\nworld\""
  , "/*g*/'hello\\nworld'"
  , "/*h*/this"
  , "/*i*//blah/"
  , "//j\nthis_"
  -- arrays
  , "/*a*/[/*b*/]"
  , "/*a*/[/*b*/,/*c*/]"
  , "/*a*/[/*b*/,/*c*/,/*d*/]"
  , "/*a*/[/*b/*,/*c*/,/*d*/x/*e*/]"
  , "/*a*/[/*b*/,/*c*/,/*d*/x/*e*/]"
  , "/*a*/[/*b*/,/*c*/x/*d*/,/*e*/,/*f*/x/*g*/]"
  , "/*a*/[/*b*/x/*c*/]"
  , "/*a*/[/*b*/x/*c*/,/*d*/]"
  -- object literals
  , "/*a*/{/*b*/}"
  , "/*a*/{/*b*/x/*c*/:/*d*/1/*e*/}"
  , "/*a*/{/*b*/x/*c*/}"
  , "/*a*/{/*b*/of/*c*/}"
  , "x=/*a*/{/*b*/x/*c*/:/*d*/1/*e*/,/*f*/y/*g*/:/*h*/2/*i*/}"
  , "x=/*a*/{/*b*/x/*c*/:/*d*/1/*e*/,/*f*/y/*g*/:/*h*/2/*i*/,/*j*/z/*k*/:/*l*/3/*m*/}"
  , "a=/*a*/{/*b*/x/*c*/:/*d*/1/*e*/,/*f*/}"
  , "/*a*/{/*b*/[/*c*/x/*d*/+/*e*/y/*f*/]/*g*/:/*h*/1/*i*/}"
  , "/*a*/{/*b*/a/*c*/(/*d*/x/*e*/,/*f*/y/*g*/)/*h*/{/*i*/}/*j*/}"
  , "/*a*/{/*b*/[/*c*/x/*d*/+/*e*/y/*f*/]/*g*/(/*h*/)/*i*/{/*j*/}/*k*/}"
  , "/*a*/{/*b*/*/*c*/a/*d*/(/*e*/x/*f*/,/*g*/y/*h*/)/*i*/{/*j*/}/*k*/}"
  -- miscellaneous
  , "/*a*/(/*b*/56/*c*/)"
  , "/*a*/true/*b*/?/*c*/1/*d*/:/*e*/2"
  , "/*a*/x/*b*/||/*c*/y"
  , "/*a*/x/*b*/&&/*c*/y"
  , "/*a*/x/*b*/|/*c*/y"
  , "/*a*/x/*b*/^/*c*/y"
  , "/*a*/x/*b*/&/*c*/y"
  , "/*a*/x/*b*/==/*c*/y"
  , "/*a*/x/*b*/!=/*c*/y"
  , "/*a*/x/*b*/===/*c*/y"
  , "/*a*/x/*b*/!==/*c*/y"
  , "/*a*/x/*b*/</*c*/y"
  , "/*a*/x/*b*/>/*c*/y"
  , "/*a*/x/*b*/<=/*c*/y"
  , "/*a*/x/*b*/>=/*c*/y"
  , "/*a*/x /*b*/instanceof /*c*/y"
  , "/*a*/x/*b*/=/*c*/{/*d*/get/*e*/ foo/*f*/(/*g*/)/*h*/ {/*i*/return/*j*/ 1/*k*/}/*l*/,/*m*/set/*n*/ foo/*o*/(/*p*/a/*q*/) /*r*/{/*s*/x/*t*/=/*u*/a/*v*/}/*w*/}"
  , "x = { set foo(/*a*/[/*b*/a/*c*/,/*d*/b/*e*/]/*f*/=/*g*/y/*h*/) {} }"
  , "... /*a*/ x"
  , "a => {}"
  , "(a) => { a + 2 }"
  , "(a, b) => {}"
  , "(a, b) => a + b"
  , "() => { 42 }"
  , "(...a) => a"
  , "(a=1, b=2) => a + b"
  , "([a, b]) => a + b"
  , "({a, b}) => a + b"
  , "function (...a) {}"
  , "function (a=1, b=2) {}"
  , "function ([a, ...b]) {}"
  , "function ({a, b: c}) {}"
  , "/*a*/function/*b*/*/*c*/f/*d*/(/*e*/)/*f*/{/*g*/yield/*h*/a/*i*/}/*j*/"
  , "function*(a, b) { yield a ; yield b ; }"
  , "/*a*/`<${/*b*/x/*c*/}>`/*d*/"
  , "`\\${}`"
  , "`\n\n`"
  , "{}+``"
  -- statement
  , "if (1) {}"
  , "if (1) {} else {}"
  , "if (1) x=1; else {}"
  , "do {x=1} while (true);"
  , "do x=x+1;while(x<4);"
  , "while(true);"
  , "for(;;);"
  , "for(x=1;x<10;x++);"
  , "for(var x;;);"
  , "for(var x=1;;);"
  , "for(var x;y;z){}"
  , "for(x in 5){}"
  , "for(var x in 5){}"
  , "for(let x;y;z){}"
  , "for(let x in 5){}"
  , "for(let x of 5){}"
  , "for(const x;y;z){}"
  , "for(const x in 5){}"
  , "for(const x of 5){}"
  , "for(x of 5){}"
  , "for(var x of 5){}"
  , "var x=1;"
  , "const x=1,y=2;"
  , "continue;"
  , "continue x;"
  , "break;"
  , "break x;"
  , "return;"
  , "return x;"
  , "with (x) {};"
  , "abc:x=1"
  , "switch (x) {}"
  , "switch (x) {case 1:break;}"
  , "switch (x) {case 0:\ncase 1:break;}"
  , "switch (x) {default:break;}"
  , "switch (x) {default:\ncase 1:break;}"
  , "var x=1;let y=2;"
  , "var [x, y]=z;"
  , "let {x: [y]}=z;"
  , "let yield=1"
  -- module
  ]

def moduleCases : List String :=
  [ "import  def  from 'mod'"
  , "import  def  from   \"mod\";"
  , "import   * as foo  from   \"mod\"  ; "
  , "import  def, * as foo  from   \"mod\"  ; "
  , "import  { baz,  bar as   foo }  from   \"mod\"  ; "
  , "import  def, { baz,  bar as   foo }  from   \"mod\"  ; "
  , "export   {};"
  , "  export {}   ;  "
  , "export {  a  ,  b  ,  c  };"
  , "export {  a, X   as B,   c }"
  , "export   {}  from \"mod\";"
  , "export const a = 1 ; "
  , "export function f () {  } ; "
  , "export function * f () {  } ; "
  , "export   class Foo\nextends Bar\n{ get a () { return 1 ; }  static b ( x,y ) {} ; }   ; "
  ]

def spec : Spec := do
  describe "Roundtrip" do
    for str in programCases do
      it (escapeLabel str) do
        shouldEqual (renderToString (readJs str)) str
    for str in moduleCases do
      it (escapeLabel str) do
        shouldEqual (renderToString (readJsModule str)) str

end LanguageJavascriptTests.RoundTrip
