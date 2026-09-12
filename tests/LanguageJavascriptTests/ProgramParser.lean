/-
Port of the Haskell test module `ProgramParser`.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.AST
import LanguageJavascript.ShowStripped

namespace LanguageJavascriptTests.ProgramParser

open Spec
open Spec.Assert
open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def showStrippedMaybe : Except String JSAST → String
  | .ok ast => "Right (" ++ showStripped ast ++ ")"
  | .error e => "Left (\"" ++ e ++ "\")"

def testProg (str : String) : String := showStrippedMaybe (parseProgram str)

def findUnicodeFile : IO System.FilePath := do
  let candidates : List System.FilePath := [
    "./LanguageJavascriptTests/test/Unicode.js",
    "./test/Unicode.js",
    "tests/LanguageJavascriptTests/test/Unicode.js"
  ]
  for c in candidates do
    if (← c.pathExists) then
      return c
  return "./LanguageJavascriptTests/test/Unicode.js"

def programCases : List (String × String) :=
  -- function
  [ ("function a(){}", "Right (JSAstProgram [JSFunction 'a' () (JSBlock [])])")
  , ("function a(b,c){}", "Right (JSAstProgram [JSFunction 'a' (JSIdentifier 'b',JSIdentifier 'c') (JSBlock [])])")
  -- comments
  , ("//blah\nx=1;//foo\na", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon,JSIdentifier 'a'])")
  , ("/*x=1\ny=2\n*/z=2;//foo\na", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'z',JSDecimal '2'),JSSemicolon,JSIdentifier 'a'])")
  , ("/* */\nfunction f() {\n/*  */\n}\n", "Right (JSAstProgram [JSFunction 'f' () (JSBlock [])])")
  , ("/* **/\nfunction f() {\n/*  */\n}\n", "Right (JSAstProgram [JSFunction 'f' () (JSBlock [])])")
  -- if
  , ("if(x);x=1", "Right (JSAstProgram [JSIf (JSIdentifier 'x') (JSEmptyStatement),JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')])")
  , ("if(a)x=1;y=2", "Right (JSAstProgram [JSIf (JSIdentifier 'a') (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon),JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2')])")
  , ("if(a)x=a()y=2", "Right (JSAstProgram [JSIf (JSIdentifier 'a') (JSOpAssign ('=',JSIdentifier 'x',JSMemberExpression (JSIdentifier 'a',JSArguments ()))),JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2')])")
  , ("if(true)break \nfoo();", "Right (JSAstProgram [JSIf (JSLiteral 'true') (JSBreak),JSMethodCall (JSIdentifier 'foo',JSArguments ()),JSSemicolon])")
  , ("if(true)continue \nfoo();", "Right (JSAstProgram [JSIf (JSLiteral 'true') (JSContinue),JSMethodCall (JSIdentifier 'foo',JSArguments ()),JSSemicolon])")
  , ("if(true)break \nfoo();", "Right (JSAstProgram [JSIf (JSLiteral 'true') (JSBreak),JSMethodCall (JSIdentifier 'foo',JSArguments ()),JSSemicolon])")
  -- assign
  , ("x = 1\n  y=2;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2'),JSSemicolon])")
  -- regex
  , ("x=/\\n/g", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSRegEx '/\\n/g')])")
  , ("x=i(/^$/g,\"\\\\$&\")", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSMemberExpression (JSIdentifier 'i',JSArguments (JSRegEx '/^$/g',JSStringLiteral \"\\\\$&\")))])")
  , ("x=i(/[?|^&(){}\\[\\]+\\-*\\/\\.]/g,\"\\\\$&\")", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSMemberExpression (JSIdentifier 'i',JSArguments (JSRegEx '/[?|^&(){}\\[\\]+\\-*\\/\\.]/g',JSStringLiteral \"\\\\$&\")))])")
  , ("(match = /^\"(?:\\\\.|[^\"])*\"|^'(?:[^']|\\\\.)*'/(input))", "Right (JSAstProgram [JSExpressionParen (JSOpAssign ('=',JSIdentifier 'match',JSMemberExpression (JSRegEx '/^\"(?:\\\\.|[^\"])*\"|^'(?:[^']|\\\\.)*'/',JSArguments (JSIdentifier 'input'))))])")
  , ("if(/^[a-z]/.test(t)){consts+=t.toUpperCase();keywords[t]=i}else consts+=(/^\\W/.test(t)?opTypeNames[t]:t);", "Right (JSAstProgram [JSIfElse (JSMemberExpression (JSMemberDot (JSRegEx '/^[a-z]/',JSIdentifier 'test'),JSArguments (JSIdentifier 't'))) (JSStatementBlock [JSOpAssign ('+=',JSIdentifier 'consts',JSMemberExpression (JSMemberDot (JSIdentifier 't',JSIdentifier 'toUpperCase'),JSArguments ())),JSSemicolon,JSOpAssign ('=',JSMemberSquare (JSIdentifier 'keywords',JSIdentifier 't'),JSIdentifier 'i')]) (JSOpAssign ('+=',JSIdentifier 'consts',JSExpressionParen (JSExpressionTernary (JSMemberExpression (JSMemberDot (JSRegEx '/^\\W/',JSIdentifier 'test'),JSArguments (JSIdentifier 't')),JSMemberSquare (JSIdentifier 'opTypeNames',JSIdentifier 't'),JSIdentifier 't'))),JSSemicolon)])")
  -- unicode
  , ("àáâãäå = 1;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'àáâãäå',JSDecimal '1'),JSSemicolon])")
  , ("//comment\u000ax=1;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])")
  , ("//comment\u000dx=1;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])")
  , ("//comment x=1;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])")
  , ("//comment x=1;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])")
  , ("$aà = 1;_b=2;Aa=2", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier '$aà',JSDecimal '1'),JSSemicolon,JSOpAssign ('=',JSIdentifier '_b',JSDecimal '2'),JSSemicolon,JSOpAssign ('=',JSIdentifier 'Aa',JSDecimal '2')])")
  , ("x=\"àáâãäå\";y='௄aD'", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"àáâãäå\"),JSSemicolon,JSOpAssign ('=',JSIdentifier 'y',JSStringLiteral '௄aD')])")
  , ("a \u000c\u000b\t\r\n=  ᠎               　1;", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'a',JSDecimal '1'),JSSemicolon])")
  , ("/* * geolocation. пытаемся определить свое местоположение * если не получается то используем defaultLocation * @Param {object} map экземпляр карты * @Param {object LatLng} defaultLocation Координаты центра по умолчанию * @Param {function} callbackAfterLocation Фу-ия которая вызывается после * геолокации. Т.к запрос геолокации асинхронен */x", "Right (JSAstProgram [JSIdentifier 'x'])")
  -- strings
  , ("x='abc\\ndef';", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral 'abc\\ndef'),JSSemicolon])")
  , ("x=\"abc\\ndef\";", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\ndef\"),JSSemicolon])")
  , ("x=\"abc\\rdef\";", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\rdef\"),JSSemicolon])")
  , ("x=\"abc\\r\\ndef\";", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\r\\ndef\"),JSSemicolon])")
  , ("x=\"abc\\x2028 def\";", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\x2028 def\"),JSSemicolon])")
  , ("x=\"abc\\x2029 def\";", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\x2029 def\"),JSSemicolon])")
  -- object literal
  , ("x = { y: 1e8 }", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSDecimal '100000000']])])")
  , ("{ y: 1e8 }", "Right (JSAstProgram [JSStatementBlock [JSLabelled (JSIdentifier 'y') (JSDecimal '100000000')]])")
  , ("{ y: 18 }", "Right (JSAstProgram [JSStatementBlock [JSLabelled (JSIdentifier 'y') (JSDecimal '18')]])")
  , ("x = { y: 18 }", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSDecimal '18']])])")
  , ("var k = {\ny: somename\n}", "Right (JSAstProgram [JSVariable (JSVarInitExpression (JSIdentifier 'k') [JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSIdentifier 'somename']]])])")
  , ("var k = {\ny: code\n}", "Right (JSAstProgram [JSVariable (JSVarInitExpression (JSIdentifier 'k') [JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSIdentifier 'code']]])])")
  , ("var k = {\ny: mode\n}", "Right (JSAstProgram [JSVariable (JSVarInitExpression (JSIdentifier 'k') [JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSIdentifier 'mode']]])])")
  -- programs
  , ("newlines=spaces.match(/\\n/g)", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'newlines',JSMemberExpression (JSMemberDot (JSIdentifier 'spaces',JSIdentifier 'match'),JSArguments (JSRegEx '/\\n/g')))])")
  , ("Animal=function(){return this.name};", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'Animal',JSFunctionExpression '' () (JSBlock [JSReturn JSMemberDot (JSLiteral 'this',JSIdentifier 'name') ])),JSSemicolon])")
  , ("$(img).click(function(){alert('clicked!')});", "Right (JSAstProgram [JSCallExpression (JSCallExpressionDot (JSMemberExpression (JSIdentifier '$',JSArguments (JSIdentifier 'img')),JSIdentifier 'click'),JSArguments (JSFunctionExpression '' () (JSBlock [JSMethodCall (JSIdentifier 'alert',JSArguments (JSStringLiteral 'clicked!'))]))),JSSemicolon])")
  , ("function() {\nz = function z(o) {\nreturn r;\n};}", "Right (JSAstProgram [JSFunctionExpression '' () (JSBlock [JSOpAssign ('=',JSIdentifier 'z',JSFunctionExpression 'z' (JSIdentifier 'o') (JSBlock [JSReturn JSIdentifier 'r' JSSemicolon])),JSSemicolon])])")
  , ("function() {\nz = function /*z*/(o) {\nreturn r;\n};}", "Right (JSAstProgram [JSFunctionExpression '' () (JSBlock [JSOpAssign ('=',JSIdentifier 'z',JSFunctionExpression '' (JSIdentifier 'o') (JSBlock [JSReturn JSIdentifier 'r' JSSemicolon])),JSSemicolon])])")
  , ("{zero}\nget;two\n{three\nfour;set;\n{\nsix;{seven;}\n}\n}", "Right (JSAstProgram [JSStatementBlock [JSIdentifier 'zero'],JSIdentifier 'get',JSSemicolon,JSIdentifier 'two',JSStatementBlock [JSIdentifier 'three',JSIdentifier 'four',JSSemicolon,JSIdentifier 'set',JSSemicolon,JSStatementBlock [JSIdentifier 'six',JSSemicolon,JSStatementBlock [JSIdentifier 'seven',JSSemicolon]]]])")
  , ("{zero}\none1;two\n{three\nfour;five;\n{\nsix;{seven;}\n}\n}", "Right (JSAstProgram [JSStatementBlock [JSIdentifier 'zero'],JSIdentifier 'one1',JSSemicolon,JSIdentifier 'two',JSStatementBlock [JSIdentifier 'three',JSIdentifier 'four',JSSemicolon,JSIdentifier 'five',JSSemicolon,JSStatementBlock [JSIdentifier 'six',JSSemicolon,JSStatementBlock [JSIdentifier 'seven',JSSemicolon]]]])")
  , ("v = getValue(execute(n[0], x)) in getValue(execute(n[1], x));", "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'v',JSExpressionBinary ('in',JSMemberExpression (JSIdentifier 'getValue',JSArguments (JSMemberExpression (JSIdentifier 'execute',JSArguments (JSMemberSquare (JSIdentifier 'n',JSDecimal '0'),JSIdentifier 'x')))),JSMemberExpression (JSIdentifier 'getValue',JSArguments (JSMemberExpression (JSIdentifier 'execute',JSArguments (JSMemberSquare (JSIdentifier 'n',JSDecimal '1'),JSIdentifier 'x')))))),JSSemicolon])")
  , ("function Animal(name){if(!name)throw new Error('Must specify an animal name');this.name=name};Animal.prototype.toString=function(){return this.name};o=new Animal(\"bob\");o.toString()==\"bob\"", "Right (JSAstProgram [JSFunction 'Animal' (JSIdentifier 'name') (JSBlock [JSIf (JSUnaryExpression ('!',JSIdentifier 'name')) (JSThrow (JSMemberNew (JSIdentifier 'Error',JSArguments (JSStringLiteral 'Must specify an animal name')))),JSOpAssign ('=',JSMemberDot (JSLiteral 'this',JSIdentifier 'name'),JSIdentifier 'name')]),JSOpAssign ('=',JSMemberDot (JSMemberDot (JSIdentifier 'Animal',JSIdentifier 'prototype'),JSIdentifier 'toString'),JSFunctionExpression '' () (JSBlock [JSReturn JSMemberDot (JSLiteral 'this',JSIdentifier 'name') ])),JSSemicolon,JSOpAssign ('=',JSIdentifier 'o',JSMemberNew (JSIdentifier 'Animal',JSArguments (JSStringLiteral \"bob\"))),JSSemicolon,JSExpressionBinary ('==',JSMemberExpression (JSMemberDot (JSIdentifier 'o',JSIdentifier 'toString'),JSArguments ()),JSStringLiteral \"bob\")])")
  ]

def spec : Spec := do
  describe "Program parser" do
    let mut seen : Std.HashSet String := {}
    for (input, expected) in programCases do
      let rawName := escapeLabel input
      let name := if seen.contains rawName then s!"{rawName} (duplicate)" else rawName
      seen := seen.insert rawName
      it name do
        shouldEqual (testProg input) expected
    it "Program parser (utf8 file)" do
      let unicodePath : System.FilePath ← findUnicodeFile
      let ast ← parseFileUtf8 unicodePath
      shouldEqual (showStripped ast)
        "JSAstProgram [JSOpAssign ('=',JSIdentifier 'àáâãäå',JSDecimal '1'),JSSemicolon]"

end LanguageJavascriptTests.ProgramParser
