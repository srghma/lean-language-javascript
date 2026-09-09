/-
Port of the Haskell test module `ProgramParser`.
-/
import LanguageJavascriptTests.Utils

namespace Test.Language.Javascript

def testProgramParser : List Test :=
  -- function
  [ shouldBe "function a(){}" (testProg "function a(){}") "Right (JSAstProgram [JSFunction 'a' () (JSBlock [])])"
  , shouldBe "function a(b,c){}" (testProg "function a(b,c){}") "Right (JSAstProgram [JSFunction 'a' (JSIdentifier 'b',JSIdentifier 'c') (JSBlock [])])"
  -- comments
  , shouldBe "//blah\nx=1;//foo\na" (testProg "//blah\nx=1;//foo\na") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon,JSIdentifier 'a'])"
  , shouldBe "/*x=1\ny=2\n*/z=2;//foo\na" (testProg "/*x=1\ny=2\n*/z=2;//foo\na") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'z',JSDecimal '2'),JSSemicolon,JSIdentifier 'a'])"
  , shouldBe "/* */\nfunction f() {\n/*  */\n}\n" (testProg "/* */\nfunction f() {\n/*  */\n}\n") "Right (JSAstProgram [JSFunction 'f' () (JSBlock [])])"
  , shouldBe "/* **/\nfunction f() {\n/*  */\n}\n" (testProg "/* **/\nfunction f() {\n/*  */\n}\n") "Right (JSAstProgram [JSFunction 'f' () (JSBlock [])])"
  -- if
  , shouldBe "if(x);x=1" (testProg "if(x);x=1") "Right (JSAstProgram [JSIf (JSIdentifier 'x') (JSEmptyStatement),JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')])"
  , shouldBe "if(a)x=1;y=2" (testProg "if(a)x=1;y=2") "Right (JSAstProgram [JSIf (JSIdentifier 'a') (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon),JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2')])"
  , shouldBe "if(a)x=a()y=2" (testProg "if(a)x=a()y=2") "Right (JSAstProgram [JSIf (JSIdentifier 'a') (JSOpAssign ('=',JSIdentifier 'x',JSMemberExpression (JSIdentifier 'a',JSArguments ()))),JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2')])"
  , shouldBe "if(true)break \nfoo();" (testProg "if(true)break \nfoo();") "Right (JSAstProgram [JSIf (JSLiteral 'true') (JSBreak),JSMethodCall (JSIdentifier 'foo',JSArguments ()),JSSemicolon])"
  , shouldBe "if(true)continue \nfoo();" (testProg "if(true)continue \nfoo();") "Right (JSAstProgram [JSIf (JSLiteral 'true') (JSContinue),JSMethodCall (JSIdentifier 'foo',JSArguments ()),JSSemicolon])"
  , shouldBe "if(true)break \nfoo();" (testProg "if(true)break \nfoo();") "Right (JSAstProgram [JSIf (JSLiteral 'true') (JSBreak),JSMethodCall (JSIdentifier 'foo',JSArguments ()),JSSemicolon])"
  -- assign
  , shouldBe "x = 1\n  y=2;" (testProg "x = 1\n  y=2;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2'),JSSemicolon])"
  -- regex
  , shouldBe "x=/\\n/g" (testProg "x=/\\n/g") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSRegEx '/\\n/g')])"
  , shouldBe "x=i(/^$/g,\"\\\\$&\")" (testProg "x=i(/^$/g,\"\\\\$&\")") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSMemberExpression (JSIdentifier 'i',JSArguments (JSRegEx '/^$/g',JSStringLiteral \"\\\\$&\")))])"
  , shouldBe "x=i(/[?|^&(){}\\[\\]+\\-*\\/\\.]/g,\"\\\\$&\")" (testProg "x=i(/[?|^&(){}\\[\\]+\\-*\\/\\.]/g,\"\\\\$&\")") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSMemberExpression (JSIdentifier 'i',JSArguments (JSRegEx '/[?|^&(){}\\[\\]+\\-*\\/\\.]/g',JSStringLiteral \"\\\\$&\")))])"
  , shouldBe "(match = /^\"(?:\\\\.|[^\"])*\"|^'(?:[^']|\\\\.)*'/(input))" (testProg "(match = /^\"(?:\\\\.|[^\"])*\"|^'(?:[^']|\\\\.)*'/(input))") "Right (JSAstProgram [JSExpressionParen (JSOpAssign ('=',JSIdentifier 'match',JSMemberExpression (JSRegEx '/^\"(?:\\\\.|[^\"])*\"|^'(?:[^']|\\\\.)*'/',JSArguments (JSIdentifier 'input'))))])"
  , shouldBe "if(/^[a-z]/.test(t)){consts+=t.toUpperCase();keywords[t]=i}else consts+=(/^\\W/.test(t)?opTypeNames[t]:t);" (testProg "if(/^[a-z]/.test(t)){consts+=t.toUpperCase();keywords[t]=i}else consts+=(/^\\W/.test(t)?opTypeNames[t]:t);") "Right (JSAstProgram [JSIfElse (JSMemberExpression (JSMemberDot (JSRegEx '/^[a-z]/',JSIdentifier 'test'),JSArguments (JSIdentifier 't'))) (JSStatementBlock [JSOpAssign ('+=',JSIdentifier 'consts',JSMemberExpression (JSMemberDot (JSIdentifier 't',JSIdentifier 'toUpperCase'),JSArguments ())),JSSemicolon,JSOpAssign ('=',JSMemberSquare (JSIdentifier 'keywords',JSIdentifier 't'),JSIdentifier 'i')]) (JSOpAssign ('+=',JSIdentifier 'consts',JSExpressionParen (JSExpressionTernary (JSMemberExpression (JSMemberDot (JSRegEx '/^\\W/',JSIdentifier 'test'),JSArguments (JSIdentifier 't')),JSMemberSquare (JSIdentifier 'opTypeNames',JSIdentifier 't'),JSIdentifier 't'))),JSSemicolon)])"
  -- unicode
  , shouldBe "àáâãäå = 1;" (testProg "àáâãäå = 1;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'àáâãäå',JSDecimal '1'),JSSemicolon])"
  , shouldBe "//comment\u000ax=1;" (testProg "//comment\u000ax=1;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])"
  , shouldBe "//comment\u000dx=1;" (testProg "//comment\u000dx=1;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])"
  , shouldBe "//comment x=1;" (testProg "//comment x=1;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])"
  , shouldBe "//comment x=1;" (testProg "//comment x=1;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon])"
  , shouldBe "$aà = 1;_b=2;Aa=2" (testProg "$aà = 1;_b=2;Aa=2") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier '$aà',JSDecimal '1'),JSSemicolon,JSOpAssign ('=',JSIdentifier '_b',JSDecimal '2'),JSSemicolon,JSOpAssign ('=',JSIdentifier 'Aa',JSDecimal '2')])"
  , shouldBe "x=\"àáâãäå\";y='௄aD'" (testProg "x=\"àáâãäå\";y='௄aD'") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"àáâãäå\"),JSSemicolon,JSOpAssign ('=',JSIdentifier 'y',JSStringLiteral '௄aD')])"
  , shouldBe "a \u000c\u000b\t\r\n=  ᠎               　1;" (testProg "a \u000c\u000b\t\r\n=  ᠎               　1;") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'a',JSDecimal '1'),JSSemicolon])"
  , shouldBe "/* * geolocation. пытаемся определить свое местоположение * если не получается то используем defaultLocation * @Param {object} map экземпляр карты * @Param {object LatLng} defaultLocation Координаты центра по умолчанию * @Param {function} callbackAfterLocation Фу-ия которая вызывается после * геолокации. Т.к запрос геолокации асинхронен */x" (testProg "/* * geolocation. пытаемся определить свое местоположение * если не получается то используем defaultLocation * @Param {object} map экземпляр карты * @Param {object LatLng} defaultLocation Координаты центра по умолчанию * @Param {function} callbackAfterLocation Фу-ия которая вызывается после * геолокации. Т.к запрос геолокации асинхронен */x") "Right (JSAstProgram [JSIdentifier 'x'])"
  -- strings
  , shouldBe "x='abc\\ndef';" (testProg "x='abc\\ndef';") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral 'abc\\ndef'),JSSemicolon])"
  , shouldBe "x=\"abc\\ndef\";" (testProg "x=\"abc\\ndef\";") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\ndef\"),JSSemicolon])"
  , shouldBe "x=\"abc\\rdef\";" (testProg "x=\"abc\\rdef\";") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\rdef\"),JSSemicolon])"
  , shouldBe "x=\"abc\\r\\ndef\";" (testProg "x=\"abc\\r\\ndef\";") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\r\\ndef\"),JSSemicolon])"
  , shouldBe "x=\"abc\\x2028 def\";" (testProg "x=\"abc\\x2028 def\";") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\x2028 def\"),JSSemicolon])"
  , shouldBe "x=\"abc\\x2029 def\";" (testProg "x=\"abc\\x2029 def\";") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSStringLiteral \"abc\\x2029 def\"),JSSemicolon])"
  -- object literal
  , shouldBe "x = { y: 1e8 }" (testProg "x = { y: 1e8 }") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSDecimal '1e8']])])"
  , shouldBe "{ y: 1e8 }" (testProg "{ y: 1e8 }") "Right (JSAstProgram [JSStatementBlock [JSLabelled (JSIdentifier 'y') (JSDecimal '1e8')]])"
  , shouldBe "{ y: 18 }" (testProg "{ y: 18 }") "Right (JSAstProgram [JSStatementBlock [JSLabelled (JSIdentifier 'y') (JSDecimal '18')]])"
  , shouldBe "x = { y: 18 }" (testProg "x = { y: 18 }") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'x',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSDecimal '18']])])"
  , shouldBe "var k = {\ny: somename\n}" (testProg "var k = {\ny: somename\n}") "Right (JSAstProgram [JSVariable (JSVarInitExpression (JSIdentifier 'k') [JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSIdentifier 'somename']]])])"
  , shouldBe "var k = {\ny: code\n}" (testProg "var k = {\ny: code\n}") "Right (JSAstProgram [JSVariable (JSVarInitExpression (JSIdentifier 'k') [JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSIdentifier 'code']]])])"
  , shouldBe "var k = {\ny: mode\n}" (testProg "var k = {\ny: mode\n}") "Right (JSAstProgram [JSVariable (JSVarInitExpression (JSIdentifier 'k') [JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'y') [JSIdentifier 'mode']]])])"
  -- programs
  , shouldBe "newlines=spaces.match(/\\n/g)" (testProg "newlines=spaces.match(/\\n/g)") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'newlines',JSMemberExpression (JSMemberDot (JSIdentifier 'spaces',JSIdentifier 'match'),JSArguments (JSRegEx '/\\n/g')))])"
  , shouldBe "Animal=function(){return this.name};" (testProg "Animal=function(){return this.name};") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'Animal',JSFunctionExpression '' () (JSBlock [JSReturn JSMemberDot (JSLiteral 'this',JSIdentifier 'name') ])),JSSemicolon])"
  , shouldBe "$(img).click(function(){alert('clicked!')});" (testProg "$(img).click(function(){alert('clicked!')});") "Right (JSAstProgram [JSCallExpression (JSCallExpressionDot (JSMemberExpression (JSIdentifier '$',JSArguments (JSIdentifier 'img')),JSIdentifier 'click'),JSArguments (JSFunctionExpression '' () (JSBlock [JSMethodCall (JSIdentifier 'alert',JSArguments (JSStringLiteral 'clicked!'))]))),JSSemicolon])"
  , shouldBe "function() {\nz = function z(o) {\nreturn r;\n};}" (testProg "function() {\nz = function z(o) {\nreturn r;\n};}") "Right (JSAstProgram [JSFunctionExpression '' () (JSBlock [JSOpAssign ('=',JSIdentifier 'z',JSFunctionExpression 'z' (JSIdentifier 'o') (JSBlock [JSReturn JSIdentifier 'r' JSSemicolon])),JSSemicolon])])"
  , shouldBe "function() {\nz = function /*z*/(o) {\nreturn r;\n};}" (testProg "function() {\nz = function /*z*/(o) {\nreturn r;\n};}") "Right (JSAstProgram [JSFunctionExpression '' () (JSBlock [JSOpAssign ('=',JSIdentifier 'z',JSFunctionExpression '' (JSIdentifier 'o') (JSBlock [JSReturn JSIdentifier 'r' JSSemicolon])),JSSemicolon])])"
  , shouldBe "{zero}\nget;two\n{three\nfour;set;\n{\nsix;{seven;}\n}\n}" (testProg "{zero}\nget;two\n{three\nfour;set;\n{\nsix;{seven;}\n}\n}") "Right (JSAstProgram [JSStatementBlock [JSIdentifier 'zero'],JSIdentifier 'get',JSSemicolon,JSIdentifier 'two',JSStatementBlock [JSIdentifier 'three',JSIdentifier 'four',JSSemicolon,JSIdentifier 'set',JSSemicolon,JSStatementBlock [JSIdentifier 'six',JSSemicolon,JSStatementBlock [JSIdentifier 'seven',JSSemicolon]]]])"
  , shouldBe "{zero}\none1;two\n{three\nfour;five;\n{\nsix;{seven;}\n}\n}" (testProg "{zero}\none1;two\n{three\nfour;five;\n{\nsix;{seven;}\n}\n}") "Right (JSAstProgram [JSStatementBlock [JSIdentifier 'zero'],JSIdentifier 'one1',JSSemicolon,JSIdentifier 'two',JSStatementBlock [JSIdentifier 'three',JSIdentifier 'four',JSSemicolon,JSIdentifier 'five',JSSemicolon,JSStatementBlock [JSIdentifier 'six',JSSemicolon,JSStatementBlock [JSIdentifier 'seven',JSSemicolon]]]])"
  , shouldBe "v = getValue(execute(n[0], x)) in getValue(execute(n[1], x));" (testProg "v = getValue(execute(n[0], x)) in getValue(execute(n[1], x));") "Right (JSAstProgram [JSOpAssign ('=',JSIdentifier 'v',JSExpressionBinary ('in',JSMemberExpression (JSIdentifier 'getValue',JSArguments (JSMemberExpression (JSIdentifier 'execute',JSArguments (JSMemberSquare (JSIdentifier 'n',JSDecimal '0'),JSIdentifier 'x')))),JSMemberExpression (JSIdentifier 'getValue',JSArguments (JSMemberExpression (JSIdentifier 'execute',JSArguments (JSMemberSquare (JSIdentifier 'n',JSDecimal '1'),JSIdentifier 'x')))))),JSSemicolon])"
  , shouldBe "function Animal(name){if(!name)throw new Error('Must specify an animal name');this.name=name};Animal.prototype.toString=function(){return this.name};o=new Animal(\"bob\");o.toString()==\"bob\"" (testProg "function Animal(name){if(!name)throw new Error('Must specify an animal name');this.name=name};Animal.prototype.toString=function(){return this.name};o=new Animal(\"bob\");o.toString()==\"bob\"") "Right (JSAstProgram [JSFunction 'Animal' (JSIdentifier 'name') (JSBlock [JSIf (JSUnaryExpression ('!',JSIdentifier 'name')) (JSThrow (JSMemberNew (JSIdentifier 'Error',JSArguments (JSStringLiteral 'Must specify an animal name')))),JSOpAssign ('=',JSMemberDot (JSLiteral 'this',JSIdentifier 'name'),JSIdentifier 'name')]),JSOpAssign ('=',JSMemberDot (JSMemberDot (JSIdentifier 'Animal',JSIdentifier 'prototype'),JSIdentifier 'toString'),JSFunctionExpression '' () (JSBlock [JSReturn JSMemberDot (JSLiteral 'this',JSIdentifier 'name') ])),JSSemicolon,JSOpAssign ('=',JSIdentifier 'o',JSMemberNew (JSIdentifier 'Animal',JSArguments (JSStringLiteral \"bob\"))),JSSemicolon,JSExpressionBinary ('==',JSMemberExpression (JSMemberDot (JSIdentifier 'o',JSIdentifier 'toString'),JSArguments ()),JSStringLiteral \"bob\")])"
  ]

#guard allPass testProgramParser

end Test.Language.Javascript
