/-
Port of the Haskell test module `StatementParser`.
-/
import LanguageJavascriptTests.Utils

namespace Test.Language.Javascript

def testStatementParser : List Test :=
  -- simple
  [ shouldBe "x" (testStmt "x") "Right (JSAstStatement (JSIdentifier 'x'))"
  , shouldBe "null" (testStmt "null") "Right (JSAstStatement (JSLiteral 'null'))"
  , shouldBe "true?1:2" (testStmt "true?1:2") "Right (JSAstStatement (JSExpressionTernary (JSLiteral 'true',JSDecimal '1',JSDecimal '2')))"
  -- block
  , shouldBe "{}" (testStmt "{}") "Right (JSAstStatement (JSStatementBlock []))"
  , shouldBe "{x=1}" (testStmt "{x=1}") "Right (JSAstStatement (JSStatementBlock [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')]))"
  , shouldBe "{x=1;y=2}" (testStmt "{x=1;y=2}") "Right (JSAstStatement (JSStatementBlock [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon,JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2')]))"
  , shouldBe "{{}}" (testStmt "{{}}") "Right (JSAstStatement (JSStatementBlock [JSStatementBlock []]))"
  , shouldBe "{{{}}}" (testStmt "{{{}}}") "Right (JSAstStatement (JSStatementBlock [JSStatementBlock [JSStatementBlock []]]))"
  -- if
  , shouldBe "if (1) {}" (testStmt "if (1) {}") "Right (JSAstStatement (JSIf (JSDecimal '1') (JSStatementBlock [])))"
  -- if/else
  , shouldBe "if (1) {} else {}" (testStmt "if (1) {} else {}") "Right (JSAstStatement (JSIfElse (JSDecimal '1') (JSStatementBlock []) (JSStatementBlock [])))"
  , shouldBe "if (1) x=1; else {}" (testStmt "if (1) x=1; else {}") "Right (JSAstStatement (JSIfElse (JSDecimal '1') (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon) (JSStatementBlock [])))"
  , shouldBe " if (1);else break" (testStmt " if (1);else break") "Right (JSAstStatement (JSIfElse (JSDecimal '1') (JSEmptyStatement) (JSBreak)))"
  -- while
  , shouldBe "while(true);" (testStmt "while(true);") "Right (JSAstStatement (JSWhile (JSLiteral 'true') (JSEmptyStatement)))"
  -- do/while
  , shouldBe "do {x=1} while (true);" (testStmt "do {x=1} while (true);") "Right (JSAstStatement (JSDoWhile (JSStatementBlock [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')]) (JSLiteral 'true') (JSSemicolon)))"
  , shouldBe "do x=x+1;while(x<4);" (testStmt "do x=x+1;while(x<4);") "Right (JSAstStatement (JSDoWhile (JSOpAssign ('=',JSIdentifier 'x',JSExpressionBinary ('+',JSIdentifier 'x',JSDecimal '1')),JSSemicolon) (JSExpressionBinary ('<',JSIdentifier 'x',JSDecimal '4')) (JSSemicolon)))"
  -- for
  , shouldBe "for(;;);" (testStmt "for(;;);") "Right (JSAstStatement (JSFor () () () (JSEmptyStatement)))"
  , shouldBe "for(x=1;x<10;x++);" (testStmt "for(x=1;x<10;x++);") "Right (JSAstStatement (JSFor (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')) (JSExpressionBinary ('<',JSIdentifier 'x',JSDecimal '10')) (JSExpressionPostfix ('++',JSIdentifier 'x')) (JSEmptyStatement)))"
  , shouldBe "for(var x;;);" (testStmt "for(var x;;);") "Right (JSAstStatement (JSForVar (JSVarInitExpression (JSIdentifier 'x') ) () () (JSEmptyStatement)))"
  , shouldBe "for(var x=1;;);" (testStmt "for(var x=1;;);") "Right (JSAstStatement (JSForVar (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1']) () () (JSEmptyStatement)))"
  , shouldBe "for(var x;y;z){}" (testStmt "for(var x;y;z){}") "Right (JSAstStatement (JSForVar (JSVarInitExpression (JSIdentifier 'x') ) (JSIdentifier 'y') (JSIdentifier 'z') (JSStatementBlock [])))"
  , shouldBe "for(x in 5){}" (testStmt "for(x in 5){}") "Right (JSAstStatement (JSForIn JSIdentifier 'x' (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(var x in 5){}" (testStmt "for(var x in 5){}") "Right (JSAstStatement (JSForVarIn (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(let x;y;z){}" (testStmt "for(let x;y;z){}") "Right (JSAstStatement (JSForLet (JSVarInitExpression (JSIdentifier 'x') ) (JSIdentifier 'y') (JSIdentifier 'z') (JSStatementBlock [])))"
  , shouldBe "for(let x in 5){}" (testStmt "for(let x in 5){}") "Right (JSAstStatement (JSForLetIn (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(let x of 5){}" (testStmt "for(let x of 5){}") "Right (JSAstStatement (JSForLetOf (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(const x;y;z){}" (testStmt "for(const x;y;z){}") "Right (JSAstStatement (JSForConst (JSVarInitExpression (JSIdentifier 'x') ) (JSIdentifier 'y') (JSIdentifier 'z') (JSStatementBlock [])))"
  , shouldBe "for(const x in 5){}" (testStmt "for(const x in 5){}") "Right (JSAstStatement (JSForConstIn (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(const x of 5){}" (testStmt "for(const x of 5){}") "Right (JSAstStatement (JSForConstOf (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(x of 5){}" (testStmt "for(x of 5){}") "Right (JSAstStatement (JSForOf JSIdentifier 'x' (JSDecimal '5') (JSStatementBlock [])))"
  , shouldBe "for(var x of 5){}" (testStmt "for(var x of 5){}") "Right (JSAstStatement (JSForVarOf (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))"
  -- variable/constant/let declaration
  , shouldBe "var x=1;" (testStmt "var x=1;") "Right (JSAstStatement (JSVariable (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1'])))"
  , shouldBe "const x=1,y=2;" (testStmt "const x=1,y=2;") "Right (JSAstStatement (JSConstant (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1'],JSVarInitExpression (JSIdentifier 'y') [JSDecimal '2'])))"
  , shouldBe "let x=1,y=2;" (testStmt "let x=1,y=2;") "Right (JSAstStatement (JSLet (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1'],JSVarInitExpression (JSIdentifier 'y') [JSDecimal '2'])))"
  , shouldBe "var [a,b]=x" (testStmt "var [a,b]=x") "Right (JSAstStatement (JSVariable (JSVarInitExpression (JSArrayLiteral [JSIdentifier 'a',JSComma,JSIdentifier 'b']) [JSIdentifier 'x'])))"
  , shouldBe "const {a:b}=x" (testStmt "const {a:b}=x") "Right (JSAstStatement (JSConstant (JSVarInitExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'a') [JSIdentifier 'b']]) [JSIdentifier 'x'])))"
  -- break
  , shouldBe "break;" (testStmt "break;") "Right (JSAstStatement (JSBreak,JSSemicolon))"
  , shouldBe "break x;" (testStmt "break x;") "Right (JSAstStatement (JSBreak 'x',JSSemicolon))"
  , shouldBe "{break}" (testStmt "{break}") "Right (JSAstStatement (JSStatementBlock [JSBreak]))"
  -- continue
  , shouldBe "continue;" (testStmt "continue;") "Right (JSAstStatement (JSContinue,JSSemicolon))"
  , shouldBe "continue x;" (testStmt "continue x;") "Right (JSAstStatement (JSContinue 'x',JSSemicolon))"
  , shouldBe "{continue}" (testStmt "{continue}") "Right (JSAstStatement (JSStatementBlock [JSContinue]))"
  -- return
  , shouldBe "return;" (testStmt "return;") "Right (JSAstStatement (JSReturn JSSemicolon))"
  , shouldBe "return x;" (testStmt "return x;") "Right (JSAstStatement (JSReturn JSIdentifier 'x' JSSemicolon))"
  , shouldBe "return 123;" (testStmt "return 123;") "Right (JSAstStatement (JSReturn JSDecimal '123' JSSemicolon))"
  , shouldBe "{return}" (testStmt "{return}") "Right (JSAstStatement (JSStatementBlock [JSReturn ]))"
  -- with
  , shouldBe "with (x) {};" (testStmt "with (x) {};") "Right (JSAstStatement (JSWith (JSIdentifier 'x') (JSStatementBlock [])))"
  -- assign
  , shouldBe "var z = x[i] / y;" (testStmt "var z = x[i] / y;") "Right (JSAstStatement (JSVariable (JSVarInitExpression (JSIdentifier 'z') [JSExpressionBinary ('/',JSMemberSquare (JSIdentifier 'x',JSIdentifier 'i'),JSIdentifier 'y')])))"
  -- label
  , shouldBe "abc:x=1" (testStmt "abc:x=1") "Right (JSAstStatement (JSLabelled (JSIdentifier 'abc') (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'))))"
  -- throw
  , shouldBe "throw 1" (testStmt "throw 1") "Right (JSAstStatement (JSThrow (JSDecimal '1')))"
  -- switch
  , shouldBe "switch (x) {}" (testStmt "switch (x) {}") "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') []))"
  , shouldBe "switch (x) {case 1:break;}" (testStmt "switch (x) {case 1:break;}") "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSCase (JSDecimal '1') ([JSBreak,JSSemicolon])]))"
  , shouldBe "switch (x) {case 0:\ncase 1:break;}" (testStmt "switch (x) {case 0:\ncase 1:break;}") "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSCase (JSDecimal '0') ([]),JSCase (JSDecimal '1') ([JSBreak,JSSemicolon])]))"
  , shouldBe "switch (x) {default:break;}" (testStmt "switch (x) {default:break;}") "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSDefault ([JSBreak,JSSemicolon])]))"
  , shouldBe "switch (x) {default:\ncase 1:break;}" (testStmt "switch (x) {default:\ncase 1:break;}") "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSDefault ([]),JSCase (JSDecimal '1') ([JSBreak,JSSemicolon])]))"
  -- try/cathc/finally
  , shouldBe "try{}catch(a){}" (testStmt "try{}catch(a){}") "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock [])],JSFinally ())))"
  , shouldBe "try{}finally{}" (testStmt "try{}finally{}") "Right (JSAstStatement (JSTry (JSBlock [],[],JSFinally (JSBlock []))))"
  , shouldBe "try{}catch(a){}finally{}" (testStmt "try{}catch(a){}finally{}") "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock [])],JSFinally (JSBlock []))))"
  , shouldBe "try{}catch(a){}catch(b){}finally{}" (testStmt "try{}catch(a){}catch(b){}finally{}") "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock []),JSCatch (JSIdentifier 'b',JSBlock [])],JSFinally (JSBlock []))))"
  , shouldBe "try{}catch(a){}catch(b){}" (testStmt "try{}catch(a){}catch(b){}") "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock []),JSCatch (JSIdentifier 'b',JSBlock [])],JSFinally ())))"
  , shouldBe "try{}catch(a if true){}catch(b){}" (testStmt "try{}catch(a if true){}catch(b){}") "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a') if JSLiteral 'true' (JSBlock []),JSCatch (JSIdentifier 'b',JSBlock [])],JSFinally ())))"
  -- function
  , shouldBe "function x(){}" (testStmt "function x(){}") "Right (JSAstStatement (JSFunction 'x' () (JSBlock [])))"
  , shouldBe "function x(a){}" (testStmt "function x(a){}") "Right (JSAstStatement (JSFunction 'x' (JSIdentifier 'a') (JSBlock [])))"
  , shouldBe "function x(a,b){}" (testStmt "function x(a,b){}") "Right (JSAstStatement (JSFunction 'x' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))"
  , shouldBe "function x(...a){}" (testStmt "function x(...a){}") "Right (JSAstStatement (JSFunction 'x' (JSSpreadExpression (JSIdentifier 'a')) (JSBlock [])))"
  , shouldBe "function x(a=1){}" (testStmt "function x(a=1){}") "Right (JSAstStatement (JSFunction 'x' (JSOpAssign ('=',JSIdentifier 'a',JSDecimal '1')) (JSBlock [])))"
  , shouldBe "function x([a]){}" (testStmt "function x([a]){}") "Right (JSAstStatement (JSFunction 'x' (JSArrayLiteral [JSIdentifier 'a']) (JSBlock [])))"
  , shouldBe "function x({a}){}" (testStmt "function x({a}){}") "Right (JSAstStatement (JSFunction 'x' (JSObjectLiteral [JSPropertyIdentRef 'a']) (JSBlock [])))"
  -- generator
  , shouldBe "function* x(){}" (testStmt "function* x(){}") "Right (JSAstStatement (JSGenerator 'x' () (JSBlock [])))"
  , shouldBe "function* x(a){}" (testStmt "function* x(a){}") "Right (JSAstStatement (JSGenerator 'x' (JSIdentifier 'a') (JSBlock [])))"
  , shouldBe "function* x(a,b){}" (testStmt "function* x(a,b){}") "Right (JSAstStatement (JSGenerator 'x' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))"
  , shouldBe "function* x(a,...b){}" (testStmt "function* x(a,...b){}") "Right (JSAstStatement (JSGenerator 'x' (JSIdentifier 'a',JSSpreadExpression (JSIdentifier 'b')) (JSBlock [])))"
  -- class
  , shouldBe "class Foo extends Bar { a(x,y) {} *b() {} }" (testStmt "class Foo extends Bar { a(x,y) {} *b() {} }") "Right (JSAstStatement (JSClass 'Foo' (JSIdentifier 'Bar') [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock []),JSGeneratorMethodDefinition (JSIdentifier 'b') () (JSBlock [])]))"
  , shouldBe "class Foo { static get [a]() {}; }" (testStmt "class Foo { static get [a]() {}; }") "Right (JSAstStatement (JSClass 'Foo' () [JSClassStaticMethod (JSPropertyAccessor JSAccessorGet (JSPropertyComputed (JSIdentifier 'a')) () (JSBlock [])),JSClassSemi]))"
  , shouldBe "class Foo extends Bar { a(x,y) { super[x](y); } }" (testStmt "class Foo extends Bar { a(x,y) { super[x](y); } }") "Right (JSAstStatement (JSClass 'Foo' (JSIdentifier 'Bar') [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock [JSMethodCall (JSMemberSquare (JSLiteral 'super',JSIdentifier 'x'),JSArguments (JSIdentifier 'y')),JSSemicolon])]))"
  ]

#guard allPass testStatementParser

end Test.Language.Javascript
