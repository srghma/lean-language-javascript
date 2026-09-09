/-
Port of the Haskell test module `StatementParser`.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.AST

namespace LanguageJavascriptTests.StatementParser

open Spec
open Spec.Assert
open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.AST

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def showStrippedMaybe : Except String JSAST → String
  | .ok ast => "Right (" ++ showStripped ast ++ ")"
  | .error e => "Left (\"" ++ e ++ "\")"

def testStmt (str : String) : String := showStrippedMaybe (parseStatementAST str)

def statementCases : List (String × String) :=
  -- simple
  [ ("x", "Right (JSAstStatement (JSIdentifier 'x'))")
  , ("null", "Right (JSAstStatement (JSLiteral 'null'))")
  , ("true?1:2", "Right (JSAstStatement (JSExpressionTernary (JSLiteral 'true',JSDecimal '1',JSDecimal '2')))")
  -- block
  , ("{}", "Right (JSAstStatement (JSStatementBlock []))")
  , ("{x=1}", "Right (JSAstStatement (JSStatementBlock [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')]))")
  , ("{x=1;y=2}", "Right (JSAstStatement (JSStatementBlock [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon,JSOpAssign ('=',JSIdentifier 'y',JSDecimal '2')]))")
  , ("{{}}", "Right (JSAstStatement (JSStatementBlock [JSStatementBlock []]))")
  , ("{{{}}}", "Right (JSAstStatement (JSStatementBlock [JSStatementBlock [JSStatementBlock []]]))")
  -- if
  , ("if (1) {}", "Right (JSAstStatement (JSIf (JSDecimal '1') (JSStatementBlock [])))")
  -- if/else
  , ("if (1) {} else {}", "Right (JSAstStatement (JSIfElse (JSDecimal '1') (JSStatementBlock []) (JSStatementBlock [])))")
  , ("if (1) x=1; else {}", "Right (JSAstStatement (JSIfElse (JSDecimal '1') (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'),JSSemicolon) (JSStatementBlock [])))")
  , (" if (1);else break", "Right (JSAstStatement (JSIfElse (JSDecimal '1') (JSEmptyStatement) (JSBreak)))")
  -- while
  , ("while(true);", "Right (JSAstStatement (JSWhile (JSLiteral 'true') (JSEmptyStatement)))")
  -- do/while
  , ("do {x=1} while (true);", "Right (JSAstStatement (JSDoWhile (JSStatementBlock [JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')]) (JSLiteral 'true') (JSSemicolon)))")
  , ("do x=x+1;while(x<4);", "Right (JSAstStatement (JSDoWhile (JSOpAssign ('=',JSIdentifier 'x',JSExpressionBinary ('+',JSIdentifier 'x',JSDecimal '1')),JSSemicolon) (JSExpressionBinary ('<',JSIdentifier 'x',JSDecimal '4')) (JSSemicolon)))")
  -- for
  , ("for(;;);", "Right (JSAstStatement (JSFor () () () (JSEmptyStatement)))")
  , ("for(x=1;x<10;x++);", "Right (JSAstStatement (JSFor (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')) (JSExpressionBinary ('<',JSIdentifier 'x',JSDecimal '10')) (JSExpressionPostfix ('++',JSIdentifier 'x')) (JSEmptyStatement)))")
  , ("for(var x;;);", "Right (JSAstStatement (JSForVar (JSVarInitExpression (JSIdentifier 'x') ) () () (JSEmptyStatement)))")
  , ("for(var x=1;;);", "Right (JSAstStatement (JSForVar (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1']) () () (JSEmptyStatement)))")
  , ("for(var x;y;z){}", "Right (JSAstStatement (JSForVar (JSVarInitExpression (JSIdentifier 'x') ) (JSIdentifier 'y') (JSIdentifier 'z') (JSStatementBlock [])))")
  , ("for(x in 5){}", "Right (JSAstStatement (JSForIn JSIdentifier 'x' (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(var x in 5){}", "Right (JSAstStatement (JSForVarIn (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(let x;y;z){}", "Right (JSAstStatement (JSForLet (JSVarInitExpression (JSIdentifier 'x') ) (JSIdentifier 'y') (JSIdentifier 'z') (JSStatementBlock [])))")
  , ("for(let x in 5){}", "Right (JSAstStatement (JSForLetIn (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(let x of 5){}", "Right (JSAstStatement (JSForLetOf (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(const x;y;z){}", "Right (JSAstStatement (JSForConst (JSVarInitExpression (JSIdentifier 'x') ) (JSIdentifier 'y') (JSIdentifier 'z') (JSStatementBlock [])))")
  , ("for(const x in 5){}", "Right (JSAstStatement (JSForConstIn (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(const x of 5){}", "Right (JSAstStatement (JSForConstOf (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(x of 5){}", "Right (JSAstStatement (JSForOf JSIdentifier 'x' (JSDecimal '5') (JSStatementBlock [])))")
  , ("for(var x of 5){}", "Right (JSAstStatement (JSForVarOf (JSVarInitExpression (JSIdentifier 'x') ) (JSDecimal '5') (JSStatementBlock [])))")
  -- variable/constant/let declaration
  , ("var x=1;", "Right (JSAstStatement (JSVariable (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1'])))")
  , ("const x=1,y=2;", "Right (JSAstStatement (JSConstant (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1'],JSVarInitExpression (JSIdentifier 'y') [JSDecimal '2'])))")
  , ("let x=1,y=2;", "Right (JSAstStatement (JSLet (JSVarInitExpression (JSIdentifier 'x') [JSDecimal '1'],JSVarInitExpression (JSIdentifier 'y') [JSDecimal '2'])))")
  , ("var [a,b]=x", "Right (JSAstStatement (JSVariable (JSVarInitExpression (JSArrayLiteral [JSIdentifier 'a',JSComma,JSIdentifier 'b']) [JSIdentifier 'x'])))")
  , ("const {a:b}=x", "Right (JSAstStatement (JSConstant (JSVarInitExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'a') [JSIdentifier 'b']]) [JSIdentifier 'x'])))")
  -- break
  , ("break;", "Right (JSAstStatement (JSBreak,JSSemicolon))")
  , ("break x;", "Right (JSAstStatement (JSBreak 'x',JSSemicolon))")
  , ("{break}", "Right (JSAstStatement (JSStatementBlock [JSBreak]))")
  -- continue
  , ("continue;", "Right (JSAstStatement (JSContinue,JSSemicolon))")
  , ("continue x;", "Right (JSAstStatement (JSContinue 'x',JSSemicolon))")
  , ("{continue}", "Right (JSAstStatement (JSStatementBlock [JSContinue]))")
  -- return
  , ("return;", "Right (JSAstStatement (JSReturn JSSemicolon))")
  , ("return x;", "Right (JSAstStatement (JSReturn JSIdentifier 'x' JSSemicolon))")
  , ("return 123;", "Right (JSAstStatement (JSReturn JSDecimal '123' JSSemicolon))")
  , ("{return}", "Right (JSAstStatement (JSStatementBlock [JSReturn ]))")
  -- with
  , ("with (x) {};", "Right (JSAstStatement (JSWith (JSIdentifier 'x') (JSStatementBlock [])))")
  -- assign
  , ("var z = x[i] / y;", "Right (JSAstStatement (JSVariable (JSVarInitExpression (JSIdentifier 'z') [JSExpressionBinary ('/',JSMemberSquare (JSIdentifier 'x',JSIdentifier 'i'),JSIdentifier 'y')])))")
  -- label
  , ("abc:x=1", "Right (JSAstStatement (JSLabelled (JSIdentifier 'abc') (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1'))))")
  -- throw
  , ("throw 1", "Right (JSAstStatement (JSThrow (JSDecimal '1')))")
  -- switch
  , ("switch (x) {}", "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') []))")
  , ("switch (x) {case 1:break;}", "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSCase (JSDecimal '1') ([JSBreak,JSSemicolon])]))")
  , ("switch (x) {case 0:\ncase 1:break;}", "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSCase (JSDecimal '0') ([]),JSCase (JSDecimal '1') ([JSBreak,JSSemicolon])]))")
  , ("switch (x) {default:break;}", "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSDefault ([JSBreak,JSSemicolon])]))")
  , ("switch (x) {default:\ncase 1:break;}", "Right (JSAstStatement (JSSwitch (JSIdentifier 'x') [JSDefault ([]),JSCase (JSDecimal '1') ([JSBreak,JSSemicolon])]))")
  -- try/cathc/finally
  , ("try{}catch(a){}", "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock [])],JSFinally ())))")
  , ("try{}finally{}", "Right (JSAstStatement (JSTry (JSBlock [],[],JSFinally (JSBlock []))))")
  , ("try{}catch(a){}finally{}", "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock [])],JSFinally (JSBlock []))))")
  , ("try{}catch(a){}catch(b){}finally{}", "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock []),JSCatch (JSIdentifier 'b',JSBlock [])],JSFinally (JSBlock []))))")
  , ("try{}catch(a){}catch(b){}", "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a',JSBlock []),JSCatch (JSIdentifier 'b',JSBlock [])],JSFinally ())))")
  , ("try{}catch(a if true){}catch(b){}", "Right (JSAstStatement (JSTry (JSBlock [],[JSCatch (JSIdentifier 'a') if JSLiteral 'true' (JSBlock []),JSCatch (JSIdentifier 'b',JSBlock [])],JSFinally ())))")
  -- function
  , ("function x(){}", "Right (JSAstStatement (JSFunction 'x' () (JSBlock [])))")
  , ("function x(a){}", "Right (JSAstStatement (JSFunction 'x' (JSIdentifier 'a') (JSBlock [])))")
  , ("function x(a,b){}", "Right (JSAstStatement (JSFunction 'x' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))")
  , ("function x(...a){}", "Right (JSAstStatement (JSFunction 'x' (JSSpreadExpression (JSIdentifier 'a')) (JSBlock [])))")
  , ("function x(a=1){}", "Right (JSAstStatement (JSFunction 'x' (JSOpAssign ('=',JSIdentifier 'a',JSDecimal '1')) (JSBlock [])))")
  , ("function x([a]){}", "Right (JSAstStatement (JSFunction 'x' (JSArrayLiteral [JSIdentifier 'a']) (JSBlock [])))")
  , ("function x({a}){}", "Right (JSAstStatement (JSFunction 'x' (JSObjectLiteral [JSPropertyIdentRef 'a']) (JSBlock [])))")
  -- generator
  , ("function* x(){}", "Right (JSAstStatement (JSGenerator 'x' () (JSBlock [])))")
  , ("function* x(a){}", "Right (JSAstStatement (JSGenerator 'x' (JSIdentifier 'a') (JSBlock [])))")
  , ("function* x(a,b){}", "Right (JSAstStatement (JSGenerator 'x' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))")
  , ("function* x(a,...b){}", "Right (JSAstStatement (JSGenerator 'x' (JSIdentifier 'a',JSSpreadExpression (JSIdentifier 'b')) (JSBlock [])))")
  -- class
  , ("class Foo extends Bar { a(x,y) {} *b() {} }", "Right (JSAstStatement (JSClass 'Foo' (JSIdentifier 'Bar') [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock []),JSGeneratorMethodDefinition (JSIdentifier 'b') () (JSBlock [])]))")
  , ("class Foo { static get [a]() {}; }", "Right (JSAstStatement (JSClass 'Foo' () [JSClassStaticMethod (JSPropertyAccessor JSAccessorGet (JSPropertyComputed (JSIdentifier 'a')) () (JSBlock [])),JSClassSemi]))")
  , ("class Foo extends Bar { a(x,y) { super[x](y); } }", "Right (JSAstStatement (JSClass 'Foo' (JSIdentifier 'Bar') [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock [JSMethodCall (JSMemberSquare (JSLiteral 'super',JSIdentifier 'x'),JSArguments (JSIdentifier 'y')),JSSemicolon])]))")
  ]

def spec : Spec := do
  describe "Parse statements" do
    let mut seen : Std.HashSet String := {}
    for (input, expected) in statementCases do
      let rawName := escapeLabel input
      let name := if seen.contains rawName then s!"{rawName} (duplicate)" else rawName
      seen := seen.insert rawName
      it name do
        shouldEqual (testStmt input) expected

end LanguageJavascriptTests.StatementParser
