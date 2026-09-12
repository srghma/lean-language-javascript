/-
Port of the Haskell test module `ExpressionParser`.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.AST
import LanguageJavascript.ShowStripped

namespace LanguageJavascriptTests.ExpressionParser

open Spec
open Spec.Assert
open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def showStrippedMaybe : Except String JSAST → String
  | .ok ast => "Right (" ++ showStripped ast ++ ")"
  | .error e => "Left (\"" ++ e ++ "\")"

def testExpr (str : String) : String := showStrippedMaybe (parseExpressionAST str)

def expressionCases : List (String × String) :=
  -- this
  [ ("this", "Right (JSAstExpression (JSLiteral 'this'))")
  -- regex
  , ("/blah/", "Right (JSAstExpression (JSRegEx '/blah/'))")
  , ("/$/g", "Right (JSAstExpression (JSRegEx '/$/g'))")
  , ("/\\n/g", "Right (JSAstExpression (JSRegEx '/\\n/g'))")
  , ("/(\\/)/", "Right (JSAstExpression (JSRegEx '/(\\/)/'))")
  , ("/a[/]b/", "Right (JSAstExpression (JSRegEx '/a[/]b/'))")
  , ("/[/\\]/", "Right (JSAstExpression (JSRegEx '/[/\\]/'))")
  , ("/(\\/|\\)/", "Right (JSAstExpression (JSRegEx '/(\\/|\\)/'))")
  , ("/a\\[|\\]$/g", "Right (JSAstExpression (JSRegEx '/a\\[|\\]$/g'))")
  , ("/[(){}\\[\\]]/g", "Right (JSAstExpression (JSRegEx '/[(){}\\[\\]]/g'))")
  , ("/^\"(?:\\.|[^\"])*\"|^'(?:[^']|\\.)*'/", "Right (JSAstExpression (JSRegEx '/^\"(?:\\.|[^\"])*\"|^'(?:[^']|\\.)*'/'))")
  -- identifier
  , ("_$", "Right (JSAstExpression (JSIdentifier '_$'))")
  , ("this_", "Right (JSAstExpression (JSIdentifier 'this_'))")
  -- array literal
  , ("[]", "Right (JSAstExpression (JSArrayLiteral []))")
  , ("[,]", "Right (JSAstExpression (JSArrayLiteral [JSComma]))")
  , ("[,,]", "Right (JSAstExpression (JSArrayLiteral [JSComma,JSComma]))")
  , ("[,,x]", "Right (JSAstExpression (JSArrayLiteral [JSComma,JSComma,JSIdentifier 'x']))")
  , ("[,,x]", "Right (JSAstExpression (JSArrayLiteral [JSComma,JSComma,JSIdentifier 'x']))")
  , ("[,x,,x]", "Right (JSAstExpression (JSArrayLiteral [JSComma,JSIdentifier 'x',JSComma,JSComma,JSIdentifier 'x']))")
  , ("[x]", "Right (JSAstExpression (JSArrayLiteral [JSIdentifier 'x']))")
  , ("[x,]", "Right (JSAstExpression (JSArrayLiteral [JSIdentifier 'x',JSComma]))")
  , ("[,,,]", "Right (JSAstExpression (JSArrayLiteral [JSComma,JSComma,JSComma]))")
  , ("[a,,]", "Right (JSAstExpression (JSArrayLiteral [JSIdentifier 'a',JSComma,JSComma]))")
  -- operator precedence
  , ("2+3*4+5", "Right (JSAstExpression (JSExpressionBinary ('+',JSExpressionBinary ('+',JSDecimal '2',JSExpressionBinary ('*',JSDecimal '3',JSDecimal '4')),JSDecimal '5')))")
  -- parentheses
  , ("(56)", "Right (JSAstExpression (JSExpressionParen (JSDecimal '56')))")
  -- string concatenation
  , ("'ab' + 'bc'", "Right (JSAstExpression (JSExpressionBinary ('+',JSStringLiteral 'ab',JSStringLiteral 'bc')))")
  , ("'bc' + \"cd\"", "Right (JSAstExpression (JSExpressionBinary ('+',JSStringLiteral 'bc',JSStringLiteral \"cd\")))")
  -- object literal
  , ("{}", "Right (JSAstExpression (JSObjectLiteral []))")
  , ("{x:1}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'x') [JSDecimal '1']]))")
  , ("{x:1,y:2}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'x') [JSDecimal '1'],JSPropertyNameandValue (JSIdentifier 'y') [JSDecimal '2']]))")
  , ("{x:1,}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'x') [JSDecimal '1'],JSComma]))")
  , ("{yield:1}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'yield') [JSDecimal '1']]))")
  , ("{x}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyIdentRef 'x']))")
  , ("{x,}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyIdentRef 'x',JSComma]))")
  , ("{set x([a,b]=y) {this.a=a;this.b=b}}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyAccessor JSAccessorSet (JSIdentifier 'x') (JSOpAssign ('=',JSArrayLiteral [JSIdentifier 'a',JSComma,JSIdentifier 'b'],JSIdentifier 'y')) (JSBlock [JSOpAssign ('=',JSMemberDot (JSLiteral 'this',JSIdentifier 'a'),JSIdentifier 'a'),JSSemicolon,JSOpAssign ('=',JSMemberDot (JSLiteral 'this',JSIdentifier 'b'),JSIdentifier 'b')])]))")
  , ("a={if:1,interface:2}", "Right (JSAstExpression (JSOpAssign ('=',JSIdentifier 'a',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'if') [JSDecimal '1'],JSPropertyNameandValue (JSIdentifier 'interface') [JSDecimal '2']])))")
  , ("a={\n  values: 7,\n}\n", "Right (JSAstExpression (JSOpAssign ('=',JSIdentifier 'a',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'values') [JSDecimal '7'],JSComma])))")
  , ("x={get foo() {return 1},set foo(a) {x=a}}", "Right (JSAstExpression (JSOpAssign ('=',JSIdentifier 'x',JSObjectLiteral [JSPropertyAccessor JSAccessorGet (JSIdentifier 'foo') () (JSBlock [JSReturn JSDecimal '1' ]),JSPropertyAccessor JSAccessorSet (JSIdentifier 'foo') (JSIdentifier 'a') (JSBlock [JSOpAssign ('=',JSIdentifier 'x',JSIdentifier 'a')])])))")
  , ("{evaluate:evaluate,load:function load(s){if(x)return s;1}}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'evaluate') [JSIdentifier 'evaluate'],JSPropertyNameandValue (JSIdentifier 'load') [JSFunctionExpression 'load' (JSIdentifier 's') (JSBlock [JSIf (JSIdentifier 'x') (JSReturn JSIdentifier 's' JSSemicolon),JSDecimal '1'])]]))")
  , ("obj = { name : 'A', 'str' : 'B', 123 : 'C', }", "Right (JSAstExpression (JSOpAssign ('=',JSIdentifier 'obj',JSObjectLiteral [JSPropertyNameandValue (JSIdentifier 'name') [JSStringLiteral 'A'],JSPropertyNameandValue (JSIdentifier ''str'') [JSStringLiteral 'B'],JSPropertyNameandValue (JSIdentifier '123') [JSStringLiteral 'C'],JSComma])))")
  , ("{[x]:1}", "Right (JSAstExpression (JSObjectLiteral [JSPropertyNameandValue (JSPropertyComputed (JSIdentifier 'x')) [JSDecimal '1']]))")
  , ("{ a(x,y) {}, 'blah blah'() {} }", "Right (JSAstExpression (JSObjectLiteral [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock []),JSMethodDefinition (JSIdentifier ''blah blah'') () (JSBlock [])]))")
  , ("{[x]() {}}", "Right (JSAstExpression (JSObjectLiteral [JSMethodDefinition (JSPropertyComputed (JSIdentifier 'x')) () (JSBlock [])]))")
  , ("{*a(x,y) {yield y;}}", "Right (JSAstExpression (JSObjectLiteral [JSGeneratorMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock [JSYieldExpression (JSIdentifier 'y'),JSSemicolon])]))")
  , ("{*[x]({y},...z) {}}", "Right (JSAstExpression (JSObjectLiteral [JSGeneratorMethodDefinition (JSPropertyComputed (JSIdentifier 'x')) (JSObjectLiteral [JSPropertyIdentRef 'y'],JSSpreadExpression (JSIdentifier 'z')) (JSBlock [])]))")
  -- unary expression
  , ("delete y", "Right (JSAstExpression (JSUnaryExpression ('delete',JSIdentifier 'y')))")
  , ("void y", "Right (JSAstExpression (JSUnaryExpression ('void',JSIdentifier 'y')))")
  , ("typeof y", "Right (JSAstExpression (JSUnaryExpression ('typeof',JSIdentifier 'y')))")
  , ("++y", "Right (JSAstExpression (JSUnaryExpression ('++',JSIdentifier 'y')))")
  , ("--y", "Right (JSAstExpression (JSUnaryExpression ('--',JSIdentifier 'y')))")
  , ("+y", "Right (JSAstExpression (JSUnaryExpression ('+',JSIdentifier 'y')))")
  , ("-y", "Right (JSAstExpression (JSUnaryExpression ('-',JSIdentifier 'y')))")
  , ("~y", "Right (JSAstExpression (JSUnaryExpression ('~',JSIdentifier 'y')))")
  , ("!y", "Right (JSAstExpression (JSUnaryExpression ('!',JSIdentifier 'y')))")
  , ("y++", "Right (JSAstExpression (JSExpressionPostfix ('++',JSIdentifier 'y')))")
  , ("y--", "Right (JSAstExpression (JSExpressionPostfix ('--',JSIdentifier 'y')))")
  , ("...y", "Right (JSAstExpression (JSSpreadExpression (JSIdentifier 'y')))")
  -- new expression
  , ("new x()", "Right (JSAstExpression (JSMemberNew (JSIdentifier 'x',JSArguments ())))")
  , ("new x.y", "Right (JSAstExpression (JSNewExpression JSMemberDot (JSIdentifier 'x',JSIdentifier 'y')))")
  -- binary expression
  , ("x||y", "Right (JSAstExpression (JSExpressionBinary ('||',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x&&y", "Right (JSAstExpression (JSExpressionBinary ('&&',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x|y", "Right (JSAstExpression (JSExpressionBinary ('|',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x^y", "Right (JSAstExpression (JSExpressionBinary ('^',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x&y", "Right (JSAstExpression (JSExpressionBinary ('&',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x==y", "Right (JSAstExpression (JSExpressionBinary ('==',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x!=y", "Right (JSAstExpression (JSExpressionBinary ('!=',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x===y", "Right (JSAstExpression (JSExpressionBinary ('===',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x!==y", "Right (JSAstExpression (JSExpressionBinary ('!==',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x<y", "Right (JSAstExpression (JSExpressionBinary ('<',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x>y", "Right (JSAstExpression (JSExpressionBinary ('>',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x<=y", "Right (JSAstExpression (JSExpressionBinary ('<=',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x>=y", "Right (JSAstExpression (JSExpressionBinary ('>=',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x<<y", "Right (JSAstExpression (JSExpressionBinary ('<<',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x>>y", "Right (JSAstExpression (JSExpressionBinary ('>>',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x>>>y", "Right (JSAstExpression (JSExpressionBinary ('>>>',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x+y", "Right (JSAstExpression (JSExpressionBinary ('+',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x-y", "Right (JSAstExpression (JSExpressionBinary ('-',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x*y", "Right (JSAstExpression (JSExpressionBinary ('*',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x/y", "Right (JSAstExpression (JSExpressionBinary ('/',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x%y", "Right (JSAstExpression (JSExpressionBinary ('%',JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x instanceof y", "Right (JSAstExpression (JSExpressionBinary ('instanceof',JSIdentifier 'x',JSIdentifier 'y')))")
  -- assign expression
  , ("x=1", "Right (JSAstExpression (JSOpAssign ('=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x*=1", "Right (JSAstExpression (JSOpAssign ('*=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x/=1", "Right (JSAstExpression (JSOpAssign ('/=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x%=1", "Right (JSAstExpression (JSOpAssign ('%=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x+=1", "Right (JSAstExpression (JSOpAssign ('+=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x-=1", "Right (JSAstExpression (JSOpAssign ('-=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x<<=1", "Right (JSAstExpression (JSOpAssign ('<<=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x>>=1", "Right (JSAstExpression (JSOpAssign ('>>=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x>>>=1", "Right (JSAstExpression (JSOpAssign ('>>>=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x&=1", "Right (JSAstExpression (JSOpAssign ('&=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x^=1", "Right (JSAstExpression (JSOpAssign ('^=',JSIdentifier 'x',JSDecimal '1')))")
  , ("x|=1", "Right (JSAstExpression (JSOpAssign ('|=',JSIdentifier 'x',JSDecimal '1')))")
  -- function expression
  , ("function(){}", "Right (JSAstExpression (JSFunctionExpression '' () (JSBlock [])))")
  , ("function(a){}", "Right (JSAstExpression (JSFunctionExpression '' (JSIdentifier 'a') (JSBlock [])))")
  , ("function(a,b){}", "Right (JSAstExpression (JSFunctionExpression '' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))")
  , ("function(...a){}", "Right (JSAstExpression (JSFunctionExpression '' (JSSpreadExpression (JSIdentifier 'a')) (JSBlock [])))")
  , ("function(a=1){}", "Right (JSAstExpression (JSFunctionExpression '' (JSOpAssign ('=',JSIdentifier 'a',JSDecimal '1')) (JSBlock [])))")
  , ("function([a,b]){}", "Right (JSAstExpression (JSFunctionExpression '' (JSArrayLiteral [JSIdentifier 'a',JSComma,JSIdentifier 'b']) (JSBlock [])))")
  , ("function([a,...b]){}", "Right (JSAstExpression (JSFunctionExpression '' (JSArrayLiteral [JSIdentifier 'a',JSComma,JSSpreadExpression (JSIdentifier 'b')]) (JSBlock [])))")
  , ("function({a,b}){}", "Right (JSAstExpression (JSFunctionExpression '' (JSObjectLiteral [JSPropertyIdentRef 'a',JSPropertyIdentRef 'b']) (JSBlock [])))")
  , ("a => {}", "Right (JSAstExpression (JSArrowExpression (JSIdentifier 'a') => JSStatementBlock []))")
  , ("(a) => { a + 2 }", "Right (JSAstExpression (JSArrowExpression ((JSIdentifier 'a')) => JSStatementBlock [JSExpressionBinary ('+',JSIdentifier 'a',JSDecimal '2')]))")
  , ("(a, b) => {}", "Right (JSAstExpression (JSArrowExpression ((JSIdentifier 'a',JSIdentifier 'b')) => JSStatementBlock []))")
  , ("(a, b) => a + b", "Right (JSAstExpression (JSArrowExpression ((JSIdentifier 'a',JSIdentifier 'b')) => JSExpressionBinary ('+',JSIdentifier 'a',JSIdentifier 'b')))")
  , ("() => { 42 }", "Right (JSAstExpression (JSArrowExpression (()) => JSStatementBlock [JSDecimal '42']))")
  , ("(a, ...b) => b", "Right (JSAstExpression (JSArrowExpression ((JSIdentifier 'a',JSSpreadExpression (JSIdentifier 'b'))) => JSIdentifier 'b'))")
  , ("(a,b=1) => a + b", "Right (JSAstExpression (JSArrowExpression ((JSIdentifier 'a',JSOpAssign ('=',JSIdentifier 'b',JSDecimal '1'))) => JSExpressionBinary ('+',JSIdentifier 'a',JSIdentifier 'b')))")
  , ("([a,b]) => a + b", "Right (JSAstExpression (JSArrowExpression ((JSArrayLiteral [JSIdentifier 'a',JSComma,JSIdentifier 'b'])) => JSExpressionBinary ('+',JSIdentifier 'a',JSIdentifier 'b')))")
  -- generator expression
  , ("function*(){}", "Right (JSAstExpression (JSGeneratorExpression '' () (JSBlock [])))")
  , ("function*(a){}", "Right (JSAstExpression (JSGeneratorExpression '' (JSIdentifier 'a') (JSBlock [])))")
  , ("function*(a,b){}", "Right (JSAstExpression (JSGeneratorExpression '' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))")
  , ("function*(a,...b){}", "Right (JSAstExpression (JSGeneratorExpression '' (JSIdentifier 'a',JSSpreadExpression (JSIdentifier 'b')) (JSBlock [])))")
  , ("function*f(){}", "Right (JSAstExpression (JSGeneratorExpression 'f' () (JSBlock [])))")
  , ("function*f(a){}", "Right (JSAstExpression (JSGeneratorExpression 'f' (JSIdentifier 'a') (JSBlock [])))")
  , ("function*f(a,b){}", "Right (JSAstExpression (JSGeneratorExpression 'f' (JSIdentifier 'a',JSIdentifier 'b') (JSBlock [])))")
  , ("function*f(a,...b){}", "Right (JSAstExpression (JSGeneratorExpression 'f' (JSIdentifier 'a',JSSpreadExpression (JSIdentifier 'b')) (JSBlock [])))")
  -- member expression
  , ("x[y]", "Right (JSAstExpression (JSMemberSquare (JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x[y][z]", "Right (JSAstExpression (JSMemberSquare (JSMemberSquare (JSIdentifier 'x',JSIdentifier 'y'),JSIdentifier 'z')))")
  , ("x.y", "Right (JSAstExpression (JSMemberDot (JSIdentifier 'x',JSIdentifier 'y')))")
  , ("x.y.z", "Right (JSAstExpression (JSMemberDot (JSMemberDot (JSIdentifier 'x',JSIdentifier 'y'),JSIdentifier 'z')))")
  -- call expression
  , ("x()", "Right (JSAstExpression (JSMemberExpression (JSIdentifier 'x',JSArguments ())))")
  , ("x()()", "Right (JSAstExpression (JSCallExpression (JSMemberExpression (JSIdentifier 'x',JSArguments ()),JSArguments ())))")
  , ("x()[4]", "Right (JSAstExpression (JSCallExpressionSquare (JSMemberExpression (JSIdentifier 'x',JSArguments ()),JSDecimal '4')))")
  , ("x().x", "Right (JSAstExpression (JSCallExpressionDot (JSMemberExpression (JSIdentifier 'x',JSArguments ()),JSIdentifier 'x')))")
  , ("x(a,b=2).x", "Right (JSAstExpression (JSCallExpressionDot (JSMemberExpression (JSIdentifier 'x',JSArguments (JSIdentifier 'a',JSOpAssign ('=',JSIdentifier 'b',JSDecimal '2'))),JSIdentifier 'x')))")
  , ("foo (56.8379100, 60.5806664)", "Right (JSAstExpression (JSMemberExpression (JSIdentifier 'foo',JSArguments (JSDecimal '56.83791',JSDecimal '60.5806664'))))")
  -- spread expression
  , ("... x", "Right (JSAstExpression (JSSpreadExpression (JSIdentifier 'x')))")
  -- template literal
  , ("``", "Right (JSAstExpression (JSTemplateLiteral ((),'``',[])))")
  , ("`$`", "Right (JSAstExpression (JSTemplateLiteral ((),'`$`',[])))")
  , ("`$\\n`", "Right (JSAstExpression (JSTemplateLiteral ((),'`$\\n`',[])))")
  , ("`\\${x}`", "Right (JSAstExpression (JSTemplateLiteral ((),'`\\${x}`',[])))")
  , ("`$ {x}`", "Right (JSAstExpression (JSTemplateLiteral ((),'`$ {x}`',[])))")
  , ("`\n\n`", "Right (JSAstExpression (JSTemplateLiteral ((),'`\n\n`',[])))")
  , ("`${x+y} ${z}`", "Right (JSAstExpression (JSTemplateLiteral ((),'`${',[(JSExpressionBinary ('+',JSIdentifier 'x',JSIdentifier 'y'),'} ${'),(JSIdentifier 'z','}`')])))")
  , ("`<${x} ${y}>`", "Right (JSAstExpression (JSTemplateLiteral ((),'`<${',[(JSIdentifier 'x','} ${'),(JSIdentifier 'y','}>`')])))")
  , ("tag `xyz`", "Right (JSAstExpression (JSTemplateLiteral ((JSIdentifier 'tag'),'`xyz`',[])))")
  , ("tag()`xyz`", "Right (JSAstExpression (JSTemplateLiteral ((JSMemberExpression (JSIdentifier 'tag',JSArguments ())),'`xyz`',[])))")
  -- yield
  , ("yield", "Right (JSAstExpression (JSYieldExpression ()))")
  , ("yield a + b", "Right (JSAstExpression (JSYieldExpression (JSExpressionBinary ('+',JSIdentifier 'a',JSIdentifier 'b'))))")
  , ("yield* g()", "Right (JSAstExpression (JSYieldFromExpression (JSMemberExpression (JSIdentifier 'g',JSArguments ()))))")
  -- class expression
  , ("class Foo extends Bar { a(x,y) {} *b() {} }", "Right (JSAstExpression (JSClassExpression 'Foo' (JSIdentifier 'Bar') [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock []),JSGeneratorMethodDefinition (JSIdentifier 'b') () (JSBlock [])]))")
  , ("class { static get [a]() {}; }", "Right (JSAstExpression (JSClassExpression '' () [JSClassStaticMethod (JSPropertyAccessor JSAccessorGet (JSPropertyComputed (JSIdentifier 'a')) () (JSBlock [])),JSClassSemi]))")
  , ("class Foo extends Bar { a(x,y) { super(x); } }", "Right (JSAstExpression (JSClassExpression 'Foo' (JSIdentifier 'Bar') [JSMethodDefinition (JSIdentifier 'a') (JSIdentifier 'x',JSIdentifier 'y') (JSBlock [JSCallExpression (JSLiteral 'super',JSArguments (JSIdentifier 'x')),JSSemicolon])]))")
  ]

def spec : Spec := do
  describe "Parse expressions" do
    let mut seen : Std.HashSet String := {}
    for (input, expected) in expressionCases do
      let rawName := escapeLabel input
      let name := if seen.contains rawName then s!"{rawName} (duplicate)" else rawName
      seen := seen.insert rawName
      it name do
        shouldEqual (testExpr input) expected

end LanguageJavascriptTests.ExpressionParser
