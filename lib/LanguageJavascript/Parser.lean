/-
A recursive descent parser for JavaScript, following the LALR grammar of
`LanguageJavaScript.Parser.Grammar7` (the Happy grammar of the Haskell
package) production by production, and building exactly the same AST.

Entry points (mirroring the Haskell module):

* `parseProgram`    -- a whole script
* `parseModule`     -- a module (with import/export declarations)
* `parseStatement`  -- a single statement
* `parseExpression` -- a single expression
* `parseLiteral`    -- a single literal
* `readJs`, `readJsModule` -- convenience wrappers used by the round trip tests
-/
import LanguageJavascript.AST
import LanguageJavascript.Lexer

namespace LanguageJavaScript.Parser

open LanguageJavaScript.Parser.AST
open LanguageJavaScript.Parser.Lexer

/-- The state of the parser: the lexer state together with a one entry cache
of the token most recently read.

The parser is a backtracking recursive descent parser, so it looks at the
same token several times: once for each alternative it tries, and then again
when it consumes it.  The cache records the token produced at a given
position in a given lexer mode, so that each token is only scanned once.  It
is part of the parser state, hence it is restored together with the position
when an alternative fails, which is exactly what makes it useful for
backtracking. -/
structure PState where
  /-- The lexer state, i.e. the current position in the input. -/
  lex : LexState
  /-- The token last read: its mode, the byte position it starts at, the
  token itself and the lexer state following it. -/
  cache : Option (LexMode × Nat × Token × LexState) := none
deriving Inhabited

/-- The parser monad: the parser state plus the possibility of failure. -/
abbrev P (α : Type) := StateT PState (Except String) α

namespace P

/-- Run a parser, restoring the state if it fails. -/
def attempt {α : Type} [Inhabited α] (p : P α) : P (Option α) := StateT.mk fun s =>
  match p.run s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

/-- Read the token at the current position, using (and filling) the cache. -/
@[inline] def lexCached (mode : LexMode) (s : PState) :
    Except String (Token × LexState × PState) :=
  match s.cache with
  | some (m, start, t, s') =>
      if m == mode && start == s.lex.pos.byteIdx then .ok (t, s', s) else lexFresh
  | none => lexFresh
where
  lexFresh : Except String (Token × LexState × PState) :=
    match lexToken mode s.lex with
    | .error e => .error e
    | .ok (t, s') => .ok (t, s', { s with cache := some (mode, s.lex.pos.byteIdx, t, s') })

/-- Look at the next token without consuming it. -/
def peekTok (mode : LexMode) : P Token := StateT.mk fun s =>
  match lexCached mode s with
  | .error e => .error e
  | .ok (t, _, s') => .ok (t, s')

/-- Consume the next token. -/
def nextTok (mode : LexMode) : P Token := StateT.mk fun s =>
  match lexCached mode s with
  | .error e => .error e
  | .ok (t, after, s') => .ok (t, { s' with lex := after })

/-- Is there a line break between the previous token and the next one? -/
def newlineBefore (mode : LexMode) : P Bool := do
  let s ← get
  let t ← peekTok mode
  return t.span.line > s.lex.line

/-- Fail with a message mentioning the offending token. -/
def parseError {α : Type} (t : Token) : P α := StateT.mk fun _ =>
  .error s!"parse error at line {t.span.line} and column {t.span.column} ({t.kind.name})"

/-- Fail at the current position. -/
def failHere {α : Type} (mode : LexMode) : P α := do
  let t ← peekTok mode
  parseError t

end P

open P

/-- The annotation carried by a token. -/
def mkAnnot (t : Token) : JSAnnot := .JSAnnot t.span t.comment

/-- Token kinds which are `Identifier`s in the grammar. -/
def isIdentifierKind : TokenKind → Bool
  | .IdentifierToken | .AsToken | .GetToken | .SetToken | .FromToken | .YieldToken => true
  | _ => false

/-- The text an `Identifier` token stands for. -/
def identifierText (t : Token) : String :=
  match t.kind with
  | .IdentifierToken => t.text
  | .AsToken => "as"
  | .GetToken => "get"
  | .SetToken => "set"
  | .FromToken => "from"
  | .YieldToken => "yield"
  | _ => t.text

/-- Token kinds which are `IdentifierName`s in the grammar: identifiers and
all keywords except `import`. -/
def identifierNameText? (t : Token) : Option String :=
  if isIdentifierKind t.kind then some (identifierText t)
  else
    match t.kind with
    | .AsyncToken => some "async"
    | .AwaitToken => some "await"
    | .BreakToken => some "break"
    | .CaseToken => some "case"
    | .CatchToken => some "catch"
    | .ClassToken => some "class"
    | .ConstToken => some "const"
    | .ContinueToken => some "continue"
    | .DebuggerToken => some "debugger"
    | .DefaultToken => some "default"
    | .DeleteToken => some "delete"
    | .DoToken => some "do"
    | .ElseToken => some "else"
    | .EnumToken => some "enum"
    | .ExportToken => some "export"
    | .ExtendsToken => some "extends"
    | .FalseToken => some "false"
    | .FinallyToken => some "finally"
    | .ForToken => some "for"
    | .FunctionToken => some "function"
    | .IfToken => some "if"
    | .InToken => some "in"
    | .InstanceofToken => some "instanceof"
    | .LetToken => some "let"
    | .NewToken => some "new"
    | .NullToken => some "null"
    | .OfToken => some "of"
    | .ReturnToken => some "return"
    | .StaticToken => some "static"
    | .SuperToken => some "super"
    | .SwitchToken => some "switch"
    | .ThisToken => some "this"
    | .ThrowToken => some "throw"
    | .TrueToken => some "true"
    | .TryToken => some "try"
    | .TypeofToken => some "typeof"
    | .VarToken => some "var"
    | .VoidToken => some "void"
    | .WhileToken => some "while"
    | .WithToken => some "with"
    | .FutureToken => some t.text
    | _ => none

/-- `identName` of the grammar. -/
def identName : JSExpression → JSIdent
  | .JSIdentifier a s => .JSIdentName a s
  | _ => .JSIdentNone

/-- `propName` of the grammar. -/
def propName : JSExpression → JSPropertyName
  | .JSIdentifier a s => .JSPropertyIdent a s
  | .JSDecimal a s => .JSPropertyNumber a s
  | .JSHexInteger a s => .JSPropertyNumber a s
  | .JSOctal a s => .JSPropertyNumber a s
  | .JSStringLiteral a s => .JSPropertyString a s
  | _ => .JSPropertyIdent .JSNoAnnot ""

/-- `blockToStatement` of the grammar. -/
def blockToStatement : JSBlock → JSSemi → JSStatement
  | .JSBlock a b c, s => .JSStatementBlock a b c s

/-- `expressionToStatement` of the grammar. -/
def expressionToStatement (e : JSExpression) (s : JSSemi) : JSStatement :=
  match e with
  | .JSFunctionExpression a (.JSIdentName ia n) c d f g =>
      .JSFunction a (.JSIdentName ia n) c d f g s
  | .JSGeneratorExpression a b (.JSIdentName ia n) d e f g =>
      .JSGenerator a b (.JSIdentName ia n) d e f g s
  | .JSAssignExpression lhs op rhs => .JSAssignStatement lhs op rhs s
  | .JSMemberExpression e' l a r => .JSMethodCall e' l a r s
  | .JSClassExpression a (.JSIdentName ia n) c d e' f =>
      .JSClass a (.JSIdentName ia n) c d e' f s
  | _ => .JSExpressionStatement e s

/-- `commasToCommaList` of the grammar. -/
def commasToCommaList : JSExpression → JSCommaList JSExpression
  | .JSCommaExpression l c r => .JSLCons (commasToCommaList l) c r
  | x => .JSLOne x

/-- Binary operator precedence, following the grammar's expression levels. -/
def binOpPrec (noIn : Bool) : TokenKind → Option (Nat × (JSAnnot → JSBinOp))
  | .OrToken => some (1, .JSBinOpOr)
  | .AndToken => some (2, .JSBinOpAnd)
  | .BitwiseOrToken => some (3, .JSBinOpBitOr)
  | .BitwiseXorToken => some (4, .JSBinOpBitXor)
  | .BitwiseAndToken => some (5, .JSBinOpBitAnd)
  | .EqToken => some (6, .JSBinOpEq)
  | .NeToken => some (6, .JSBinOpNeq)
  | .StrictEqToken => some (6, .JSBinOpStrictEq)
  | .StrictNeToken => some (6, .JSBinOpStrictNeq)
  | .LtToken => some (7, .JSBinOpLt)
  | .GtToken => some (7, .JSBinOpGt)
  | .LeToken => some (7, .JSBinOpLe)
  | .GeToken => some (7, .JSBinOpGe)
  | .InstanceofToken => some (7, .JSBinOpInstanceOf)
  | .InToken => if noIn then none else some (7, .JSBinOpIn)
  | .LshToken => some (8, .JSBinOpLsh)
  | .RshToken => some (8, .JSBinOpRsh)
  | .UrshToken => some (8, .JSBinOpUrsh)
  | .PlusToken => some (9, .JSBinOpPlus)
  | .MinusToken => some (9, .JSBinOpMinus)
  | .MulToken => some (10, .JSBinOpTimes)
  | .DivToken => some (10, .JSBinOpDivide)
  | .ModToken => some (10, .JSBinOpMod)
  | _ => none

/-- The assignment operators. -/
def assignOp? : TokenKind → Option (JSAnnot → JSAssignOp)
  | .SimpleAssignToken => some .JSAssign
  | .TimesAssignToken => some .JSTimesAssign
  | .DivideAssignToken => some .JSDivideAssign
  | .ModAssignToken => some .JSModAssign
  | .PlusAssignToken => some .JSPlusAssign
  | .MinusAssignToken => some .JSMinusAssign
  | .LshAssignToken => some .JSLshAssign
  | .RshAssignToken => some .JSRshAssign
  | .UrshAssignToken => some .JSUrshAssign
  | .AndAssignToken => some .JSBwAndAssign
  | .XorAssignToken => some .JSBwXorAssign
  | .OrAssignToken => some .JSBwOrAssign
  | _ => none

/-- The unary operators which may precede a unary expression. -/
def unaryOp? : TokenKind → Option (JSAnnot → JSUnaryOp)
  | .DeleteToken => some .JSUnaryOpDelete
  | .VoidToken => some .JSUnaryOpVoid
  | .TypeofToken => some .JSUnaryOpTypeof
  | .IncrementToken => some .JSUnaryOpIncr
  | .DecrementToken => some .JSUnaryOpDecr
  | .PlusToken => some .JSUnaryOpPlus
  | .MinusToken => some .JSUnaryOpMinus
  | .BitwiseNotToken => some .JSUnaryOpTilde
  | .NotToken => some .JSUnaryOpNot
  | _ => none

/-- Expect a token of the given kind. -/
def expect (kind : TokenKind) (mode : LexMode := .div) : P Token := do
  let t ← nextTok mode
  if t.kind == kind then pure t else parseError t

/-- Expect a token of the given kind, returning its annotation. -/
def expectA (kind : TokenKind) (mode : LexMode := .div) : P JSAnnot := do
  let t ← expect kind mode
  return mkAnnot t

/-- Consume the next token if it has the given kind. -/
def accept? (kind : TokenKind) (mode : LexMode := .div) : P (Option Token) := do
  let t ← peekTok mode
  if t.kind == kind then
    let t ← nextTok mode
    return some t
  else return none

/-- An optional semicolon (`MaybeSemi`/`AutoSemi` of the grammar). -/
def maybeSemi : P JSSemi := do
  match ← accept? .SemiColonToken with
  | some t => return .JSSemi (mkAnnot t)
  | none => return .JSSemiAuto

set_option maxHeartbeats 4000000 in
mutual

-- ### Expressions

partial def parsePrimaryExpression : P JSExpression := do
  let t ← nextTok .regex
  let a := mkAnnot t
  match t.kind with
  | .ThisToken => return .JSLiteral a "this"
  | .SuperToken => return .JSLiteral a "super"
  | .NullToken => return .JSLiteral a "null"
  | .TrueToken => return .JSLiteral a "true"
  | .FalseToken => return .JSLiteral a "false"
  | .DecimalToken => return .JSDecimal a t.text
  | .HexIntegerToken => return .JSHexInteger a t.text
  | .OctalToken => return .JSOctal a t.text
  | .StringToken => return .JSStringLiteral a t.text
  | .RegExToken => return .JSRegEx a t.text
  | .NoSubstitutionTemplateToken => return .JSTemplateLiteral none a t.text []
  | .TemplateHeadToken =>
      let parts ← parseTemplateParts
      return .JSTemplateLiteral none a t.text parts
  | .LeftBracketToken => parseArrayLiteral a
  | .LeftCurlyToken => parseObjectLiteral a
  | .ClassToken => parseClassExpression a
  | .FunctionToken => parseFunctionExpression a
  | .LeftParenToken =>
      let e ← parseExpression false
      let rb ← expectA .RightParenToken
      return .JSExpressionParen a e rb
  | _ =>
      if isIdentifierKind t.kind then return .JSIdentifier a (identifierText t)
      else parseError t

/-- The parts of a template literal following the head. -/
partial def parseTemplateParts : P (List JSTemplatePart) := do
  let e ← parseExpression false
  let rb ← expect .RightCurlyToken
  let cont ← nextTok .template
  let part := JSTemplatePart.JSTemplatePart e (mkAnnot rb) ("}" ++ cont.text)
  if cont.kind == .TemplateTailToken then return [part]
  else if cont.kind == .TemplateMiddleToken then
    let rest ← parseTemplateParts
    return part :: rest
  else parseError cont

partial def parseArrayLiteral (lb : JSAnnot) : P JSExpression := do
  let rec go (acc : List JSArrayElement) : P (List JSArrayElement × JSAnnot) := do
    let t ← peekTok .regex
    if t.kind == .RightBracketToken then
      let rb ← nextTok .regex
      return (acc, mkAnnot rb)
    else if t.kind == .CommaToken then
      let c ← nextTok .regex
      go (acc ++ [.JSArrayComma (mkAnnot c)])
    else
      let e ← parseAssignmentExpression false
      go (acc ++ [.JSArrayElement e])
  let (elems, rb) ← go []
  return .JSArrayLiteral lb elems rb

partial def parseObjectLiteral (lb : JSAnnot) : P JSExpression := do
  let t ← peekTok .regex
  if t.kind == .RightCurlyToken then
    let rb ← nextTok .regex
    return .JSObjectLiteral lb (.JSCTLNone .JSLNil) (mkAnnot rb)
  -- Parse the (comma separated, possibly trailing comma) property list.
  let first ← parseObjectProperty
  let rec loop (acc : JSCommaList JSObjectProperty) :
      P (JSCommaTrailingList JSObjectProperty × JSAnnot) := do
    match ← accept? .CommaToken with
    | none =>
        let rb ← expectA .RightCurlyToken
        return (.JSCTLNone acc, rb)
    | some c =>
        let t ← peekTok .regex
        if t.kind == .RightCurlyToken then
          let rb ← nextTok .regex
          return (.JSCTLComma acc (mkAnnot c), mkAnnot rb)
        else
          let p ← parseObjectProperty
          loop (.JSLCons acc (mkAnnot c) p)
  let (props, rb) ← loop (.JSLOne first)
  return .JSObjectLiteral lb props rb

partial def parseObjectProperty : P JSObjectProperty := do
  let t ← peekTok .regex
  if t.kind == .MulToken then
    let m ← parseMethodDefinition
    return .JSObjectMethod m
  if t.kind == .GetToken || t.kind == .SetToken then
    match ← attempt parseMethodDefinition with
    | some m => return .JSObjectMethod m
    | none => pure ()
  let name ← parsePropertyName
  let t2 ← peekTok .div
  if t2.kind == .ColonToken then
    let c ← nextTok .div
    let v ← parseAssignmentExpression false
    return .JSPropertyNameandValue name (mkAnnot c) [v]
  else if t2.kind == .LeftParenToken then
    let m ← parseMethodDefinitionAfterName name
    return .JSObjectMethod m
  else
    match name with
    | .JSPropertyIdent a s => return .JSPropertyIdentRef a s
    | _ => parseError t2

/-- A `PropertyName`: an identifier name, a string, a number or `[expr]`. -/
partial def parsePropertyName : P JSPropertyName := do
  let t ← nextTok .regex
  let a := mkAnnot t
  match t.kind with
  | .StringToken => return .JSPropertyString a t.text
  | .DecimalToken => return .JSPropertyNumber a t.text
  | .HexIntegerToken => return .JSPropertyNumber a t.text
  | .OctalToken => return .JSPropertyNumber a t.text
  | .LeftBracketToken =>
      let e ← parseAssignmentExpression false
      let rb ← expectA .RightBracketToken
      return .JSPropertyComputed a e rb
  | _ =>
      match identifierNameText? t with
      | some s => return .JSPropertyIdent a s
      | none => parseError t

partial def parseMethodDefinition : P JSMethodDefinition := do
  let t ← peekTok .regex
  if t.kind == .MulToken then
    let star ← nextTok .regex
    let name ← parsePropertyName
    let (lb, params, rb, body) ← parseMethodTail
    return .JSGeneratorMethodDefinition (mkAnnot star) name lb params rb body
  else if t.kind == .GetToken || t.kind == .SetToken then
    let kw ← nextTok .regex
    let acc : JSAccessor :=
      if kw.kind == .GetToken then .JSAccessorGet (mkAnnot kw) else .JSAccessorSet (mkAnnot kw)
    let name ← parsePropertyName
    let (lb, params, rb, body) ← parseMethodTail
    return .JSPropertyAccessor acc name lb params rb body
  else
    let name ← parsePropertyName
    parseMethodDefinitionAfterName name

partial def parseMethodDefinitionAfterName (name : JSPropertyName) : P JSMethodDefinition := do
  let (lb, params, rb, body) ← parseMethodTail
  return .JSMethodDefinition name lb params rb body

/-- `( FormalParameterList? ) FunctionBody` -/
partial def parseMethodTail : P (JSAnnot × JSCommaList JSExpression × JSAnnot × JSBlock) := do
  let lb ← expectA .LeftParenToken
  let params ← parseFormalParameterList
  let rb ← expectA .RightParenToken
  let body ← parseBlock
  return (lb, params, rb, body)

/-- A possibly empty, comma separated list of parameters, up to (not
including) the closing parenthesis. -/
partial def parseFormalParameterList : P (JSCommaList JSExpression) := do
  let t ← peekTok .regex
  if t.kind == .RightParenToken then return .JSLNil
  let first ← parseAssignmentExpression false
  let rec loop (acc : JSCommaList JSExpression) : P (JSCommaList JSExpression) := do
    match ← accept? .CommaToken with
    | none => return acc
    | some c =>
        let e ← parseAssignmentExpression false
        loop (.JSLCons acc (mkAnnot c) e)
  loop (.JSLOne first)

partial def parseArguments : P (JSAnnot × JSCommaList JSExpression × JSAnnot) := do
  let lb ← expectA .LeftParenToken
  let args ← parseFormalParameterList
  let rb ← expectA .RightParenToken
  return (lb, args, rb)

/-- `function` (already consumed) followed by an optional `*`, an optional
name, the parameters and the body. -/
partial def parseFunctionExpression (fnA : JSAnnot) : P JSExpression := do
  match ← accept? .MulToken with
  | some star =>
      let name ← parseOptionalIdent
      let lb ← expectA .LeftParenToken
      let params ← parseFormalParameterList
      let rb ← expectA .RightParenToken
      let body ← parseBlock
      return .JSGeneratorExpression fnA (mkAnnot star) name lb params rb body
  | none =>
      let name ← parseOptionalIdent
      let lb ← expectA .LeftParenToken
      let params ← parseFormalParameterList
      let rb ← expectA .RightParenToken
      let body ← parseBlock
      return .JSFunctionExpression fnA name lb params rb body

partial def parseOptionalIdent : P JSIdent := do
  let t ← peekTok .div
  if isIdentifierKind t.kind then
    let t ← nextTok .div
    return .JSIdentName (mkAnnot t) (identifierText t)
  else return .JSIdentNone

/-- `class` (already consumed): an optional name, an optional heritage and
the class body. -/
partial def parseClassExpression (classA : JSAnnot) : P JSExpression := do
  let name ← parseOptionalIdent
  let heritage ← parseClassHeritage
  let lb ← expectA .LeftCurlyToken
  let body ← parseClassBody
  let rb ← expectA .RightCurlyToken
  return .JSClassExpression classA name heritage lb body rb

partial def parseClassHeritage : P JSClassHeritage := do
  match ← accept? .ExtendsToken with
  | none => return .JSExtendsNone
  | some t =>
      let e ← parseLeftHandSideExpression
      return .JSExtends (mkAnnot t) e

partial def parseClassBody : P (List JSClassElement) := do
  let rec go (acc : List JSClassElement) : P (List JSClassElement) := do
    let t ← peekTok .regex
    if t.kind == .RightCurlyToken then return acc
    else if t.kind == .SemiColonToken then
      let s ← nextTok .regex
      go (acc ++ [.JSClassSemi (mkAnnot s)])
    else if t.kind == .StaticToken then
      let s ← nextTok .regex
      let m ← parseMethodDefinition
      go (acc ++ [.JSClassStaticMethod (mkAnnot s) m])
    else
      let m ← parseMethodDefinition
      go (acc ++ [.JSClassInstanceMethod m])
  go []

/-- `MemberExpression`/`CallExpression`/`NewExpression`. -/
partial def parseLeftHandSideExpression : P JSExpression := do
  let t ← peekTok .regex
  if t.kind == .NewToken then
    let n ← nextTok .regex
    let target ← parseMemberOnly
    let t2 ← peekTok .div
    if t2.kind == .LeftParenToken then
      let (lb, args, rb) ← parseArguments
      parseCallTail (.JSMemberNew (mkAnnot n) target lb args rb) true
    else
      return .JSNewExpression (mkAnnot n) target
  else if t.kind == .AwaitToken then
    let a ← nextTok .regex
    let e ← parseExpression false
    return .JSAwaitExpression (mkAnnot a) e
  else
    let isSuper := t.kind == .SuperToken
    let e ← parsePrimaryExpression
    -- `super` followed by arguments is a call; `super[x]`/`super.x` are
    -- member expressions.
    let startCall ←
      if isSuper then (do let t2 ← peekTok .div; pure (t2.kind == .LeftParenToken))
      else pure false
    parseCallTail e startCall

/-- A `MemberExpression` without any call suffixes (used for `new`). -/
partial def parseMemberOnly : P JSExpression := do
  let t ← peekTok .regex
  if t.kind == .NewToken then
    let n ← nextTok .regex
    let target ← parseMemberOnly
    let t2 ← peekTok .div
    if t2.kind == .LeftParenToken then
      let (lb, args, rb) ← parseArguments
      return .JSMemberNew (mkAnnot n) target lb args rb
    else
      return .JSNewExpression (mkAnnot n) target
  else
    let e ← parsePrimaryExpression
    parseMemberTail e

/-- `[ expr ]`, `.name` and tagged template suffixes, but no calls. -/
partial def parseMemberTail (e : JSExpression) : P JSExpression := do
  let t ← peekTok .div
  match t.kind with
  | .LeftBracketToken =>
      let lb ← nextTok .div
      let idx ← parseExpression false
      let rb ← expectA .RightBracketToken
      parseMemberTail (.JSMemberSquare e (mkAnnot lb) idx rb)
  | .DotToken =>
      let d ← nextTok .div
      let n ← parseIdentifierNameExpr
      parseMemberTail (.JSMemberDot e (mkAnnot d) n)
  | .NoSubstitutionTemplateToken =>
      let tok ← nextTok .div
      parseMemberTail (.JSTemplateLiteral (some e) (mkAnnot tok) tok.text [])
  | .TemplateHeadToken =>
      let tok ← nextTok .div
      let parts ← parseTemplateParts
      parseMemberTail (.JSTemplateLiteral (some e) (mkAnnot tok) tok.text parts)
  | _ => return e

/-- All the `MemberExpression`/`CallExpression` suffixes. -/
partial def parseCallTail (e : JSExpression) (isCall : Bool) : P JSExpression := do
  let t ← peekTok .div
  match t.kind with
  | .LeftParenToken =>
      let (lb, args, rb) ← parseArguments
      let e' :=
        if isCall then JSExpression.JSCallExpression e lb args rb
        else JSExpression.JSMemberExpression e lb args rb
      parseCallTail e' true
  | .LeftBracketToken =>
      let lb ← nextTok .div
      let idx ← parseExpression false
      let rb ← expectA .RightBracketToken
      let e' :=
        if isCall then JSExpression.JSCallExpressionSquare e (mkAnnot lb) idx rb
        else JSExpression.JSMemberSquare e (mkAnnot lb) idx rb
      parseCallTail e' isCall
  | .DotToken =>
      let d ← nextTok .div
      let n ← parseIdentifierNameExpr
      let e' :=
        if isCall then JSExpression.JSCallExpressionDot e (mkAnnot d) n
        else JSExpression.JSMemberDot e (mkAnnot d) n
      parseCallTail e' isCall
  | .NoSubstitutionTemplateToken =>
      let tok ← nextTok .div
      parseCallTail (.JSTemplateLiteral (some e) (mkAnnot tok) tok.text []) isCall
  | .TemplateHeadToken =>
      let tok ← nextTok .div
      let parts ← parseTemplateParts
      parseCallTail (.JSTemplateLiteral (some e) (mkAnnot tok) tok.text parts) isCall
  | _ => return e

partial def parseIdentifierNameExpr : P JSExpression := do
  let t ← nextTok .div
  match identifierNameText? t with
  | some s => return .JSIdentifier (mkAnnot t) s
  | none => parseError t

partial def parsePostfixExpression : P JSExpression := do
  let e ← parseLeftHandSideExpression
  let rec go (e : JSExpression) : P JSExpression := do
    let t ← peekTok .div
    if t.kind == .IncrementToken then
      let t ← nextTok .div
      go (.JSExpressionPostfix e (.JSUnaryOpIncr (mkAnnot t)))
    else if t.kind == .DecrementToken then
      let t ← nextTok .div
      go (.JSExpressionPostfix e (.JSUnaryOpDecr (mkAnnot t)))
    else return e
  go e

partial def parseUnaryExpression : P JSExpression := do
  let t ← peekTok .regex
  match unaryOp? t.kind with
  | some mk =>
      let t ← nextTok .regex
      let e ← parseUnaryExpression
      return .JSUnaryExpression (mk (mkAnnot t)) e
  | none => parsePostfixExpression

/-- Binary operators, by precedence climbing. -/
partial def parseBinaryExpression (minPrec : Nat) (noIn : Bool) : P JSExpression := do
  let lhs ← parseUnaryExpression
  let rec go (lhs : JSExpression) : P JSExpression := do
    let t ← peekTok .div
    match binOpPrec noIn t.kind with
    | some (prec, mk) =>
        if prec ≥ minPrec then
          let t ← nextTok .div
          let rhs ← parseBinaryExpression (prec + 1) noIn
          go (.JSExpressionBinary lhs (mk (mkAnnot t)) rhs)
        else return lhs
    | none => return lhs
  go lhs

partial def parseConditionalExpression (noIn : Bool) : P JSExpression := do
  let c ← parseBinaryExpression 1 noIn
  match ← accept? .HookToken with
  | none => return c
  | some h =>
      let t ← parseAssignmentExpression noIn
      let colon ← expectA .ColonToken
      let f ← parseAssignmentExpression noIn
      return .JSExpressionTernary c (mkAnnot h) t colon f

partial def parseAssignmentExpression (noIn : Bool) : P JSExpression := do
  let t ← peekTok .regex
  if t.kind == .YieldToken then
    -- `yield` is a keyword here; as an identifier it is handled by the
    -- productions which explicitly ask for an `Identifier`.
    let y ← nextTok .regex
    match ← accept? .MulToken with
    | some star =>
        let e ← parseAssignmentExpression noIn
        return .JSYieldFromExpression (mkAnnot y) (mkAnnot star) e
    | none =>
        match ← attempt (parseAssignmentExpression noIn) with
        | some e => return .JSYieldExpression (mkAnnot y) (some e)
        | none => return .JSYieldExpression (mkAnnot y) none
  if t.kind == .SpreadToken then
    let s ← nextTok .regex
    let e ← parseAssignmentExpression noIn
    return .JSSpreadExpression (mkAnnot s) e
  -- `() => ...`
  if t.kind == .LeftParenToken then
    match ← attempt parseEmptyArrow with
    | some e => return e
    | none => pure ()
  let lhs ← parseConditionalExpression noIn
  let t2 ← peekTok .div
  if t2.kind == .ArrowToken then
    let arrow ← nextTok .div
    let params ← toArrowParameterList lhs
    let body ← parseStatementOrBlock
    return .JSArrowExpression params (mkAnnot arrow) body
  match assignOp? t2.kind with
  | some mk =>
      let op ← nextTok .div
      let rhs ← parseAssignmentExpression noIn
      return .JSAssignExpression lhs (mk (mkAnnot op)) rhs
  | none => return lhs

/-- `( ) => ...` -/
partial def parseEmptyArrow : P JSExpression := do
  let lb ← expectA .LeftParenToken
  let rb ← expectA .RightParenToken
  let arrow ← expect .ArrowToken
  let body ← parseStatementOrBlock
  return .JSArrowExpression (.JSParenthesizedArrowParameterList lb .JSLNil rb)
    (mkAnnot arrow) body

partial def toArrowParameterList : JSExpression → P JSArrowParameterList
  | .JSIdentifier a s => return .JSUnparenthesizedArrowParameter (.JSIdentName a s)
  | .JSExpressionParen lb x rb =>
      return .JSParenthesizedArrowParameterList lb (commasToCommaList x) rb
  | _ => failHere .div

partial def parseStatementOrBlock : P JSStatement := do
  let t ← peekTok .regex
  if t.kind == .LeftCurlyToken then
    let b ← parseBlock
    let s ← maybeSemi
    return blockToStatement b s
  else
    let e ← parseExpression false
    let s ← maybeSemi
    return expressionToStatement e s

partial def parseExpression (noIn : Bool) : P JSExpression := do
  let e ← parseAssignmentExpression noIn
  let rec go (e : JSExpression) : P JSExpression := do
    match ← accept? .CommaToken with
    | none => return e
    | some c =>
        let r ← parseAssignmentExpression noIn
        go (.JSCommaExpression e (mkAnnot c) r)
  go e

-- ### Statements

partial def parseBlock : P JSBlock := do
  let lb ← expectA .LeftCurlyToken
  let stmts ← parseStatementList
  let rb ← expectA .RightCurlyToken
  return .JSBlock lb stmts rb

/-- Statements up to (not including) a `}` or the end of the input. -/
partial def parseStatementList : P (List JSStatement) := do
  let rec go (acc : List JSStatement) : P (List JSStatement) := do
    let t ← peekTok .regex
    if t.kind == .RightCurlyToken || t.kind == .TailToken then return acc
    let s ← parseStatement
    go (acc ++ [s])
  go []

partial def parseVarDeclaration (noIn : Bool) : P JSExpression := do
  let t ← peekTok .regex
  if isIdentifierKind t.kind then
    let t ← nextTok .regex
    let ident := JSExpression.JSIdentifier (mkAnnot t) (identifierText t)
    match ← accept? .SimpleAssignToken with
    | none => return .JSVarInitExpression ident .JSVarInitNone
    | some eq =>
        let e ← parseAssignmentExpression noIn
        return .JSVarInitExpression ident (.JSVarInit (mkAnnot eq) e)
  else
    -- Destructuring patterns are parsed as primary expressions.
    let p ← parsePrimaryExpression
    let eq ← expect .SimpleAssignToken
    let e ← parseAssignmentExpression noIn
    return .JSVarInitExpression p (.JSVarInit (mkAnnot eq) e)

partial def parseVarDeclarationList (noIn : Bool) : P (JSCommaList JSExpression) := do
  let first ← parseVarDeclaration noIn
  let rec loop (acc : JSCommaList JSExpression) : P (JSCommaList JSExpression) := do
    match ← accept? .CommaToken with
    | none => return acc
    | some c =>
        let d ← parseVarDeclaration noIn
        loop (.JSLCons acc (mkAnnot c) d)
  loop (.JSLOne first)

/-- The three `var`-like statements. -/
partial def parseVariableStatement : P JSStatement := do
  let kw ← nextTok .regex
  let decls ← parseVarDeclarationList false
  let s ← maybeSemi
  let a := mkAnnot kw
  match kw.kind with
  | .VarToken => return .JSVariable a decls s
  | .LetToken => return .JSLet a decls s
  | _ => return .JSConstant a decls s

partial def parseCaseBlock : P (List JSSwitchParts) := do
  let rec go (acc : List JSSwitchParts) : P (List JSSwitchParts) := do
    let t ← peekTok .regex
    if t.kind == .CaseToken then
      let c ← nextTok .regex
      let e ← parseExpression false
      let colon ← expectA .ColonToken
      let stmts ← parseCaseStatementList
      go (acc ++ [.JSCase (mkAnnot c) e colon stmts])
    else if t.kind == .DefaultToken then
      let d ← nextTok .regex
      let colon ← expectA .ColonToken
      let stmts ← parseCaseStatementList
      go (acc ++ [.JSDefault (mkAnnot d) colon stmts])
    else return acc
  go []

/-- Statements of a `case`/`default` clause. -/
partial def parseCaseStatementList : P (List JSStatement) := do
  let rec go (acc : List JSStatement) : P (List JSStatement) := do
    let t ← peekTok .regex
    if t.kind == .RightCurlyToken || t.kind == .TailToken || t.kind == .CaseToken
        || t.kind == .DefaultToken then return acc
    let s ← parseStatement
    go (acc ++ [s])
  go []

partial def parseForStatement (forA : JSAnnot) : P JSStatement := do
  let lb ← expectA .LeftParenToken
  let t ← peekTok .regex
  if t.kind == .VarToken || t.kind == .LetToken || t.kind == .ConstToken then
    let kw ← nextTok .regex
    let kwA := mkAnnot kw
    let first ← parseVarDeclaration true
    let t2 ← peekTok .div
    if t2.kind == .InToken || t2.kind == .OfToken then
      let op ← nextTok .div
      let opB : JSBinOp :=
        if op.kind == .InToken then .JSBinOpIn (mkAnnot op) else .JSBinOpOf (mkAnnot op)
      let rhs ← parseExpression false
      let rb ← expectA .RightParenToken
      let body ← parseStatement
      match kw.kind, op.kind with
      | .VarToken, .InToken => return .JSForVarIn forA lb kwA first opB rhs rb body
      | .VarToken, _ => return .JSForVarOf forA lb kwA first opB rhs rb body
      | .LetToken, .InToken => return .JSForLetIn forA lb kwA first opB rhs rb body
      | .LetToken, _ => return .JSForLetOf forA lb kwA first opB rhs rb body
      | _, .InToken => return .JSForConstIn forA lb kwA first opB rhs rb body
      | _, _ => return .JSForConstOf forA lb kwA first opB rhs rb body
    else
      let rec loop (acc : JSCommaList JSExpression) : P (JSCommaList JSExpression) := do
        match ← accept? .CommaToken with
        | none => return acc
        | some c =>
            let d ← parseVarDeclaration true
            loop (.JSLCons acc (mkAnnot c) d)
      let decls ← loop (.JSLOne first)
      let s1 ← expectA .SemiColonToken
      let cond ← parseExpressionOpt
      let s2 ← expectA .SemiColonToken
      let step ← parseExpressionOpt
      let rb ← expectA .RightParenToken
      let body ← parseStatement
      match kw.kind with
      | .VarToken => return .JSForVar forA lb kwA decls s1 cond s2 step rb body
      | .LetToken => return .JSForLet forA lb kwA decls s1 cond s2 step rb body
      | _ => return .JSForConst forA lb kwA decls s1 cond s2 step rb body
  else if t.kind == .SemiColonToken then
    let s1 ← expectA .SemiColonToken
    let cond ← parseExpressionOpt
    let s2 ← expectA .SemiColonToken
    let step ← parseExpressionOpt
    let rb ← expectA .RightParenToken
    let body ← parseStatement
    return .JSFor forA lb .JSLNil s1 cond s2 step rb body
  else
    let e ← parseExpression true
    let t2 ← peekTok .div
    if t2.kind == .InToken || t2.kind == .OfToken then
      let op ← nextTok .div
      let opB : JSBinOp :=
        if op.kind == .InToken then .JSBinOpIn (mkAnnot op) else .JSBinOpOf (mkAnnot op)
      let rhs ← parseExpression false
      let rb ← expectA .RightParenToken
      let body ← parseStatement
      if op.kind == .InToken then return .JSForIn forA lb e opB rhs rb body
      else return .JSForOf forA lb e opB rhs rb body
    else
      let s1 ← expectA .SemiColonToken
      let cond ← parseExpressionOpt
      let s2 ← expectA .SemiColonToken
      let step ← parseExpressionOpt
      let rb ← expectA .RightParenToken
      let body ← parseStatement
      return .JSFor forA lb (.JSLOne e) s1 cond s2 step rb body

/-- An optional expression, as a comma list with zero or one element. -/
partial def parseExpressionOpt : P (JSCommaList JSExpression) := do
  let t ← peekTok .regex
  if t.kind == .SemiColonToken || t.kind == .RightParenToken then return .JSLNil
  let e ← parseExpression false
  return .JSLOne e

partial def parseTryStatement (tryA : JSAnnot) : P JSStatement := do
  let blk ← parseBlock
  let rec catches (acc : List JSTryCatch) : P (List JSTryCatch) := do
    let t ← peekTok .regex
    if t.kind == .CatchToken then
      let c ← nextTok .regex
      let lb ← expectA .LeftParenToken
      let identTok ← nextTok .regex
      if !isIdentifierKind identTok.kind then parseError identTok
      let ident := JSExpression.JSIdentifier (mkAnnot identTok) (identifierText identTok)
      let t2 ← peekTok .div
      if t2.kind == .IfToken then
        let ifTok ← nextTok .div
        let cond ← parseConditionalExpression false
        let rb ← expectA .RightParenToken
        let body ← parseBlock
        catches (acc ++ [.JSCatchIf (mkAnnot c) lb ident (mkAnnot ifTok) cond rb body])
      else
        let rb ← expectA .RightParenToken
        let body ← parseBlock
        catches (acc ++ [.JSCatch (mkAnnot c) lb ident rb body])
    else return acc
  let cs ← catches []
  let t ← peekTok .regex
  if t.kind == .FinallyToken then
    let f ← nextTok .regex
    let blk2 ← parseBlock
    return .JSTry tryA blk cs (.JSFinally (mkAnnot f) blk2)
  else
    return .JSTry tryA blk cs .JSNoFinally

partial def parseStatement : P JSStatement := do
  let t ← peekTok .regex
  match t.kind with
  | .SemiColonToken =>
      let s ← nextTok .regex
      return .JSEmptyStatement (mkAnnot s)
  | .LeftCurlyToken =>
      -- `{ ... }` is a block if it parses as one, and an object literal
      -- otherwise; the LALR grammar resolves the same ambiguity by rule
      -- ordering.
      match ← attempt parseBlockStatement with
      | some st => return st
      | none => parseExpressionStatement
  | .VarToken | .LetToken | .ConstToken => parseVariableStatement
  | .IfToken =>
      let i ← nextTok .regex
      let lb ← expectA .LeftParenToken
      let cond ← parseExpression false
      let rb ← expectA .RightParenToken
      let thenS ← parseStatement
      let t2 ← peekTok .regex
      if t2.kind == .ElseToken then
        let e ← nextTok .regex
        let elseS ← parseStatement
        return .JSIfElse (mkAnnot i) lb cond rb thenS (mkAnnot e) elseS
      else
        return .JSIf (mkAnnot i) lb cond rb thenS
  | .DoToken =>
      let d ← nextTok .regex
      let body ← parseStatement
      let w ← expect .WhileToken
      let lb ← expectA .LeftParenToken
      let cond ← parseExpression false
      let rb ← expectA .RightParenToken
      let s ← maybeSemi
      return .JSDoWhile (mkAnnot d) body (mkAnnot w) lb cond rb s
  | .WhileToken =>
      let w ← nextTok .regex
      let lb ← expectA .LeftParenToken
      let cond ← parseExpression false
      let rb ← expectA .RightParenToken
      let body ← parseStatement
      return .JSWhile (mkAnnot w) lb cond rb body
  | .ForToken =>
      let f ← nextTok .regex
      parseForStatement (mkAnnot f)
  | .ContinueToken | .BreakToken =>
      let kw ← nextTok .regex
      let nl ← newlineBefore .div
      let t2 ← peekTok .div
      if !nl && isIdentifierKind t2.kind then
        let i ← nextTok .div
        let s ← maybeSemi
        let ident := JSIdent.JSIdentName (mkAnnot i) (identifierText i)
        if kw.kind == .BreakToken then return .JSBreak (mkAnnot kw) ident s
        else return .JSContinue (mkAnnot kw) ident s
      else
        let s ← maybeSemi
        if kw.kind == .BreakToken then return .JSBreak (mkAnnot kw) .JSIdentNone s
        else return .JSContinue (mkAnnot kw) .JSIdentNone s
  | .ReturnToken =>
      let kw ← nextTok .regex
      let nl ← newlineBefore .regex
      let t2 ← peekTok .regex
      if nl || t2.kind == .SemiColonToken || t2.kind == .RightCurlyToken
          || t2.kind == .TailToken then
        let s ← maybeSemi
        return .JSReturn (mkAnnot kw) none s
      else
        let e ← parseExpression false
        let s ← maybeSemi
        return .JSReturn (mkAnnot kw) (some e) s
  | .WithToken =>
      let w ← nextTok .regex
      let lb ← expectA .LeftParenToken
      let e ← parseExpression false
      let rb ← expectA .RightParenToken
      let body ← parseStatement
      let s ← maybeSemi
      return .JSWith (mkAnnot w) lb e rb body s
  | .SwitchToken =>
      let sw ← nextTok .regex
      let lp ← expectA .LeftParenToken
      let e ← parseExpression false
      let rp ← expectA .RightParenToken
      let lb ← expectA .LeftCurlyToken
      let parts ← parseCaseBlock
      let rb ← expectA .RightCurlyToken
      let s ← maybeSemi
      return .JSSwitch (mkAnnot sw) lp e rp lb parts rb s
  | .ThrowToken =>
      let th ← nextTok .regex
      let e ← parseExpression false
      let s ← maybeSemi
      return .JSThrow (mkAnnot th) e s
  | .TryToken =>
      let tr ← nextTok .regex
      parseTryStatement (mkAnnot tr)
  | .DebuggerToken =>
      let d ← nextTok .regex
      let s ← maybeSemi
      return .JSExpressionStatement (.JSLiteral (mkAnnot d) "debugger") s
  | .AsyncToken =>
      match ← attempt parseAsyncFunctionStatement with
      | some st => return st
      | none => parseExpressionStatement
  | _ =>
      -- A labelled statement?
      if isIdentifierKind t.kind then
        match ← attempt parseLabelledStatement with
        | some st => return st
        | none => parseExpressionStatement
      else parseExpressionStatement

partial def parseBlockStatement : P JSStatement := do
  let b ← parseBlock
  let s ← maybeSemi
  return blockToStatement b s

partial def parseLabelledStatement : P JSStatement := do
  let i ← nextTok .regex
  if !isIdentifierKind i.kind then parseError i
  let colon ← expect .ColonToken
  let body ← parseStatement
  return .JSLabelled (.JSIdentName (mkAnnot i) (identifierText i)) (mkAnnot colon) body

partial def parseAsyncFunctionStatement : P JSStatement := do
  let a ← expect .AsyncToken .regex
  let f ← expect .FunctionToken .regex
  let e ← parseFunctionExpression (mkAnnot f)
  let s ← maybeSemi
  match e with
  | .JSFunctionExpression fa (.JSIdentName ia n) lb ps rb blk =>
      return .JSAsyncFunction (mkAnnot a) fa (.JSIdentName ia n) lb ps rb blk s
  | _ => failHere .div

partial def parseExpressionStatement : P JSStatement := do
  let e ← parseExpression false
  let s ← maybeSemi
  return expressionToStatement e s

-- ### Modules

partial def parseModuleItem : P JSModuleItem := do
  let t ← peekTok .regex
  if t.kind == .ImportToken then
    let i ← nextTok .regex
    let d ← parseImportDeclaration
    return .JSModuleImportDeclaration (mkAnnot i) d
  else if t.kind == .ExportToken then
    let e ← nextTok .regex
    let d ← parseExportDeclaration
    return .JSModuleExportDeclaration (mkAnnot e) d
  else
    let s ← parseStatement
    return .JSModuleStatementListItem s

partial def parseImportDeclaration : P JSImportDeclaration := do
  let t ← peekTok .regex
  if t.kind == .StringToken then
    let str ← nextTok .regex
    let s ← maybeSemi
    return .JSImportDeclarationBare (mkAnnot str) str.text s
  let clause ← parseImportClause
  let from_ ← parseFromClause
  let s ← maybeSemi
  return .JSImportDeclaration clause from_ s

partial def parseImportClause : P JSImportClause := do
  let t ← peekTok .regex
  if t.kind == .MulToken then
    let ns ← parseNameSpaceImport
    return .JSImportClauseNameSpace ns
  else if t.kind == .LeftCurlyToken then
    let named ← parseNamedImports
    return .JSImportClauseNamed named
  else
    let n ← parseIdentifierNameIdent
    match ← accept? .CommaToken with
    | none => return .JSImportClauseDefault n
    | some c =>
        let t2 ← peekTok .regex
        if t2.kind == .MulToken then
          let ns ← parseNameSpaceImport
          return .JSImportClauseDefaultNameSpace n (mkAnnot c) ns
        else
          let named ← parseNamedImports
          return .JSImportClauseDefaultNamed n (mkAnnot c) named

partial def parseIdentifierNameIdent : P JSIdent := do
  let e ← parseIdentifierNameExprRegex
  return identName e

partial def parseIdentifierNameExprRegex : P JSExpression := do
  let t ← nextTok .regex
  match identifierNameText? t with
  | some s => return .JSIdentifier (mkAnnot t) s
  | none => parseError t

partial def parseNameSpaceImport : P JSImportNameSpace := do
  let star ← expect .MulToken .regex
  let as ← expect .AsToken
  let n ← parseIdentifierNameIdent
  return .JSImportNameSpace (.JSBinOpTimes (mkAnnot star)) (mkAnnot as) n

partial def parseNamedImports : P JSImportsNamed := do
  let lb ← expectA .LeftCurlyToken
  let t ← peekTok .regex
  if t.kind == .RightCurlyToken then
    let rb ← nextTok .regex
    return .JSImportsNamed lb .JSLNil (mkAnnot rb)
  let first ← parseImportSpecifier
  let rec loop (acc : JSCommaList JSImportSpecifier) :
      P (JSCommaList JSImportSpecifier × JSAnnot) := do
    match ← accept? .CommaToken with
    | none =>
        let rb ← expectA .RightCurlyToken
        return (acc, rb)
    | some c =>
        let s ← parseImportSpecifier
        loop (.JSLCons acc (mkAnnot c) s)
  let (specs, rb) ← loop (.JSLOne first)
  return .JSImportsNamed lb specs rb

partial def parseImportSpecifier : P JSImportSpecifier := do
  let n ← parseIdentifierNameIdent
  let t ← peekTok .div
  if t.kind == .AsToken then
    let as ← nextTok .div
    let n2 ← parseIdentifierNameIdent
    return .JSImportSpecifierAs n (mkAnnot as) n2
  else return .JSImportSpecifier n

partial def parseFromClause : P JSFromClause := do
  let f ← expect .FromToken .regex
  let str ← expect .StringToken .regex
  return .JSFromClause (mkAnnot f) (mkAnnot str) str.text

partial def parseExportDeclaration : P JSExportDeclaration := do
  let t ← peekTok .regex
  if t.kind == .LeftCurlyToken then
    let clause ← parseExportClause
    let t2 ← peekTok .regex
    if t2.kind == .FromToken then
      let from_ ← parseFromClause
      let s ← maybeSemi
      return .JSExportFrom clause from_ s
    else
      let s ← maybeSemi
      return .JSExportLocals clause s
  else
    let st ← parseStatement
    let s ← maybeSemi
    return .JSExport st s

partial def parseExportClause : P JSExportClause := do
  let lb ← expectA .LeftCurlyToken
  let t ← peekTok .regex
  if t.kind == .RightCurlyToken then
    let rb ← nextTok .regex
    return .JSExportClause lb .JSLNil (mkAnnot rb)
  let first ← parseExportSpecifier
  let rec loop (acc : JSCommaList JSExportSpecifier) :
      P (JSCommaList JSExportSpecifier × JSAnnot) := do
    match ← accept? .CommaToken with
    | none =>
        let rb ← expectA .RightCurlyToken
        return (acc, rb)
    | some c =>
        let s ← parseExportSpecifier
        loop (.JSLCons acc (mkAnnot c) s)
  let (specs, rb) ← loop (.JSLOne first)
  return .JSExportClause lb specs rb

partial def parseExportSpecifier : P JSExportSpecifier := do
  let n ← parseIdentifierNameIdent
  let t ← peekTok .div
  if t.kind == .AsToken then
    let as ← nextTok .div
    let n2 ← parseIdentifierNameIdent
    return .JSExportSpecifierAs n (mkAnnot as) n2
  else return .JSExportSpecifier n

partial def parseModuleItemList : P (List JSModuleItem) := do
  let rec go (acc : List JSModuleItem) : P (List JSModuleItem) := do
    let t ← peekTok .regex
    if t.kind == .TailToken then return acc
    let i ← parseModuleItem
    go (acc ++ [i])
  go []

end

/-- The `tail` token, which carries the trailing whitespace and comments. -/
def parseTail : P JSAnnot := do
  let t ← peekTok .regex
  if t.kind == .TailToken then
    let t ← nextTok .regex
    return mkAnnot t
  else parseError t

/-- Run a parser on a string. -/
def runParser {α : Type} (p : P α) (input : String) : Except String α :=
  match p.run { lex := LexState.ofString input } with
  | .error e => .error e
  | .ok (a, _) => .ok a

/-- Parse a whole program. -/
def parseProgram (input : String) : Except String JSAST :=
  runParser (do
    let stmts ← parseStatementList
    let a ← parseTail
    return JSAST.JSAstProgram stmts a) input

/-- Parse a module. -/
def parseModule (input : String) : Except String JSAST :=
  runParser (do
    let items ← parseModuleItemList
    let a ← parseTail
    return JSAST.JSAstModule items a) input

/-- Parse a single statement. -/
def parseStatementAST (input : String) : Except String JSAST :=
  runParser (do
    let s ← parseStatement
    let a ← parseTail
    return JSAST.JSAstStatement s a) input

/-- Parse a single expression. -/
def parseExpressionAST (input : String) : Except String JSAST :=
  runParser (do
    let e ← parseExpression false
    let a ← parseTail
    return JSAST.JSAstExpression e a) input

/-- Parse a single literal. -/
def parseLiteralAST (input : String) : Except String JSAST :=
  runParser (do
    let t ← nextTok .regex
    let a := mkAnnot t
    let e : JSExpression ←
      match t.kind with
      | .NullToken => pure (.JSLiteral a "null")
      | .TrueToken => pure (.JSLiteral a "true")
      | .FalseToken => pure (.JSLiteral a "false")
      | .DecimalToken => pure (.JSDecimal a t.text)
      | .HexIntegerToken => pure (.JSHexInteger a t.text)
      | .OctalToken => pure (.JSOctal a t.text)
      | .StringToken => pure (.JSStringLiteral a t.text)
      | .RegExToken => pure (.JSRegEx a t.text)
      | _ => parseError t
    let ann ← parseTail
    return JSAST.JSAstLiteral e ann) input

/-- Parse a program, as `readJs` of the Haskell package (which raises an
error on a parse failure; here the default value is an empty program). -/
def readJs (input : String) : JSAST :=
  match parseProgram input with
  | .ok ast => ast
  | .error _ => .JSAstProgram [] .JSNoAnnot

/-- Parse a module, as `readJsModule` of the Haskell package. -/
def readJsModule (input : String) : JSAST :=
  match parseModule input with
  | .ok ast => ast
  | .error _ => .JSAstModule [] .JSNoAnnot

/-- Read a file as UTF-8 and parse it as a program; `parseFileUtf8` of the
Haskell package.  Throws an `IO` error if the source does not parse. -/
def parseFileUtf8 (fileName : System.FilePath) : IO JSAST := do
  let contents ← IO.FS.readFile fileName
  match parseProgram contents with
  | .ok ast => return ast
  | .error e => throw (IO.userError e)

end LanguageJavaScript.Parser
