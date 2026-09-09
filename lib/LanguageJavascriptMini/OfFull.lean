/-
Conversion of the annotated AST of `RequestProject.JavaScript.AST` into the
deterministic `MiniAST`.

Everything that only records how the source was written down — positions,
comments, whitespace, parentheses, the difference between an explicit and an
inserted semicolon, the two spellings of a call — is dropped here, and the
literals are normalised.  Together with `Parser.parseModule` this gives
`Language.JavaScript.MiniAST.parse`, which reads JavaScript source into a
`MiniProgram`.

The conversion can fail: the annotated AST can describe things the
deterministic one deliberately rules out, such as a `var` statement with no
declarator or an anonymous function *declaration*.
-/
import LanguageJavascriptMini.AST
import LanguageJavascript.Parser

namespace Language.JavaScript.MiniAST

open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.AST

/-- Result of a conversion: either the node or a message. -/
abbrev ConvM := Except String

private def unsupported (what : String) : ConvM α := .error ("MiniAST: unsupported " ++ what)

/-- A name that has to be there. -/
private def nonempty (what : String) (s : String) : ConvM NEString :=
  match NEString.ofString? s with
  | some s => pure s
  | none => .error ("MiniAST: empty " ++ what)

/-- A list that has to be non-empty. -/
private def nonemptyList (what : String) (l : List α) : ConvM (NEList α) :=
  match NEList.ofList? l with
  | some l => pure l
  | none => .error ("MiniAST: empty " ++ what)

private def identName? : JSIdent → Option NEString
  | .JSIdentName _ s => NEString.ofString? s
  | .JSIdentNone => none

private def identName (what : String) : JSIdent → ConvM NEString
  | .JSIdentName _ s => nonempty what s
  | .JSIdentNone => unsupported ("anonymous " ++ what)

private def binOp : JSBinOp → ConvM MiniBinOp
  | .JSBinOpAnd _ => pure .and
  | .JSBinOpOr _ => pure .or
  | .JSBinOpBitAnd _ => pure .bitAnd
  | .JSBinOpBitOr _ => pure .bitOr
  | .JSBinOpBitXor _ => pure .bitXor
  | .JSBinOpEq _ => pure .eq
  | .JSBinOpNeq _ => pure .neq
  | .JSBinOpStrictEq _ => pure .strictEq
  | .JSBinOpStrictNeq _ => pure .strictNeq
  | .JSBinOpLt _ => pure .lt
  | .JSBinOpLe _ => pure .le
  | .JSBinOpGt _ => pure .gt
  | .JSBinOpGe _ => pure .ge
  | .JSBinOpLsh _ => pure .lsh
  | .JSBinOpRsh _ => pure .rsh
  | .JSBinOpUrsh _ => pure .ursh
  | .JSBinOpPlus _ => pure .plus
  | .JSBinOpMinus _ => pure .minus
  | .JSBinOpTimes _ => pure .times
  | .JSBinOpDivide _ => pure .divide
  | .JSBinOpMod _ => pure .mod
  | .JSBinOpIn _ => pure .inOp
  | .JSBinOpInstanceOf _ => pure .instanceOf
  | .JSBinOpOf _ => unsupported "'of' outside a for statement"

private def unaryOp : JSUnaryOp → ConvM MiniUnaryOp
  | .JSUnaryOpNot _ => pure .not
  | .JSUnaryOpTilde _ => pure .tilde
  | .JSUnaryOpPlus _ => pure .plus
  | .JSUnaryOpMinus _ => pure .minus
  | .JSUnaryOpTypeof _ => pure .typeof
  | .JSUnaryOpVoid _ => pure .void
  | .JSUnaryOpDelete _ => pure .delete
  | .JSUnaryOpIncr _ => pure .preIncr
  | .JSUnaryOpDecr _ => pure .preDecr

private def postfixOp : JSUnaryOp → ConvM MiniPostfixOp
  | .JSUnaryOpIncr _ => pure .incr
  | .JSUnaryOpDecr _ => pure .decr
  | _ => unsupported "postfix operator"

private def assignOp : JSAssignOp → ConvM MiniAssignOp
  | .JSAssign _ => pure .assign
  | .JSPlusAssign _ => pure .plus
  | .JSMinusAssign _ => pure .minus
  | .JSTimesAssign _ => pure .times
  | .JSDivideAssign _ => pure .divide
  | .JSModAssign _ => pure .mod
  | .JSLshAssign _ => pure .lsh
  | .JSRshAssign _ => pure .rsh
  | .JSUrshAssign _ => pure .ursh
  | .JSBwAndAssign _ => pure .bitAnd
  | .JSBwXorAssign _ => pure .bitXor
  | .JSBwOrAssign _ => pure .bitOr

private def fromCommaTrailingList {a : Type} : JSCommaTrailingList a → List a
  | .JSCTLComma xs _ => fromCommaList xs
  | .JSCTLNone xs => fromCommaList xs

/-- Drop the delimiters of the head of a template literal: `` `text${ `` or
`` `text` ``. -/
private def templateHeadText (s : String) : String :=
  let cs := s.toList
  let cs := match cs with | '`' :: r => r | r => r
  let cs :=
    if cs.length ≥ 2 && (cs.drop (cs.length - 2)) == ['$', '{'] then cs.take (cs.length - 2)
    else match cs.reverse with | '`' :: r => r.reverse | _ => cs
  String.ofList cs

/-- Drop the delimiters of the text following a substitution: `}text${` or
`` }text` ``. -/
private def templatePartText (s : String) : String :=
  let cs := s.toList
  let cs := match cs with | '}' :: r => r | r => r
  let cs :=
    if cs.length ≥ 2 && (cs.drop (cs.length - 2)) == ['$', '{'] then cs.take (cs.length - 2)
    else match cs.reverse with | '`' :: r => r.reverse | _ => cs
  String.ofList cs

mutual

/-- Convert an expression, dropping parentheses. -/
partial def ofExpression : JSExpression → ConvM MiniExpr
  | .JSIdentifier _ n => do pure (.ident (← nonempty "identifier" n))
  | .JSDecimal _ s => do pure (.number (← nonempty "number" (normalizeNumber s)))
  | .JSHexInteger _ s => do pure (.number (← nonempty "number" (normalizeNumber s)))
  | .JSOctal _ s => do pure (.number (← nonempty "number" (normalizeNumber s)))
  | .JSStringLiteral _ s => pure (.string (decodeStringLiteral s))
  | .JSRegEx _ s => do pure (.regex (← nonempty "regular expression" s))
  | .JSLiteral _ s =>
      match s with
      | "null" => pure .null
      | "true" => pure .true_
      | "false" => pure .false_
      | "this" => pure .this
      | _ => do pure (.ident (← nonempty "identifier" s))
  | .JSArrayLiteral _ els _ => do
      let els ← ofArrayElements true els
      pure (.array els)
  | .JSObjectLiteral _ props _ => do
      let ps ← (fromCommaTrailingList props).mapM ofObjectProperty
      pure (.object ps)
  | .JSAssignExpression l op r => do
      pure (.assign (← ofExpression l) (← assignOp op) (← ofExpression r))
  | .JSAwaitExpression _ e => do pure (.await (← ofExpression e))
  | .JSCallExpression e _ args _ => do
      pure (.call (← ofExpression e) (← (fromCommaList args).mapM ofExpression))
  | .JSMemberExpression e _ args _ => do
      pure (.call (← ofExpression e) (← (fromCommaList args).mapM ofExpression))
  | .JSCallExpressionDot e _ p => do pure (.dot (← ofExpression e) (← ofMemberName p))
  | .JSMemberDot e _ p => do pure (.dot (← ofExpression e) (← ofMemberName p))
  | .JSCallExpressionSquare e _ i _ => do pure (.index (← ofExpression e) (← ofExpression i))
  | .JSMemberSquare e _ i _ => do pure (.index (← ofExpression e) (← ofExpression i))
  | .JSClassExpression _ n h _ body _ => do
      pure (.classExpr (identName? n) (← ofHeritage h) (← ofClassElements body))
  | .JSCommaExpression l _ r => do pure (.seq (← ofExpression l) (← ofExpression r))
  | .JSExpressionBinary l op r => do
      pure (.binary (← ofExpression l) (← binOp op) (← ofExpression r))
  | .JSExpressionParen _ e _ => ofExpression e
  | .JSExpressionPostfix e op => do pure (.postfix (← ofExpression e) (← postfixOp op))
  | .JSExpressionTernary c _ t _ f => do
      pure (.ternary (← ofExpression c) (← ofExpression t) (← ofExpression f))
  | .JSArrowExpression params _ body => do
      pure (.arrow (← ofArrowParams params) (← ofArrowBody body))
  | .JSFunctionExpression _ n _ params _ body => do
      pure (.func false false (identName? n) (← (fromCommaList params).mapM ofExpression)
        (← ofBlockBody body))
  | .JSGeneratorExpression _ _ n _ params _ body => do
      pure (.func false true (identName? n) (← (fromCommaList params).mapM ofExpression)
        (← ofBlockBody body))
  | .JSMemberNew _ e _ args _ => do
      pure (.new (← ofExpression e) (← (fromCommaList args).mapM ofExpression))
  | .JSNewExpression _ e => do pure (.new (← ofExpression e) [])
  | .JSSpreadExpression _ e => do pure (.spread (← ofExpression e))
  | .JSTemplateLiteral tag _ head parts => do
      let tag ← match tag with
        | none => pure none
        | some t => pure (some (← ofExpression t))
      pure (.template tag (templateHeadText head) (← parts.mapM ofTemplatePart))
  | .JSUnaryExpression op e => do pure (.unary (← unaryOp op) (← ofExpression e))
  | .JSVarInitExpression lhs init => do
      match init with
      | .JSVarInitNone => ofExpression lhs
      | .JSVarInit _ e => pure (.assign (← ofExpression lhs) .assign (← ofExpression e))
  | .JSYieldExpression _ e => do
      match e with
      | none => pure (.yield none)
      | some e => pure (.yield (some (← ofExpression e)))
  | .JSYieldFromExpression _ _ e => do pure (.yieldFrom (← ofExpression e))

/-- The name after a `.`. -/
partial def ofMemberName : JSExpression → ConvM NEString
  | .JSIdentifier _ n => nonempty "member name" n
  | .JSLiteral _ n => nonempty "member name" n
  | _ => unsupported "member name"

/-- Array literal elements; the annotated AST interleaves the commas, so an
elision is a comma where an element was expected. -/
partial def ofArrayElements (expectElem : Bool) :
    List JSArrayElement → ConvM (List MiniArrayElement)
  | [] => pure []
  | .JSArrayElement e :: rest => do
      let e ← ofExpression e
      pure (.elem e :: (← ofArrayElements false rest))
  | .JSArrayComma _ :: rest =>
      if expectElem then do pure (.hole :: (← ofArrayElements true rest))
      else ofArrayElements true rest

partial def ofTemplatePart : JSTemplatePart → ConvM MiniTemplatePart
  | .JSTemplatePart e _ suffix => do pure ⟨← ofExpression e, templatePartText suffix⟩

partial def ofPropertyName : JSPropertyName → ConvM MiniPropertyName
  | .JSPropertyIdent _ n => do pure (.ident (← nonempty "property name" n))
  | .JSPropertyString _ s => pure (.string (decodeStringLiteral s))
  | .JSPropertyNumber _ n => do pure (.number (← nonempty "property name" (normalizeNumber n)))
  | .JSPropertyComputed _ e _ => do pure (.computed (← ofExpression e))

partial def ofObjectProperty : JSObjectProperty → ConvM MiniProperty
  | .JSPropertyIdentRef _ n => do pure (.shorthand (← nonempty "property name" n))
  | .JSPropertyNameandValue name _ values => do
      match values with
      | [v] => pure (.keyValue (← ofPropertyName name) (← ofExpression v))
      | _ => unsupported "property value"
  | .JSObjectMethod m => do
      let (kind, name, params, body) ← ofMethodDefinition m
      pure (.method kind name params body)

partial def ofMethodDefinition :
    JSMethodDefinition →
      ConvM (MiniMethodKind × MiniPropertyName × List MiniExpr × List MiniStatement)
  | .JSMethodDefinition name _ params _ body => do
      pure (.normal, ← ofPropertyName name, ← (fromCommaList params).mapM ofExpression,
        ← ofBlockBody body)
  | .JSGeneratorMethodDefinition _ name _ params _ body => do
      pure (.generator, ← ofPropertyName name, ← (fromCommaList params).mapM ofExpression,
        ← ofBlockBody body)
  | .JSPropertyAccessor acc name _ params _ body => do
      let kind := match acc with
        | .JSAccessorGet _ => MiniMethodKind.get
        | .JSAccessorSet _ => MiniMethodKind.set
      pure (kind, ← ofPropertyName name, ← (fromCommaList params).mapM ofExpression,
        ← ofBlockBody body)

partial def ofClassElements (els : List JSClassElement) : ConvM (List MiniClassElement) := do
  let mut out := #[]
  for el in els do
    match el with
    | .JSClassSemi _ => pure ()
    | .JSClassInstanceMethod m =>
        let (kind, name, params, body) ← ofMethodDefinition m
        out := out.push ⟨false, kind, name, params, body⟩
    | .JSClassStaticMethod _ m =>
        let (kind, name, params, body) ← ofMethodDefinition m
        out := out.push ⟨true, kind, name, params, body⟩
  pure out.toList

partial def ofHeritage : JSClassHeritage → ConvM (Option MiniExpr)
  | .JSExtendsNone => pure none
  | .JSExtends _ e => do pure (some (← ofExpression e))

partial def ofArrowParams : JSArrowParameterList → ConvM (List MiniExpr)
  | .JSUnparenthesizedArrowParameter i => do pure [.ident (← identName "arrow parameter" i)]
  | .JSParenthesizedArrowParameterList _ ps _ => (fromCommaList ps).mapM ofExpression

partial def ofArrowBody : JSStatement → ConvM MiniArrowBody
  | .JSStatementBlock _ stmts _ _ => do pure (.block (← ofStatements stmts))
  | .JSExpressionStatement e _ => do pure (.expr (← ofExpression e))
  | s => do pure (.block [← ofStatement s])

partial def ofBlockBody : JSBlock → ConvM (List MiniStatement)
  | .JSBlock _ stmts _ => ofStatements stmts

/-- A statement list.  Stray empty statements carry no meaning, so — like
`prettier` — they are dropped; an empty statement is still kept where it is
the *body* of a loop or an `if`. -/
partial def ofStatements (stmts : List JSStatement) : ConvM (List MiniStatement) := do
  pure ((← stmts.mapM ofStatement).filter fun s => !(s matches .empty))

/-- One declarator of a `var`, `let` or `const` statement. -/
partial def ofDeclarator : JSExpression → ConvM MiniDeclarator
  | .JSVarInitExpression lhs .JSVarInitNone => do pure ⟨← ofExpression lhs, none⟩
  | .JSVarInitExpression lhs (.JSVarInit _ e) => do
      pure ⟨← ofExpression lhs, some (← ofExpression e)⟩
  | e => do pure ⟨← ofExpression e, none⟩

partial def ofDeclarators (xs : JSCommaList JSExpression) : ConvM (NEList MiniDeclarator) := do
  nonemptyList "declaration" (← (fromCommaList xs).mapM ofDeclarator)

/-- Combine a comma separated list of expressions into a single expression
with the comma operator. -/
partial def ofExpressionList (xs : JSCommaList JSExpression) : ConvM (Option MiniExpr) := do
  match ← (fromCommaList xs).mapM ofExpression with
  | [] => pure none
  | e :: es => pure (some (es.foldl (fun a b => .seq a b) e))

partial def ofSwitchPart : JSSwitchParts → ConvM MiniSwitchCase
  | .JSCase _ e _ stmts => do pure (.case (← ofExpression e) (← ofStatements stmts))
  | .JSDefault _ _ stmts => do pure (.default (← ofStatements stmts))

partial def ofCatch : JSTryCatch → ConvM MiniCatchClause
  | .JSCatch _ _ p _ body => do pure ⟨← ofExpression p, none, ← ofBlockBody body⟩
  | .JSCatchIf _ _ p _ cond _ body => do
      pure ⟨← ofExpression p, some (← ofExpression cond), ← ofBlockBody body⟩

partial def ofFinally : JSTryFinally → ConvM MiniFinallyClause
  | .JSNoFinally => pure .none
  | .JSFinally _ body => do pure (.some (← ofBlockBody body))

partial def ofTryTail (catches : List JSTryCatch) (fin : JSTryFinally) : ConvM MiniTryTail := do
  let fin ← ofFinally fin
  match ← catches.mapM ofCatch with
  | [] =>
      match fin with
      | .some body => pure (.finallyOnly body)
      | .none => .error "MiniAST: try without catch or finally"
  | c :: cs => pure (.catches ⟨c, cs⟩ fin)

partial def ofStatement : JSStatement → ConvM MiniStatement
  | .JSStatementBlock _ stmts _ _ => do pure (.block (← ofStatements stmts))
  | .JSBreak _ i _ => pure (.break_ (identName? i))
  | .JSContinue _ i _ => pure (.continue_ (identName? i))
  | .JSClass _ n h _ body _ _ => do
      pure (.classDecl (← identName "class" n) (← ofHeritage h) (← ofClassElements body))
  | .JSVariable _ decls _ => do pure (.decl .var (← ofDeclarators decls))
  | .JSLet _ decls _ => do pure (.decl .let_ (← ofDeclarators decls))
  | .JSConstant _ decls _ => do pure (.decl .const (← ofDeclarators decls))
  | .JSDoWhile _ body _ _ cond _ _ => do
      pure (.doWhile (← ofStatement body) (← ofExpression cond))
  | .JSFor _ _ init _ cond _ step _ body => do
      let init ← ofExpressionList init
      pure (.for_ (match init with | none => .none | some e => .expr e)
        (← ofExpressionList cond) (← ofExpressionList step) (← ofStatement body))
  | .JSForVar _ _ _ init _ cond _ step _ body => do
      pure (.for_ (.decl .var (← ofDeclarators init)) (← ofExpressionList cond)
        (← ofExpressionList step) (← ofStatement body))
  | .JSForLet _ _ _ init _ cond _ step _ body => do
      pure (.for_ (.decl .let_ (← ofDeclarators init)) (← ofExpressionList cond)
        (← ofExpressionList step) (← ofStatement body))
  | .JSForConst _ _ _ init _ cond _ step _ body => do
      pure (.for_ (.decl .const (← ofDeclarators init)) (← ofExpressionList cond)
        (← ofExpressionList step) (← ofStatement body))
  | .JSForIn _ _ lhs _ rhs _ body => do
      pure (.forIn (.pattern (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForVarIn _ _ _ lhs _ rhs _ body => do
      pure (.forIn (.decl .var (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForLetIn _ _ _ lhs _ rhs _ body => do
      pure (.forIn (.decl .let_ (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForConstIn _ _ _ lhs _ rhs _ body => do
      pure (.forIn (.decl .const (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForOf _ _ lhs _ rhs _ body => do
      pure (.forOf (.pattern (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForVarOf _ _ _ lhs _ rhs _ body => do
      pure (.forOf (.decl .var (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForLetOf _ _ _ lhs _ rhs _ body => do
      pure (.forOf (.decl .let_ (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForConstOf _ _ _ lhs _ rhs _ body => do
      pure (.forOf (.decl .const (← ofExpression lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSAsyncFunction _ _ n _ params _ body _ => do
      pure (.funcDecl true false (← identName "function" n)
        (← (fromCommaList params).mapM ofExpression) (← ofBlockBody body))
  | .JSFunction _ n _ params _ body _ => do
      pure (.funcDecl false false (← identName "function" n)
        (← (fromCommaList params).mapM ofExpression) (← ofBlockBody body))
  | .JSGenerator _ _ n _ params _ body _ => do
      pure (.funcDecl false true (← identName "function" n)
        (← (fromCommaList params).mapM ofExpression) (← ofBlockBody body))
  | .JSIf _ _ cond _ thenS => do
      pure (.if_ (← ofExpression cond) (← ofStatement thenS) none)
  | .JSIfElse _ _ cond _ thenS _ elseS => do
      pure (.if_ (← ofExpression cond) (← ofStatement thenS) (some (← ofStatement elseS)))
  | .JSLabelled l _ s => do pure (.labelled (← identName "label" l) (← ofStatement s))
  | .JSEmptyStatement _ => pure .empty
  | .JSExpressionStatement e _ => do pure (.expr (← ofExpression e))
  | .JSAssignStatement lhs op rhs _ => do
      pure (.expr (.assign (← ofExpression lhs) (← assignOp op) (← ofExpression rhs)))
  | .JSMethodCall e _ args _ _ => do
      pure (.expr (.call (← ofExpression e) (← (fromCommaList args).mapM ofExpression)))
  | .JSReturn _ e _ => do
      match e with
      | none => pure (.return_ none)
      | some e => pure (.return_ (some (← ofExpression e)))
  | .JSSwitch _ _ e _ _ parts _ _ => do
      pure (.switch (← ofExpression e) (← parts.mapM ofSwitchPart))
  | .JSThrow _ e _ => do pure (.throw (← ofExpression e))
  | .JSTry _ body catches fin => do
      pure (.try_ (← ofBlockBody body) (← ofTryTail catches fin))
  | .JSWhile _ _ cond _ body => do pure (.while_ (← ofExpression cond) (← ofStatement body))
  | .JSWith _ _ e _ body _ => do pure (.with_ (← ofExpression e) (← ofStatement body))

end

/-! ## Modules -/

private def ofImportSpecifier : JSImportSpecifier → ConvM MiniSpecifier
  | .JSImportSpecifier i => do pure ⟨← identName "import specifier" i, none⟩
  | .JSImportSpecifierAs i _ a => do
      pure ⟨← identName "import specifier" i, some (← identName "import alias" a)⟩

private def ofExportSpecifier : JSExportSpecifier → ConvM MiniSpecifier
  | .JSExportSpecifier i => do pure ⟨← identName "export specifier" i, none⟩
  | .JSExportSpecifierAs i _ a => do
      pure ⟨← identName "export specifier" i, some (← identName "export alias" a)⟩

private def ofFromClause : JSFromClause → ConvM NEString
  | .JSFromClause _ _ mod => nonempty "module name" (decodeStringLiteral mod)

private def ofImportsNamed : JSImportsNamed → ConvM (List MiniSpecifier)
  | .JSImportsNamed _ specs _ => (fromCommaList specs).mapM ofImportSpecifier

private def ofImportNameSpace : JSImportNameSpace → ConvM NEString
  | .JSImportNameSpace _ _ i => identName "namespace import" i

private def importClause (mod : NEString) (default_ namespace_ : Option NEString)
    (named : Option (List MiniSpecifier)) : ConvM MiniImportDeclaration :=
  match MiniImportClause.mk? default_ namespace_ named mod with
  | some c => pure (.clause c)
  | none => .error "MiniAST: import without a binding"

private def ofImportClause (mod : NEString) : JSImportClause → ConvM MiniImportDeclaration
  | .JSImportClauseDefault i => do
      importClause mod (some (← identName "default import" i)) none none
  | .JSImportClauseNameSpace ns => do
      importClause mod none (some (← ofImportNameSpace ns)) none
  | .JSImportClauseNamed named => do
      importClause mod none none (some (← ofImportsNamed named))
  | .JSImportClauseDefaultNameSpace i _ ns => do
      importClause mod (some (← identName "default import" i))
        (some (← ofImportNameSpace ns)) none
  | .JSImportClauseDefaultNamed i _ named => do
      importClause mod (some (← identName "default import" i)) none
        (some (← ofImportsNamed named))

private def ofImportDeclaration : JSImportDeclaration → ConvM MiniImportDeclaration
  | .JSImportDeclarationBare _ mod _ => do
      pure (.bare (← nonempty "module name" (decodeStringLiteral mod)))
  | .JSImportDeclaration clause from_ _ => do ofImportClause (← ofFromClause from_) clause

private def ofExportClause : JSExportClause → ConvM (List MiniSpecifier)
  | .JSExportClause _ specs _ => (fromCommaList specs).mapM ofExportSpecifier

private def ofExportDeclaration : JSExportDeclaration → ConvM MiniExportDeclaration
  | .JSExportFrom clause from_ _ => do
      pure (.fromClause (← ofExportClause clause) (← ofFromClause from_))
  | .JSExportLocals clause _ => do pure (.locals (← ofExportClause clause))
  | .JSExport stmt _ => do pure (.decl (← ofStatement stmt))

def ofModuleItem : JSModuleItem → ConvM MiniModuleItem
  | .JSModuleStatementListItem s => do pure (.stmt (← ofStatement s))
  | .JSModuleImportDeclaration _ d => do pure (.importDecl (← ofImportDeclaration d))
  | .JSModuleExportDeclaration _ d => do pure (.exportDecl (← ofExportDeclaration d))

/-- Convert a parsed, annotated AST into the deterministic `MiniProgram`. -/
def ofAST : JSAST → ConvM MiniProgram
  | .JSAstProgram stmts _ => do pure ⟨(← ofStatements stmts).map .stmt⟩
  | .JSAstModule items _ => do
      pure ⟨(← items.mapM ofModuleItem).filter fun i => !(i matches .stmt .empty)⟩
  | .JSAstStatement s _ => do pure ⟨[.stmt (← ofStatement s)]⟩
  | .JSAstExpression e _ => do pure ⟨[.stmt (.expr (← ofExpression e))]⟩
  | .JSAstLiteral e _ => do pure ⟨[.stmt (.expr (← ofExpression e))]⟩

/-- Parse JavaScript source into a `MiniProgram`.  Both `import`/`export`
declarations and plain statements are accepted. -/
def parse (input : String) : Except String MiniProgram := do
  ofAST (← Parser.parseModule input)

/-- Parse a single expression into a `MiniExpr`. -/
def parseExpr (input : String) : Except String MiniExpr := do
  match ← Parser.parseExpressionAST input with
  | .JSAstExpression e _ => ofExpression e
  | _ => .error "MiniAST: expected an expression"

end Language.JavaScript.MiniAST
