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

open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

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
  | .JSIdentName _ s => some s
  | .JSIdentNone => none

private def identName (what : String) : JSIdent → ConvM NEString
  | .JSIdentName _ s => pure s
  | .JSIdentNone => unsupported ("anonymous " ++ what)

private def binOp : JSBinOp → ConvM BinOp
  | .JSBinOpAnd _ => pure .and
  | .JSBinOpOr _ => pure .or
  | .JSBinOpNullish _ => pure .coalesce
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

private def unaryOp : JSUnaryOp → ConvM UnaryOp
  | .JSUnaryOpNot _ => pure .not
  | .JSUnaryOpTilde _ => pure .tilde
  | .JSUnaryOpPlus _ => pure .plus
  | .JSUnaryOpMinus _ => pure .minus
  | .JSUnaryOpTypeof _ => pure .typeof
  | .JSUnaryOpVoid _ => pure .void
  | .JSUnaryOpDelete _ => pure .delete
  | .JSUnaryOpIncr _ => pure .preIncr
  | .JSUnaryOpDecr _ => pure .preDecr

private def postfixOp : JSUnaryOp → ConvM PostfixOp
  | .JSUnaryOpIncr _ => pure .incr
  | .JSUnaryOpDecr _ => pure .decr
  | _ => unsupported "postfix operator"

private def assignOp : JSAssignOp → ConvM AssignOp
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
  | .JSLogicalAndAssign _ => pure .logicalAnd
  | .JSLogicalOrAssign _ => pure .logicalOr
  | .JSNullishAssign _ => pure .coalesce

private def fromCommaTrailingList {a : Type} : JSCommaTrailingList a → List a
  | .JSCTLComma xs _ => fromCommaList xs
  | .JSCTLNone xs => fromCommaList xs

/-! The conversion is *structurally* recursive: every function below
recurses on a component of its argument, so the block has equations and can
be reasoned about, rather than being `partial` and opaque.

Three things had to be arranged for that.  A comma list is walked as the
inductive value it is instead of being flattened first, since the flattened
list is not a component of the node; the flattened forms (`ofExprsRev` and
friends) return their elements in *reverse* order — one `List.reverse` at
the end is cheaper than an append per element, and reversing keeps the
conversions in source order, so it is still the leftmost failure that is
reported.  Every `mapM` of a conversion is spelled out as a function of the
same block.  And the wrappers which convert something without descending
into it (`ofArrowBody`, `ofParams`, `ofExpressionList`, …) are defined
after the block in terms of the functions in it. -/

/-- The elements of a list of expressions, combined with the comma
operator; `none` if there are none. -/
private def seqOf : List MiniExpr → Option MiniExpr
  | [] => none
  | e :: es => some (es.foldl (fun a b => .seq a b) e)

/-- A class member, from its already converted method definition. -/
private def classElemOf (decorators : List MiniExpr) (isStatic : Bool)
    (m : MethodKind × MiniPropertyName × List MiniParam × List MiniStatement) :
    MiniClassElement :=
  .method decorators isStatic m.1 m.2.1 m.2.2.1 m.2.2.2

/-- Is this expression the *syntax* of an optional chain — does it contain a
`?.` which a further `.name`, `[i]` or `(args)` written after it would
short circuit?  A pair of parentheses closes the chain, and so stops this. -/
private def isChainSyntax : JSExpression → Bool
  | .JSOptionalMemberDot .. | .JSOptionalMemberSquare .. | .JSOptionalCallExpression .. => true
  | .JSMemberDot e _ _ | .JSMemberSquare e _ _ _ | .JSCallExpression e _ _ _
  | .JSCallExpressionDot e _ _ | .JSCallExpressionSquare e _ _ _
  | .JSMemberExpression e _ _ _ => isChainSyntax e
  | _ => false

/-- Add a link to the end of an optional chain, starting one if the base is
not a chain already. -/
private def chainWith (base : MiniExpr) (link : MiniChainLink) : MiniExpr :=
  match base with
  | .chain b links => .chain b ⟨links.hd, links.tl ++ [link]⟩
  | _ => .chain base ⟨link, []⟩

/-- Is this a rest element, `...r`, of a parameter list or of an array
pattern? -/
private def isRestElem : JSExpression → Bool
  | .JSSpreadExpression .. => true
  | _ => false

/-- Is this the left hand side of a *destructuring* assignment, an array or
object pattern rather than an ordinary target? -/
private def isPatternLhs : JSExpression → Bool
  | .JSArrayLiteral .. | .JSObjectLiteral .. => true
  | _ => false

/-- Is this the plain `=`, the only assignment operator a destructuring
assignment may use? -/
private def isSimpleAssign : JSAssignOp → Bool
  | .JSAssign _ => true
  | _ => false

/-- The name written after a `.` or a `?.`, and whether it is private. -/
private def dotName : JSExpression → ConvM (Bool × NEString)
  | .JSIdentifier _ n => pure (false, n)
  | .JSLiteral _ k => pure (false, k.text)
  | .JSPrivateName _ n => pure (true, n)
  | _ => unsupported "member name"

/-- `super.name`; a private name may not follow `super`. -/
private def superDotOf : Bool × NEString → ConvM MiniExpr
  | (true, _) => unsupported "a private name after `super`"
  | (false, n) => pure (.superDot n)

/-- The member access `obj.name`, extending the chain `obj` is part of, if
it is part of one. -/
private def dotOf (inChain : Bool) (obj : MiniExpr) (priv : Bool) (name : NEString) : MiniExpr :=
  if inChain then chainWith obj (if priv then .privateDot false name else .dot false name)
  else if priv then .privateDot obj name else .dot obj name

/-- The index access `obj[idx]`, extending the chain `obj` is part of. -/
private def indexOf (inChain : Bool) (obj idx : MiniExpr) : MiniExpr :=
  if inChain then chainWith obj (.index false idx) else .index obj idx

/-- The call `callee(args)`, extending the chain `callee` is part of. -/
private def callOf (inChain : Bool) (callee : MiniExpr) (args : List MiniExpr) : MiniExpr :=
  if inChain then chainWith callee (.call false args) else .call callee args

mutual

/-- Convert an expression, dropping parentheses. -/
def ofExpression : JSExpression → ConvM MiniExpr
  | .JSIdentifier _ n => pure (.ident n)
  | .JSNumberLit _ s => pure (.number s)
  | .JSStringLiteral _ s => pure (.string (decodeStringLiteral s.render))
  | .JSRegEx _ s => pure (.regex s)
  | .JSLiteral _ k =>
      match k with
      | .null => pure .null
      | .true_ => pure .true_
      | .false_ => pure .false_
      | .this_ => pure .this
      -- `super` is only an expression as `super.x`, `super[i]` or
      -- `super(...)`, which the cases below read
      | .super => unsupported "`super` outside a member access or a call"
      | .debugger => pure (.ident k.text)
  | .JSArrayLiteral _ els _ => do
      let els ← ofArrayElements true els
      pure (.array els)
  | .JSObjectLiteral _ props _ => do
      pure (.object (← ofPropsTrailingRev props).reverse)
  | .JSAssignExpression l op r => do
      -- `[a, b] = xs` and `({ a } = o)` assign to a *pattern*
      if isPatternLhs l && isSimpleAssign op then
        pure (.assignPattern (← ofPattern l) (← ofExpression r))
      else pure (.assign (← ofExpression l) (← assignOp op) (← ofExpression r))
  | .JSAwaitExpression _ e => do pure (.await (← ofExpression e))
  -- the three forms `super` may be written in
  | .JSCallExpression (.JSLiteral _ .super) _ args _ => do
      pure (.superCall (← ofExprsRev args).reverse)
  | .JSMemberExpression (.JSLiteral _ .super) _ args _ => do
      pure (.superCall (← ofExprsRev args).reverse)
  | .JSCallExpressionDot (.JSLiteral _ .super) _ p => do
      pure (← superDotOf (← dotName p))
  | .JSMemberDot (.JSLiteral _ .super) _ p => do
      pure (← superDotOf (← dotName p))
  | .JSCallExpressionSquare (.JSLiteral _ .super) _ i _ => do
      pure (.superIndex (← ofExpression i))
  | .JSMemberSquare (.JSLiteral _ .super) _ i _ => do
      pure (.superIndex (← ofExpression i))
  | .JSCallExpression e _ args _ => do
      pure (callOf (isChainSyntax e) (← ofExpression e) (← ofExprsRev args).reverse)
  | .JSMemberExpression e _ args _ => do
      pure (callOf (isChainSyntax e) (← ofExpression e) (← ofExprsRev args).reverse)
  | .JSCallExpressionDot e _ p => do
      let (priv, n) ← dotName p
      pure (dotOf (isChainSyntax e) (← ofExpression e) priv n)
  | .JSMemberDot e _ p => do
      let (priv, n) ← dotName p
      pure (dotOf (isChainSyntax e) (← ofExpression e) priv n)
  | .JSCallExpressionSquare e _ i _ => do
      pure (indexOf (isChainSyntax e) (← ofExpression e) (← ofExpression i))
  | .JSMemberSquare e _ i _ => do
      pure (indexOf (isChainSyntax e) (← ofExpression e) (← ofExpression i))
  | .JSOptionalMemberDot e _ p => do
      let (priv, n) ← dotName p
      pure (chainWith (← ofExpression e) (if priv then .privateDot true n else .dot true n))
  | .JSOptionalMemberSquare e _ _ i _ => do
      pure (chainWith (← ofExpression e) (.index true (← ofExpression i)))
  | .JSOptionalCallExpression e _ _ args _ => do
      pure (chainWith (← ofExpression e) (.call true (← ofExprsRev args).reverse))
  | .JSPrivateName _ n => pure (.privateName n)
  | .JSImportMeta _ _ _ => pure .importMeta
  | .JSNewTarget _ _ _ => pure .newTarget
  | .JSImportCall _ _ args _ => do
      match (← ofExprsRev args).reverse with
      | [spec] => pure (.importCall spec none)
      | [spec, opts] => pure (.importCall spec (some opts))
      | _ => unsupported "a dynamic import with no specifier or too many arguments"
  | .JSClassExpression ds _ n h _ body _ => do
      pure (.classExpr (← ofDecorators ds) (identName? n) (← ofHeritage h)
        (← ofClassElements body))
  | .JSCommaExpression l _ r => do pure (.seq (← ofExpression l) (← ofExpression r))
  | .JSExpressionBinary l op r => do
      pure (.binary (← ofExpression l) (← binOp op) (← ofExpression r))
  | .JSExpressionParen _ e _ => ofExpression e
  | .JSExpressionPostfix e op => do pure (.postfix (← ofExpression e) (← postfixOp op))
  | .JSExpressionTernary c _ t _ f => do
      pure (.ternary (← ofExpression c) (← ofExpression t) (← ofExpression f))
  | .JSArrowExpression params _ body => do
      let ps ← ofArrowParams params
      match body with
      | .JSStatementBlock _ stmts _ _ => pure (.arrow ps (.block (← ofStatements stmts)))
      | .JSExpressionStatement e _ => pure (.arrow ps (.expr (← ofExpression e)))
      | s => pure (.arrow ps (.block [← ofStatement s]))
  | .JSFunctionExpression _ n _ params _ body => do
      pure (.func false false (identName? n) (← ofParamsRev params).reverse
        (← ofBlockBody body))
  | .JSGeneratorExpression _ _ n _ params _ body => do
      pure (.func false true (identName? n) (← ofParamsRev params).reverse
        (← ofBlockBody body))
  | .JSMemberNew _ e _ args _ => do
      pure (.new (← ofExpression e) (← ofExprsRev args).reverse)
  | .JSNewExpression _ e => do pure (.new (← ofExpression e) [])
  | .JSSpreadExpression _ e => do pure (.spread (← ofExpression e))
  | .JSTemplateLiteral tag _ head parts => do
      let tag ← match tag with
        | none => pure none
        | some t => pure (some (← ofExpression t))
      pure (.template tag head (← ofTemplateParts parts))
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
termination_by structural e => e

/-- The expressions of a comma list, in reverse order. -/
def ofExprsRev : JSCommaList JSExpression → ConvM (List MiniExpr)
  | .JSLNil => pure []
  | .JSLOne e => do pure [← ofExpression e]
  | .JSLCons l _ e => do
      let init ← ofExprsRev l
      let last ← ofExpression e
      pure (last :: init)

/-- The decorators of a class or of one of its members. -/
def ofDecorators : List JSDecorator → ConvM (List MiniExpr)
  | [] => pure []
  | .JSDecorator _ e :: rest => do pure ((← ofExpression e) :: (← ofDecorators rest))

/-- The pattern an expression of the annotated tree spells: a name, an
array or object pattern, a default value, or — outside a declaration — an
assignment target such as `o.p`. -/
def ofPattern : JSExpression → ConvM MiniPattern
  | .JSIdentifier _ n => pure (.ident n)
  | .JSExpressionParen _ e _ => ofPattern e
  | .JSArrayLiteral _ els _ => do pure (.array (← ofArrayPatternElems true els))
  | .JSObjectLiteral _ props _ => do
      let (ps, rest) ← ofObjectPatternRev props
      pure (.object ps.reverse rest)
  | .JSAssignExpression lhs (.JSAssign _) rhs => do
      pure (.withDefault (← ofPattern lhs) (← ofExpression rhs))
  | .JSVarInitExpression lhs (.JSVarInit _ e) => do
      pure (.withDefault (← ofPattern lhs) (← ofExpression e))
  | .JSVarInitExpression lhs .JSVarInitNone => ofPattern lhs
  -- the pattern of a rest element, `...r`; which of the two it is, the
  -- caller decides
  | .JSSpreadExpression _ e => ofPattern e
  | .JSMemberDot e _ p => do
      let (priv, n) ← dotName p
      pure (.target (dotOf (isChainSyntax e) (← ofExpression e) priv n))
  | .JSMemberSquare e _ i _ => do
      pure (.target (indexOf (isChainSyntax e) (← ofExpression e) (← ofExpression i)))
  | .JSCallExpressionDot e _ p => do
      let (priv, n) ← dotName p
      pure (.target (dotOf (isChainSyntax e) (← ofExpression e) priv n))
  | .JSCallExpressionSquare e _ i _ => do
      pure (.target (indexOf (isChainSyntax e) (← ofExpression e) (← ofExpression i)))
  | _ => unsupported "binding pattern"

/-- One element of an array pattern; `...r` binds the rest of the array. -/
def ofArrayPatternElem : JSArrayElement → ConvM MiniArrayPatternElem
  | .JSArrayElement e => do
      let p ← ofPattern e
      pure (if isRestElem e then .rest p else .elem p)
  | .JSArrayComma _ => pure .hole

/-- The elements of an array pattern; as in an array literal, the commas
are interleaved, so an elision is a comma where an element was expected. -/
def ofArrayPatternElems (expectElem : Bool) :
    List JSArrayElement → ConvM (List MiniArrayPatternElem)
  | [] => pure []
  | .JSArrayComma _ :: rest =>
      if expectElem then do pure (.hole :: (← ofArrayPatternElems true rest))
      else ofArrayPatternElems true rest
  | e :: rest => do
      pure ((← ofArrayPatternElem e) :: (← ofArrayPatternElems false rest))

/-- One property of an object pattern: a key/value pair, or the `...rest`. -/
def ofObjectPatternEntry :
    JSObjectProperty → ConvM (MiniObjectPatternProp ⊕ MiniPattern)
  | .JSObjectSpread _ e => do pure (.inr (← ofPattern e))
  | .JSPropertyIdentRef _ n => pure (.inl ⟨.ident n, .ident n⟩)
  | .JSPropertyIdentRefDefault _ n _ v => do
      pure (.inl ⟨.ident n, .withDefault (.ident n) (← ofExpression v)⟩)
  | .JSPropertyNameandValue key _ value => do
      pure (.inl ⟨← ofPropertyName key, ← ofPattern value⟩)
  | _ => unsupported "property of an object pattern"

/-- The properties of an object pattern, in reverse order, together with
its `...rest`, which JavaScript only allows as the last property. -/
def ofObjectPatternRev :
    JSCommaTrailingList JSObjectProperty →
      ConvM (List MiniObjectPatternProp × Option MiniPattern)
  | .JSCTLComma ps _ => ofObjectPatternPropsRev ps
  | .JSCTLNone ps => ofObjectPatternPropsRev ps

def ofObjectPatternPropsRev :
    JSCommaList JSObjectProperty → ConvM (List MiniObjectPatternProp × Option MiniPattern)
  | .JSLNil => pure ([], none)
  | .JSLOne p => do
      match ← ofObjectPatternEntry p with
      | .inl prop => pure ([prop], none)
      | .inr r => pure ([], some r)
  | .JSLCons l _ p => do
      let (init, rest) ← ofObjectPatternPropsRev l
      if rest.isSome then unsupported "a rest property which is not the last one"
      else
        match ← ofObjectPatternEntry p with
        | .inl prop => pure (prop :: init, none)
        | .inr r => pure (init, some r)


/-- Array literal elements; the annotated AST interleaves the commas, so an
elision is a comma where an element was expected. -/
def ofArrayElements (expectElem : Bool) :
    List JSArrayElement → ConvM (List MiniArrayElement)
  | [] => pure []
  | .JSArrayElement e :: rest => do
      let e ← ofExpression e
      pure (.elem e :: (← ofArrayElements false rest))
  | .JSArrayComma _ :: rest =>
      if expectElem then do pure (.hole :: (← ofArrayElements true rest))
      else ofArrayElements true rest

def ofTemplatePart : JSTemplatePart → ConvM MiniTemplatePart
  | .JSTemplatePart e _ suffix => do pure ⟨← ofExpression e, suffix⟩

def ofTemplateParts : List JSTemplatePart → ConvM (List MiniTemplatePart)
  | [] => pure []
  | p :: rest => do pure ((← ofTemplatePart p) :: (← ofTemplateParts rest))

def ofPropertyName : JSPropertyName → ConvM MiniPropertyName
  | .JSPropertyIdent _ n => pure (.ident n)
  | .JSPropertyPrivate _ n => pure (.private_ n)
  | .JSPropertyString _ s => pure (.string (decodeStringLiteral s.render))
  | .JSPropertyNumber _ n => pure (.number n)
  | .JSPropertyComputed _ e _ => do pure (.computed (← ofExpression e))

def ofObjectProperty : JSObjectProperty → ConvM MiniProperty
  | .JSPropertyIdentRef _ n => pure (.shorthand n)
  | .JSPropertyIdentRefDefault .. =>
      unsupported "a default value in an object literal which is not a pattern"
  | .JSObjectSpread _ e => do pure (.spread (← ofExpression e))
  | .JSPropertyNameandValue name _ value => do
      pure (.keyValue (← ofPropertyName name) (← ofExpression value))
  | .JSObjectMethod m => do
      let (kind, name, params, body) ← ofMethodDefinition m
      pure (.method kind name params body)

/-- The properties of an object literal, in reverse order. -/
def ofPropsRev : JSCommaList JSObjectProperty → ConvM (List MiniProperty)
  | .JSLNil => pure []
  | .JSLOne p => do pure [← ofObjectProperty p]
  | .JSLCons l _ p => do
      let init ← ofPropsRev l
      let last ← ofObjectProperty p
      pure (last :: init)

/-- The properties of an object literal (which may end with a comma), in
reverse order. -/
def ofPropsTrailingRev : JSCommaTrailingList JSObjectProperty → ConvM (List MiniProperty)
  | .JSCTLComma ps _ => ofPropsRev ps
  | .JSCTLNone ps => ofPropsRev ps

def ofMethodDefinition :
    JSMethodDefinition →
      ConvM (MethodKind × MiniPropertyName × List MiniParam × List MiniStatement)
  | .JSMethodDefinition name _ params _ body => do
      pure (.normal, ← ofPropertyName name, (← ofParamsRev params).reverse, ← ofBlockBody body)
  | .JSGeneratorMethodDefinition _ name _ params _ body => do
      pure (.generator, ← ofPropertyName name, (← ofParamsRev params).reverse,
        ← ofBlockBody body)
  | .JSPropertyAccessor acc name _ params _ body => do
      let kind := match acc with
        | .JSAccessorGet _ => MethodKind.get
        | .JSAccessorSet _ => MethodKind.set
      pure (kind, ← ofPropertyName name, (← ofParamsRev params).reverse, ← ofBlockBody body)

/-- The members of a class body; an empty member (a stray `;`) is
dropped. -/
def ofClassElements : List JSClassElement → ConvM (List MiniClassElement)
  | [] => pure []
  | .JSClassSemi _ :: rest => ofClassElements rest
  | .JSClassInstanceMethod ds m :: rest => do
      let ds ← ofDecorators ds
      let m ← ofMethodDefinition m
      pure (classElemOf ds false m :: (← ofClassElements rest))
  | .JSClassStaticMethod ds _ m :: rest => do
      let ds ← ofDecorators ds
      let m ← ofMethodDefinition m
      pure (classElemOf ds true m :: (← ofClassElements rest))
  | .JSClassInstanceField ds n i _ :: rest => do
      pure (.field (← ofDecorators ds) false (← ofPropertyName n) (← ofInitializer i)
        :: (← ofClassElements rest))
  | .JSClassStaticField ds _ n i _ :: rest => do
      pure (.field (← ofDecorators ds) true (← ofPropertyName n) (← ofInitializer i)
        :: (← ofClassElements rest))
  | .JSClassStaticBlock _ b :: rest => do
      pure (.staticBlock (← ofBlockBody b) :: (← ofClassElements rest))

/-- The `= value` of a class field, if there is one. -/
def ofInitializer : JSVarInitializer → ConvM (Option MiniExpr)
  | .JSVarInitNone => pure none
  | .JSVarInit _ e => do pure (some (← ofExpression e))

def ofHeritage : JSClassHeritage → ConvM (Option MiniExpr)
  | .JSExtendsNone => pure none
  | .JSExtends _ e => do pure (some (← ofExpression e))

/-- The parameters of a function, in reverse order.  A parameter is
converted by the `match` below rather than by a function of its own,
because its last case would convert the very node it was given — which is
not a recursive step. -/
def ofParamsRev : JSCommaList JSExpression → ConvM (List MiniParam)
  | .JSLNil => pure []
  | .JSLOne e => do
      let p ← ofPattern e
      pure [if isRestElem e then .rest p else .plain p]
  | .JSLCons l _ e => do
      let init ← ofParamsRev l
      let p ← ofPattern e
      pure ((if isRestElem e then .rest p else .plain p) :: init)

def ofArrowParams : JSArrowParameterList → ConvM (List MiniParam)
  | .JSUnparenthesizedArrowParameter i => do
      pure [.plain (.ident (← identName "arrow parameter" i))]
  | .JSParenthesizedArrowParameterList _ ps _ => do pure (← ofParamsRev ps).reverse

def ofBlockBody : JSBlock → ConvM (List MiniStatement)
  | .JSBlock _ stmts _ => ofStatements stmts

/-- A statement list.  Stray empty statements carry no meaning, so — like
`prettier` — they are dropped; an empty statement is still kept where it is
the *body* of a loop or an `if`. -/
def ofStatements : List JSStatement → ConvM (List MiniStatement)
  | [] => pure []
  | s :: rest => do
      let s ← ofStatement s
      let rest ← ofStatements rest
      pure (if s matches .empty then rest else s :: rest)

/-- The declarators of a `var`, `let` or `const`, in reverse order.  They
are a non-empty comma list, so the result is a non-empty list and the
conversion cannot fail for want of a declarator.

One declarator is converted by the `match` below rather than by a function
of its own, because its last case would convert the very node it was given
— which is not a recursive step. -/
def ofDeclaratorsRev : JSCommaList1 JSExpression → ConvM (NEList MiniDeclarator)
  | .JSL1One d => do
      let last : MiniDeclarator ← match d with
        | .JSVarInitExpression lhs .JSVarInitNone => do pure ⟨← ofPattern lhs, none⟩
        | .JSVarInitExpression lhs (.JSVarInit _ e) => do
            pure ⟨← ofPattern lhs, some (← ofExpression e)⟩
        | e => do pure ⟨← ofPattern e, none⟩
      pure ⟨last, []⟩
  | .JSL1Cons l _ d => do
      let init ← ofDeclaratorsRev l
      let last : MiniDeclarator ← match d with
        | .JSVarInitExpression lhs .JSVarInitNone => do pure ⟨← ofPattern lhs, none⟩
        | .JSVarInitExpression lhs (.JSVarInit _ e) => do
            pure ⟨← ofPattern lhs, some (← ofExpression e)⟩
        | e => do pure ⟨← ofPattern e, none⟩
      pure ⟨last, init.hd :: init.tl⟩

def ofSwitchPart : JSSwitchParts → ConvM MiniSwitchCase
  | .JSCase _ e _ stmts => do pure (.case (← ofExpression e) (← ofStatements stmts))
  | .JSDefault _ _ stmts => do pure (.default (← ofStatements stmts))

def ofSwitchParts : List JSSwitchParts → ConvM (List MiniSwitchCase)
  | [] => pure []
  | p :: rest => do pure ((← ofSwitchPart p) :: (← ofSwitchParts rest))

def ofCatch : JSTryCatch → ConvM MiniCatchClause
  | .JSCatch _ _ p _ body => do pure ⟨← ofPattern p, none, ← ofBlockBody body⟩
  | .JSCatchIf _ _ p _ cond _ body => do
      pure ⟨← ofPattern p, some (← ofExpression cond), ← ofBlockBody body⟩

def ofCatches : List JSTryCatch → ConvM (List MiniCatchClause)
  | [] => pure []
  | c :: rest => do pure ((← ofCatch c) :: (← ofCatches rest))

def ofFinally : JSTryFinally → ConvM MiniFinallyClause
  | .JSNoFinally => pure .none
  | .JSFinally _ body => do pure (.some (← ofBlockBody body))

def ofStatement : JSStatement → ConvM MiniStatement
  | .JSStatementBlock _ stmts _ _ => do pure (.block (← ofStatements stmts))
  | .JSBreak _ i _ => pure (.break_ (identName? i))
  | .JSContinue _ i _ => pure (.continue_ (identName? i))
  | .JSClass ds _ n h _ body _ _ => do
      pure (.classDecl (← ofDecorators ds) (← identName "class" n) (← ofHeritage h)
        (← ofClassElements body))
  | .JSVariable _ decls _ => do pure (.decl .var (← ofDeclaratorsRev decls).reverse)
  | .JSLet _ decls _ => do pure (.decl .let_ (← ofDeclaratorsRev decls).reverse)
  | .JSConstant _ decls _ => do pure (.decl .const (← ofDeclaratorsRev decls).reverse)
  | .JSUsing _ decls _ => do pure (.using_ false (← ofDeclaratorsRev decls).reverse)
  | .JSAwaitUsing _ _ decls _ => do pure (.using_ true (← ofDeclaratorsRev decls).reverse)
  | .JSDoWhile _ body _ _ cond _ _ => do
      pure (.doWhile (← ofStatement body) (← ofExpression cond))
  | .JSFor _ _ init _ cond _ step _ body => do
      let init := seqOf (← ofExprsRev init).reverse
      pure (.for_ (match init with | none => .none | some e => .expr e)
        (seqOf (← ofExprsRev cond).reverse) (seqOf (← ofExprsRev step).reverse)
        (← ofStatement body))
  | .JSForVar _ _ _ init _ cond _ step _ body => do
      pure (.for_ (.decl .var (← ofDeclaratorsRev init).reverse)
        (seqOf (← ofExprsRev cond).reverse) (seqOf (← ofExprsRev step).reverse)
        (← ofStatement body))
  | .JSForLet _ _ _ init _ cond _ step _ body => do
      pure (.for_ (.decl .let_ (← ofDeclaratorsRev init).reverse)
        (seqOf (← ofExprsRev cond).reverse) (seqOf (← ofExprsRev step).reverse)
        (← ofStatement body))
  | .JSForConst _ _ _ init _ cond _ step _ body => do
      pure (.for_ (.decl .const (← ofDeclaratorsRev init).reverse)
        (seqOf (← ofExprsRev cond).reverse) (seqOf (← ofExprsRev step).reverse)
        (← ofStatement body))
  | .JSForIn _ _ lhs _ rhs _ body => do
      pure (.forIn (.pattern (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForVarIn _ _ _ lhs _ rhs _ body => do
      pure (.forIn (.decl .var (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForLetIn _ _ _ lhs _ rhs _ body => do
      pure (.forIn (.decl .let_ (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForConstIn _ _ _ lhs _ rhs _ body => do
      pure (.forIn (.decl .const (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForOf _ _ lhs _ rhs _ body => do
      pure (.forOf (.pattern (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForVarOf _ _ _ lhs _ rhs _ body => do
      pure (.forOf (.decl .var (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForLetOf _ _ _ lhs _ rhs _ body => do
      pure (.forOf (.decl .let_ (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSForConstOf _ _ _ lhs _ rhs _ body => do
      pure (.forOf (.decl .const (← ofPattern lhs)) (← ofExpression rhs) (← ofStatement body))
  | .JSAsyncFunction _ _ n _ params _ body _ => do
      pure (.funcDecl true false (← identName "function" n)
        (← ofParamsRev params).reverse (← ofBlockBody body))
  | .JSFunction _ n _ params _ body _ => do
      pure (.funcDecl false false (← identName "function" n)
        (← ofParamsRev params).reverse (← ofBlockBody body))
  | .JSGenerator _ _ n _ params _ body _ => do
      pure (.funcDecl false true (← identName "function" n)
        (← ofParamsRev params).reverse (← ofBlockBody body))
  | .JSIf _ _ cond _ thenS => do
      pure (.if_ (← ofExpression cond) (← ofStatement thenS) none)
  | .JSIfElse _ _ cond _ thenS _ elseS => do
      pure (.if_ (← ofExpression cond) (← ofStatement thenS) (some (← ofStatement elseS)))
  | .JSLabelled l _ s => do pure (.labelled (← identName "label" l) (← ofStatement s))
  | .JSEmptyStatement _ => pure .empty
  | .JSExpressionStatement e _ => do pure (.expr (← ofExpression e))
  | .JSAssignStatement lhs op rhs _ => do
      if isPatternLhs lhs && isSimpleAssign op then
        pure (.expr (.assignPattern (← ofPattern lhs) (← ofExpression rhs)))
      else pure (.expr (.assign (← ofExpression lhs) (← assignOp op) (← ofExpression rhs)))
  | .JSMethodCall e _ args _ _ => do
      pure (.expr (.call (← ofExpression e) (← ofExprsRev args).reverse))
  | .JSReturn _ e _ => do
      match e with
      | none => pure (.return_ none)
      | some e => pure (.return_ (some (← ofExpression e)))
  | .JSSwitch _ _ e _ _ parts _ _ => do
      pure (.switch (← ofExpression e) (← ofSwitchParts parts))
  | .JSThrow _ e _ => do pure (.throw (← ofExpression e))
  | .JSTry _ body catches fin => do
      let body ← ofBlockBody body
      let fin ← ofFinally fin
      let tail ← match ← ofCatches catches with
        | [] =>
            match fin with
            | .some f => pure (MiniTryTail.finallyOnly f)
            | .none => .error "MiniAST: try without catch or finally"
        | c :: cs => pure (.catches ⟨c, cs⟩ fin)
      pure (.try_ body tail)
  | .JSWhile _ _ cond _ body => do pure (.while_ (← ofExpression cond) (← ofStatement body))
  | .JSWith _ _ e _ body _ => do pure (.with_ (← ofExpression e) (← ofStatement body))

end

/-- The body of an arrow function. -/
def ofArrowBody : JSStatement → ConvM MiniArrowBody
  | .JSStatementBlock _ stmts _ _ => do pure (.block (← ofStatements stmts))
  | .JSExpressionStatement e _ => do pure (.expr (← ofExpression e))
  | s => do pure (.block [← ofStatement s])

/-- A parameter: a pattern, or a rest parameter. -/
def ofParam (e : JSExpression) : ConvM MiniParam := do
  let p ← ofPattern e
  pure (if isRestElem e then .rest p else .plain p)

/-- The parameters of a function. -/
def ofParams (ps : JSCommaList JSExpression) : ConvM (List MiniParam) := do
  pure (← ofParamsRev ps).reverse

/-- One declarator of a `var`, `let` or `const` statement. -/
def ofDeclarator : JSExpression → ConvM MiniDeclarator
  | .JSVarInitExpression lhs .JSVarInitNone => do pure ⟨← ofPattern lhs, none⟩
  | .JSVarInitExpression lhs (.JSVarInit _ e) => do
      pure ⟨← ofPattern lhs, some (← ofExpression e)⟩
  | e => do pure ⟨← ofPattern e, none⟩

/-- The declarators of a `var`, `let` or `const`. -/
def ofDeclarators (decls : JSCommaList1 JSExpression) : ConvM (NEList MiniDeclarator) := do
  pure (← ofDeclaratorsRev decls).reverse

/-- Combine a comma separated list of expressions into a single expression
with the comma operator. -/
def ofExpressionList (xs : JSCommaList JSExpression) : ConvM (Option MiniExpr) := do
  pure (seqOf (← ofExprsRev xs).reverse)

/-- What follows the block of a `try`. -/
def ofTryTail (catches : List JSTryCatch) (fin : JSTryFinally) : ConvM MiniTryTail := do
  let fin ← ofFinally fin
  match ← ofCatches catches with
  | [] =>
      match fin with
      | .some body => pure (.finallyOnly body)
      | .none => .error "MiniAST: try without catch or finally"
  | c :: cs => pure (.catches ⟨c, cs⟩ fin)

/-! ## Modules -/

private def ofImportSpecifier : JSImportSpecifier → ConvM Specifier
  | .JSImportSpecifier i => do pure ⟨← identName "import specifier" i, none⟩
  | .JSImportSpecifierAs i _ a => do
      pure ⟨← identName "import specifier" i, some (← identName "import alias" a)⟩

private def ofExportSpecifier : JSExportSpecifier → ConvM Specifier
  | .JSExportSpecifier i => do pure ⟨← identName "export specifier" i, none⟩
  | .JSExportSpecifierAs i _ a => do
      pure ⟨← identName "export specifier" i, some (← identName "export alias" a)⟩

/-- One import attribute; the key and the value hold the characters they
denote, so a key written as an identifier and the same key written as a
string literal give the same attribute. -/
private def ofImportAttribute : JSImportAttribute → ImportAttr
  | .JSImportAttribute _ k _ _ v =>
      ⟨decodeStringLiteral k.val, decodeStringLiteral v.val⟩

private def ofImportAttributes? : Option JSImportAttributes → List ImportAttr
  | none => []
  | some (.JSImportAttributes _ _ attrs _) => (fromCommaList attrs).map ofImportAttribute

/-- The module of a `from` clause, and its import attributes. -/
private def ofFromClauseWith : JSFromClause → ConvM (NEString × List ImportAttr)
  | .JSFromClause _ _ mod attrs => do
      pure (← nonempty "module name" (decodeStringLiteral mod.val), ofImportAttributes? attrs)

private def ofFromClause (f : JSFromClause) : ConvM NEString := do
  pure (← ofFromClauseWith f).1

private def ofImportsNamed : JSImportsNamed → ConvM (List Specifier)
  | .JSImportsNamed _ specs _ => (fromCommaList specs).mapM ofImportSpecifier

private def ofImportNameSpace : JSImportNameSpace → ConvM NEString
  | .JSImportNameSpace _ _ i => identName "namespace import" i

private def importClause (mod : NEString) (attrs : List ImportAttr)
    (default_ namespace_ : Option NEString)
    (named : Option (List Specifier)) : ConvM MiniImportDeclaration :=
  match MiniImportClause.mk? default_ namespace_ named mod attrs with
  | some c => pure (.clause c)
  | none => .error "MiniAST: import without a binding"

private def ofImportClause (mod : NEString) (attrs : List ImportAttr) :
    JSImportClause → ConvM MiniImportDeclaration
  | .JSImportClauseDefault i => do
      importClause mod attrs (some (← identName "default import" i)) none none
  | .JSImportClauseNameSpace ns => do
      importClause mod attrs none (some (← ofImportNameSpace ns)) none
  | .JSImportClauseNamed named => do
      importClause mod attrs none none (some (← ofImportsNamed named))
  | .JSImportClauseDefaultNameSpace i _ ns => do
      importClause mod attrs (some (← identName "default import" i))
        (some (← ofImportNameSpace ns)) none
  | .JSImportClauseDefaultNamed i _ named => do
      importClause mod attrs (some (← identName "default import" i)) none
        (some (← ofImportsNamed named))

private def ofImportDeclaration : JSImportDeclaration → ConvM MiniImportDeclaration
  | .JSImportDeclarationBare _ mod attrs _ => do
      pure (.bare (← nonempty "module name" (decodeStringLiteral mod.val))
        (ofImportAttributes? attrs))
  | .JSImportDeclaration clause from_ _ => do
      let (mod, attrs) ← ofFromClauseWith from_
      ofImportClause mod attrs clause

private def ofExportClause : JSExportClause → ConvM (List Specifier)
  | .JSExportClause _ specs _ => (fromCommaList specs).mapM ofExportSpecifier

private def ofExportDeclaration : JSExportDeclaration → ConvM MiniExportDeclaration
  | .JSExportFrom clause from_ _ => do
      let (mod, attrs) ← ofFromClauseWith from_
      pure (.fromClause (← ofExportClause clause) mod attrs)
  | .JSExportLocals clause _ => do pure (.locals (← ofExportClause clause))
  | .JSExportAll _ from_ _ => do
      let (mod, attrs) ← ofFromClauseWith from_
      pure (.all none mod attrs)
  | .JSExportAllAs _ _ i from_ _ => do
      let (mod, attrs) ← ofFromClauseWith from_
      pure (.all (some (← identName "namespace export" i)) mod attrs)
  | .JSExportDefault _ e _ => do pure (.defaultExpr (← ofExpression e))
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
  ofAST (← Language.JavaScript.Parser.parseModule input)

/-- Parse a single expression into a `MiniExpr`. -/
def parseExpr (input : String) : Except String MiniExpr := do
  match ← Language.JavaScript.Parser.parseExpressionAST input with
  | .JSAstExpression e _ => ofExpression e
  | _ => .error "MiniAST: expected an expression"

end Language.JavaScript.MiniAST
