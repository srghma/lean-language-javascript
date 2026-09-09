/-
Port of `LanguageJavaScript.Parser.AST` to Lean 4.

The constructor names are kept identical to the Haskell original so that the
two versions can be read side by side.  Types which are not mutually
recursive with the expression/statement grammar are defined first; the rest
live in one big `mutual` block.
-/
import LanguageJavascript.Token

namespace LanguageJavaScript.Parser.AST

open LanguageJavaScript.Parser

/-- Annotation: position and comment/whitespace information. -/
inductive JSAnnot where
  /-- Annotation: position and comment/whitespace information. -/
  | JSAnnot (pos : TokenPosn) (comments : List CommentAnnotation)
  /-- A single space character. -/
  | JSAnnotSpace
  /-- No annotation. -/
  | JSNoAnnot
deriving Repr, BEq, DecidableEq, Inhabited

inductive JSBinOp where
  | JSBinOpAnd (annot : JSAnnot)
  | JSBinOpBitAnd (annot : JSAnnot)
  | JSBinOpBitOr (annot : JSAnnot)
  | JSBinOpBitXor (annot : JSAnnot)
  | JSBinOpDivide (annot : JSAnnot)
  | JSBinOpEq (annot : JSAnnot)
  | JSBinOpGe (annot : JSAnnot)
  | JSBinOpGt (annot : JSAnnot)
  | JSBinOpIn (annot : JSAnnot)
  | JSBinOpInstanceOf (annot : JSAnnot)
  | JSBinOpLe (annot : JSAnnot)
  | JSBinOpLsh (annot : JSAnnot)
  | JSBinOpLt (annot : JSAnnot)
  | JSBinOpMinus (annot : JSAnnot)
  | JSBinOpMod (annot : JSAnnot)
  | JSBinOpNeq (annot : JSAnnot)
  | JSBinOpOf (annot : JSAnnot)
  | JSBinOpOr (annot : JSAnnot)
  | JSBinOpPlus (annot : JSAnnot)
  | JSBinOpRsh (annot : JSAnnot)
  | JSBinOpStrictEq (annot : JSAnnot)
  | JSBinOpStrictNeq (annot : JSAnnot)
  | JSBinOpTimes (annot : JSAnnot)
  | JSBinOpUrsh (annot : JSAnnot)
deriving Repr, BEq, DecidableEq, Inhabited

inductive JSUnaryOp where
  | JSUnaryOpDecr (annot : JSAnnot)
  | JSUnaryOpDelete (annot : JSAnnot)
  | JSUnaryOpIncr (annot : JSAnnot)
  | JSUnaryOpMinus (annot : JSAnnot)
  | JSUnaryOpNot (annot : JSAnnot)
  | JSUnaryOpPlus (annot : JSAnnot)
  | JSUnaryOpTilde (annot : JSAnnot)
  | JSUnaryOpTypeof (annot : JSAnnot)
  | JSUnaryOpVoid (annot : JSAnnot)
deriving Repr, BEq, DecidableEq, Inhabited

inductive JSSemi where
  | JSSemi (annot : JSAnnot)
  | JSSemiAuto
deriving Repr, BEq, DecidableEq, Inhabited

inductive JSAssignOp where
  | JSAssign (annot : JSAnnot)
  | JSTimesAssign (annot : JSAnnot)
  | JSDivideAssign (annot : JSAnnot)
  | JSModAssign (annot : JSAnnot)
  | JSPlusAssign (annot : JSAnnot)
  | JSMinusAssign (annot : JSAnnot)
  | JSLshAssign (annot : JSAnnot)
  | JSRshAssign (annot : JSAnnot)
  | JSUrshAssign (annot : JSAnnot)
  | JSBwAndAssign (annot : JSAnnot)
  | JSBwXorAssign (annot : JSAnnot)
  | JSBwOrAssign (annot : JSAnnot)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Accessors for `JSObjectProperty`: either 'get' or 'set'. -/
inductive JSAccessor where
  | JSAccessorGet (annot : JSAnnot)
  | JSAccessorSet (annot : JSAnnot)
deriving Repr, BEq, DecidableEq, Inhabited

inductive JSIdent where
  | JSIdentName (annot : JSAnnot) (name : String)
  | JSIdentNone
deriving Repr, BEq, DecidableEq, Inhabited

/-- A comma separated list. -/
inductive JSCommaList (a : Type) where
  /-- head, comma, element -/
  | JSLCons (init : JSCommaList a) (annot : JSAnnot) (last : a)
  /-- single element (no comma) -/
  | JSLOne (x : a)
  | JSLNil
deriving Repr, BEq, Inhabited

/-- A comma separated list which may have a trailing comma. -/
inductive JSCommaTrailingList (a : Type) where
  /-- list, trailing comma -/
  | JSCTLComma (xs : JSCommaList a) (annot : JSAnnot)
  /-- list -/
  | JSCTLNone (xs : JSCommaList a)
deriving Repr, BEq, Inhabited

mutual

inductive JSAST where
  /-- source elements, trailing whitespace -/
  | JSAstProgram (stmts : List JSStatement) (annot : JSAnnot)
  | JSAstModule (items : List JSModuleItem) (annot : JSAnnot)
  | JSAstStatement (stmt : JSStatement) (annot : JSAnnot)
  | JSAstExpression (expr : JSExpression) (annot : JSAnnot)
  | JSAstLiteral (expr : JSExpression) (annot : JSAnnot)

inductive JSModuleItem where
  /-- import, decl -/
  | JSModuleImportDeclaration (annot : JSAnnot) (decl : JSImportDeclaration)
  /-- export, decl -/
  | JSModuleExportDeclaration (annot : JSAnnot) (decl : JSExportDeclaration)
  | JSModuleStatementListItem (stmt : JSStatement)

inductive JSImportDeclaration where
  /-- imports, module, semi -/
  | JSImportDeclaration (clause : JSImportClause) (from_ : JSFromClause) (semi : JSSemi)
  /-- module, module, semi -/
  | JSImportDeclarationBare (annot : JSAnnot) (mod : String) (semi : JSSemi)

inductive JSImportClause where
  | JSImportClauseDefault (ident : JSIdent)
  | JSImportClauseNameSpace (ns : JSImportNameSpace)
  | JSImportClauseNamed (named : JSImportsNamed)
  /-- default, comma, namespace -/
  | JSImportClauseDefaultNameSpace (ident : JSIdent) (annot : JSAnnot) (ns : JSImportNameSpace)
  /-- default, comma, named imports -/
  | JSImportClauseDefaultNamed (ident : JSIdent) (annot : JSAnnot) (named : JSImportsNamed)

inductive JSFromClause where
  /-- from, string literal, string literal contents -/
  | JSFromClause (from_ : JSAnnot) (annot : JSAnnot) (mod : String)

/-- Import namespace, e.g. `* as whatever`. -/
inductive JSImportNameSpace where
  /-- `*`, `as`, ident -/
  | JSImportNameSpace (star : JSBinOp) (annot : JSAnnot) (ident : JSIdent)

/-- Named imports, e.g. `{ foo, bar, baz as quux }`. -/
inductive JSImportsNamed where
  /-- lb, specifiers, rb -/
  | JSImportsNamed (lb : JSAnnot) (specs : JSCommaList JSImportSpecifier) (rb : JSAnnot)

/-- Note that this data type is separate from `JSExportSpecifier` because the
grammar is slightly different (e.g. in handling of reserved words). -/
inductive JSImportSpecifier where
  | JSImportSpecifier (ident : JSIdent)
  /-- ident, as, ident -/
  | JSImportSpecifierAs (ident : JSIdent) (annot : JSAnnot) (as_ : JSIdent)

inductive JSExportDeclaration where
  /-- exports, module, semi -/
  | JSExportFrom (clause : JSExportClause) (from_ : JSFromClause) (semi : JSSemi)
  /-- exports, autosemi -/
  | JSExportLocals (clause : JSExportClause) (semi : JSSemi)
  /-- body, autosemi -/
  | JSExport (stmt : JSStatement) (semi : JSSemi)

inductive JSExportClause where
  /-- lb, specifiers, rb -/
  | JSExportClause (lb : JSAnnot) (specs : JSCommaList JSExportSpecifier) (rb : JSAnnot)

inductive JSExportSpecifier where
  | JSExportSpecifier (ident : JSIdent)
  /-- ident1, as, ident2 -/
  | JSExportSpecifierAs (ident : JSIdent) (annot : JSAnnot) (as_ : JSIdent)

inductive JSStatement where
  /-- lbrace, stmts, rbrace, autosemi -/
  | JSStatementBlock (lb : JSAnnot) (stmts : List JSStatement) (rb : JSAnnot) (semi : JSSemi)
  /-- break, optional identifier, autosemi -/
  | JSBreak (annot : JSAnnot) (ident : JSIdent) (semi : JSSemi)
  /-- let, decl, autosemi -/
  | JSLet (annot : JSAnnot) (decls : JSCommaList JSExpression) (semi : JSSemi)
  /-- class, name, optional extends clause, lb, body, rb, autosemi -/
  | JSClass (annot : JSAnnot) (name : JSIdent) (heritage : JSClassHeritage) (lb : JSAnnot)
      (body : List JSClassElement) (rb : JSAnnot) (semi : JSSemi)
  /-- const, decl, autosemi -/
  | JSConstant (annot : JSAnnot) (decls : JSCommaList JSExpression) (semi : JSSemi)
  /-- continue, optional identifier, autosemi -/
  | JSContinue (annot : JSAnnot) (ident : JSIdent) (semi : JSSemi)
  /-- do, stmt, while, lb, expr, rb, autosemi -/
  | JSDoWhile (doA : JSAnnot) (stmt : JSStatement) (whileA : JSAnnot) (lb : JSAnnot)
      (cond : JSExpression) (rb : JSAnnot) (semi : JSSemi)
  /-- for, lb, expr, semi, expr, semi, expr, rb, stmt -/
  | JSFor (forA : JSAnnot) (lb : JSAnnot) (init : JSCommaList JSExpression) (s1 : JSAnnot)
      (cond : JSCommaList JSExpression) (s2 : JSAnnot) (step : JSCommaList JSExpression)
      (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, expr, in, expr, rb, stmt -/
  | JSForIn (forA : JSAnnot) (lb : JSAnnot) (lhs : JSExpression) (op : JSBinOp)
      (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, var, vardecl, semi, expr, semi, expr, rb, stmt -/
  | JSForVar (forA : JSAnnot) (lb : JSAnnot) (varA : JSAnnot) (init : JSCommaList JSExpression)
      (s1 : JSAnnot) (cond : JSCommaList JSExpression) (s2 : JSAnnot)
      (step : JSCommaList JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, var, vardecl, in, expr, rb, stmt -/
  | JSForVarIn (forA : JSAnnot) (lb : JSAnnot) (varA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, let, vardecl, semi, expr, semi, expr, rb, stmt -/
  | JSForLet (forA : JSAnnot) (lb : JSAnnot) (letA : JSAnnot) (init : JSCommaList JSExpression)
      (s1 : JSAnnot) (cond : JSCommaList JSExpression) (s2 : JSAnnot)
      (step : JSCommaList JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, let, vardecl, in, expr, rb, stmt -/
  | JSForLetIn (forA : JSAnnot) (lb : JSAnnot) (letA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, let, vardecl, of, expr, rb, stmt -/
  | JSForLetOf (forA : JSAnnot) (lb : JSAnnot) (letA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, const, vardecl, semi, expr, semi, expr, rb, stmt -/
  | JSForConst (forA : JSAnnot) (lb : JSAnnot) (constA : JSAnnot)
      (init : JSCommaList JSExpression) (s1 : JSAnnot) (cond : JSCommaList JSExpression)
      (s2 : JSAnnot) (step : JSCommaList JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, const, vardecl, in, expr, rb, stmt -/
  | JSForConstIn (forA : JSAnnot) (lb : JSAnnot) (constA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, const, vardecl, of, expr, rb, stmt -/
  | JSForConstOf (forA : JSAnnot) (lb : JSAnnot) (constA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, expr, of, expr, rb, stmt -/
  | JSForOf (forA : JSAnnot) (lb : JSAnnot) (lhs : JSExpression) (op : JSBinOp)
      (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, var, vardecl, of, expr, rb, stmt -/
  | JSForVarOf (forA : JSAnnot) (lb : JSAnnot) (varA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- async, fn, name, lb, parameter list, rb, block, autosemi -/
  | JSAsyncFunction (asyncA : JSAnnot) (fnA : JSAnnot) (name : JSIdent) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (body : JSBlock) (semi : JSSemi)
  /-- fn, name, lb, parameter list, rb, block, autosemi -/
  | JSFunction (fnA : JSAnnot) (name : JSIdent) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (body : JSBlock) (semi : JSSemi)
  /-- fn, *, name, lb, parameter list, rb, block, autosemi -/
  | JSGenerator (fnA : JSAnnot) (starA : JSAnnot) (name : JSIdent) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (body : JSBlock) (semi : JSSemi)
  /-- if, (, expr, ), stmt -/
  | JSIf (ifA : JSAnnot) (lb : JSAnnot) (cond : JSExpression) (rb : JSAnnot)
      (thenS : JSStatement)
  /-- if, (, expr, ), stmt, else, rest -/
  | JSIfElse (ifA : JSAnnot) (lb : JSAnnot) (cond : JSExpression) (rb : JSAnnot)
      (thenS : JSStatement) (elseA : JSAnnot) (elseS : JSStatement)
  /-- identifier, colon, stmt -/
  | JSLabelled (label : JSIdent) (colon : JSAnnot) (stmt : JSStatement)
  | JSEmptyStatement (annot : JSAnnot)
  | JSExpressionStatement (expr : JSExpression) (semi : JSSemi)
  /-- lhs, assignop, rhs, autosemi -/
  | JSAssignStatement (lhs : JSExpression) (op : JSAssignOp) (rhs : JSExpression) (semi : JSSemi)
  | JSMethodCall (expr : JSExpression) (lb : JSAnnot) (args : JSCommaList JSExpression)
      (rb : JSAnnot) (semi : JSSemi)
  /-- optional expression, autosemi -/
  | JSReturn (annot : JSAnnot) (expr : Option JSExpression) (semi : JSSemi)
  /-- switch, lb, expr, rb, caseblock, autosemi -/
  | JSSwitch (annot : JSAnnot) (lp : JSAnnot) (expr : JSExpression) (rp : JSAnnot)
      (lb : JSAnnot) (parts : List JSSwitchParts) (rb : JSAnnot) (semi : JSSemi)
  /-- throw, val, autosemi -/
  | JSThrow (annot : JSAnnot) (expr : JSExpression) (semi : JSSemi)
  /-- try, block, catches, finally -/
  | JSTry (annot : JSAnnot) (block : JSBlock) (catches : List JSTryCatch) (fin : JSTryFinally)
  /-- var, decl, autosemi -/
  | JSVariable (annot : JSAnnot) (decls : JSCommaList JSExpression) (semi : JSSemi)
  /-- while, lb, expr, rb, stmt -/
  | JSWhile (annot : JSAnnot) (lb : JSAnnot) (cond : JSExpression) (rb : JSAnnot)
      (body : JSStatement)
  /-- with, lb, expr, rb, stmt list -/
  | JSWith (annot : JSAnnot) (lb : JSAnnot) (expr : JSExpression) (rb : JSAnnot)
      (body : JSStatement) (semi : JSSemi)

inductive JSExpression where
  -- Terminals
  | JSIdentifier (annot : JSAnnot) (name : String)
  | JSDecimal (annot : JSAnnot) (lit : String)
  | JSLiteral (annot : JSAnnot) (lit : String)
  | JSHexInteger (annot : JSAnnot) (lit : String)
  | JSOctal (annot : JSAnnot) (lit : String)
  | JSStringLiteral (annot : JSAnnot) (lit : String)
  | JSRegEx (annot : JSAnnot) (lit : String)
  -- Non terminals
  /-- lb, contents, rb -/
  | JSArrayLiteral (lb : JSAnnot) (elements : List JSArrayElement) (rb : JSAnnot)
  /-- lhs, assignop, rhs -/
  | JSAssignExpression (lhs : JSExpression) (op : JSAssignOp) (rhs : JSExpression)
  /-- await, expr -/
  | JSAwaitExpression (annot : JSAnnot) (expr : JSExpression)
  /-- expr, lb, args, rb -/
  | JSCallExpression (expr : JSExpression) (lb : JSAnnot) (args : JSCommaList JSExpression)
      (rb : JSAnnot)
  /-- expr, dot, expr -/
  | JSCallExpressionDot (expr : JSExpression) (dot : JSAnnot) (prop : JSExpression)
  /-- expr, [, expr, ] -/
  | JSCallExpressionSquare (expr : JSExpression) (lb : JSAnnot) (idx : JSExpression)
      (rb : JSAnnot)
  /-- class, optional identifier, optional extends clause, lb, body, rb -/
  | JSClassExpression (annot : JSAnnot) (name : JSIdent) (heritage : JSClassHeritage)
      (lb : JSAnnot) (body : List JSClassElement) (rb : JSAnnot)
  /-- expression components -/
  | JSCommaExpression (lhs : JSExpression) (comma : JSAnnot) (rhs : JSExpression)
  /-- lhs, op, rhs -/
  | JSExpressionBinary (lhs : JSExpression) (op : JSBinOp) (rhs : JSExpression)
  /-- lb, expression, rb -/
  | JSExpressionParen (lb : JSAnnot) (expr : JSExpression) (rb : JSAnnot)
  /-- expression, operator -/
  | JSExpressionPostfix (expr : JSExpression) (op : JSUnaryOp)
  /-- cond, ?, trueval, :, falseval -/
  | JSExpressionTernary (cond : JSExpression) (hook : JSAnnot) (trueE : JSExpression)
      (colon : JSAnnot) (falseE : JSExpression)
  /-- parameter list, arrow, block -/
  | JSArrowExpression (params : JSArrowParameterList) (arrow : JSAnnot) (body : JSStatement)
  /-- fn, name, lb, parameter list, rb, block -/
  | JSFunctionExpression (fnA : JSAnnot) (name : JSIdent) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (body : JSBlock)
  /-- fn, *, name, lb, parameter list, rb, block -/
  | JSGeneratorExpression (fnA : JSAnnot) (starA : JSAnnot) (name : JSIdent) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (body : JSBlock)
  /-- firstpart, dot, name -/
  | JSMemberDot (expr : JSExpression) (dot : JSAnnot) (prop : JSExpression)
  /-- expr, lb, args, rb -/
  | JSMemberExpression (expr : JSExpression) (lb : JSAnnot) (args : JSCommaList JSExpression)
      (rb : JSAnnot)
  /-- new, name, lb, args, rb -/
  | JSMemberNew (annot : JSAnnot) (expr : JSExpression) (lb : JSAnnot)
      (args : JSCommaList JSExpression) (rb : JSAnnot)
  /-- firstpart, lb, expr, rb -/
  | JSMemberSquare (expr : JSExpression) (lb : JSAnnot) (idx : JSExpression) (rb : JSAnnot)
  /-- new, expr -/
  | JSNewExpression (annot : JSAnnot) (expr : JSExpression)
  /-- lbrace, contents, rbrace -/
  | JSObjectLiteral (lb : JSAnnot) (props : JSCommaTrailingList JSObjectProperty) (rb : JSAnnot)
  | JSSpreadExpression (annot : JSAnnot) (expr : JSExpression)
  /-- optional tag, lquot, head, parts -/
  | JSTemplateLiteral (tag : Option JSExpression) (lquot : JSAnnot) (head : String)
      (parts : List JSTemplatePart)
  | JSUnaryExpression (op : JSUnaryOp) (expr : JSExpression)
  /-- identifier, initializer -/
  | JSVarInitExpression (lhs : JSExpression) (init : JSVarInitializer)
  /-- yield, optional expr -/
  | JSYieldExpression (annot : JSAnnot) (expr : Option JSExpression)
  /-- yield, *, expr -/
  | JSYieldFromExpression (yieldA : JSAnnot) (starA : JSAnnot) (expr : JSExpression)

inductive JSArrowParameterList where
  | JSUnparenthesizedArrowParameter (ident : JSIdent)
  | JSParenthesizedArrowParameterList (lb : JSAnnot) (params : JSCommaList JSExpression)
      (rb : JSAnnot)

inductive JSTryCatch where
  /-- catch, lb, ident, rb, block -/
  | JSCatch (annot : JSAnnot) (lb : JSAnnot) (ident : JSExpression) (rb : JSAnnot)
      (block : JSBlock)
  /-- catch, lb, ident, if, expr, rb, block -/
  | JSCatchIf (annot : JSAnnot) (lb : JSAnnot) (ident : JSExpression) (ifA : JSAnnot)
      (cond : JSExpression) (rb : JSAnnot) (block : JSBlock)

inductive JSTryFinally where
  /-- finally, block -/
  | JSFinally (annot : JSAnnot) (block : JSBlock)
  | JSNoFinally

inductive JSBlock where
  /-- lbrace, stmts, rbrace -/
  | JSBlock (lb : JSAnnot) (stmts : List JSStatement) (rb : JSAnnot)

inductive JSSwitchParts where
  /-- case, expr, colon, stmtlist -/
  | JSCase (annot : JSAnnot) (expr : JSExpression) (colon : JSAnnot) (stmts : List JSStatement)
  /-- default, colon, stmtlist -/
  | JSDefault (annot : JSAnnot) (colon : JSAnnot) (stmts : List JSStatement)

inductive JSVarInitializer where
  /-- assignop, initializer -/
  | JSVarInit (annot : JSAnnot) (expr : JSExpression)
  | JSVarInitNone

inductive JSObjectProperty where
  /-- name, colon, value -/
  | JSPropertyNameandValue (name : JSPropertyName) (colon : JSAnnot) (value : List JSExpression)
  | JSPropertyIdentRef (annot : JSAnnot) (name : String)
  | JSObjectMethod (method : JSMethodDefinition)

inductive JSMethodDefinition where
  /-- name, lb, params, rb, block -/
  | JSMethodDefinition (name : JSPropertyName) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (block : JSBlock)
  /-- *, name, lb, params, rb, block -/
  | JSGeneratorMethodDefinition (starA : JSAnnot) (name : JSPropertyName) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (block : JSBlock)
  /-- get/set, name, lb, params, rb, block -/
  | JSPropertyAccessor (accessor : JSAccessor) (name : JSPropertyName) (lb : JSAnnot)
      (params : JSCommaList JSExpression) (rb : JSAnnot) (block : JSBlock)

inductive JSPropertyName where
  | JSPropertyIdent (annot : JSAnnot) (name : String)
  | JSPropertyString (annot : JSAnnot) (name : String)
  | JSPropertyNumber (annot : JSAnnot) (name : String)
  /-- lb, expr, rb -/
  | JSPropertyComputed (lb : JSAnnot) (expr : JSExpression) (rb : JSAnnot)

inductive JSArrayElement where
  | JSArrayElement (expr : JSExpression)
  | JSArrayComma (annot : JSAnnot)

inductive JSTemplatePart where
  /-- expr, rb, suffix -/
  | JSTemplatePart (expr : JSExpression) (rb : JSAnnot) (suffix : String)

inductive JSClassHeritage where
  | JSExtends (annot : JSAnnot) (expr : JSExpression)
  | JSExtendsNone

inductive JSClassElement where
  | JSClassInstanceMethod (method : JSMethodDefinition)
  | JSClassStaticMethod (annot : JSAnnot) (method : JSMethodDefinition)
  | JSClassSemi (annot : JSAnnot)

end

/-- The property list of an object literal. -/
abbrev JSObjectPropertyList := JSCommaTrailingList JSObjectProperty

/-! ## Default values

Lean cannot derive `Inhabited` for the mutually recursive AST types, so the
instances are given by hand; they are needed for functions defined by
general (`partial`) recursion. -/

instance : Inhabited JSExpression := ⟨.JSLiteral .JSNoAnnot ""⟩
instance : Inhabited JSStatement := ⟨.JSEmptyStatement .JSNoAnnot⟩
instance : Inhabited JSBlock := ⟨.JSBlock .JSNoAnnot [] .JSNoAnnot⟩
instance : Inhabited JSAST := ⟨.JSAstProgram [] .JSNoAnnot⟩
instance : Inhabited JSVarInitializer := ⟨.JSVarInitNone⟩
instance : Inhabited JSTryFinally := ⟨.JSNoFinally⟩
instance : Inhabited JSTryCatch :=
  ⟨.JSCatch .JSNoAnnot .JSNoAnnot default .JSNoAnnot default⟩
instance : Inhabited JSSwitchParts := ⟨.JSDefault .JSNoAnnot .JSNoAnnot []⟩
instance : Inhabited JSClassHeritage := ⟨.JSExtendsNone⟩
instance : Inhabited JSPropertyName := ⟨.JSPropertyIdent .JSNoAnnot ""⟩
instance : Inhabited JSMethodDefinition :=
  ⟨.JSMethodDefinition default .JSNoAnnot .JSLNil .JSNoAnnot default⟩
instance : Inhabited JSObjectProperty := ⟨.JSPropertyIdentRef .JSNoAnnot ""⟩
instance : Inhabited JSArrayElement := ⟨.JSArrayComma .JSNoAnnot⟩
instance : Inhabited JSTemplatePart := ⟨.JSTemplatePart default .JSNoAnnot ""⟩
instance : Inhabited JSClassElement := ⟨.JSClassSemi .JSNoAnnot⟩
instance : Inhabited JSArrowParameterList := ⟨.JSUnparenthesizedArrowParameter .JSIdentNone⟩
instance : Inhabited JSModuleItem := ⟨.JSModuleStatementListItem default⟩
instance : Inhabited JSImportDeclaration := ⟨.JSImportDeclarationBare .JSNoAnnot "" .JSSemiAuto⟩
instance : Inhabited JSImportClause := ⟨.JSImportClauseDefault .JSIdentNone⟩
instance : Inhabited JSFromClause := ⟨.JSFromClause .JSNoAnnot .JSNoAnnot ""⟩
instance : Inhabited JSImportNameSpace :=
  ⟨.JSImportNameSpace (.JSBinOpTimes .JSNoAnnot) .JSNoAnnot .JSIdentNone⟩
instance : Inhabited JSImportsNamed := ⟨.JSImportsNamed .JSNoAnnot .JSLNil .JSNoAnnot⟩
instance : Inhabited JSImportSpecifier := ⟨.JSImportSpecifier .JSIdentNone⟩
instance : Inhabited JSExportClause := ⟨.JSExportClause .JSNoAnnot .JSLNil .JSNoAnnot⟩
instance : Inhabited JSExportDeclaration := ⟨.JSExportLocals default .JSSemiAuto⟩
instance : Inhabited JSExportSpecifier := ⟨.JSExportSpecifier .JSIdentNone⟩

/-! ## Helpers -/

/-- Flatten a comma list into an ordinary list. -/
def fromCommaList {a : Type} : JSCommaList a → List a
  | .JSLCons l _ i => fromCommaList l ++ [i]
  | .JSLOne i => [i]
  | .JSLNil => []

/-- Join with commas, dropping empty strings. -/
def commaJoin (s : List String) : String :=
  String.intercalate "," (s.filter (· ≠ ""))

/-- Wrap a string in single quotes. -/
def singleQuote (s : String) : String := "'" ++ s ++ "'"

/-- Prefix with a comma if non-empty. -/
def commaIf (s : String) : String := if s == "" then "" else "," ++ s

/-! ## Show the AST elements stripped of their `JSAnnot` data.

These functions correspond to the `ShowStripped` class of the Haskell
original; since Lean has no ad hoc overloading by argument type in mutual
recursion, each instance becomes a separate function `ss<Type>`. -/

def ssIdent : JSIdent → String
  | .JSIdentName _ s => "JSIdentifier " ++ singleQuote s
  | .JSIdentNone => "JSIdentNone"

/-- `ssid` of the Haskell original: the name of an identifier, quoted. -/
def ssid : JSIdent → String
  | .JSIdentName _ s => singleQuote s
  | .JSIdentNone => "''"

def ssBinOp : JSBinOp → String
  | .JSBinOpAnd _ => "'&&'"
  | .JSBinOpBitAnd _ => "'&'"
  | .JSBinOpBitOr _ => "'|'"
  | .JSBinOpBitXor _ => "'^'"
  | .JSBinOpDivide _ => "'/'"
  | .JSBinOpEq _ => "'=='"
  | .JSBinOpGe _ => "'>='"
  | .JSBinOpGt _ => "'>'"
  | .JSBinOpIn _ => "'in'"
  | .JSBinOpInstanceOf _ => "'instanceof'"
  | .JSBinOpLe _ => "'<='"
  | .JSBinOpLsh _ => "'<<'"
  | .JSBinOpLt _ => "'<'"
  | .JSBinOpMinus _ => "'-'"
  | .JSBinOpMod _ => "'%'"
  | .JSBinOpNeq _ => "'!='"
  | .JSBinOpOf _ => "'of'"
  | .JSBinOpOr _ => "'||'"
  | .JSBinOpPlus _ => "'+'"
  | .JSBinOpRsh _ => "'>>'"
  | .JSBinOpStrictEq _ => "'==='"
  | .JSBinOpStrictNeq _ => "'!=='"
  | .JSBinOpTimes _ => "'*'"
  | .JSBinOpUrsh _ => "'>>>'"

def ssUnaryOp : JSUnaryOp → String
  | .JSUnaryOpDecr _ => "'--'"
  | .JSUnaryOpDelete _ => "'delete'"
  | .JSUnaryOpIncr _ => "'++'"
  | .JSUnaryOpMinus _ => "'-'"
  | .JSUnaryOpNot _ => "'!'"
  | .JSUnaryOpPlus _ => "'+'"
  | .JSUnaryOpTilde _ => "'~'"
  | .JSUnaryOpTypeof _ => "'typeof'"
  | .JSUnaryOpVoid _ => "'void'"

def ssAssignOp : JSAssignOp → String
  | .JSAssign _ => "'='"
  | .JSTimesAssign _ => "'*='"
  | .JSDivideAssign _ => "'/='"
  | .JSModAssign _ => "'%='"
  | .JSPlusAssign _ => "'+='"
  | .JSMinusAssign _ => "'-='"
  | .JSLshAssign _ => "'<<='"
  | .JSRshAssign _ => "'>>='"
  | .JSUrshAssign _ => "'>>>='"
  | .JSBwAndAssign _ => "'&='"
  | .JSBwXorAssign _ => "'^='"
  | .JSBwOrAssign _ => "'|='"

def ssAccessor : JSAccessor → String
  | .JSAccessorGet _ => "JSAccessorGet"
  | .JSAccessorSet _ => "JSAccessorSet"

def ssSemi : JSSemi → String
  | .JSSemi _ => "JSSemicolon"
  | .JSSemiAuto => ""

set_option maxHeartbeats 2000000 in
mutual

def ssStatement : JSStatement → String
  | .JSStatementBlock _ xs _ _ => "JSStatementBlock " ++ ssStatements xs
  | .JSBreak _ .JSIdentNone s => "JSBreak" ++ commaIf (ssSemi s)
  | .JSBreak _ (.JSIdentName _ n) s => "JSBreak " ++ singleQuote n ++ commaIf (ssSemi s)
  | .JSClass _ n h _ xs _ _ =>
      "JSClass " ++ ssid n ++ " (" ++ ssClassHeritage h ++ ") " ++ ssClassElements xs
  | .JSContinue _ .JSIdentNone s => "JSContinue" ++ commaIf (ssSemi s)
  | .JSContinue _ (.JSIdentName _ n) s => "JSContinue " ++ singleQuote n ++ commaIf (ssSemi s)
  | .JSConstant _ xs _ => "JSConstant " ++ ssExprCommaList xs
  | .JSDoWhile _ x1 _ _ x2 _ x3 =>
      "JSDoWhile (" ++ ssStatement x1 ++ ") (" ++ ssExpression x2 ++ ") (" ++ ssSemi x3 ++ ")"
  | .JSFor _ _ x1s _ x2s _ x3s _ x4 =>
      "JSFor " ++ ssExprCommaList x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForIn _ _ x1s _ x2 _ x3 =>
      "JSForIn " ++ ssExpression x1s ++ " (" ++ ssExpression x2 ++ ") (" ++ ssStatement x3 ++ ")"
  | .JSForVar _ _ _ x1s _ x2s _ x3s _ x4 =>
      "JSForVar " ++ ssExprCommaList x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForVarIn _ _ _ x1 _ x2 _ x3 =>
      "JSForVarIn (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForLet _ _ _ x1s _ x2s _ x3s _ x4 =>
      "JSForLet " ++ ssExprCommaList x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForLetIn _ _ _ x1 _ x2 _ x3 =>
      "JSForLetIn (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForLetOf _ _ _ x1 _ x2 _ x3 =>
      "JSForLetOf (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForConst _ _ _ x1s _ x2s _ x3s _ x4 =>
      "JSForConst " ++ ssExprCommaList x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForConstIn _ _ _ x1 _ x2 _ x3 =>
      "JSForConstIn (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForConstOf _ _ _ x1 _ x2 _ x3 =>
      "JSForConstOf (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForOf _ _ x1s _ x2 _ x3 =>
      "JSForOf " ++ ssExpression x1s ++ " (" ++ ssExpression x2 ++ ") (" ++ ssStatement x3 ++ ")"
  | .JSForVarOf _ _ _ x1 _ x2 _ x3 =>
      "JSForVarOf (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSAsyncFunction _ _ n _ pl _ x3 _ =>
      "JSAsyncFunction " ++ ssid n ++ " " ++ ssExprCommaList pl ++ " (" ++ ssBlock x3 ++ ")"
  | .JSFunction _ n _ pl _ x3 _ =>
      "JSFunction " ++ ssid n ++ " " ++ ssExprCommaList pl ++ " (" ++ ssBlock x3 ++ ")"
  | .JSGenerator _ _ n _ pl _ x3 _ =>
      "JSGenerator " ++ ssid n ++ " " ++ ssExprCommaList pl ++ " (" ++ ssBlock x3 ++ ")"
  | .JSIf _ _ x1 _ x2 => "JSIf (" ++ ssExpression x1 ++ ") (" ++ ssStatement x2 ++ ")"
  | .JSIfElse _ _ x1 _ x2 _ x3 =>
      "JSIfElse (" ++ ssExpression x1 ++ ") (" ++ ssStatement x2 ++ ") (" ++ ssStatement x3 ++ ")"
  | .JSLabelled x1 _ x2 => "JSLabelled (" ++ ssIdent x1 ++ ") (" ++ ssStatement x2 ++ ")"
  | .JSLet _ xs _ => "JSLet " ++ ssExprCommaList xs
  | .JSEmptyStatement _ => "JSEmptyStatement"
  | .JSExpressionStatement l s => ssExpression l ++ commaIf (ssSemi s)
  | .JSAssignStatement lhs op rhs s =>
      "JSOpAssign (" ++ ssAssignOp op ++ "," ++ ssExpression lhs ++ "," ++ ssExpression rhs
        ++ (let x := ssSemi s; if x ≠ "" then ")," ++ x else ")")
  | .JSMethodCall e _ a _ s =>
      "JSMethodCall (" ++ ssExpression e ++ ",JSArguments " ++ ssExprCommaList a
        ++ (let x := ssSemi s; if x ≠ "" then ")," ++ x else ")")
  | .JSReturn _ (some me) s => "JSReturn " ++ ssExpression me ++ " " ++ ssSemi s
  | .JSReturn _ none s => "JSReturn " ++ ssSemi s
  | .JSSwitch _ _ x _ _ x2 _ _ => "JSSwitch (" ++ ssExpression x ++ ") " ++ ssSwitchParts x2
  | .JSThrow _ x _ => "JSThrow (" ++ ssExpression x ++ ")"
  | .JSTry _ xt1 xtc xtf =>
      "JSTry (" ++ ssBlock xt1 ++ "," ++ ssTryCatches xtc ++ "," ++ ssTryFinally xtf ++ ")"
  | .JSVariable _ xs _ => "JSVariable " ++ ssExprCommaList xs
  | .JSWhile _ _ x1 _ x2 => "JSWhile (" ++ ssExpression x1 ++ ") (" ++ ssStatement x2 ++ ")"
  | .JSWith _ _ x1 _ x _ => "JSWith (" ++ ssExpression x1 ++ ") (" ++ ssStatement x ++ ")"

def ssExpression : JSExpression → String
  | .JSArrayLiteral _ xs _ => "JSArrayLiteral " ++ ssArrayElements xs
  | .JSAssignExpression lhs op rhs =>
      "JSOpAssign (" ++ ssAssignOp op ++ "," ++ ssExpression lhs ++ "," ++ ssExpression rhs ++ ")"
  | .JSAwaitExpression _ e => "JSAwaitExpresson " ++ ssExpression e
  | .JSCallExpression ex _ xs _ =>
      "JSCallExpression (" ++ ssExpression ex ++ ",JSArguments " ++ ssExprCommaList xs ++ ")"
  | .JSCallExpressionDot ex _ xs =>
      "JSCallExpressionDot (" ++ ssExpression ex ++ "," ++ ssExpression xs ++ ")"
  | .JSCallExpressionSquare ex _ xs _ =>
      "JSCallExpressionSquare (" ++ ssExpression ex ++ "," ++ ssExpression xs ++ ")"
  | .JSClassExpression _ n h _ xs _ =>
      "JSClassExpression " ++ ssid n ++ " (" ++ ssClassHeritage h ++ ") " ++ ssClassElements xs
  | .JSDecimal _ s => "JSDecimal " ++ singleQuote s
  | .JSCommaExpression l _ r => "JSExpression [" ++ ssExpression l ++ "," ++ ssExpression r ++ "]"
  | .JSExpressionBinary x2 op x3 =>
      "JSExpressionBinary (" ++ ssBinOp op ++ "," ++ ssExpression x2 ++ "," ++ ssExpression x3
        ++ ")"
  | .JSExpressionParen _ x _ => "JSExpressionParen (" ++ ssExpression x ++ ")"
  | .JSExpressionPostfix xs op =>
      "JSExpressionPostfix (" ++ ssUnaryOp op ++ "," ++ ssExpression xs ++ ")"
  | .JSExpressionTernary x1 _ x2 _ x3 =>
      "JSExpressionTernary (" ++ ssExpression x1 ++ "," ++ ssExpression x2 ++ ","
        ++ ssExpression x3 ++ ")"
  | .JSArrowExpression ps _ e =>
      "JSArrowExpression (" ++ ssArrowParameterList ps ++ ") => " ++ ssStatement e
  | .JSFunctionExpression _ n _ pl _ x3 =>
      "JSFunctionExpression " ++ ssid n ++ " " ++ ssExprCommaList pl ++ " (" ++ ssBlock x3 ++ ")"
  | .JSGeneratorExpression _ _ n _ pl _ x3 =>
      "JSGeneratorExpression " ++ ssid n ++ " " ++ ssExprCommaList pl ++ " (" ++ ssBlock x3 ++ ")"
  | .JSHexInteger _ s => "JSHexInteger " ++ singleQuote s
  | .JSOctal _ s => "JSOctal " ++ singleQuote s
  | .JSIdentifier _ s => "JSIdentifier " ++ singleQuote s
  | .JSLiteral _ s => "JSLiteral " ++ singleQuote s
  | .JSMemberDot x1s _ x2 => "JSMemberDot (" ++ ssExpression x1s ++ "," ++ ssExpression x2 ++ ")"
  | .JSMemberExpression e _ a _ =>
      "JSMemberExpression (" ++ ssExpression e ++ ",JSArguments " ++ ssExprCommaList a ++ ")"
  | .JSMemberNew _ n _ s _ =>
      "JSMemberNew (" ++ ssExpression n ++ ",JSArguments " ++ ssExprCommaList s ++ ")"
  | .JSMemberSquare x1s _ x2 _ =>
      "JSMemberSquare (" ++ ssExpression x1s ++ "," ++ ssExpression x2 ++ ")"
  | .JSNewExpression _ e => "JSNewExpression " ++ ssExpression e
  | .JSObjectLiteral _ xs _ => "JSObjectLiteral " ++ ssObjectPropertyList xs
  | .JSRegEx _ s => "JSRegEx " ++ singleQuote s
  | .JSStringLiteral _ s => "JSStringLiteral " ++ s
  | .JSUnaryExpression op x =>
      "JSUnaryExpression (" ++ ssUnaryOp op ++ "," ++ ssExpression x ++ ")"
  | .JSVarInitExpression x1 x2 =>
      "JSVarInitExpression (" ++ ssExpression x1 ++ ") " ++ ssVarInitializer x2
  | .JSYieldExpression _ none => "JSYieldExpression ()"
  | .JSYieldExpression _ (some x) => "JSYieldExpression (" ++ ssExpression x ++ ")"
  | .JSYieldFromExpression _ _ x => "JSYieldFromExpression (" ++ ssExpression x ++ ")"
  | .JSSpreadExpression _ x1 => "JSSpreadExpression (" ++ ssExpression x1 ++ ")"
  | .JSTemplateLiteral none _ s ps =>
      "JSTemplateLiteral (()," ++ singleQuote s ++ "," ++ ssTemplateParts ps ++ ")"
  | .JSTemplateLiteral (some t) _ s ps =>
      "JSTemplateLiteral ((" ++ ssExpression t ++ ")," ++ singleQuote s ++ ","
        ++ ssTemplateParts ps ++ ")"

def ssArrowParameterList : JSArrowParameterList → String
  | .JSUnparenthesizedArrowParameter x => ssIdent x
  | .JSParenthesizedArrowParameterList _ xs _ => ssExprCommaList xs

def ssBlock : JSBlock → String
  | .JSBlock _ xs _ => "JSBlock " ++ ssStatements xs

def ssTryCatch : JSTryCatch → String
  | .JSCatch _ _ x1 _ x3 => "JSCatch (" ++ ssExpression x1 ++ "," ++ ssBlock x3 ++ ")"
  | .JSCatchIf _ _ x1 _ ex _ x3 =>
      "JSCatch (" ++ ssExpression x1 ++ ") if " ++ ssExpression ex ++ " (" ++ ssBlock x3 ++ ")"

def ssTryFinally : JSTryFinally → String
  | .JSFinally _ x => "JSFinally (" ++ ssBlock x ++ ")"
  | .JSNoFinally => "JSFinally ()"

def ssSwitchPart : JSSwitchParts → String
  | .JSCase _ x1 _ x2s => "JSCase (" ++ ssExpression x1 ++ ") (" ++ ssStatements x2s ++ ")"
  | .JSDefault _ _ xs => "JSDefault (" ++ ssStatements xs ++ ")"

def ssVarInitializer : JSVarInitializer → String
  | .JSVarInit _ n => "[" ++ ssExpression n ++ "]"
  | .JSVarInitNone => ""

def ssObjectProperty : JSObjectProperty → String
  | .JSPropertyNameandValue x1 _ x2s =>
      "JSPropertyNameandValue (" ++ ssPropertyName x1 ++ ") " ++ ssExpressions x2s
  | .JSPropertyIdentRef _ s => "JSPropertyIdentRef " ++ singleQuote s
  | .JSObjectMethod m => ssMethodDefinition m

def ssMethodDefinition : JSMethodDefinition → String
  | .JSMethodDefinition x1 _ x2s _ x3 =>
      "JSMethodDefinition (" ++ ssPropertyName x1 ++ ") " ++ ssExprCommaList x2s ++ " ("
        ++ ssBlock x3 ++ ")"
  | .JSGeneratorMethodDefinition _ x1 _ x2s _ x3 =>
      "JSGeneratorMethodDefinition (" ++ ssPropertyName x1 ++ ") " ++ ssExprCommaList x2s
        ++ " (" ++ ssBlock x3 ++ ")"
  | .JSPropertyAccessor s x1 _ x2s _ x3 =>
      "JSPropertyAccessor " ++ ssAccessor s ++ " (" ++ ssPropertyName x1 ++ ") "
        ++ ssExprCommaList x2s ++ " (" ++ ssBlock x3 ++ ")"

def ssPropertyName : JSPropertyName → String
  | .JSPropertyIdent _ s => "JSIdentifier " ++ singleQuote s
  | .JSPropertyString _ s => "JSIdentifier " ++ singleQuote s
  | .JSPropertyNumber _ s => "JSIdentifier " ++ singleQuote s
  | .JSPropertyComputed _ x _ => "JSPropertyComputed (" ++ ssExpression x ++ ")"

def ssArrayElement : JSArrayElement → String
  | .JSArrayElement e => ssExpression e
  | .JSArrayComma _ => "JSComma"

def ssTemplatePart : JSTemplatePart → String
  | .JSTemplatePart e _ s => "(" ++ ssExpression e ++ "," ++ singleQuote s ++ ")"

def ssClassHeritage : JSClassHeritage → String
  | .JSExtendsNone => ""
  | .JSExtends _ x => ssExpression x

def ssClassElement : JSClassElement → String
  | .JSClassInstanceMethod m => ssMethodDefinition m
  | .JSClassStaticMethod _ m => "JSClassStaticMethod (" ++ ssMethodDefinition m ++ ")"
  | .JSClassSemi _ => "JSClassSemi"

def ssModuleItem : JSModuleItem → String
  | .JSModuleExportDeclaration _ x1 =>
      "JSModuleExportDeclaration (" ++ ssExportDeclaration x1 ++ ")"
  | .JSModuleImportDeclaration _ x1 =>
      "JSModuleImportDeclaration (" ++ ssImportDeclaration x1 ++ ")"
  | .JSModuleStatementListItem x1 => "JSModuleStatementListItem (" ++ ssStatement x1 ++ ")"

def ssImportDeclaration : JSImportDeclaration → String
  | .JSImportDeclaration imp from_ _ =>
      "JSImportDeclaration (" ++ ssImportClause imp ++ "," ++ ssFromClause from_ ++ ")"
  | .JSImportDeclarationBare _ m _ => "JSImportDeclarationBare (" ++ singleQuote m ++ ")"

def ssImportClause : JSImportClause → String
  | .JSImportClauseDefault x => "JSImportClauseDefault (" ++ ssIdent x ++ ")"
  | .JSImportClauseNameSpace x => "JSImportClauseNameSpace (" ++ ssImportNameSpace x ++ ")"
  | .JSImportClauseNamed x => "JSImportClauseNameSpace (" ++ ssImportsNamed x ++ ")"
  | .JSImportClauseDefaultNameSpace x1 _ x2 =>
      "JSImportClauseDefaultNameSpace (" ++ ssIdent x1 ++ "," ++ ssImportNameSpace x2 ++ ")"
  | .JSImportClauseDefaultNamed x1 _ x2 =>
      "JSImportClauseDefaultNamed (" ++ ssIdent x1 ++ "," ++ ssImportsNamed x2 ++ ")"

def ssFromClause : JSFromClause → String
  | .JSFromClause _ _ m => "JSFromClause " ++ singleQuote m

def ssImportNameSpace : JSImportNameSpace → String
  | .JSImportNameSpace _ _ x => "JSImportNameSpace (" ++ ssIdent x ++ ")"

def ssImportsNamed : JSImportsNamed → String
  | .JSImportsNamed _ xs _ => "JSImportsNamed (" ++ ssImportSpecCommaList xs ++ ")"

def ssImportSpecifier : JSImportSpecifier → String
  | .JSImportSpecifier x1 => "JSImportSpecifier (" ++ ssIdent x1 ++ ")"
  | .JSImportSpecifierAs x1 _ x2 =>
      "JSImportSpecifierAs (" ++ ssIdent x1 ++ "," ++ ssIdent x2 ++ ")"

def ssExportDeclaration : JSExportDeclaration → String
  | .JSExportFrom xs from_ _ =>
      "JSExportFrom (" ++ ssExportClause xs ++ "," ++ ssFromClause from_ ++ ")"
  | .JSExportLocals xs _ => "JSExportLocals (" ++ ssExportClause xs ++ ")"
  | .JSExport x1 _ => "JSExport (" ++ ssStatement x1 ++ ")"

def ssExportClause : JSExportClause → String
  | .JSExportClause _ xs _ => "JSExportClause (" ++ ssExportSpecCommaList xs ++ ")"

def ssExportSpecifier : JSExportSpecifier → String
  | .JSExportSpecifier x1 => "JSExportSpecifier (" ++ ssIdent x1 ++ ")"
  | .JSExportSpecifierAs x1 _ x2 =>
      "JSExportSpecifierAs (" ++ ssIdent x1 ++ "," ++ ssIdent x2 ++ ")"

-- Helpers rendering the various list shapes.

def ssStatementsAux : List JSStatement → List String
  | [] => []
  | x :: xs => ssStatement x :: ssStatementsAux xs

def ssStatements (xs : List JSStatement) : String :=
  "[" ++ commaJoin (ssStatementsAux xs) ++ "]"

def ssExpressionsAux : List JSExpression → List String
  | [] => []
  | x :: xs => ssExpression x :: ssExpressionsAux xs

def ssExpressions (xs : List JSExpression) : String :=
  "[" ++ commaJoin (ssExpressionsAux xs) ++ "]"

def ssExprCommaListAux : JSCommaList JSExpression → List String
  | .JSLCons l _ i => ssExprCommaListAux l ++ [ssExpression i]
  | .JSLOne i => [ssExpression i]
  | .JSLNil => []

def ssExprCommaList (xs : JSCommaList JSExpression) : String :=
  "(" ++ commaJoin (ssExprCommaListAux xs) ++ ")"

def ssImportSpecCommaListAux : JSCommaList JSImportSpecifier → List String
  | .JSLCons l _ i => ssImportSpecCommaListAux l ++ [ssImportSpecifier i]
  | .JSLOne i => [ssImportSpecifier i]
  | .JSLNil => []

def ssImportSpecCommaList (xs : JSCommaList JSImportSpecifier) : String :=
  "(" ++ commaJoin (ssImportSpecCommaListAux xs) ++ ")"

def ssExportSpecCommaListAux : JSCommaList JSExportSpecifier → List String
  | .JSLCons l _ i => ssExportSpecCommaListAux l ++ [ssExportSpecifier i]
  | .JSLOne i => [ssExportSpecifier i]
  | .JSLNil => []

def ssExportSpecCommaList (xs : JSCommaList JSExportSpecifier) : String :=
  "(" ++ commaJoin (ssExportSpecCommaListAux xs) ++ ")"

def ssObjectPropertyCommaListAux : JSCommaList JSObjectProperty → List String
  | .JSLCons l _ i => ssObjectPropertyCommaListAux l ++ [ssObjectProperty i]
  | .JSLOne i => [ssObjectProperty i]
  | .JSLNil => []

def ssObjectPropertyList : JSCommaTrailingList JSObjectProperty → String
  | .JSCTLComma xs _ => "[" ++ commaJoin (ssObjectPropertyCommaListAux xs) ++ ",JSComma]"
  | .JSCTLNone xs => "[" ++ commaJoin (ssObjectPropertyCommaListAux xs) ++ "]"

def ssArrayElementsAux : List JSArrayElement → List String
  | [] => []
  | x :: xs => ssArrayElement x :: ssArrayElementsAux xs

def ssArrayElements (xs : List JSArrayElement) : String :=
  "[" ++ commaJoin (ssArrayElementsAux xs) ++ "]"

def ssClassElementsAux : List JSClassElement → List String
  | [] => []
  | x :: xs => ssClassElement x :: ssClassElementsAux xs

def ssClassElements (xs : List JSClassElement) : String :=
  "[" ++ commaJoin (ssClassElementsAux xs) ++ "]"

def ssTemplatePartsAux : List JSTemplatePart → List String
  | [] => []
  | x :: xs => ssTemplatePart x :: ssTemplatePartsAux xs

def ssTemplateParts (xs : List JSTemplatePart) : String :=
  "[" ++ commaJoin (ssTemplatePartsAux xs) ++ "]"

def ssSwitchPartsAux : List JSSwitchParts → List String
  | [] => []
  | x :: xs => ssSwitchPart x :: ssSwitchPartsAux xs

def ssSwitchParts (xs : List JSSwitchParts) : String :=
  "[" ++ commaJoin (ssSwitchPartsAux xs) ++ "]"

def ssTryCatchesAux : List JSTryCatch → List String
  | [] => []
  | x :: xs => ssTryCatch x :: ssTryCatchesAux xs

def ssTryCatches (xs : List JSTryCatch) : String :=
  "[" ++ commaJoin (ssTryCatchesAux xs) ++ "]"

def ssModuleItemsAux : List JSModuleItem → List String
  | [] => []
  | x :: xs => ssModuleItem x :: ssModuleItemsAux xs

def ssModuleItems (xs : List JSModuleItem) : String :=
  "[" ++ commaJoin (ssModuleItemsAux xs) ++ "]"

end

/-- Show the AST stripped of its `JSAnnot` data. -/
def showStripped : JSAST → String
  | .JSAstProgram xs _ => "JSAstProgram " ++ ssStatements xs
  | .JSAstModule xs _ => "JSAstModule " ++ ssModuleItems xs
  | .JSAstStatement s _ => "JSAstStatement (" ++ ssStatement s ++ ")"
  | .JSAstExpression e _ => "JSAstExpression (" ++ ssExpression e ++ ")"
  | .JSAstLiteral s _ => "JSAstLiteral (" ++ ssExpression s ++ ")"

/-! ## Comparison of binary operators, ignoring annotations. -/

/-- Replace the annotation of a binary operator by `JSNoAnnot`. -/
def deAnnot : JSBinOp → JSBinOp
  | .JSBinOpAnd _ => .JSBinOpAnd .JSNoAnnot
  | .JSBinOpBitAnd _ => .JSBinOpBitAnd .JSNoAnnot
  | .JSBinOpBitOr _ => .JSBinOpBitOr .JSNoAnnot
  | .JSBinOpBitXor _ => .JSBinOpBitXor .JSNoAnnot
  | .JSBinOpDivide _ => .JSBinOpDivide .JSNoAnnot
  | .JSBinOpEq _ => .JSBinOpEq .JSNoAnnot
  | .JSBinOpGe _ => .JSBinOpGe .JSNoAnnot
  | .JSBinOpGt _ => .JSBinOpGt .JSNoAnnot
  | .JSBinOpIn _ => .JSBinOpIn .JSNoAnnot
  | .JSBinOpInstanceOf _ => .JSBinOpInstanceOf .JSNoAnnot
  | .JSBinOpLe _ => .JSBinOpLe .JSNoAnnot
  | .JSBinOpLsh _ => .JSBinOpLsh .JSNoAnnot
  | .JSBinOpLt _ => .JSBinOpLt .JSNoAnnot
  | .JSBinOpMinus _ => .JSBinOpMinus .JSNoAnnot
  | .JSBinOpMod _ => .JSBinOpMod .JSNoAnnot
  | .JSBinOpNeq _ => .JSBinOpNeq .JSNoAnnot
  | .JSBinOpOf _ => .JSBinOpOf .JSNoAnnot
  | .JSBinOpOr _ => .JSBinOpOr .JSNoAnnot
  | .JSBinOpPlus _ => .JSBinOpPlus .JSNoAnnot
  | .JSBinOpRsh _ => .JSBinOpRsh .JSNoAnnot
  | .JSBinOpStrictEq _ => .JSBinOpStrictEq .JSNoAnnot
  | .JSBinOpStrictNeq _ => .JSBinOpStrictNeq .JSNoAnnot
  | .JSBinOpTimes _ => .JSBinOpTimes .JSNoAnnot
  | .JSBinOpUrsh _ => .JSBinOpUrsh .JSNoAnnot

/-- Compare two binary operators, ignoring their annotations. -/
def binOpEq (a b : JSBinOp) : Bool := deAnnot a == deAnnot b

end LanguageJavaScript.Parser.AST
