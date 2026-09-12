/-
Port of `Language.JavaScript.Parser.AST` to Lean 4.

The constructor names are kept identical to the Haskell original so that the
two versions can be read side by side.  Types which are not mutually
recursive with the expression/statement grammar are defined first; the rest
live in one big `mutual` block.

**Refined types.**  Where the Haskell original uses `String` for something
that can never be empty — a name, a numeric literal, the text of a keyword
— this port uses the types of `Language.JavaScript.Types`: `NEString` for a
name, `JSKeywordLiteral` for `this`/`null`/`true`/`false`/`super`/
`debugger`.  Every node with a single shape which is not part of the
recursive knot is a `structure` rather than a one constructor inductive;
the constructor keeps the name it had, so `.JSFromClause a b c` still reads
the same.

**Literals.**  This tree keeps the whitespace and the comments of the
input, so `Pretty.renderToString` reproduces the *layout* of the source;
it does not reproduce the exact spelling of a number or of a regular
expression, which is printed canonically instead — `0X1f` comes back as
`0x1f`, `070` as `0o70`, `1.50` as `1.5`.  A numeric literal is therefore a
`JSNumber` (`JSNumberLit`, one constructor: the base is part of the value)
and a regular expression literal is a `RegExpLit`, exactly as in the other
two trees, so `JSDecimal "potato"` cannot even be written.  A string
literal is a `JSStringSrc`, the quote it is written with together with the
source text between the quotes, so it can be neither unterminated nor
closed by the wrong quote, and the escapes the source wrote are kept.
`JSExpression.numberValue?` and `JSExpression.regexValue?` give the value
of a literal node.

A template literal keeps its chunks *without* their delimiters: the tree
records the text, and which of `` ` ``, `${` and `}` surrounds it follows
from the shape of the node (`templateHeadSpelling`,
`templatePartSpelling`).
-/
import LanguageJavascript.Token
import LanguageJavascript.Types

namespace Language.JavaScript.Parser.AST

open Language.JavaScript.Parser

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
  /-- `??`, the nullish coalescing operator. -/
  | JSBinOpNullish (annot : JSAnnot)
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
  /-- `&&=` -/
  | JSLogicalAndAssign (annot : JSAnnot)
  /-- `||=` -/
  | JSLogicalOrAssign (annot : JSAnnot)
  /-- `??=` -/
  | JSNullishAssign (annot : JSAnnot)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Accessors for `JSObjectProperty`: either 'get' or 'set'. -/
inductive JSAccessor where
  | JSAccessorGet (annot : JSAnnot)
  | JSAccessorSet (annot : JSAnnot)
deriving Repr, BEq, DecidableEq, Inhabited

/-- A literal written as a keyword.  The Haskell original stores the text
of the keyword in a `String`; an enumeration cannot describe a keyword that
does not exist. -/
inductive JSKeywordLiteral where
  | this_
  | super
  | null
  | true_
  | false_
  | debugger
deriving Repr, BEq, DecidableEq, Inhabited

namespace JSKeywordLiteral

/-- The keyword, as it is written. -/
def text : JSKeywordLiteral → NEString
  | .this_ => ⟨"this", by decide⟩
  | .super => ⟨"super", by decide⟩
  | .null => ⟨"null", by decide⟩
  | .true_ => ⟨"true", by decide⟩
  | .false_ => ⟨"false", by decide⟩
  | .debugger => ⟨"debugger", by decide⟩

/-- The keyword written `s`, if there is one. -/
def ofString? : String → Option JSKeywordLiteral
  | "this" => some .this_
  | "super" => some .super
  | "null" => some .null
  | "true" => some .true_
  | "false" => some .false_
  | "debugger" => some .debugger
  | _ => none

end JSKeywordLiteral

inductive JSIdent where
  | JSIdentName (annot : JSAnnot) (name : NEString)
  | JSIdentNone
deriving Repr, BEq, DecidableEq, Inhabited

/-- A comma separated list. -/
inductive JSCommaList (a : Type) where
  /-- head, comma, element -/
  | JSLCons (init : JSCommaList a) (annot : JSAnnot) (last : a)
  /-- single element (no comma) -/
  | JSLOne (x : a)
  | JSLNil
deriving Repr, BEq, DecidableEq, Inhabited

/-- A comma separated list which has at least one element.

The grammar does not allow the declarators of a `var`, `let` or `const` to
be empty — `var;` is not a statement — so those lists are a `JSCommaList1`
rather than a `JSCommaList`, and the empty one cannot be written down. -/
inductive JSCommaList1 (a : Type) where
  /-- head, comma, element -/
  | JSL1Cons (init : JSCommaList1 a) (annot : JSAnnot) (last : a)
  /-- single element (no comma) -/
  | JSL1One (x : a)
deriving Repr, BEq, Inhabited

/-- A comma separated list which may have a trailing comma. -/
inductive JSCommaTrailingList (a : Type) where
  /-- list, trailing comma -/
  | JSCTLComma (xs : JSCommaList a) (annot : JSAnnot)
  /-- list -/
  | JSCTLNone (xs : JSCommaList a)
deriving Repr, BEq, Inhabited

/-! ## Imports and exports

An `import` declaration and everything inside it, and the *clause* of an
`export` declaration, do not mention a statement or an expression, so they
are not part of the recursive knot below.  Each of them that has a single
shape is a `structure`; the constructor keeps its name, so that
`.JSFromClause f a m` still builds one and still matches one. -/

/-- Note that this data type is separate from `JSExportSpecifier` because the
grammar is slightly different (e.g. in handling of reserved words). -/
inductive JSImportSpecifier where
  | JSImportSpecifier (ident : JSIdent)
  /-- ident, as, ident -/
  | JSImportSpecifierAs (ident : JSIdent) (annot : JSAnnot) (as_ : JSIdent)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Named imports, e.g. `{ foo, bar, baz as quux }`. -/
structure JSImportsNamed where
  JSImportsNamed ::
  /-- The `{`. -/
  lb : JSAnnot
  /-- The specifiers. -/
  specs : JSCommaList JSImportSpecifier
  /-- The `}`. -/
  rb : JSAnnot
deriving Repr, BEq, Inhabited

/-- Import namespace, e.g. `* as whatever`. -/
structure JSImportNameSpace where
  JSImportNameSpace ::
  /-- The `*`. -/
  star : JSBinOp
  /-- The `as`. -/
  annot : JSAnnot
  /-- The local name. -/
  ident : JSIdent
deriving Repr, BEq, DecidableEq, Inhabited

/-- One entry of an import attributes clause, `type: "json"`.  The key is
an identifier name or a string literal, the value is always a string
literal; both are kept as they are written. -/
structure JSImportAttribute where
  JSImportAttribute ::
  /-- The key. -/
  keyAnnot : JSAnnot
  /-- The key, as it is written: an identifier name, or a string literal
  with its quotes. -/
  key : NEString
  /-- The `:`. -/
  colon : JSAnnot
  /-- The value. -/
  valueAnnot : JSAnnot
  /-- The value, a string literal with its quotes. -/
  value : NEString
deriving Repr, BEq, DecidableEq, Inhabited

/-- The `with { type: "json" }` of an `import` or of an `export ... from`
declaration. -/
structure JSImportAttributes where
  JSImportAttributes ::
  /-- The `with`. -/
  withA : JSAnnot
  /-- The `{`. -/
  lb : JSAnnot
  /-- The attributes. -/
  attrs : JSCommaList JSImportAttribute
  /-- The `}`. -/
  rb : JSAnnot
deriving Repr, BEq, DecidableEq, Inhabited

/-- `from "mod"`, with the import attributes which may follow it. -/
structure JSFromClause where
  JSFromClause ::
  /-- The `from`. -/
  from_ : JSAnnot
  /-- The string literal. -/
  annot : JSAnnot
  /-- The contents of the string literal. -/
  mod : NEString
  /-- The `with { ... }` clause, when the declaration has one. -/
  attrs : Option JSImportAttributes := none
deriving Repr, BEq, DecidableEq, Inhabited

inductive JSImportClause where
  | JSImportClauseDefault (ident : JSIdent)
  | JSImportClauseNameSpace (ns : JSImportNameSpace)
  | JSImportClauseNamed (named : JSImportsNamed)
  /-- default, comma, namespace -/
  | JSImportClauseDefaultNameSpace (ident : JSIdent) (annot : JSAnnot) (ns : JSImportNameSpace)
  /-- default, comma, named imports -/
  | JSImportClauseDefaultNamed (ident : JSIdent) (annot : JSAnnot) (named : JSImportsNamed)
deriving Repr, BEq, Inhabited

inductive JSImportDeclaration where
  /-- imports, module, semi -/
  | JSImportDeclaration (clause : JSImportClause) (from_ : JSFromClause) (semi : JSSemi)
  /-- `import "mod" with { ... };`: module, attributes, semi -/
  | JSImportDeclarationBare (annot : JSAnnot) (mod : NEString)
      (attrs : Option JSImportAttributes) (semi : JSSemi)
deriving Repr, BEq, Inhabited

inductive JSExportSpecifier where
  | JSExportSpecifier (ident : JSIdent)
  /-- ident1, as, ident2 -/
  | JSExportSpecifierAs (ident : JSIdent) (annot : JSAnnot) (as_ : JSIdent)
deriving Repr, BEq, DecidableEq, Inhabited

/-- `{ foo, bar as baz }` of an `export` declaration. -/
structure JSExportClause where
  JSExportClause ::
  /-- The `{`. -/
  lb : JSAnnot
  /-- The specifiers. -/
  specs : JSCommaList JSExportSpecifier
  /-- The `}`. -/
  rb : JSAnnot
deriving Repr, BEq, Inhabited

/-! ## The syntax tree

`JSBlock` and `JSTemplatePart` also have a single shape, but they are part
of the knot below and Lean has no `mutual` block containing a `structure`,
so they stay one constructor inductives. -/

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

inductive JSExportDeclaration where
  /-- exports, module, semi -/
  | JSExportFrom (clause : JSExportClause) (from_ : JSFromClause) (semi : JSSemi)
  /-- exports, autosemi -/
  | JSExportLocals (clause : JSExportClause) (semi : JSSemi)
  /-- `export * from "mod";`: `*`, from clause, autosemi -/
  | JSExportAll (star : JSAnnot) (from_ : JSFromClause) (semi : JSSemi)
  /-- `export * as ns from "mod";`: `*`, `as`, the name, from clause,
  autosemi -/
  | JSExportAllAs (star : JSAnnot) (asA : JSAnnot) (ident : JSIdent)
      (from_ : JSFromClause) (semi : JSSemi)
  /-- `export default <expression>;`: `default`, the expression, autosemi.
  `export default function f () {}` and `export default class A {}` are
  this node too, the body being a function respectively a class
  expression. -/
  | JSExportDefault (defaultA : JSAnnot) (expr : JSExpression) (semi : JSSemi)
  /-- body, autosemi -/
  | JSExport (stmt : JSStatement) (semi : JSSemi)

inductive JSStatement where
  /-- lbrace, stmts, rbrace, autosemi -/
  | JSStatementBlock (lb : JSAnnot) (stmts : List JSStatement) (rb : JSAnnot) (semi : JSSemi)
  /-- break, optional identifier, autosemi -/
  | JSBreak (annot : JSAnnot) (ident : JSIdent) (semi : JSSemi)
  /-- let, decl, autosemi -/
  | JSLet (annot : JSAnnot) (decls : JSCommaList1 JSExpression) (semi : JSSemi)
  /-- class, name, optional extends clause, lb, body, rb, autosemi -/
  | JSClass (decorators : List JSDecorator) (annot : JSAnnot) (name : JSIdent)
      (heritage : JSClassHeritage) (lb : JSAnnot) (body : List JSClassElement) (rb : JSAnnot)
      (semi : JSSemi)
  /-- const, decl, autosemi -/
  | JSConstant (annot : JSAnnot) (decls : JSCommaList1 JSExpression) (semi : JSSemi)
  /-- `using x = e;`, an explicit resource management declaration:
  `using`, declarators, autosemi. -/
  | JSUsing (annot : JSAnnot) (decls : JSCommaList1 JSExpression) (semi : JSSemi)
  /-- `await using x = e;`: `await`, `using`, declarators, autosemi. -/
  | JSAwaitUsing (awaitA : JSAnnot) (usingA : JSAnnot)
      (decls : JSCommaList1 JSExpression) (semi : JSSemi)
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
  | JSForVar (forA : JSAnnot) (lb : JSAnnot) (varA : JSAnnot) (init : JSCommaList1 JSExpression)
      (s1 : JSAnnot) (cond : JSCommaList JSExpression) (s2 : JSAnnot)
      (step : JSCommaList JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, var, vardecl, in, expr, rb, stmt -/
  | JSForVarIn (forA : JSAnnot) (lb : JSAnnot) (varA : JSAnnot) (lhs : JSExpression)
      (op : JSBinOp) (rhs : JSExpression) (rb : JSAnnot) (body : JSStatement)
  /-- for, lb, let, vardecl, semi, expr, semi, expr, rb, stmt -/
  | JSForLet (forA : JSAnnot) (lb : JSAnnot) (letA : JSAnnot) (init : JSCommaList1 JSExpression)
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
      (init : JSCommaList1 JSExpression) (s1 : JSAnnot) (cond : JSCommaList JSExpression)
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
  | JSVariable (annot : JSAnnot) (decls : JSCommaList1 JSExpression) (semi : JSSemi)
  /-- while, lb, expr, rb, stmt -/
  | JSWhile (annot : JSAnnot) (lb : JSAnnot) (cond : JSExpression) (rb : JSAnnot)
      (body : JSStatement)
  /-- with, lb, expr, rb, stmt list -/
  | JSWith (annot : JSAnnot) (lb : JSAnnot) (expr : JSExpression) (rb : JSAnnot)
      (body : JSStatement) (semi : JSSemi)

inductive JSExpression where
  -- Terminals
  | JSIdentifier (annot : JSAnnot) (name : NEString)
  /-- A numeric literal, as the number it denotes: a base ten literal, a
  `0x…`/`0o…`/`0b…` (or legacy `0…`) one, or a `BigInt`.  The base is part
  of `lit`, which is why there is one constructor and not three, and the
  literal is printed canonically (`JSNumber.render`). -/
  | JSNumberLit (annot : JSAnnot) (lit : JSNumber)
  /-- `this`, `super`, `null`, `true`, `false` or `debugger`. -/
  | JSLiteral (annot : JSAnnot) (lit : JSKeywordLiteral)
  /-- A string literal: its quote, and its escapes as they were written. -/
  | JSStringLiteral (annot : JSAnnot) (lit : JSStringSrc)
  /-- A regular expression literal: the pattern and the typed flags.  It is
  printed as `/pattern/flags`, the flags in the canonical order. -/
  | JSRegEx (annot : JSAnnot) (lit : RegExpLit)
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
  /-- decorators, class, optional identifier, optional extends clause, lb,
  body, rb.  `decorators` is empty for an undecorated class. -/
  | JSClassExpression (decorators : List JSDecorator) (annot : JSAnnot) (name : JSIdent)
      (heritage : JSClassHeritage) (lb : JSAnnot) (body : List JSClassElement) (rb : JSAnnot)
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
  /-- `obj?.prop`: firstpart, `?.`, name.  `prop` is an identifier or a
  private name. -/
  | JSOptionalMemberDot (expr : JSExpression) (chain : JSAnnot) (prop : JSExpression)
  /-- `obj?.[idx]`: firstpart, `?.`, `[`, expr, `]` -/
  | JSOptionalMemberSquare (expr : JSExpression) (chain : JSAnnot) (lb : JSAnnot)
      (idx : JSExpression) (rb : JSAnnot)
  /-- `f?.(args)`: callee, `?.`, `(`, args, `)` -/
  | JSOptionalCallExpression (expr : JSExpression) (chain : JSAnnot) (lb : JSAnnot)
      (args : JSCommaList JSExpression) (rb : JSAnnot)
  /-- A private class name, `#x`, without its `#`: the name of a private
  member, the property of `obj.#x`, or the left operand of `#x in obj`. -/
  | JSPrivateName (annot : JSAnnot) (name : NEString)
  /-- `import.meta`: `import`, `.`, `meta` -/
  | JSImportMeta (importA : JSAnnot) (dot : JSAnnot) (metaA : JSAnnot)
  /-- `new.target`: `new`, `.`, `target` -/
  | JSNewTarget (newA : JSAnnot) (dot : JSAnnot) (targetA : JSAnnot)
  /-- A dynamic import, `import(specifier)` or `import(specifier, options)`:
  `import`, `(`, args, `)` -/
  | JSImportCall (importA : JSAnnot) (lb : JSAnnot) (args : JSCommaList JSExpression)
      (rb : JSAnnot)
  /-- new, expr -/
  | JSNewExpression (annot : JSAnnot) (expr : JSExpression)
  /-- lbrace, contents, rbrace -/
  | JSObjectLiteral (lb : JSAnnot) (props : JSCommaTrailingList JSObjectProperty) (rb : JSAnnot)
  | JSSpreadExpression (annot : JSAnnot) (expr : JSExpression)
  /-- optional tag, lquot, head, parts.  `head` is the text of the first
  chunk *without* its delimiters: the backquote which opens the literal and
  the `${` (or the closing backquote, when there is no substitution) are
  not part of it, since the shape of the node already says which one comes
  there. -/
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
  /-- `name: value`.  A property has exactly one value, so this is an
  expression rather than a list of them. -/
  | JSPropertyNameandValue (name : JSPropertyName) (colon : JSAnnot) (value : JSExpression)
  | JSPropertyIdentRef (annot : JSAnnot) (name : NEString)
  /-- `{ x = 1 }`: a shorthand property with a default value.  It is only
  legal in a destructuring pattern, where it binds `x` to `1` when the
  property is missing: name, `=`, the default. -/
  | JSPropertyIdentRefDefault (annot : JSAnnot) (name : NEString) (eq : JSAnnot)
      (value : JSExpression)
  /-- `{ ...rest }`: a spread in an object literal, or the rest property of
  a destructuring pattern. -/
  | JSObjectSpread (annot : JSAnnot) (expr : JSExpression)
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
  | JSPropertyIdent (annot : JSAnnot) (name : NEString)
  /-- A private name, `#x`, without its `#`; only a class member may have
  one. -/
  | JSPropertyPrivate (annot : JSAnnot) (name : NEString)
  /-- A quoted name, with its quotes as they were written. -/
  | JSPropertyString (annot : JSAnnot) (name : JSStringSrc)
  /-- A numeric name, as the number it denotes. -/
  | JSPropertyNumber (annot : JSAnnot) (name : JSNumber)
  /-- lb, expr, rb -/
  | JSPropertyComputed (lb : JSAnnot) (expr : JSExpression) (rb : JSAnnot)

inductive JSArrayElement where
  | JSArrayElement (expr : JSExpression)
  | JSArrayComma (annot : JSAnnot)

inductive JSTemplatePart where
  /-- expr, rb, suffix.  As with the head of the literal, `suffix` is the
  text of the chunk without its delimiters: neither the `}` which closes
  the substitution nor the `${` (or the closing backquote, for the last
  part) is part of it. -/
  | JSTemplatePart (expr : JSExpression) (rb : JSAnnot) (suffix : String)

inductive JSClassHeritage where
  | JSExtends (annot : JSAnnot) (expr : JSExpression)
  | JSExtendsNone

/-- A decorator, `@expr`, in front of a class or of one of its members. -/
inductive JSDecorator where
  /-- `@`, the expression decorating. -/
  | JSDecorator (at_ : JSAnnot) (expr : JSExpression)

inductive JSClassElement where
  /-- decorators, method -/
  | JSClassInstanceMethod (decorators : List JSDecorator) (method : JSMethodDefinition)
  /-- decorators, static, method -/
  | JSClassStaticMethod (decorators : List JSDecorator) (annot : JSAnnot)
      (method : JSMethodDefinition)
  /-- A class field, `x = 1;` or `#x;`: decorators, name, initializer,
  semicolon. -/
  | JSClassInstanceField (decorators : List JSDecorator) (name : JSPropertyName)
      (init : JSVarInitializer) (semi : JSSemi)
  /-- A static class field, `static x = 1;`: decorators, `static`, name,
  initializer, semicolon. -/
  | JSClassStaticField (decorators : List JSDecorator) (annot : JSAnnot)
      (name : JSPropertyName) (init : JSVarInitializer) (semi : JSSemi)
  /-- A static initialisation block, `static { ... }`: `static`, block. -/
  | JSClassStaticBlock (annot : JSAnnot) (block : JSBlock)
  | JSClassSemi (annot : JSAnnot)

end

/-- The property list of an object literal. -/
abbrev JSObjectPropertyList := JSCommaTrailingList JSObjectProperty

/-! ## Default values

Lean cannot derive `Inhabited` for the mutually recursive AST types, so the
instances are given by hand; they are needed for functions defined by
general (`partial`) recursion. -/

instance : Inhabited JSExpression := ⟨.JSLiteral .JSNoAnnot .null⟩
instance : Inhabited JSStatement := ⟨.JSEmptyStatement .JSNoAnnot⟩
instance : Inhabited JSBlock := ⟨.JSBlock .JSNoAnnot [] .JSNoAnnot⟩
instance : Inhabited JSAST := ⟨.JSAstProgram [] .JSNoAnnot⟩
instance : Inhabited JSVarInitializer := ⟨.JSVarInitNone⟩
instance : Inhabited JSTryFinally := ⟨.JSNoFinally⟩
instance : Inhabited JSTryCatch :=
  ⟨.JSCatch .JSNoAnnot .JSNoAnnot default .JSNoAnnot default⟩
instance : Inhabited JSSwitchParts := ⟨.JSDefault .JSNoAnnot .JSNoAnnot []⟩
instance : Inhabited JSClassHeritage := ⟨.JSExtendsNone⟩
instance : Inhabited JSPropertyName := ⟨.JSPropertyIdent .JSNoAnnot default⟩
instance : Inhabited JSMethodDefinition :=
  ⟨.JSMethodDefinition default .JSNoAnnot .JSLNil .JSNoAnnot default⟩
instance : Inhabited JSObjectProperty := ⟨.JSPropertyIdentRef .JSNoAnnot default⟩
instance : Inhabited JSArrayElement := ⟨.JSArrayComma .JSNoAnnot⟩
instance : Inhabited JSTemplatePart := ⟨.JSTemplatePart default .JSNoAnnot ""⟩
instance : Inhabited JSClassElement := ⟨.JSClassSemi .JSNoAnnot⟩
instance : Inhabited JSDecorator := ⟨.JSDecorator .JSNoAnnot default⟩
instance : Inhabited JSArrowParameterList := ⟨.JSUnparenthesizedArrowParameter .JSIdentNone⟩
instance : Inhabited JSModuleItem := ⟨.JSModuleStatementListItem default⟩
instance : Inhabited JSExportDeclaration := ⟨.JSExportLocals default .JSSemiAuto⟩

/-! ## The value of a literal

A numeric and a regular expression literal are stored as their value, so
reading the value off a node is a projection; a string literal is stored as
it was written, and `JSStringSrc.render` gives the source text back. -/

/-- The value of a numeric literal, `none` for anything else. -/
def JSExpression.numberValue? : JSExpression → Option JSNumber
  | .JSNumberLit _ lit => some lit
  | _ => none

/-- The value of a regular expression literal, `none` for anything else. -/
def JSExpression.regexValue? : JSExpression → Option RegExpLit
  | .JSRegEx _ lit => some lit
  | _ => none

/-- The numeric literal `n`, as an expression node. -/
def JSExpression.ofNumber (annot : JSAnnot) (n : JSNumber) : JSExpression :=
  .JSNumberLit annot n

/-- The regular expression literal `r`, as an expression node. -/
def JSExpression.ofRegExp (annot : JSAnnot) (r : RegExpLit) : JSExpression :=
  .JSRegEx annot r

/-! ## Helpers -/

/-- The source spelling of the first chunk of a template literal: its text,
between the backquote which opens the literal and either the `${` of the
first substitution or, when there is none, the closing backquote.  The tree
stores the text alone; the delimiters are decided by the shape of the
node. -/
def templateHeadSpelling (head : String) (parts : List JSTemplatePart) : String :=
  "`" ++ head ++ (if parts.isEmpty then "`" else "${")

/-- The source spelling of the chunk which follows a substitution: its
text, between the `}` which closes the substitution and either the `${` of
the next one or, for the last part, the closing backquote. -/
def templatePartSpelling (suffix : String) (isLast : Bool) : String :=
  "}" ++ suffix ++ (if isLast then "`" else "${")

/-- The text of a chunk of a template literal written between two byte
offsets of `raw`, without its delimiters: the leading backquote of the
head, and the trailing `${` or backquote.  The tree stores the text alone,
since which delimiters surround it is decided by the shape of the node.

This is the *in place* reader: the delimiters are looked at where the lexer
left them and the text is sliced straight out of the input, so the text of
the token is not built first and sliced afterwards.  The delimiters are one
byte wide, hence the arithmetic on byte offsets.
`templateChunkRange_eq` (in `TokenTextSpec`) says that it reads what
`templateChunk` reads. -/
def templateChunkFrom (raw : String) (begin_ : Nat) (stop : String.Pos.Raw) : String :=
  if stop.byteIdx ≤ begin_ then ""
  else
    let last := String.Pos.Raw.prev raw stop
    let beforeLast := String.Pos.Raw.prev raw last
    let stop' : Nat :=
      if begin_ < last.byteIdx && String.Pos.Raw.get raw last == '{' &&
          String.Pos.Raw.get raw beforeLast == '$' then beforeLast.byteIdx
      else if String.Pos.Raw.get raw last == '`' then last.byteIdx
      else stop.byteIdx
    String.Pos.Raw.extract raw ⟨begin_⟩ ⟨stop'⟩

/-- The text of a chunk of a template literal written between two byte
offsets of `raw`. -/
def templateChunkRange (raw : String) (start stop : String.Pos.Raw) : String :=
  templateChunkFrom raw
    (if start.byteIdx < stop.byteIdx && String.Pos.Raw.get raw start == '`' then
      start.byteIdx + 1
    else start.byteIdx) stop

/-- The text of a chunk of a template literal, without its delimiters. -/
def templateChunk (raw : String) : String :=
  templateChunkRange raw ⟨0⟩ ⟨raw.utf8ByteSize⟩

/-- The text of the chunk a substring of the input spells. -/
def templateChunkSub (ss : Substring.Raw) : String :=
  templateChunkRange ss.str ss.startPos ss.stopPos

/-- Flatten a comma list into an ordinary list, in front of `acc`.

A comma list grows at its *end* (`JSLCons` holds the last element), so
flattening it by appending would cost a copy of the list already built at
every step.  Walking it inwards and pushing each element onto an
accumulator instead costs one step per element; `fromCommaList_cons` below
says that the result is the same. -/
def fromCommaListAux {a : Type} : JSCommaList a → List a → List a
  | .JSLCons l _ i, acc => fromCommaListAux l (i :: acc)
  | .JSLOne i, acc => i :: acc
  | .JSLNil, acc => acc

/-- Flatten a comma list into an ordinary list. -/
def fromCommaList {a : Type} (l : JSCommaList a) : List a := fromCommaListAux l []

theorem fromCommaListAux_eq {a : Type} :
    ∀ (l : JSCommaList a) (acc : List a), fromCommaListAux l acc = fromCommaList l ++ acc
  | .JSLNil, acc => by simp [fromCommaListAux, fromCommaList]
  | .JSLOne i, acc => by simp [fromCommaListAux, fromCommaList]
  | .JSLCons l _ i, acc => by
      rw [fromCommaList, fromCommaListAux, fromCommaListAux_eq l (i :: acc),
        fromCommaListAux, fromCommaListAux_eq l [i]]
      simp

@[simp] theorem fromCommaList_nil {a : Type} : fromCommaList (.JSLNil : JSCommaList a) = [] := rfl

@[simp] theorem fromCommaList_one {a : Type} (i : a) : fromCommaList (.JSLOne i) = [i] := rfl

@[simp] theorem fromCommaList_cons {a : Type} (l : JSCommaList a) (c : JSAnnot) (i : a) :
    fromCommaList (.JSLCons l c i) = fromCommaList l ++ [i] := by
  rw [fromCommaList, fromCommaListAux, fromCommaListAux_eq]

namespace JSCommaList1

variable {a b : Type}

/-- A non-empty comma list is a comma list. -/
def toCommaList : JSCommaList1 a → JSCommaList a
  | .JSL1Cons l c i => .JSLCons l.toCommaList c i
  | .JSL1One i => .JSLOne i

/-- Flatten a non-empty comma list in front of `acc`; as for
`fromCommaListAux`, the list is walked inwards rather than appended to. -/
def toListAux : JSCommaList1 a → List a → List a
  | .JSL1Cons l _ i, acc => toListAux l (i :: acc)
  | .JSL1One i, acc => i :: acc

/-- Flatten a non-empty comma list into an ordinary list. -/
def toList (l : JSCommaList1 a) : List a := toListAux l []

theorem toListAux_eq : ∀ (l : JSCommaList1 a) (acc : List a), toListAux l acc = l.toList ++ acc
  | .JSL1One i, acc => by simp [toListAux, toList]
  | .JSL1Cons l _ i, acc => by
      rw [toList, toListAux, toListAux_eq l (i :: acc), toListAux, toListAux_eq l [i]]
      simp

@[simp] theorem toList_one (i : a) : JSCommaList1.toList (.JSL1One i) = [i] := rfl

@[simp] theorem toList_cons (l : JSCommaList1 a) (c : JSAnnot) (i : a) :
    JSCommaList1.toList (.JSL1Cons l c i) = l.toList ++ [i] := by
  rw [toList, toListAux, toListAux_eq]

/-- Flattening a non-empty comma list never gives the empty list. -/
theorem toList_ne_nil (l : JSCommaList1 a) : l.toList ≠ [] := by
  cases l with
  | JSL1Cons l _ i => simp
  | JSL1One i => simp

/-- Flattening a non-empty comma list is flattening the comma list it
is. -/
theorem toList_eq (l : JSCommaList1 a) : l.toList = fromCommaList l.toCommaList := by
  induction l with
  | JSL1Cons l _ i ih => simp [toCommaList, ih]
  | JSL1One i => rfl

/-- Apply a function to every element. -/
def map (f : a → b) : JSCommaList1 a → JSCommaList1 b
  | .JSL1Cons l c i => .JSL1Cons (l.map f) c (f i)
  | .JSL1One i => .JSL1One (f i)

/-- The last element, and the comma list of the ones which precede it. -/
def unsnoc : JSCommaList1 a → JSCommaList a × a
  | .JSL1Cons l _ i => (l.toCommaList, i)
  | .JSL1One i => (.JSLNil, i)

/-- The elements of `l`, then those of `m`, separated by `c`. -/
def append (l : JSCommaList1 a) (c : JSAnnot) : JSCommaList1 a → JSCommaList1 a
  | .JSL1One i => .JSL1Cons l c i
  | .JSL1Cons m c' i => .JSL1Cons (l.append c m) c' i

end JSCommaList1

/-- The elements of a comma list, if there is at least one; the empty list
is not a `JSCommaList1`. -/
def toCommaList1? {a : Type} : JSCommaList a → Option (JSCommaList1 a)
  | .JSLNil => none
  | .JSLOne i => some (.JSL1One i)
  | .JSLCons l c i =>
      match toCommaList1? l with
      | some l' => some (.JSL1Cons l' c i)
      | none => some (.JSL1One i)

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
  | .JSBinOpNullish _ => .JSBinOpNullish .JSNoAnnot
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

end Language.JavaScript.Parser.AST
