/-
Port of `LanguageJavaScript.Process.Minify` to Lean 4.

The Haskell version uses a `MinifyJS` class with a single method
`fix :: JSAnnot -> a -> a`; here each instance becomes a function `fix<Type>`.
The statement list handling ("force semicolons between statements, drop
redundant statements, splice nested blocks") is not structurally recursive,
so the group is declared `partial`.
-/
import LanguageJavascript.AST

namespace LanguageJavaScript.Process

open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.AST

/-- A single space of whitespace. -/
def spaceAnnot : JSAnnot := .JSAnnot TokenPosn.empty [.WhiteSpace TokenPosn.empty " ".toRawSubstring]

/-- No annotation at all. -/
def emptyAnnot : JSAnnot := .JSNoAnnot

/-- A newline. -/
def newlineAnnot : JSAnnot := .JSAnnot TokenPosn.empty [.WhiteSpace TokenPosn.empty "\n".toRawSubstring]

def semi : JSSemi := .JSSemi emptyAnnot

def noSemi : JSSemi := .JSSemiAuto

/-- Concatenate two comma lists.  Equivalent to the Haskell version, which
peels elements off the front of `ys` with `headCommaList`. -/
def concatCommaList {a : Type} (xs ys : JSCommaList a) : JSCommaList a :=
  match xs, ys with
  | xs, .JSLNil => xs
  | .JSLNil, ys => ys
  | xs, ys => (fromCommaList ys).foldl (fun acc y => .JSLCons acc emptyAnnot y) xs

/-- Normalize a string literal.  If it is single quoted, just return it; if it
is double quoted, convert it to single quoted. -/
def normalizeToSQ (str : String) : String :=
  let rec convertSQ : List Char → List Char
    | [] => []
    | [_] => ['\'']
    | '\'' :: xs => '\\' :: '\'' :: convertSQ xs
    | '\\' :: '"' :: xs => '"' :: convertSQ xs
    | x :: xs => x :: convertSQ xs
  match str.toList with
  | [] => ""
  | '\'' :: _ => str
  | '"' :: xs => String.ofList ('\'' :: convertSQ xs)
  | _ => str -- Should not happen.

/-- Concatenate two string literals.  Since the strings include their
terminators, the terminator of the first string is used. -/
def stringLitConcat (xs ys : String) : JSExpression :=
  if ys == "" then .JSStringLiteral emptyAnnot xs
  else if xs == "" then .JSStringLiteral emptyAnnot ys
  else
    -- drop the closing quote of the first string, and the opening quote and
    -- closing quote of the second one, then re-add a single quote.
    let xinit := xs.toList.dropLast
    let yinit := ys.toList.drop 1 |>.dropLast
    .JSStringLiteral emptyAnnot (String.ofList (xinit ++ yinit ++ ['\'']))

def fixBinOp (a : JSAnnot) : JSBinOp → JSBinOp
  | .JSBinOpAnd _ => .JSBinOpAnd emptyAnnot
  | .JSBinOpBitAnd _ => .JSBinOpBitAnd emptyAnnot
  | .JSBinOpBitOr _ => .JSBinOpBitOr emptyAnnot
  | .JSBinOpBitXor _ => .JSBinOpBitXor emptyAnnot
  | .JSBinOpDivide _ => .JSBinOpDivide emptyAnnot
  | .JSBinOpEq _ => .JSBinOpEq emptyAnnot
  | .JSBinOpGe _ => .JSBinOpGe emptyAnnot
  | .JSBinOpGt _ => .JSBinOpGt emptyAnnot
  | .JSBinOpIn _ => .JSBinOpIn a
  | .JSBinOpInstanceOf _ => .JSBinOpInstanceOf a
  | .JSBinOpLe _ => .JSBinOpLe emptyAnnot
  | .JSBinOpLsh _ => .JSBinOpLsh emptyAnnot
  | .JSBinOpLt _ => .JSBinOpLt emptyAnnot
  | .JSBinOpMinus _ => .JSBinOpMinus emptyAnnot
  | .JSBinOpMod _ => .JSBinOpMod emptyAnnot
  | .JSBinOpNeq _ => .JSBinOpNeq emptyAnnot
  | .JSBinOpOf _ => .JSBinOpOf a
  | .JSBinOpOr _ => .JSBinOpOr emptyAnnot
  | .JSBinOpPlus _ => .JSBinOpPlus emptyAnnot
  | .JSBinOpRsh _ => .JSBinOpRsh emptyAnnot
  | .JSBinOpStrictEq _ => .JSBinOpStrictEq emptyAnnot
  | .JSBinOpStrictNeq _ => .JSBinOpStrictNeq emptyAnnot
  | .JSBinOpTimes _ => .JSBinOpTimes emptyAnnot
  | .JSBinOpUrsh _ => .JSBinOpUrsh emptyAnnot

def fixUnaryOpPlain (_a : JSAnnot) : JSUnaryOp → JSUnaryOp
  | .JSUnaryOpDecr _ => .JSUnaryOpDecr emptyAnnot
  | .JSUnaryOpDelete _ => .JSUnaryOpDelete emptyAnnot
  | .JSUnaryOpIncr _ => .JSUnaryOpIncr emptyAnnot
  | .JSUnaryOpMinus _ => .JSUnaryOpMinus emptyAnnot
  | .JSUnaryOpNot _ => .JSUnaryOpNot emptyAnnot
  | .JSUnaryOpPlus _ => .JSUnaryOpPlus emptyAnnot
  | .JSUnaryOpTilde _ => .JSUnaryOpTilde emptyAnnot
  | .JSUnaryOpTypeof _ => .JSUnaryOpTypeof emptyAnnot
  | .JSUnaryOpVoid _ => .JSUnaryOpVoid emptyAnnot

/-- Returns the annotation to use for the operand together with the fixed
operator: the word-like operators need a space after them. -/
def fixUnaryOp (a : JSAnnot) : JSUnaryOp → JSAnnot × JSUnaryOp
  | .JSUnaryOpDelete _ => (spaceAnnot, .JSUnaryOpDelete a)
  | .JSUnaryOpTypeof _ => (spaceAnnot, .JSUnaryOpTypeof a)
  | .JSUnaryOpVoid _ => (spaceAnnot, .JSUnaryOpVoid a)
  | x => (emptyAnnot, fixUnaryOpPlain a x)

def fixAssignOp (a : JSAnnot) : JSAssignOp → JSAssignOp
  | .JSAssign _ => .JSAssign a
  | .JSTimesAssign _ => .JSTimesAssign a
  | .JSDivideAssign _ => .JSDivideAssign a
  | .JSModAssign _ => .JSModAssign a
  | .JSPlusAssign _ => .JSPlusAssign a
  | .JSMinusAssign _ => .JSMinusAssign a
  | .JSLshAssign _ => .JSLshAssign a
  | .JSRshAssign _ => .JSRshAssign a
  | .JSUrshAssign _ => .JSUrshAssign a
  | .JSBwAndAssign _ => .JSBwAndAssign a
  | .JSBwXorAssign _ => .JSBwXorAssign a
  | .JSBwOrAssign _ => .JSBwOrAssign a

def fixIdent (a : JSAnnot) : JSIdent → JSIdent
  | .JSIdentName _ n => .JSIdentName a n
  | .JSIdentNone => .JSIdentNone

def fixAccessor (a : JSAnnot) : JSAccessor → JSAccessor
  | .JSAccessorGet _ => .JSAccessorGet a
  | .JSAccessorSet _ => .JSAccessorSet a

def fixFromClause (a : JSAnnot) : JSFromClause → JSFromClause
  | .JSFromClause _ _ m => .JSFromClause a emptyAnnot m

def fixImportNameSpace (a : JSAnnot) : JSImportNameSpace → JSImportNameSpace
  | .JSImportNameSpace _ _ ident =>
      .JSImportNameSpace (.JSBinOpTimes a) spaceAnnot (fixIdent spaceAnnot ident)

def fixImportSpecifier (_a : JSAnnot) : JSImportSpecifier → JSImportSpecifier
  | .JSImportSpecifier x1 => .JSImportSpecifier (fixIdent emptyAnnot x1)
  | .JSImportSpecifierAs x1 _ x2 =>
      .JSImportSpecifierAs (fixIdent emptyAnnot x1) spaceAnnot (fixIdent spaceAnnot x2)

def fixExportSpecifier (_a : JSAnnot) : JSExportSpecifier → JSExportSpecifier
  | .JSExportSpecifier x1 => .JSExportSpecifier (fixIdent emptyAnnot x1)
  | .JSExportSpecifierAs x1 _ x2 =>
      .JSExportSpecifierAs (fixIdent emptyAnnot x1) spaceAnnot (fixIdent spaceAnnot x2)

def fixImportSpecCommaList (_a : JSAnnot) :
    JSCommaList JSImportSpecifier → JSCommaList JSImportSpecifier
  | .JSLCons xs _ x =>
      .JSLCons (fixImportSpecCommaList emptyAnnot xs) emptyAnnot (fixImportSpecifier emptyAnnot x)
  | .JSLOne x => .JSLOne (fixImportSpecifier emptyAnnot x)
  | .JSLNil => .JSLNil

def fixExportSpecCommaList (_a : JSAnnot) :
    JSCommaList JSExportSpecifier → JSCommaList JSExportSpecifier
  | .JSLCons xs _ x =>
      .JSLCons (fixExportSpecCommaList emptyAnnot xs) emptyAnnot (fixExportSpecifier emptyAnnot x)
  | .JSLOne x => .JSLOne (fixExportSpecifier emptyAnnot x)
  | .JSLNil => .JSLNil

def fixImportsNamed (_a : JSAnnot) : JSImportsNamed → JSImportsNamed
  | .JSImportsNamed _ imps _ =>
      .JSImportsNamed emptyAnnot (fixImportSpecCommaList emptyAnnot imps) emptyAnnot

def fixImportClause (_a : JSAnnot) : JSImportClause → JSImportClause
  | .JSImportClauseDefault n => .JSImportClauseDefault (fixIdent spaceAnnot n)
  | .JSImportClauseNameSpace ns => .JSImportClauseNameSpace (fixImportNameSpace spaceAnnot ns)
  | .JSImportClauseNamed named => .JSImportClauseNamed (fixImportsNamed emptyAnnot named)
  | .JSImportClauseDefaultNameSpace def_ _ ns =>
      .JSImportClauseDefaultNameSpace (fixIdent spaceAnnot def_) emptyAnnot
        (fixImportNameSpace emptyAnnot ns)
  | .JSImportClauseDefaultNamed def_ _ ns =>
      .JSImportClauseDefaultNamed (fixIdent spaceAnnot def_) emptyAnnot
        (fixImportsNamed emptyAnnot ns)

def fixImportDeclaration (a : JSAnnot) : JSImportDeclaration → JSImportDeclaration
  | .JSImportDeclaration imps from_ _ =>
      let annot :=
        match imps with
        | .JSImportClauseDefault _ => spaceAnnot
        | .JSImportClauseNameSpace _ => spaceAnnot
        | .JSImportClauseNamed _ => emptyAnnot
        | .JSImportClauseDefaultNameSpace .. => spaceAnnot
        | .JSImportClauseDefaultNamed .. => emptyAnnot
      .JSImportDeclaration (fixImportClause emptyAnnot imps) (fixFromClause annot from_) noSemi
  | .JSImportDeclarationBare _ m _ => .JSImportDeclarationBare a m noSemi

def fixExportClause (a : JSAnnot) : JSExportClause → JSExportClause
  | .JSExportClause _ x1 _ => .JSExportClause emptyAnnot (fixExportSpecCommaList emptyAnnot x1) a

set_option maxHeartbeats 2000000 in
mutual

partial def fixStmt (a : JSAnnot) (s : JSSemi) : JSStatement → JSStatement
  | .JSStatementBlock _ ss _ _ => fixStatementBlock a s ss
  | .JSBreak _ i _ => .JSBreak a (fixIdent spaceAnnot i) s
  | .JSClass _ n h _ ms _ _ =>
      .JSClass a (fixIdent spaceAnnot n) (fixClassHeritage spaceAnnot h) emptyAnnot
        (fixClassElements emptyAnnot ms) emptyAnnot s
  | .JSConstant _ ss _ => .JSConstant a (fixVarList ss) s
  | .JSContinue _ i _ => .JSContinue a (fixIdent spaceAnnot i) s
  | .JSDoWhile _ st _ _ e _ _ =>
      .JSDoWhile a (mkStatementBlock noSemi st) emptyAnnot emptyAnnot (fixExpression emptyAnnot e)
        emptyAnnot s
  | .JSFor _ _ el1 _ el2 _ el3 _ st =>
      .JSFor a emptyAnnot (fixExprCommaList emptyAnnot el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForIn _ _ e1 op e2 _ st =>
      .JSForIn a emptyAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForVar _ _ _ el1 _ el2 _ el3 _ st =>
      .JSForVar a emptyAnnot spaceAnnot (fixExprCommaList emptyAnnot el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForVarIn _ _ _ e1 op e2 _ st =>
      .JSForVarIn a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForLet _ _ _ el1 _ el2 _ el3 _ st =>
      .JSForLet a emptyAnnot spaceAnnot (fixExprCommaList emptyAnnot el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForLetIn _ _ _ e1 op e2 _ st =>
      .JSForLetIn a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForLetOf _ _ _ e1 op e2 _ st =>
      .JSForLetOf a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForConst _ _ _ el1 _ el2 _ el3 _ st =>
      .JSForConst a emptyAnnot spaceAnnot (fixExprCommaList emptyAnnot el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForConstIn _ _ _ e1 op e2 _ st =>
      .JSForConstIn a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForConstOf _ _ _ e1 op e2 _ st =>
      .JSForConstOf a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForOf _ _ e1 op e2 _ st =>
      .JSForOf a emptyAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForVarOf _ _ _ e1 op e2 _ st =>
      .JSForVarOf a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSAsyncFunction _ _ n _ ps _ blk _ =>
      .JSAsyncFunction a spaceAnnot (fixIdent spaceAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot ps) emptyAnnot (fixBlock emptyAnnot blk) s
  | .JSFunction _ n _ ps _ blk _ =>
      .JSFunction a (fixIdent spaceAnnot n) emptyAnnot (fixExprCommaList emptyAnnot ps)
        emptyAnnot (fixBlock emptyAnnot blk) s
  | .JSGenerator _ _ n _ ps _ blk _ =>
      .JSGenerator a emptyAnnot (fixIdent emptyAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot ps) emptyAnnot (fixBlock emptyAnnot blk) s
  | .JSIf _ _ e _ st =>
      .JSIf a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot (fixIfElseBlock emptyAnnot s st)
  | .JSIfElse _ _ e _ (.JSEmptyStatement _) _ sf =>
      .JSIfElse a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot
        (.JSEmptyStatement emptyAnnot) emptyAnnot (fixStmt spaceAnnot s sf)
  | .JSIfElse _ _ e _ st _ sf =>
      .JSIfElse a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot (mkStatementBlock noSemi st)
        emptyAnnot (fixIfElseBlock spaceAnnot s sf)
  | .JSLabelled e _ st => .JSLabelled (fixIdent a e) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSLet _ xs _ => .JSLet a (fixVarList xs) s
  | .JSEmptyStatement _ => .JSEmptyStatement emptyAnnot
  | .JSExpressionStatement e _ => .JSExpressionStatement (fixExpression a e) s
  | .JSAssignStatement lhs op rhs _ =>
      .JSAssignStatement (fixExpression a lhs) (fixAssignOp emptyAnnot op)
        (fixExpression emptyAnnot rhs) s
  | .JSMethodCall e _ args _ _ =>
      .JSMethodCall (fixExpression a e) emptyAnnot (fixExprCommaList emptyAnnot args) emptyAnnot s
  | .JSReturn _ me _ => .JSReturn a (fixMaybeExpression spaceAnnot me) s
  | .JSSwitch _ _ e _ _ sps _ _ =>
      .JSSwitch a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot emptyAnnot
        (fixSwitchParts sps) emptyAnnot s
  | .JSThrow _ e _ => .JSThrow a (fixExpression spaceAnnot e) s
  | .JSTry _ b tc tf =>
      .JSTry a (fixBlock emptyAnnot b) (fixTryCatches tc) (fixTryFinally emptyAnnot tf)
  | .JSVariable _ ss _ => .JSVariable a (fixVarList ss) s
  | .JSWhile _ _ e _ st =>
      .JSWhile a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot (fixStmt a s st)
  | .JSWith _ _ e _ st _ =>
      .JSWith a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot (fixStmt emptyAnnot noSemi st) s

partial def fixIfElseBlock (a : JSAnnot) (s : JSSemi) : JSStatement → JSStatement
  | .JSStatementBlock _ [] _ _ => .JSEmptyStatement emptyAnnot
  | st => fixStmt a s st

/-- Turn a single `JSStatement` into a `JSStatementBlock`. -/
partial def mkStatementBlock (s : JSSemi) : JSStatement → JSStatement
  | .JSStatementBlock _ blk _ _ =>
      .JSStatementBlock emptyAnnot (fixStatementList noSemi blk) emptyAnnot s
  | x => .JSStatementBlock emptyAnnot [fixStmt emptyAnnot noSemi x] emptyAnnot s

/-- Filter a list of `JSStatement`, dropping `JSEmptyStatement` and empty
`JSStatementBlock`s.  If the resulting list contains only a single element,
remove the enclosing `JSStatementBlock` and return the inner statement. -/
partial def fixStatementBlock (a : JSAnnot) (s : JSSemi) (ss : List JSStatement) : JSStatement :=
  let isEmpty : JSStatement → Bool
    | .JSEmptyStatement _ => true
    | .JSStatementBlock _ [] _ _ => true
    | _ => false
  match ss.filter (fun x => !isEmpty x) with
  | [] => .JSStatementBlock emptyAnnot [] emptyAnnot s
  | [sx] => fixStmt a s sx
  | sss => .JSStatementBlock emptyAnnot (fixStatementList noSemi sss) emptyAnnot s

/-- Force semicolons between statements, and make sure the last statement in a
block has no semicolon. -/
partial def fixStatementList (trailingSemi : JSSemi) (ss : List JSStatement) : List JSStatement :=
  fixStmtList emptyAnnot trailingSemi (ss.filter (fun x => !isRedundantStmt x))

partial def isRedundantStmt : JSStatement → Bool
  | .JSStatementBlock _ [] _ _ => true
  | .JSEmptyStatement _ => true
  | _ => false

partial def fixStmtList (a : JSAnnot) (s : JSSemi) : List JSStatement → List JSStatement
  | [] => []
  | [.JSStatementBlock _ blk _ _] => fixStmtList a s blk
  | [x] => [fixStmt a s x]
  | .JSStatementBlock _ blk _ _ :: xs =>
      fixStmtList emptyAnnot semi (blk.filter (fun x => !isRedundantStmt x))
        ++ fixStmtList emptyAnnot s xs
  | .JSConstant _ vs1 _ :: .JSConstant _ vs2 _ :: xs =>
      fixStmtList a s (.JSConstant spaceAnnot (concatCommaList vs1 vs2) s :: xs)
  | .JSVariable _ vs1 _ :: .JSVariable _ vs2 _ :: xs =>
      fixStmtList a s (.JSVariable spaceAnnot (concatCommaList vs1 vs2) s :: xs)
  | (x1@(.JSFunction ..)) :: (x2@(.JSFunction ..)) :: xs =>
      fixStmt a noSemi x1 :: fixStmtList newlineAnnot s (x2 :: xs)
  | x :: xs => fixStmt a semi x :: fixStmtList emptyAnnot s xs

partial def fixExpression (a : JSAnnot) : JSExpression → JSExpression
  -- Terminals
  | .JSIdentifier _ s => .JSIdentifier a s
  | .JSDecimal _ s => .JSDecimal a s
  | .JSLiteral _ s => .JSLiteral a s
  | .JSHexInteger _ s => .JSHexInteger a s
  | .JSOctal _ s => .JSOctal a s
  | .JSStringLiteral _ s => .JSStringLiteral emptyAnnot s
  | .JSRegEx _ s => .JSRegEx emptyAnnot s
  -- Non terminals
  | .JSArrayLiteral _ xs _ =>
      .JSArrayLiteral emptyAnnot (fixArrayElements xs) emptyAnnot
  | .JSArrowExpression ps _ ss =>
      .JSArrowExpression (fixArrowParameterList a ps) emptyAnnot (fixStmt emptyAnnot noSemi ss)
  | .JSAssignExpression lhs op rhs =>
      .JSAssignExpression (fixExpression a lhs) (fixAssignOp emptyAnnot op)
        (fixExpression emptyAnnot rhs)
  | .JSAwaitExpression _ ex => .JSAwaitExpression a (fixExpression spaceAnnot ex)
  | .JSCallExpression ex _ xs _ =>
      .JSCallExpression (fixExpression a ex) emptyAnnot (fixExprCommaList emptyAnnot xs)
        emptyAnnot
  | .JSCallExpressionDot ex _ xs =>
      .JSCallExpressionDot (fixExpression a ex) emptyAnnot (fixExpression emptyAnnot xs)
  | .JSCallExpressionSquare ex _ xs _ =>
      .JSCallExpressionSquare (fixExpression a ex) emptyAnnot (fixExpression emptyAnnot xs)
        emptyAnnot
  | .JSClassExpression _ n h _ ms _ =>
      .JSClassExpression a (fixIdent spaceAnnot n) (fixClassHeritage spaceAnnot h) emptyAnnot
        (fixClassElements emptyAnnot ms) emptyAnnot
  | .JSCommaExpression le _ re =>
      .JSCommaExpression (fixExpression a le) emptyAnnot (fixExpression emptyAnnot re)
  | .JSExpressionBinary lhs op rhs => fixBinOpExpression a op lhs rhs
  | .JSExpressionParen _ e _ =>
      .JSExpressionParen emptyAnnot (fixExpression emptyAnnot e) emptyAnnot
  | .JSExpressionPostfix e op =>
      .JSExpressionPostfix (fixExpression a e) (fixUnaryOpPlain emptyAnnot op)
  | .JSExpressionTernary cond _ v1 _ v2 =>
      .JSExpressionTernary (fixExpression a cond) emptyAnnot (fixExpression emptyAnnot v1)
        emptyAnnot (fixExpression emptyAnnot v2)
  | .JSFunctionExpression _ n _ x2s _ x3 =>
      .JSFunctionExpression a (fixIdent spaceAnnot n) emptyAnnot (fixExprCommaList emptyAnnot x2s)
        emptyAnnot (fixBlock emptyAnnot x3)
  | .JSGeneratorExpression _ _ n _ x2s _ x3 =>
      .JSGeneratorExpression a emptyAnnot (fixIdent emptyAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot x2s) emptyAnnot (fixBlock emptyAnnot x3)
  | .JSMemberDot xs _ n =>
      .JSMemberDot (fixExpression a xs) emptyAnnot (fixExpression emptyAnnot n)
  | .JSMemberExpression e _ args _ =>
      .JSMemberExpression (fixExpression a e) emptyAnnot (fixExprCommaList emptyAnnot args)
        emptyAnnot
  | .JSMemberNew _ n _ s _ =>
      .JSMemberNew a (fixExpression spaceAnnot n) emptyAnnot (fixExprCommaList emptyAnnot s)
        emptyAnnot
  | .JSMemberSquare xs _ e _ =>
      .JSMemberSquare (fixExpression a xs) emptyAnnot (fixExpression emptyAnnot e) emptyAnnot
  | .JSNewExpression _ e => .JSNewExpression a (fixExpression spaceAnnot e)
  | .JSObjectLiteral _ xs _ =>
      .JSObjectLiteral emptyAnnot (fixObjectPropertyList emptyAnnot xs) emptyAnnot
  | .JSTemplateLiteral t _ s ps =>
      .JSTemplateLiteral (t.map (fixExpression a)) emptyAnnot s (fixTemplateParts ps)
  | .JSUnaryExpression op x =>
      let (ta, fop) := fixUnaryOp a op
      .JSUnaryExpression fop (fixExpression ta x)
  | .JSVarInitExpression x1 x2 =>
      .JSVarInitExpression (fixExpression a x1) (fixVarInitializer emptyAnnot x2)
  | .JSYieldExpression _ x => .JSYieldExpression a (fixMaybeExpression spaceAnnot x)
  | .JSYieldFromExpression _ _ x =>
      .JSYieldFromExpression a emptyAnnot (fixExpression emptyAnnot x)
  | .JSSpreadExpression _ e => .JSSpreadExpression a (fixExpression emptyAnnot e)

partial def fixArrowParameterList (_a : JSAnnot) : JSArrowParameterList → JSArrowParameterList
  | .JSUnparenthesizedArrowParameter p => .JSUnparenthesizedArrowParameter (fixIdent emptyAnnot p)
  | .JSParenthesizedArrowParameterList _ ps _ =>
      .JSParenthesizedArrowParameterList emptyAnnot (fixExprCommaList emptyAnnot ps) emptyAnnot

partial def fixBinOpExpression (a : JSAnnot) (op : JSBinOp) (lhs rhs : JSExpression) :
    JSExpression :=
  match op with
  | .JSBinOpPlus _ => fixBinOpPlus a lhs rhs
  | .JSBinOpIn _ =>
      .JSExpressionBinary (fixExpression a lhs) (.JSBinOpIn spaceAnnot)
        (fixExpression spaceAnnot rhs)
  | .JSBinOpInstanceOf _ =>
      .JSExpressionBinary (fixExpression a lhs) (.JSBinOpInstanceOf spaceAnnot)
        (fixExpression spaceAnnot rhs)
  | _ =>
      .JSExpressionBinary (fixExpression a lhs) (fixBinOp emptyAnnot op)
        (fixExpression emptyAnnot rhs)

partial def fixBinOpPlus (a : JSAnnot) (lhs rhs : JSExpression) : JSExpression :=
  match fixExpression a lhs, fixExpression emptyAnnot rhs with
  | .JSStringLiteral _ s1, .JSStringLiteral _ s2 =>
      stringLitConcat (normalizeToSQ s1) (normalizeToSQ s2)
  | nlhs, nrhs => .JSExpressionBinary nlhs (.JSBinOpPlus emptyAnnot) nrhs

partial def fixVarList : JSCommaList JSExpression → JSCommaList JSExpression
  | .JSLCons h _ v => .JSLCons (fixVarList h) emptyAnnot (fixExpression emptyAnnot v)
  | .JSLOne a => .JSLOne (fixExpression spaceAnnot a)
  | .JSLNil => .JSLNil

partial def fixExprCommaList (_a : JSAnnot) :
    JSCommaList JSExpression → JSCommaList JSExpression
  | .JSLCons xs _ x =>
      .JSLCons (fixExprCommaList emptyAnnot xs) emptyAnnot (fixExpression emptyAnnot x)
  | .JSLOne a => .JSLOne (fixExpression emptyAnnot a)
  | .JSLNil => .JSLNil

partial def fixObjectPropertyCommaList :
    JSCommaList JSObjectProperty → JSCommaList JSObjectProperty
  | .JSLCons xs _ x =>
      .JSLCons (fixObjectPropertyCommaList xs) emptyAnnot (fixObjectProperty emptyAnnot x)
  | .JSLOne a => .JSLOne (fixObjectProperty emptyAnnot a)
  | .JSLNil => .JSLNil

partial def fixObjectPropertyList (_a : JSAnnot) :
    JSCommaTrailingList JSObjectProperty → JSCommaTrailingList JSObjectProperty
  | .JSCTLComma xs _ => .JSCTLNone (fixObjectPropertyCommaList xs)
  | .JSCTLNone xs => .JSCTLNone (fixObjectPropertyCommaList xs)

partial def fixObjectProperty (a : JSAnnot) : JSObjectProperty → JSObjectProperty
  | .JSPropertyNameandValue n _ vs =>
      .JSPropertyNameandValue (fixPropertyName a n) emptyAnnot (fixExpressions vs)
  | .JSPropertyIdentRef _ s => .JSPropertyIdentRef a s
  | .JSObjectMethod m => .JSObjectMethod (fixMethodDefinition a m)

partial def fixMethodDefinition (a : JSAnnot) : JSMethodDefinition → JSMethodDefinition
  | .JSMethodDefinition n _ ps _ b =>
      .JSMethodDefinition (fixPropertyName a n) emptyAnnot (fixExprCommaList emptyAnnot ps)
        emptyAnnot (fixBlock emptyAnnot b)
  | .JSGeneratorMethodDefinition _ n _ ps _ b =>
      .JSGeneratorMethodDefinition emptyAnnot (fixPropertyName emptyAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot ps) emptyAnnot (fixBlock emptyAnnot b)
  | .JSPropertyAccessor s n _ ps _ b =>
      .JSPropertyAccessor (fixAccessor a s) (fixPropertyName spaceAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot ps) emptyAnnot (fixBlock emptyAnnot b)

partial def fixPropertyName (a : JSAnnot) : JSPropertyName → JSPropertyName
  | .JSPropertyIdent _ s => .JSPropertyIdent a s
  | .JSPropertyString _ s => .JSPropertyString a s
  | .JSPropertyNumber _ s => .JSPropertyNumber a s
  | .JSPropertyComputed _ x _ =>
      .JSPropertyComputed emptyAnnot (fixExpression emptyAnnot x) emptyAnnot

partial def fixBlock (_a : JSAnnot) : JSBlock → JSBlock
  | .JSBlock _ ss _ => .JSBlock emptyAnnot (fixStatementList noSemi ss) emptyAnnot

partial def fixTryCatch (a : JSAnnot) : JSTryCatch → JSTryCatch
  | .JSCatch _ _ x1 _ x3 =>
      .JSCatch a emptyAnnot (fixExpression emptyAnnot x1) emptyAnnot (fixBlock emptyAnnot x3)
  | .JSCatchIf _ _ x1 _ ex _ x3 =>
      .JSCatchIf a emptyAnnot (fixExpression emptyAnnot x1) spaceAnnot
        (fixExpression spaceAnnot ex) emptyAnnot (fixBlock emptyAnnot x3)

partial def fixTryCatches : List JSTryCatch → List JSTryCatch
  | [] => []
  | x :: xs => fixTryCatch emptyAnnot x :: fixTryCatches xs

partial def fixTryFinally (a : JSAnnot) : JSTryFinally → JSTryFinally
  | .JSFinally _ x => .JSFinally a (fixBlock emptyAnnot x)
  | .JSNoFinally => .JSNoFinally

partial def fixSwitchParts : List JSSwitchParts → List JSSwitchParts
  | [] => []
  | [x] => [fixSwitchPart noSemi x]
  | x :: xs => fixSwitchPart semi x :: fixSwitchParts xs

partial def fixSwitchPart (s : JSSemi) : JSSwitchParts → JSSwitchParts
  | .JSCase _ e _ ss => .JSCase emptyAnnot (fixCase e) emptyAnnot (fixStatementList s ss)
  | .JSDefault _ _ ss => .JSDefault emptyAnnot emptyAnnot (fixStatementList s ss)

partial def fixCase : JSExpression → JSExpression
  | .JSStringLiteral _ s => .JSStringLiteral emptyAnnot s
  | e => fixExpression spaceAnnot e

partial def fixArrayElement (_a : JSAnnot) : JSArrayElement → JSArrayElement
  | .JSArrayElement e => .JSArrayElement (fixExpression emptyAnnot e)
  | .JSArrayComma _ => .JSArrayComma emptyAnnot

partial def fixArrayElements : List JSArrayElement → List JSArrayElement
  | [] => []
  | x :: xs => fixArrayElement emptyAnnot x :: fixArrayElements xs

partial def fixExpressions : List JSExpression → List JSExpression
  | [] => []
  | x :: xs => fixExpression emptyAnnot x :: fixExpressions xs

partial def fixMaybeExpression (a : JSAnnot) : Option JSExpression → Option JSExpression
  | some e => some (fixExpression a e)
  | none => none

partial def fixVarInitializer (a : JSAnnot) : JSVarInitializer → JSVarInitializer
  | .JSVarInit _ x => .JSVarInit a (fixExpression emptyAnnot x)
  | .JSVarInitNone => .JSVarInitNone

partial def fixTemplatePart : JSTemplatePart → JSTemplatePart
  | .JSTemplatePart e _ s => .JSTemplatePart (fixExpression emptyAnnot e) emptyAnnot s

partial def fixTemplateParts : List JSTemplatePart → List JSTemplatePart
  | [] => []
  | x :: xs => fixTemplatePart x :: fixTemplateParts xs

partial def fixClassHeritage (a : JSAnnot) : JSClassHeritage → JSClassHeritage
  | .JSExtendsNone => .JSExtendsNone
  | .JSExtends _ e => .JSExtends a (fixExpression spaceAnnot e)

partial def fixClassElements (a : JSAnnot) : List JSClassElement → List JSClassElement
  | [] => []
  | .JSClassInstanceMethod m :: t =>
      .JSClassInstanceMethod (fixMethodDefinition a m) :: fixClassElements emptyAnnot t
  | .JSClassStaticMethod _ m :: t =>
      .JSClassStaticMethod a (fixMethodDefinition spaceAnnot m) :: fixClassElements emptyAnnot t
  | .JSClassSemi _ :: t => fixClassElements a t

partial def fixExportDeclaration (a : JSAnnot) : JSExportDeclaration → JSExportDeclaration
  | .JSExportFrom x1 from_ _ => .JSExportFrom (fixExportClause a x1) (fixFromClause a from_) noSemi
  | .JSExportLocals x1 _ => .JSExportLocals (fixExportClause emptyAnnot x1) noSemi
  | .JSExport x1 _ => .JSExport (fixStmt spaceAnnot noSemi x1) noSemi

partial def fixModuleItem (a : JSAnnot) : JSModuleItem → JSModuleItem
  | .JSModuleImportDeclaration _ x1 =>
      .JSModuleImportDeclaration emptyAnnot (fixImportDeclaration emptyAnnot x1)
  | .JSModuleExportDeclaration _ x1 =>
      .JSModuleExportDeclaration emptyAnnot (fixExportDeclaration emptyAnnot x1)
  | .JSModuleStatementListItem s => .JSModuleStatementListItem (fixStmt a noSemi s)

partial def fixModuleItems : List JSModuleItem → List JSModuleItem
  | [] => []
  | x :: xs => fixModuleItem emptyAnnot x :: fixModuleItems xs

end

/-- Minify a JavaScript AST: remove all unnecessary whitespace and
punctuation. -/
def minifyJS : JSAST → JSAST
  | .JSAstProgram xs _ => .JSAstProgram (fixStatementList noSemi xs) emptyAnnot
  | .JSAstModule xs _ => .JSAstModule (fixModuleItems xs) emptyAnnot
  | .JSAstStatement (.JSStatementBlock _ [s] _ _) _ =>
      .JSAstStatement (fixStmt emptyAnnot noSemi s) emptyAnnot
  | .JSAstStatement s _ => .JSAstStatement (fixStmt emptyAnnot noSemi s) emptyAnnot
  | .JSAstExpression e _ => .JSAstExpression (fixExpression emptyAnnot e) emptyAnnot
  | .JSAstLiteral s _ => .JSAstLiteral (fixExpression emptyAnnot s) emptyAnnot

end LanguageJavaScript.Process
