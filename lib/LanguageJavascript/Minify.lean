/-
Port of `Language.JavaScript.Process.Minify` to Lean 4.

The Haskell version uses a `MinifyJS` class with a single method
`fix :: JSAnnot -> a -> a`; here each instance becomes a function `fix<Type>`.
The statement list handling ("force semicolons between statements, drop
redundant statements, splice nested blocks") is written so that it recurses
on components of its argument only; see the comment before
`isRedundantStmt`.  The group is therefore an ordinary (structurally
recursive) definition: it has equations and reduces in the kernel.
-/
import LanguageJavascript.AST

namespace Language.JavaScript.Process

open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

/-- A single space of whitespace. -/
def spaceAnnot : JSAnnot := .JSAnnot TokenPosn.empty [.WhiteSpace TokenPosn.empty " ".toRawSubstring]

/-- No annotation at all. -/
def emptyAnnot : JSAnnot := .JSNoAnnot

/-- A newline. -/
def newlineAnnot : JSAnnot := .JSAnnot TokenPosn.empty [.WhiteSpace TokenPosn.empty "\n".toRawSubstring]

def semi : JSSemi := .JSSemi emptyAnnot

def noSemi : JSSemi := .JSSemiAuto

/-- Concatenate two non-empty comma lists: the declarators of two `var`
statements which are being merged into one. -/
def concatCommaList1 {a : Type} (xs ys : JSCommaList1 a) : JSCommaList1 a :=
  xs.append emptyAnnot ys

/-- Requote the body of a double quoted literal for single quotes: a single
quote has to be escaped, an escaped double quote no longer has to be.

The body is read by byte index and the result is built by pushing characters
onto it, so neither string becomes a list of characters.  `fuel` bounds the
number of characters left to read; the number of bytes left is always
enough, since every step consumes at least one byte. -/
private def convertSQ (body : String) : Nat → String.Pos.Raw → String → String
  | 0, _, acc => acc
  | fuel + 1, p, acc =>
      if body.utf8ByteSize ≤ p.byteIdx then acc
      else
        let c := String.Pos.Raw.get body p
        let q := String.Pos.Raw.next body p
        if c == '\'' then convertSQ body fuel q ((acc.push '\\').push '\'')
        else if c == '\\' && String.Pos.Raw.get body q == '"' then
          convertSQ body fuel (String.Pos.Raw.next body q) (acc.push '"')
        else convertSQ body fuel q (acc.push c)

/-- Normalize a string literal.  If it is single quoted, just return it; if it
is double quoted, convert it to single quoted. -/
def normalizeToSQ (str : JSStringSrc) : JSStringSrc :=
  match str.quote with
  | .single => str
  | .double => ⟨.single, convertSQ str.body (str.body.utf8ByteSize) ⟨0⟩ ""⟩

/-- Concatenate two string literals.  Both have been normalised to single
quotes, so the result is the two bodies, between one pair of quotes. -/
def stringLitConcat (xs ys : JSStringSrc) : JSExpression :=
  .JSStringLiteral emptyAnnot ⟨.single, xs.body ++ ys.body⟩

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
  | .JSBinOpNullish _ => .JSBinOpNullish emptyAnnot
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
  | .JSLogicalAndAssign _ => .JSLogicalAndAssign a
  | .JSLogicalOrAssign _ => .JSLogicalOrAssign a
  | .JSNullishAssign _ => .JSNullishAssign a

def fixIdent (a : JSAnnot) : JSIdent → JSIdent
  | .JSIdentName _ n => .JSIdentName a n
  | .JSIdentNone => .JSIdentNone

def fixAccessor (a : JSAnnot) : JSAccessor → JSAccessor
  | .JSAccessorGet _ => .JSAccessorGet a
  | .JSAccessorSet _ => .JSAccessorSet a

def fixImportAttribute : JSImportAttribute → JSImportAttribute
  | .JSImportAttribute _ k _ _ v => .JSImportAttribute emptyAnnot k emptyAnnot emptyAnnot v

def fixImportAttrCommaList : JSCommaList JSImportAttribute → JSCommaList JSImportAttribute
  | .JSLCons xs _ x => .JSLCons (fixImportAttrCommaList xs) emptyAnnot (fixImportAttribute x)
  | .JSLOne x => .JSLOne (fixImportAttribute x)
  | .JSLNil => .JSLNil

/-- The `with { ... }` of an import: a space keeps `with` apart from the
module string it follows. -/
def fixImportAttributes? : Option JSImportAttributes → Option JSImportAttributes
  | none => none
  | some (.JSImportAttributes _ _ attrs _) =>
      some (.JSImportAttributes spaceAnnot emptyAnnot (fixImportAttrCommaList attrs) emptyAnnot)

def fixFromClause (a : JSAnnot) : JSFromClause → JSFromClause
  | .JSFromClause _ _ m attrs => .JSFromClause a emptyAnnot m (fixImportAttributes? attrs)

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
  | .JSImportDeclarationBare _ m attrs _ =>
      .JSImportDeclarationBare a m (fixImportAttributes? attrs) noSemi

def fixExportClause (a : JSAnnot) : JSExportClause → JSExportClause
  | .JSExportClause _ x1 _ => .JSExportClause emptyAnnot (fixExportSpecCommaList emptyAnnot x1) a

/-! ## Statement lists

Three things happen to a statement list: an empty statement and an empty
block disappear, a nested block is spliced into the list around it, and two
neighbouring `var` (or `const`) declarations become one.

Doing that by rewriting the list — filtering it, and putting the merged
declaration back in front of the rest — is what used to cost this module
its recursion: neither the filtered list nor the merged declaration is a
component of anything, so `fixStmtList` had to be `partial`, which left the
whole group opaque to the kernel.

It is now done in one pass, and the pass recurses on components only:

* `filt` says whether the statements which disappear are to be dropped, so
  no list is filtered first;
* `pend` carries the declarators of the run of declarations being merged,
  already converted, so no declaration is rebuilt and converted afterwards;
* the statement of a body (`mkStatementBlock`, `fixIfElseBlock`) and the
  list of a block (`fixStatementBlock`) are given the conversion of what
  they may need as a function, because the caller has it as a component of
  the node it is looking at.

The predicates below are what replaces the look ahead into the filtered
list; they only look at the shape of a statement, so they are outside the
group. -/

/-- Statements which disappear from a statement list. -/
def isRedundantStmt : JSStatement → Bool
  | .JSStatementBlock _ [] _ _ => true
  | .JSEmptyStatement _ => true
  | _ => false

/-- Does every statement of the list disappear? -/
def allRedundant : List JSStatement → Bool
  | [] => true
  | x :: xs => isRedundantStmt x && allRedundant xs

/-- Is there no statement left after the one being looked at? -/
def isLastStmt (filt : Bool) (xs : List JSStatement) : Bool :=
  if filt then allRedundant xs else xs.isEmpty

/-- Is the next statement of the list a function declaration?  Two of them
in a row are separated by a newline. -/
def nextIsFunction (filt : Bool) : List JSStatement → Bool
  | [] => false
  | .JSFunction .. :: _ => true
  | x :: xs => filt && isRedundantStmt x && nextIsFunction filt xs

/-- The declaration a run of merged declarators becomes. -/
def declStmt (isConst : Bool) (a : JSAnnot) (vs : JSCommaList1 JSExpression) (s : JSSemi) :
    JSStatement :=
  if isConst then .JSConstant a vs s else .JSVariable a vs s

/-- Is the statement a function declaration? -/
def isFunctionStmt : JSStatement → Bool
  | .JSFunction .. => true
  | _ => false

/-- Emit the run of declarators waiting to be merged, if there is one: the
statement it becomes, and the annotation which the statement after it
carries. -/
def flushPend (pend : Option (Bool × JSCommaList1 JSExpression)) (a : JSAnnot) :
    List JSStatement × JSAnnot :=
  match pend with
  | none => ([], a)
  | some (isConst, vs) => ([declStmt isConst a vs semi], emptyAnnot)

/-- The body of an `if` or of an `else`: an empty block becomes an empty
statement.  `self` is the conversion of `st` as a statement, which the
caller passes because it has `st` as a component of the node it is
converting. -/
def fixIfElseBlock (st : JSStatement) (self : Unit → JSStatement) : JSStatement :=
  match st with
  | .JSStatementBlock _ [] _ _ => .JSEmptyStatement emptyAnnot
  | _ => self ()

set_option maxHeartbeats 2000000 in
mutual
def fixStmt (a : JSAnnot) (s : JSSemi) : JSStatement → JSStatement
  | .JSStatementBlock _ ss _ _ =>
      fixStatementBlock a s (fun _ => fixStmtList emptyAnnot noSemi none true ss) ss
  | .JSBreak _ i _ => .JSBreak a (fixIdent spaceAnnot i) s
  | .JSClass ds _ n h _ ms _ _ =>
      .JSClass (fixDecorators a ds) (if ds.isEmpty then a else spaceAnnot)
        (fixIdent spaceAnnot n) (fixClassHeritage spaceAnnot h) emptyAnnot
        (fixClassElements emptyAnnot ms) emptyAnnot s
  | .JSConstant _ ss _ => .JSConstant a (fixVarList ss) s
  | .JSUsing _ ss _ => .JSUsing a (fixVarList ss) s
  | .JSAwaitUsing _ _ ss _ => .JSAwaitUsing a spaceAnnot (fixVarList ss) s
  | .JSContinue _ i _ => .JSContinue a (fixIdent spaceAnnot i) s
  | .JSDoWhile _ st _ _ e _ _ =>
      .JSDoWhile a (mkStatementBlock noSemi st (fun _ => fixStmt emptyAnnot noSemi st))
        emptyAnnot emptyAnnot (fixExpression emptyAnnot e) emptyAnnot s
  | .JSFor _ _ el1 _ el2 _ el3 _ st =>
      .JSFor a emptyAnnot (fixExprCommaList emptyAnnot el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForIn _ _ e1 op e2 _ st =>
      .JSForIn a emptyAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForVar _ _ _ el1 _ el2 _ el3 _ st =>
      .JSForVar a emptyAnnot spaceAnnot (fixExprCommaList1 el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForVarIn _ _ _ e1 op e2 _ st =>
      .JSForVarIn a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForLet _ _ _ el1 _ el2 _ el3 _ st =>
      .JSForLet a emptyAnnot spaceAnnot (fixExprCommaList1 el1) emptyAnnot
        (fixExprCommaList emptyAnnot el2) emptyAnnot (fixExprCommaList emptyAnnot el3) emptyAnnot
        (fixStmt emptyAnnot s st)
  | .JSForLetIn _ _ _ e1 op e2 _ st =>
      .JSForLetIn a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForLetOf _ _ _ e1 op e2 _ st =>
      .JSForLetOf a emptyAnnot spaceAnnot (fixExpression emptyAnnot e1) (fixBinOp spaceAnnot op)
        (fixExpression spaceAnnot e2) emptyAnnot (fixStmt emptyAnnot s st)
  | .JSForConst _ _ _ el1 _ el2 _ el3 _ st =>
      .JSForConst a emptyAnnot spaceAnnot (fixExprCommaList1 el1) emptyAnnot
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
      .JSIf a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot
        (fixIfElseBlock st (fun _ => fixStmt emptyAnnot s st))
  | .JSIfElse _ _ e _ (.JSEmptyStatement _) _ sf =>
      .JSIfElse a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot
        (.JSEmptyStatement emptyAnnot) emptyAnnot (fixStmt spaceAnnot s sf)
  | .JSIfElse _ _ e _ st _ sf =>
      .JSIfElse a emptyAnnot (fixExpression emptyAnnot e) emptyAnnot
        (mkStatementBlock noSemi st (fun _ => fixStmt emptyAnnot noSemi st))
        emptyAnnot (fixIfElseBlock sf (fun _ => fixStmt spaceAnnot s sf))
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
termination_by structural x => x

/-- Turn a single `JSStatement` into a `JSStatementBlock`; `self` is as in
`fixIfElseBlock`. -/
def mkStatementBlock (s : JSSemi) (st : JSStatement) (self : Unit → JSStatement) :
    JSStatement :=
  match st with
  | .JSStatementBlock _ blk _ _ =>
      .JSStatementBlock emptyAnnot (fixStmtList emptyAnnot noSemi none true blk) emptyAnnot s
  | _ => .JSStatementBlock emptyAnnot [self ()] emptyAnnot s
termination_by structural st

/-- The statements of a block, as a statement: the statements which
disappear are dropped, and a block which is left with a single statement is
that statement.  `whole` is the conversion of the whole list, which the
caller passes because it has the list as a component of the node it is
converting. -/
def fixStatementBlock (a : JSAnnot) (s : JSSemi) (whole : Unit → List JSStatement) :
    List JSStatement → JSStatement
  | [] => .JSStatementBlock emptyAnnot [] emptyAnnot s
  | x :: xs =>
      if isRedundantStmt x then fixStatementBlock a s whole xs
      else if allRedundant xs then fixStmt a s x
      else .JSStatementBlock emptyAnnot (whole ()) emptyAnnot s
termination_by structural x => x

/-- Convert a statement list: force the semicolons between the statements,
make sure the last one has none, drop the statements which disappear (when
`filt`), splice the nested blocks and merge the neighbouring declarations.

`pend` is the run of declarations being merged: `some (isConst, vs)` is a
`const` (respectively `var`) statement whose declarators `vs` are already
converted and which is waiting to be put in front of what follows it; it is
emitted by `flushPend` as soon as a statement which is not a declaration of
the same kind turns up.

The head of the list is destructured by the patterns of this `match` and
never by a nested one, because a nested `match` on it would hide from the
kernel that it is a component of the list. -/
def fixStmtList (a : JSAnnot) (s : JSSemi)
    (pend : Option (Bool × JSCommaList1 JSExpression)) (filt : Bool) :
    List JSStatement → List JSStatement
  | [] =>
      match pend with
      | none => []
      | some (isConst, vs) => [declStmt isConst a vs s]
  | .JSConstant _ vs1 _ :: xs =>
      match pend with
      | some (true, vs) =>
          fixStmtList a s (some (true, concatCommaList1 vs (fixExprCommaList1 vs1))) filt xs
      | some (false, vs) =>
          declStmt false a vs semi ::
            fixStmtList emptyAnnot s (some (true, fixVarList vs1)) filt xs
      | none => fixStmtList a s (some (true, fixVarList vs1)) filt xs
  | .JSVariable _ vs1 _ :: xs =>
      match pend with
      | some (false, vs) =>
          fixStmtList a s (some (false, concatCommaList1 vs (fixExprCommaList1 vs1))) filt xs
      | some (true, vs) =>
          declStmt true a vs semi ::
            fixStmtList emptyAnnot s (some (false, fixVarList vs1)) filt xs
      | none => fixStmtList a s (some (false, fixVarList vs1)) filt xs
  | .JSStatementBlock _ blk _ _ :: xs =>
      if filt && blk.isEmpty then fixStmtList a s pend filt xs
      else
        let (pre, a') := flushPend pend a
        pre ++
          (if isLastStmt filt xs then fixStmtList a' s none false blk
           else
             fixStmtList emptyAnnot semi none true blk ++ fixStmtList emptyAnnot s none filt xs)
  | x :: xs =>
      if filt && isRedundantStmt x then fixStmtList a s pend filt xs
      else
        let (pre, a') := flushPend pend a
        pre ++
          (if isLastStmt filt xs then [fixStmt a' s x]
           else if isFunctionStmt x && nextIsFunction filt xs then
             fixStmt a' noSemi x :: fixStmtList newlineAnnot s none filt xs
           else fixStmt a' semi x :: fixStmtList emptyAnnot s none filt xs)
termination_by structural x => x

def fixExpression (a : JSAnnot) : JSExpression → JSExpression
  -- Terminals
  | .JSIdentifier _ s => .JSIdentifier a s
  | .JSNumberLit _ s => .JSNumberLit a s
  | .JSLiteral _ s => .JSLiteral a s
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
  | .JSClassExpression ds _ n h _ ms _ =>
      .JSClassExpression (fixDecorators a ds) (if ds.isEmpty then a else spaceAnnot)
        (fixIdent spaceAnnot n) (fixClassHeritage spaceAnnot h) emptyAnnot
        (fixClassElements emptyAnnot ms) emptyAnnot
  | .JSCommaExpression le _ re =>
      .JSCommaExpression (fixExpression a le) emptyAnnot (fixExpression emptyAnnot re)
  | .JSExpressionBinary lhs op rhs =>
      match op with
      | .JSBinOpPlus _ =>
          match fixExpression a lhs, fixExpression emptyAnnot rhs with
          | .JSStringLiteral _ s1, .JSStringLiteral _ s2 =>
              stringLitConcat (normalizeToSQ s1) (normalizeToSQ s2)
          | nlhs, nrhs => .JSExpressionBinary nlhs (.JSBinOpPlus emptyAnnot) nrhs
      | .JSBinOpIn _ =>
          .JSExpressionBinary (fixExpression a lhs) (.JSBinOpIn spaceAnnot)
            (fixExpression spaceAnnot rhs)
      | .JSBinOpInstanceOf _ =>
          .JSExpressionBinary (fixExpression a lhs) (.JSBinOpInstanceOf spaceAnnot)
            (fixExpression spaceAnnot rhs)
      | _ =>
          .JSExpressionBinary (fixExpression a lhs) (fixBinOp emptyAnnot op)
            (fixExpression emptyAnnot rhs)
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
  | .JSOptionalMemberDot xs _ n =>
      .JSOptionalMemberDot (fixExpression a xs) emptyAnnot (fixExpression emptyAnnot n)
  | .JSOptionalMemberSquare xs _ _ e _ =>
      .JSOptionalMemberSquare (fixExpression a xs) emptyAnnot emptyAnnot
        (fixExpression emptyAnnot e) emptyAnnot
  | .JSOptionalCallExpression ex _ _ xs _ =>
      .JSOptionalCallExpression (fixExpression a ex) emptyAnnot emptyAnnot
        (fixExprCommaList emptyAnnot xs) emptyAnnot
  | .JSPrivateName _ n => .JSPrivateName a n
  | .JSImportMeta _ _ _ => .JSImportMeta a emptyAnnot emptyAnnot
  | .JSNewTarget _ _ _ => .JSNewTarget a emptyAnnot emptyAnnot
  | .JSImportCall _ _ xs _ =>
      .JSImportCall a emptyAnnot (fixExprCommaList emptyAnnot xs) emptyAnnot
  | .JSNewExpression _ e => .JSNewExpression a (fixExpression spaceAnnot e)
  | .JSObjectLiteral _ xs _ =>
      .JSObjectLiteral emptyAnnot (fixObjectPropertyList emptyAnnot xs) emptyAnnot
  | .JSTemplateLiteral t _ s ps =>
      .JSTemplateLiteral (fixMaybeExpression a t) emptyAnnot s (fixTemplateParts ps)
  | .JSUnaryExpression op x =>
      let (ta, fop) := fixUnaryOp a op
      .JSUnaryExpression fop (fixExpression ta x)
  | .JSVarInitExpression x1 x2 =>
      .JSVarInitExpression (fixExpression a x1) (fixVarInitializer emptyAnnot x2)
  | .JSYieldExpression _ x => .JSYieldExpression a (fixMaybeExpression spaceAnnot x)
  | .JSYieldFromExpression _ _ x =>
      .JSYieldFromExpression a emptyAnnot (fixExpression emptyAnnot x)
  | .JSSpreadExpression _ e => .JSSpreadExpression a (fixExpression emptyAnnot e)
termination_by structural x => x

def fixArrowParameterList (_a : JSAnnot) : JSArrowParameterList → JSArrowParameterList
  | .JSUnparenthesizedArrowParameter p => .JSUnparenthesizedArrowParameter (fixIdent emptyAnnot p)
  | .JSParenthesizedArrowParameterList _ ps _ =>
      .JSParenthesizedArrowParameterList emptyAnnot (fixExprCommaList emptyAnnot ps) emptyAnnot
termination_by structural x => x

def fixVarList : JSCommaList1 JSExpression → JSCommaList1 JSExpression
  | .JSL1Cons h _ v => .JSL1Cons (fixVarList h) emptyAnnot (fixExpression emptyAnnot v)
  | .JSL1One a => .JSL1One (fixExpression spaceAnnot a)
termination_by structural x => x

/-- The declarators of a `for (var ...; ...; ...)`, which are a non-empty
comma list. -/
def fixExprCommaList1 : JSCommaList1 JSExpression → JSCommaList1 JSExpression
  | .JSL1Cons xs _ x => .JSL1Cons (fixExprCommaList1 xs) emptyAnnot (fixExpression emptyAnnot x)
  | .JSL1One a => .JSL1One (fixExpression emptyAnnot a)
termination_by structural x => x

def fixExprCommaList (_a : JSAnnot) :
    JSCommaList JSExpression → JSCommaList JSExpression
  | .JSLCons xs _ x =>
      .JSLCons (fixExprCommaList emptyAnnot xs) emptyAnnot (fixExpression emptyAnnot x)
  | .JSLOne a => .JSLOne (fixExpression emptyAnnot a)
  | .JSLNil => .JSLNil
termination_by structural x => x

def fixObjectPropertyCommaList :
    JSCommaList JSObjectProperty → JSCommaList JSObjectProperty
  | .JSLCons xs _ x =>
      .JSLCons (fixObjectPropertyCommaList xs) emptyAnnot (fixObjectProperty emptyAnnot x)
  | .JSLOne a => .JSLOne (fixObjectProperty emptyAnnot a)
  | .JSLNil => .JSLNil
termination_by structural x => x

def fixObjectPropertyList (_a : JSAnnot) :
    JSCommaTrailingList JSObjectProperty → JSCommaTrailingList JSObjectProperty
  | .JSCTLComma xs _ => .JSCTLNone (fixObjectPropertyCommaList xs)
  | .JSCTLNone xs => .JSCTLNone (fixObjectPropertyCommaList xs)
termination_by structural x => x

def fixObjectProperty (a : JSAnnot) : JSObjectProperty → JSObjectProperty
  | .JSPropertyNameandValue n _ v =>
      .JSPropertyNameandValue (fixPropertyName a n) emptyAnnot (fixExpression emptyAnnot v)
  | .JSPropertyIdentRef _ s => .JSPropertyIdentRef a s
  | .JSPropertyIdentRefDefault _ s _ v =>
      .JSPropertyIdentRefDefault a s emptyAnnot (fixExpression emptyAnnot v)
  | .JSObjectSpread _ e => .JSObjectSpread a (fixExpression emptyAnnot e)
  | .JSObjectMethod m => .JSObjectMethod (fixMethodDefinition a m)
termination_by structural x => x

def fixMethodDefinition (a : JSAnnot) : JSMethodDefinition → JSMethodDefinition
  | .JSMethodDefinition n _ ps _ b =>
      .JSMethodDefinition (fixPropertyName a n) emptyAnnot (fixExprCommaList emptyAnnot ps)
        emptyAnnot (fixBlock emptyAnnot b)
  | .JSGeneratorMethodDefinition _ n _ ps _ b =>
      .JSGeneratorMethodDefinition emptyAnnot (fixPropertyName emptyAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot ps) emptyAnnot (fixBlock emptyAnnot b)
  | .JSPropertyAccessor s n _ ps _ b =>
      .JSPropertyAccessor (fixAccessor a s) (fixPropertyName spaceAnnot n) emptyAnnot
        (fixExprCommaList emptyAnnot ps) emptyAnnot (fixBlock emptyAnnot b)
termination_by structural x => x

def fixPropertyName (a : JSAnnot) : JSPropertyName → JSPropertyName
  | .JSPropertyIdent _ s => .JSPropertyIdent a s
  | .JSPropertyPrivate _ s => .JSPropertyPrivate a s
  | .JSPropertyString _ s => .JSPropertyString a s
  | .JSPropertyNumber _ s => .JSPropertyNumber a s
  | .JSPropertyComputed _ x _ =>
      .JSPropertyComputed emptyAnnot (fixExpression emptyAnnot x) emptyAnnot
termination_by structural x => x

def fixBlock (_a : JSAnnot) : JSBlock → JSBlock
  | .JSBlock _ ss _ =>
      .JSBlock emptyAnnot (fixStmtList emptyAnnot noSemi none true ss) emptyAnnot
termination_by structural x => x

def fixTryCatch (a : JSAnnot) : JSTryCatch → JSTryCatch
  | .JSCatch _ _ x1 _ x3 =>
      .JSCatch a emptyAnnot (fixExpression emptyAnnot x1) emptyAnnot (fixBlock emptyAnnot x3)
  | .JSCatchIf _ _ x1 _ ex _ x3 =>
      .JSCatchIf a emptyAnnot (fixExpression emptyAnnot x1) spaceAnnot
        (fixExpression spaceAnnot ex) emptyAnnot (fixBlock emptyAnnot x3)
termination_by structural x => x

def fixTryCatches : List JSTryCatch → List JSTryCatch
  | [] => []
  | x :: xs => fixTryCatch emptyAnnot x :: fixTryCatches xs
termination_by structural x => x

def fixTryFinally (a : JSAnnot) : JSTryFinally → JSTryFinally
  | .JSFinally _ x => .JSFinally a (fixBlock emptyAnnot x)
  | .JSNoFinally => .JSNoFinally
termination_by structural x => x

def fixSwitchParts : List JSSwitchParts → List JSSwitchParts
  | [] => []
  | [x] => [fixSwitchPart noSemi x]
  | x :: xs => fixSwitchPart semi x :: fixSwitchParts xs
termination_by structural x => x

def fixSwitchPart (s : JSSemi) : JSSwitchParts → JSSwitchParts
  | .JSCase _ e _ ss =>
      .JSCase emptyAnnot (fixExpression spaceAnnot e) emptyAnnot
        (fixStmtList emptyAnnot s none true ss)
  | .JSDefault _ _ ss =>
      .JSDefault emptyAnnot emptyAnnot (fixStmtList emptyAnnot s none true ss)
termination_by structural x => x

def fixArrayElement (_a : JSAnnot) : JSArrayElement → JSArrayElement
  | .JSArrayElement e => .JSArrayElement (fixExpression emptyAnnot e)
  | .JSArrayComma _ => .JSArrayComma emptyAnnot
termination_by structural x => x

def fixArrayElements : List JSArrayElement → List JSArrayElement
  | [] => []
  | x :: xs => fixArrayElement emptyAnnot x :: fixArrayElements xs
termination_by structural x => x

def fixMaybeExpression (a : JSAnnot) : Option JSExpression → Option JSExpression
  | some e => some (fixExpression a e)
  | none => none
termination_by structural x => x

def fixVarInitializer (a : JSAnnot) : JSVarInitializer → JSVarInitializer
  | .JSVarInit _ x => .JSVarInit a (fixExpression emptyAnnot x)
  | .JSVarInitNone => .JSVarInitNone
termination_by structural x => x

def fixTemplatePart : JSTemplatePart → JSTemplatePart
  | .JSTemplatePart e _ s => .JSTemplatePart (fixExpression emptyAnnot e) emptyAnnot s
termination_by structural x => x

def fixTemplateParts : List JSTemplatePart → List JSTemplatePart
  | [] => []
  | x :: xs => fixTemplatePart x :: fixTemplateParts xs
termination_by structural x => x

def fixClassHeritage (a : JSAnnot) : JSClassHeritage → JSClassHeritage
  | .JSExtendsNone => .JSExtendsNone
  | .JSExtends _ e => .JSExtends a (fixExpression spaceAnnot e)
termination_by structural x => x

def fixClassElements (a : JSAnnot) : List JSClassElement → List JSClassElement
  | [] => []
  | .JSClassInstanceMethod ds m :: t =>
      .JSClassInstanceMethod (fixDecorators a ds)
          (fixMethodDefinition (if ds.isEmpty then a else spaceAnnot) m)
        :: fixClassElements emptyAnnot t
  | .JSClassStaticMethod ds _ m :: t =>
      .JSClassStaticMethod (fixDecorators a ds) (if ds.isEmpty then a else spaceAnnot)
          (fixMethodDefinition spaceAnnot m)
        :: fixClassElements emptyAnnot t
  -- a field keeps its semicolon: it is what separates it from the next
  -- member
  | .JSClassInstanceField ds n i _ :: t =>
      .JSClassInstanceField (fixDecorators a ds)
          (fixPropertyName (if ds.isEmpty then a else spaceAnnot) n)
          (fixVarInitializer emptyAnnot i) semi
        :: fixClassElements emptyAnnot t
  | .JSClassStaticField ds _ n i _ :: t =>
      .JSClassStaticField (fixDecorators a ds) (if ds.isEmpty then a else spaceAnnot)
          (fixPropertyName spaceAnnot n) (fixVarInitializer emptyAnnot i) semi
        :: fixClassElements emptyAnnot t
  | .JSClassStaticBlock _ b :: t =>
      .JSClassStaticBlock a (fixBlock emptyAnnot b) :: fixClassElements emptyAnnot t
  | .JSClassSemi _ :: t => fixClassElements a t
termination_by structural x => x

/-- The decorators of a class or of one of its members; the first one
carries the annotation of the construct it decorates. -/
def fixDecorators (a : JSAnnot) : List JSDecorator → List JSDecorator
  | [] => []
  | .JSDecorator _ e :: t =>
      .JSDecorator a (fixExpression emptyAnnot e) :: fixDecorators spaceAnnot t
termination_by structural x => x

def fixExportDeclaration (a : JSAnnot) : JSExportDeclaration → JSExportDeclaration
  | .JSExportFrom x1 from_ _ => .JSExportFrom (fixExportClause a x1) (fixFromClause a from_) noSemi
  | .JSExportLocals x1 _ => .JSExportLocals (fixExportClause emptyAnnot x1) noSemi
  | .JSExportAll _ from_ _ => .JSExportAll a (fixFromClause emptyAnnot from_) noSemi
  | .JSExportAllAs _ _ n from_ _ =>
      .JSExportAllAs a spaceAnnot (fixIdent spaceAnnot n) (fixFromClause spaceAnnot from_) noSemi
  | .JSExportDefault _ e _ => .JSExportDefault a (fixExpression spaceAnnot e) noSemi
  | .JSExport x1 _ => .JSExport (fixStmt spaceAnnot noSemi x1) noSemi

def fixModuleItem (a : JSAnnot) : JSModuleItem → JSModuleItem
  | .JSModuleImportDeclaration _ x1 =>
      .JSModuleImportDeclaration emptyAnnot (fixImportDeclaration emptyAnnot x1)
  | .JSModuleExportDeclaration _ x1 =>
      .JSModuleExportDeclaration emptyAnnot (fixExportDeclaration emptyAnnot x1)
  | .JSModuleStatementListItem s => .JSModuleStatementListItem (fixStmt a noSemi s)

def fixModuleItems : List JSModuleItem → List JSModuleItem
  | [] => []
  | x :: xs => fixModuleItem emptyAnnot x :: fixModuleItems xs
termination_by structural x => x

end

/-- Convert a statement list: the entry point of the group above, which
starts with nothing pending and drops the statements which disappear. -/
def fixStatementList (trailingSemi : JSSemi) (ss : List JSStatement) : List JSStatement :=
  fixStmtList emptyAnnot trailingSemi none true ss

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

end Language.JavaScript.Process
