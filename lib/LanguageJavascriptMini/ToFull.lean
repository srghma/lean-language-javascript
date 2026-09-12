/-
Conversion of the deterministic `MiniAST` back into the annotated AST of
`RequestProject.JavaScript.AST`.

The conversion in this direction cannot invent what `MiniAST` deliberately
does not store — positions, comments, the original layout — so every token
is given the same annotation, a single space (`JSAnnotSpace`).  Rendering
the result with `Language.JavaScript.Pretty.renderToString` therefore
produces valid, if unattractive, JavaScript with one space between any two
tokens; `MiniASTPrinter` is what produces the pretty output.

What the conversion *does* guarantee is that no meaning is lost:
`ofAST (toAST p) = p` for every `MiniProgram p` that the annotated AST can
represent (see `RequestProject/Tests/MiniAST.lean`).
-/
import LanguageJavascriptMini.OfFull
import LanguageJavascriptMini.Printer
import LanguageJavascript.Printer

namespace Language.JavaScript.MiniAST

open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

/-- The annotation given to every token: a single space.  Keeping the tokens
separated is all that is needed for the result to render as valid source. -/
private def sp : JSAnnot := .JSAnnotSpace

private def semi : JSSemi := .JSSemi sp

private def toCommaList {α : Type} : List α → JSCommaList α
  | [] => .JSLNil
  | x :: xs => xs.foldl (fun acc y => .JSLCons acc sp y) (.JSLOne x)

/-- A non-empty list becomes a non-empty comma list. -/
private def toCommaList1 {α : Type} (l : NEList α) : JSCommaList1 α :=
  l.tl.foldl (fun acc y => .JSL1Cons acc sp y) (.JSL1One l.hd)

private def toIdent (n : NEString) : JSIdent := .JSIdentName sp n

private def toIdentOpt : Option NEString → JSIdent
  | none => .JSIdentNone
  | some n => toIdent n

/-- The literal node a numeric literal belongs to. -/
private def numberExpr (n : JSNumber) : JSExpression := JSExpression.ofNumber sp n

private def toBinOp : BinOp → JSBinOp
  | .and => .JSBinOpAnd sp
  | .or => .JSBinOpOr sp
  | .coalesce => .JSBinOpNullish sp
  | .bitAnd => .JSBinOpBitAnd sp
  | .bitOr => .JSBinOpBitOr sp
  | .bitXor => .JSBinOpBitXor sp
  | .eq => .JSBinOpEq sp
  | .neq => .JSBinOpNeq sp
  | .strictEq => .JSBinOpStrictEq sp
  | .strictNeq => .JSBinOpStrictNeq sp
  | .lt => .JSBinOpLt sp
  | .le => .JSBinOpLe sp
  | .gt => .JSBinOpGt sp
  | .ge => .JSBinOpGe sp
  | .lsh => .JSBinOpLsh sp
  | .rsh => .JSBinOpRsh sp
  | .ursh => .JSBinOpUrsh sp
  | .plus => .JSBinOpPlus sp
  | .minus => .JSBinOpMinus sp
  | .times => .JSBinOpTimes sp
  | .divide => .JSBinOpDivide sp
  | .mod => .JSBinOpMod sp
  | .inOp => .JSBinOpIn sp
  | .instanceOf => .JSBinOpInstanceOf sp

private def toUnaryOp : UnaryOp → JSUnaryOp
  | .not => .JSUnaryOpNot sp
  | .tilde => .JSUnaryOpTilde sp
  | .plus => .JSUnaryOpPlus sp
  | .minus => .JSUnaryOpMinus sp
  | .typeof => .JSUnaryOpTypeof sp
  | .void => .JSUnaryOpVoid sp
  | .delete => .JSUnaryOpDelete sp
  | .preIncr => .JSUnaryOpIncr sp
  | .preDecr => .JSUnaryOpDecr sp

private def toPostfixOp : PostfixOp → JSUnaryOp
  | .incr => .JSUnaryOpIncr sp
  | .decr => .JSUnaryOpDecr sp

private def toAssignOp : AssignOp → JSAssignOp
  | .assign => .JSAssign sp
  | .plus => .JSPlusAssign sp
  | .minus => .JSMinusAssign sp
  | .times => .JSTimesAssign sp
  | .divide => .JSDivideAssign sp
  | .mod => .JSModAssign sp
  | .lsh => .JSLshAssign sp
  | .rsh => .JSRshAssign sp
  | .ursh => .JSUrshAssign sp
  | .bitAnd => .JSBwAndAssign sp
  | .bitXor => .JSBwXorAssign sp
  | .bitOr => .JSBwOrAssign sp
  | .logicalAnd => .JSLogicalAndAssign sp
  | .logicalOr => .JSLogicalOrAssign sp
  | .coalesce => .JSNullishAssign sp

/-! The conversion is *structurally* recursive: every function below
recurses on a component of its argument, so the whole block is a plain
definition with equations, rather than a `partial` one the kernel cannot
look into.

Two things had to be arranged for that.  The wrappers which decide whether
a converted expression needs parentheses (`parenIf`, `memberObjectWith`,
`calleeWith`, `newCalleeWith`) take the *converted* expression as an
argument instead of calling the conversion themselves, since a call on the
same expression is not a recursive step; and every `List.map` of a
conversion is spelled out as a function of the same block, since a
conversion passed to `map` is not a recursive step either. -/

/-- Parenthesise `d`, the conversion of `e`, if `e` binds less tightly than
the position it stands in requires. -/
private def parenIf (minPrec : Nat) (e : MiniExpr) (d : JSExpression) : JSExpression :=
  if Printer.exprPrec e < minPrec then .JSExpressionParen sp d sp else d

/-- The object of a `.` or `[]` access: `d` is the conversion of `e`.  A
numeric literal always takes parentheses, so that `1 .toString()` is not
written `1.toString()`; and so does an optional chain, since `(a?.b).c` is
not `a?.b.c`. -/
private def memberObjectWith (e : MiniExpr) (d : JSExpression) : JSExpression :=
  match e with
  | .number _ => .JSExpressionParen sp d sp
  | .chain _ _ => .JSExpressionParen sp d sp
  | _ => parenIf 16 e d

/-- The callee of a call: `d` is the conversion of `f`. -/
private def calleeWith (f : MiniExpr) (d : JSExpression) : JSExpression :=
  match f with
  | .func .. => .JSExpressionParen sp d sp
  | _ => memberObjectWith f d

/-- The callee of a `new`: `d` is the conversion of `callee`. -/
private def newCalleeWith (callee : MiniExpr) (d : JSExpression) : JSExpression :=
  if Printer.newCalleeOk callee then d else .JSExpressionParen sp d sp

/-- A block, from its already converted statements. -/
private def blockOf (ss : List JSStatement) : JSBlock := .JSBlock sp ss sp

/-- A method, from its already converted name, parameter list and body.  The
three components are converted by the caller, since a function converting
all three of them at once has no single argument to recurse on. -/
private def methodDefWith (kind : MethodKind) (key : JSPropertyName)
    (ps : JSCommaList JSExpression) (body : JSBlock) : JSMethodDefinition :=
  match kind with
  | .normal => .JSMethodDefinition key sp ps sp body
  | .generator => .JSGeneratorMethodDefinition sp key sp ps sp body
  | .get => .JSPropertyAccessor (.JSAccessorGet sp) key sp ps sp body
  | .set => .JSPropertyAccessor (.JSAccessorSet sp) key sp ps sp body

mutual

/-- An expression. -/
def toExpression : MiniExpr → JSExpression
  | .ident n => .JSIdentifier sp n
  | .number n => numberExpr n
  | .string v => .JSStringLiteral sp (JSStringSrc.ofString! (encodeStringLiteral v))
  | .regex r => JSExpression.ofRegExp sp r
  | .null => .JSLiteral sp .null
  | .true_ => .JSLiteral sp .true_
  | .false_ => .JSLiteral sp .false_
  | .this => .JSLiteral sp .this_
  | .superDot n => .JSMemberDot (.JSLiteral sp .super) sp (.JSIdentifier sp n)
  | .superIndex i => .JSMemberSquare (.JSLiteral sp .super) sp (parenIf 1 i (toExpression i)) sp
  | .superCall args =>
      .JSCallExpression (.JSLiteral sp .super) sp (toCommaList (toArgs args)) sp
  | .newTarget => .JSNewTarget sp sp sp
  | .array els => .JSArrayLiteral sp (toArrayElementsGo true els) sp
  | .object props => .JSObjectLiteral sp (.JSCTLNone (toCommaList (toProperties props))) sp
  | .assign l op r =>
      .JSAssignExpression (parenIf 16 l (toExpression l)) (toAssignOp op)
        (parenIf 2 r (toExpression r))
  | .assignPattern l r =>
      .JSAssignExpression (toPattern l) (.JSAssign sp) (parenIf 2 r (toExpression r))
  | .await e => .JSAwaitExpression sp (parenIf 14 e (toExpression e))
  | .call f args =>
      .JSCallExpression (calleeWith f (toExpression f)) sp (toCommaList (toArgs args)) sp
  | .dot o n => .JSMemberDot (memberObjectWith o (toExpression o)) sp (.JSIdentifier sp n)
  | .privateDot o n => .JSMemberDot (memberObjectWith o (toExpression o)) sp (.JSPrivateName sp n)
  | .privateName n => .JSPrivateName sp n
  | .index o i =>
      .JSMemberSquare (memberObjectWith o (toExpression o)) sp (parenIf 1 i (toExpression i)) sp
  | .chain base ⟨hd, tl⟩ =>
      toChainList (toChainLink (memberObjectWith base (toExpression base)) hd) tl
  | .importMeta => .JSImportMeta sp sp sp
  | .importCall spec opts =>
      .JSImportCall sp sp
        (toCommaList (parenIf 2 spec (toExpression spec) :: toArgOptList opts)) sp
  | .classExpr ds name heritage body =>
      .JSClassExpression (toDecorators ds) sp (toIdentOpt name) (toHeritage heritage) sp
        (toClassElements body) sp
  | .seq l r => .JSCommaExpression (parenIf 1 l (toExpression l)) sp (parenIf 2 r (toExpression r))
  | .binary l op r =>
      let p := Printer.binOpPrec op
      let lhs := parenIf p l (toExpression l)
      let rhs := parenIf (p + 1) r (toExpression r)
      .JSExpressionBinary
        (if Printer.logicalMix op l then .JSExpressionParen sp lhs sp else lhs)
        (toBinOp op)
        (if Printer.logicalMix op r then .JSExpressionParen sp rhs sp else rhs)
  | .postfix e op => .JSExpressionPostfix (parenIf 16 e (toExpression e)) (toPostfixOp op)
  | .ternary c a b =>
      .JSExpressionTernary (parenIf 4 c (toExpression c)) sp (parenIf 2 a (toExpression a)) sp
        (parenIf 2 b (toExpression b))
  | .arrow params body =>
      .JSArrowExpression
        (.JSParenthesizedArrowParameterList sp (toCommaList (toParamList params)) sp)
        sp (toArrowBody body)
  | .func _ isGen name params body =>
      -- an `async` function *expression* has no counterpart in the annotated AST
      if isGen then
        .JSGeneratorExpression sp sp (toIdentOpt name) sp (toCommaList (toParamList params)) sp
          (blockOf (toStatements body))
      else
        .JSFunctionExpression sp (toIdentOpt name) sp (toCommaList (toParamList params)) sp
          (blockOf (toStatements body))
  | .new callee args =>
      .JSMemberNew sp (newCalleeWith callee (toExpression callee)) sp
        (toCommaList (toArgs args)) sp
  | .spread e => .JSSpreadExpression sp (parenIf 2 e (toExpression e))
  | .template tag head parts =>
      .JSTemplateLiteral (toTagOpt tag) sp head (toTemplateParts parts)
  | .unary op e => .JSUnaryExpression (toUnaryOp op) (parenIf 14 e (toExpression e))
  | .yield e => .JSYieldExpression sp (toArgOpt e)
  | .yieldFrom e => .JSYieldFromExpression sp sp (parenIf 2 e (toExpression e))
termination_by structural e => e

/-- The arguments of a call or of a `new`. -/
def toArgs : List MiniExpr → List JSExpression
  | [] => []
  | e :: rest => parenIf 2 e (toExpression e) :: toArgs rest

/-- The optional second argument of a dynamic import, as a list. -/
def toArgOptList : Option MiniExpr → List JSExpression
  | none => []
  | some e => [parenIf 2 e (toExpression e)]

/-- The links of an optional chain, written after the expression they
apply to. -/
def toChainLink : JSExpression → MiniChainLink → JSExpression
  | base, .dot opt n =>
      if opt then .JSOptionalMemberDot base sp (.JSIdentifier sp n)
      else .JSMemberDot base sp (.JSIdentifier sp n)
  | base, .privateDot opt n =>
      if opt then .JSOptionalMemberDot base sp (.JSPrivateName sp n)
      else .JSMemberDot base sp (.JSPrivateName sp n)
  | base, .index opt i =>
      let idx := parenIf 1 i (toExpression i)
      if opt then .JSOptionalMemberSquare base sp sp idx sp
      else .JSMemberSquare base sp idx sp
  | base, .call opt args =>
      let as := toCommaList (toArgs args)
      if opt then .JSOptionalCallExpression base sp sp as sp
      else .JSCallExpression base sp as sp

def toChainList : JSExpression → List MiniChainLink → JSExpression
  | base, [] => base
  | base, l :: rest => toChainList (toChainLink base l) rest

/-- The decorators of a class or of one of its members. -/
def toDecorators : List MiniExpr → List JSDecorator
  | [] => []
  | e :: rest => .JSDecorator sp (parenIf 16 e (toExpression e)) :: toDecorators rest

/-- A binding pattern, as the expression the annotated tree spells it
with. -/
def toPattern : MiniPattern → JSExpression
  | .ident n => .JSIdentifier sp n
  | .array els => .JSArrayLiteral sp (toArrayPatternElems true els) sp
  | .object props none =>
      .JSObjectLiteral sp (.JSCTLNone (toCommaList (toObjectPatternProps props))) sp
  | .object props (some r) =>
      .JSObjectLiteral sp
        (.JSCTLNone (toCommaList
          (toObjectPatternProps props ++ [.JSObjectSpread sp (toPattern r)]))) sp
  | .withDefault p v =>
      .JSAssignExpression (toPattern p) (.JSAssign sp) (parenIf 2 v (toExpression v))
  | .target e => parenIf 2 e (toExpression e)

/-- The elements of an array pattern, with the commas the annotated AST
records explicitly; `first` says whether a separating comma has still to be
written. -/
def toArrayPatternElems (first : Bool) : List MiniArrayPatternElem → List JSArrayElement
  | [] => []
  | el :: rest =>
    let sep : List JSArrayElement := if first then [] else [.JSArrayComma sp]
    let this_ : List JSArrayElement := match el with
      | .elem p => [.JSArrayElement (toPattern p)]
      | .rest p => [.JSArrayElement (.JSSpreadExpression sp (toPattern p))]
      | .hole => []
    let tail := if rest.isEmpty && el matches .hole then [JSArrayElement.JSArrayComma sp] else []
    sep ++ this_ ++ tail ++ toArrayPatternElems false rest

/-- The properties of an object pattern. -/
def toObjectPatternProps : List MiniObjectPatternProp → List JSObjectProperty
  | [] => []
  | ⟨key, value⟩ :: rest =>
      .JSPropertyNameandValue (toPropertyName key) sp (toPattern value)
        :: toObjectPatternProps rest

/-- An optional argument, as in `yield e`. -/
def toArgOpt : Option MiniExpr → Option JSExpression
  | none => none
  | some e => some (parenIf 2 e (toExpression e))

/-- The tag of a template literal. -/
def toTagOpt : Option MiniExpr → Option JSExpression
  | none => none
  | some e => some (parenIf 16 e (toExpression e))

/-- The substitutions of a template literal. -/
def toTemplateParts : List MiniTemplatePart → List JSTemplatePart
  | [] => []
  | ⟨e, suffix⟩ :: rest =>
      .JSTemplatePart (parenIf 1 e (toExpression e)) sp suffix :: toTemplateParts rest

/-- Array elements, with the commas the annotated AST records explicitly;
`first` says whether a separating comma has still to be written. -/
def toArrayElementsGo (first : Bool) : List MiniArrayElement → List JSArrayElement
  | [] => []
  | el :: rest =>
    let sep : List JSArrayElement := if first then [] else [.JSArrayComma sp]
    let this_ : List JSArrayElement := match el with
      | .elem e => [.JSArrayElement (parenIf 2 e (toExpression e))]
      | .hole => []
    let tail := if rest.isEmpty && el matches .hole then [JSArrayElement.JSArrayComma sp] else []
    sep ++ this_ ++ tail ++ toArrayElementsGo false rest

def toPropertyName : MiniPropertyName → JSPropertyName
  | .ident n => .JSPropertyIdent sp n
  | .private_ n => .JSPropertyPrivate sp n
  | .string v => .JSPropertyString sp (JSStringSrc.ofString! (encodeStringLiteral v))
  | .number n => .JSPropertyNumber sp n
  | .computed e => .JSPropertyComputed sp (parenIf 2 e (toExpression e)) sp

/-- A parameter, as the expression the annotated tree spells it with. -/
def toParam : MiniParam → JSExpression
  | .plain p => toPattern p
  | .rest p => .JSSpreadExpression sp (toPattern p)

/-- A parameter list. -/
def toParamList : List MiniParam → List JSExpression
  | [] => []
  | p :: rest => toParam p :: toParamList rest

def toProperty : MiniProperty → JSObjectProperty
  | .keyValue k v => .JSPropertyNameandValue (toPropertyName k) sp (parenIf 2 v (toExpression v))
  | .shorthand n => .JSPropertyIdentRef sp n
  | .spread e => .JSObjectSpread sp (parenIf 2 e (toExpression e))
  | .method kind key params body =>
      .JSObjectMethod
        (methodDefWith kind (toPropertyName key) (toCommaList (toParamList params))
          (blockOf (toStatements body)))

def toProperties : List MiniProperty → List JSObjectProperty
  | [] => []
  | p :: rest => toProperty p :: toProperties rest

def toClassElement : MiniClassElement → JSClassElement
  | .method ds isStatic kind key params body =>
    let m := methodDefWith kind (toPropertyName key) (toCommaList (toParamList params))
      (blockOf (toStatements body))
    if isStatic then .JSClassStaticMethod (toDecorators ds) sp m
    else .JSClassInstanceMethod (toDecorators ds) m
  | .field ds isStatic key init =>
    let i : JSVarInitializer := match init with
      | none => .JSVarInitNone
      | some e => .JSVarInit sp (parenIf 2 e (toExpression e))
    if isStatic then .JSClassStaticField (toDecorators ds) sp (toPropertyName key) i semi
    else .JSClassInstanceField (toDecorators ds) (toPropertyName key) i semi
  | .staticBlock body => .JSClassStaticBlock sp (blockOf (toStatements body))

def toClassElements : List MiniClassElement → List JSClassElement
  | [] => []
  | el :: rest => toClassElement el :: toClassElements rest

def toHeritage : Option MiniExpr → JSClassHeritage
  | none => .JSExtendsNone
  | some e => .JSExtends sp (parenIf 16 e (toExpression e))

def toArrowBody : MiniArrowBody → JSStatement
  | .expr (.object props) =>
      .JSExpressionStatement
        (.JSExpressionParen sp
          (.JSObjectLiteral sp (.JSCTLNone (toCommaList (toProperties props))) sp) sp)
        .JSSemiAuto
  | .expr e => .JSExpressionStatement (parenIf 2 e (toExpression e)) .JSSemiAuto
  | .block body => .JSStatementBlock sp (toStatements body) sp .JSSemiAuto

def toDeclarator : MiniDeclarator → JSExpression
  | ⟨lhs, init⟩ =>
    .JSVarInitExpression (toPattern lhs)
      (match init with
       | none => .JSVarInitNone
       | some e => .JSVarInit sp (parenIf 2 e (toExpression e)))

def toDeclaratorList : List MiniDeclarator → List JSExpression
  | [] => []
  | d :: rest => toDeclarator d :: toDeclaratorList rest

def toDeclarators : NEList MiniDeclarator → JSCommaList1 JSExpression
  | ⟨hd, tl⟩ =>
    (toDeclaratorList tl).foldl (fun acc y => .JSL1Cons acc sp y) (.JSL1One (toDeclarator hd))

def toOptExprList : Option MiniExpr → JSCommaList JSExpression
  | none => .JSLNil
  | some e => .JSLOne (toExpression e)

def toSwitchPart : MiniSwitchCase → JSSwitchParts
  | .case test body => .JSCase sp (parenIf 2 test (toExpression test)) sp (toStatements body)
  | .default body => .JSDefault sp sp (toStatements body)

def toSwitchParts : List MiniSwitchCase → List JSSwitchParts
  | [] => []
  | c :: rest => toSwitchPart c :: toSwitchParts rest

def toCatch : MiniCatchClause → JSTryCatch
  | ⟨param, none, body⟩ => .JSCatch sp sp (toPattern param) sp (blockOf (toStatements body))
  | ⟨param, some g, body⟩ =>
      .JSCatchIf sp sp (toPattern param) sp (toExpression g) sp (blockOf (toStatements body))

def toCatchList : List MiniCatchClause → List JSTryCatch
  | [] => []
  | c :: rest => toCatch c :: toCatchList rest

def toCatches : NEList MiniCatchClause → List JSTryCatch
  | ⟨hd, tl⟩ => toCatch hd :: toCatchList tl

def toStatements : List MiniStatement → List JSStatement
  | [] => []
  | s :: rest => toStatement s :: toStatements rest

def toStatement : MiniStatement → JSStatement
  | .block body => .JSStatementBlock sp (toStatements body) sp .JSSemiAuto
  | .break_ l => .JSBreak sp (toIdentOpt l) semi
  | .continue_ l => .JSContinue sp (toIdentOpt l) semi
  | .classDecl ds name heritage body =>
      .JSClass (toDecorators ds) sp (toIdent name) (toHeritage heritage) sp
        (toClassElements body) sp semi
  | .decl kind decls =>
      let ds := toDeclarators decls
      match kind with
      | .var => .JSVariable sp ds semi
      | .let_ => .JSLet sp ds semi
      | .const => .JSConstant sp ds semi
  | .using_ isAwait decls =>
      let ds := toDeclarators decls
      if isAwait then .JSAwaitUsing sp sp ds semi else .JSUsing sp ds semi
  | .doWhile body cond =>
      .JSDoWhile sp (toStatement body) sp sp (toExpression cond) sp semi
  | .for_ init cond step body =>
      let c := toOptExprList cond
      let s := toOptExprList step
      let b := toStatement body
      match init with
      | .none => .JSFor sp sp .JSLNil sp c sp s sp b
      | .expr e => .JSFor sp sp (.JSLOne (toExpression e)) sp c sp s sp b
      | .decl kind decls =>
          let ds := toDeclarators decls
          match kind with
          | .var => .JSForVar sp sp sp ds sp c sp s sp b
          | .let_ => .JSForLet sp sp sp ds sp c sp s sp b
          | .const => .JSForConst sp sp sp ds sp c sp s sp b
  | .forIn head obj body =>
      let o := parenIf 2 obj (toExpression obj)
      let b := toStatement body
      let op : JSBinOp := .JSBinOpIn sp
      match head with
      | .pattern p => .JSForIn sp sp (toPattern p) op o sp b
      | .decl .var p => .JSForVarIn sp sp sp (toPattern p) op o sp b
      | .decl .let_ p => .JSForLetIn sp sp sp (toPattern p) op o sp b
      | .decl .const p => .JSForConstIn sp sp sp (toPattern p) op o sp b
  | .forOf head obj body =>
      let o := parenIf 2 obj (toExpression obj)
      let b := toStatement body
      let op : JSBinOp := .JSBinOpOf sp
      match head with
      | .pattern p => .JSForOf sp sp (toPattern p) op o sp b
      | .decl .var p => .JSForVarOf sp sp sp (toPattern p) op o sp b
      | .decl .let_ p => .JSForLetOf sp sp sp (toPattern p) op o sp b
      | .decl .const p => .JSForConstOf sp sp sp (toPattern p) op o sp b
  | .funcDecl isAsync isGen name params body =>
      let ps := toCommaList (toParamList params)
      if isAsync then .JSAsyncFunction sp sp (toIdent name) sp ps sp (blockOf (toStatements body)) semi
      else if isGen then .JSGenerator sp sp (toIdent name) sp ps sp (blockOf (toStatements body)) semi
      else .JSFunction sp (toIdent name) sp ps sp (blockOf (toStatements body)) semi
  | .if_ cond thenS none => .JSIf sp sp (toExpression cond) sp (toStatement thenS)
  | .if_ cond thenS (some e) =>
      .JSIfElse sp sp (toExpression cond) sp (toStatement thenS) sp (toStatement e)
  | .labelled l s => .JSLabelled (toIdent l) sp (toStatement s)
  | .empty => .JSEmptyStatement sp
  | .expr e =>
      let d := parenIf 1 e (toExpression e)
      let d := if Printer.needsStatementParens e then .JSExpressionParen sp d sp else d
      .JSExpressionStatement d semi
  | .return_ e =>
      .JSReturn sp (match e with | none => none | some x => some (toExpression x)) semi
  | .switch disc cases =>
      .JSSwitch sp sp (toExpression disc) sp sp (toSwitchParts cases) sp semi
  | .throw e => .JSThrow sp (toExpression e) semi
  | .try_ body tail =>
      let blk := blockOf (toStatements body)
      match tail with
      | .finallyOnly f => .JSTry sp blk [] (.JSFinally sp (blockOf (toStatements f)))
      | .catches cs fin =>
          .JSTry sp blk (toCatches cs)
            (match fin with
             | .none => .JSNoFinally
             | .some f => .JSFinally sp (blockOf (toStatements f)))
  | .while_ cond body => .JSWhile sp sp (toExpression cond) sp (toStatement body)
  | .with_ obj body => .JSWith sp sp (toExpression obj) sp (toStatement body) semi

end

/-- An expression in a position that requires precedence `minPrec`; the
parentheses `MiniAST` does not store are put back here, exactly as
`MiniASTPrinter` puts them back in the printed output. -/
def toExpressionPrec (minPrec : Nat) (e : MiniExpr) : JSExpression :=
  parenIf minPrec e (toExpression e)

/-- The object of a `.` or `[]` access. -/
def toMemberObject (e : MiniExpr) : JSExpression := memberObjectWith e (toExpression e)

/-- Array elements, with the commas the annotated AST records explicitly. -/
def toArrayElements (els : List MiniArrayElement) : List JSArrayElement :=
  toArrayElementsGo true els

/-- A parameter list. -/
def toParams (params : List MiniParam) : JSCommaList JSExpression :=
  toCommaList (toParamList params)

/-- The block of statements a function or a `try` is written with. -/
def toBlock (body : List MiniStatement) : JSBlock := blockOf (toStatements body)

/-- A method definition. -/
def toMethodDefinition (kind : MethodKind) (key : MiniPropertyName)
    (params : List MiniParam) (body : List MiniStatement) : JSMethodDefinition :=
  methodDefWith kind (toPropertyName key) (toParams params) (blockOf (toStatements body))

/-! ## Modules -/

private def toSpecifierImport (s : Specifier) : JSImportSpecifier :=
  match s.alias_ with
  | none => .JSImportSpecifier (toIdent s.name)
  | some a => .JSImportSpecifierAs (toIdent s.name) sp (toIdent a)

private def toSpecifierExport (s : Specifier) : JSExportSpecifier :=
  match s.alias_ with
  | none => .JSExportSpecifier (toIdent s.name)
  | some a => .JSExportSpecifierAs (toIdent s.name) sp (toIdent a)

private def toImportsNamed (specs : List Specifier) : JSImportsNamed :=
  .JSImportsNamed sp (toCommaList (specs.map toSpecifierImport)) sp

private def toNameSpace (n : NEString) : JSImportNameSpace :=
  .JSImportNameSpace (.JSBinOpTimes sp) sp (toIdent n)

private def toImportClause (c : MiniImportClause) : JSImportClause :=
  match c.default_, c.namespace_, c.named with
  | some d, some n, _ => .JSImportClauseDefaultNameSpace (toIdent d) sp (toNameSpace n)
  | some d, none, some specs => .JSImportClauseDefaultNamed (toIdent d) sp (toImportsNamed specs)
  | some d, none, none => .JSImportClauseDefault (toIdent d)
  | none, some n, _ => .JSImportClauseNameSpace (toNameSpace n)
  | none, none, some specs => .JSImportClauseNamed (toImportsNamed specs)
  -- unreachable: an import clause binds at least one name
  | none, none, none => .JSImportClauseNamed (toImportsNamed [])

private def toImportAttribute (a : ImportAttr) : JSImportAttribute :=
  .JSImportAttribute sp (NEString.ofString! (encodeStringLiteral a.key)) sp sp
    (NEString.ofString! (encodeStringLiteral a.value))

private def toImportAttributes? (attrs : List ImportAttr) : Option JSImportAttributes :=
  if attrs.isEmpty then none
  else some (.JSImportAttributes sp sp (toCommaList (attrs.map toImportAttribute)) sp)

private def toFromClause (mod : NEString) (attrs : List ImportAttr) : JSFromClause :=
  .JSFromClause sp sp (NEString.ofString! (encodeStringLiteral mod.val))
    (toImportAttributes? attrs)

private def toImportDeclaration : MiniImportDeclaration → JSImportDeclaration
  | .bare mod attrs =>
      .JSImportDeclarationBare sp (NEString.ofString! (encodeStringLiteral mod.val))
        (toImportAttributes? attrs) semi
  | .clause c => .JSImportDeclaration (toImportClause c) (toFromClause c.mod c.attrs) semi

private def toExportClause (specs : List Specifier) : JSExportClause :=
  .JSExportClause sp (toCommaList (specs.map toSpecifierExport)) sp

private def toExportDeclaration : MiniExportDeclaration → JSExportDeclaration
  | .fromClause specs mod attrs =>
      .JSExportFrom (toExportClause specs) (toFromClause mod attrs) semi
  | .locals specs => .JSExportLocals (toExportClause specs) semi
  | .all none mod attrs => .JSExportAll sp (toFromClause mod attrs) semi
  | .all (some n) mod attrs => .JSExportAllAs sp sp (toIdent n) (toFromClause mod attrs) semi
  | .defaultExpr e => .JSExportDefault sp (parenIf 2 e (toExpression e)) semi
  | .decl s => .JSExport (toStatement s) semi

def toModuleItem : MiniModuleItem → JSModuleItem
  | .stmt s => .JSModuleStatementListItem (toStatement s)
  | .importDecl d => .JSModuleImportDeclaration sp (toImportDeclaration d)
  | .exportDecl d => .JSModuleExportDeclaration sp (toExportDeclaration d)

/-- Convert a `MiniProgram` back into an annotated AST.  Positions, comments
and the original layout are gone: every token is preceded by one space. -/
def toAST (p : MiniProgram) : JSAST :=
  .JSAstModule (p.items.map toModuleItem) sp

/-- Render a `MiniProgram` through the annotated AST and its printer.  This
is the *lossy* round trip; use `printProgram` for the pretty output. -/
def renderViaAST (p : MiniProgram) : String :=
  Language.JavaScript.Pretty.renderToString (toAST p)

end Language.JavaScript.MiniAST
