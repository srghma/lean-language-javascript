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

private def toIdent (n : NEString) : JSIdent := .JSIdentName sp n.val

private def toIdentOpt : Option NEString → JSIdent
  | none => .JSIdentNone
  | some n => toIdent n

/-- The literal node a normalised numeric literal belongs to. -/
private def numberExpr (raw : String) : JSExpression :=
  if raw.startsWith "0x" then .JSHexInteger sp raw
  else if raw.startsWith "0b" || raw.startsWith "0o" then .JSOctal sp raw
  else if raw.startsWith "0" && raw.length > 1 && raw.toList.all Char.isDigit then
    .JSOctal sp raw
  else .JSDecimal sp raw

private def toBinOp : MiniBinOp → JSBinOp
  | .and => .JSBinOpAnd sp
  | .or => .JSBinOpOr sp
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

private def toUnaryOp : MiniUnaryOp → JSUnaryOp
  | .not => .JSUnaryOpNot sp
  | .tilde => .JSUnaryOpTilde sp
  | .plus => .JSUnaryOpPlus sp
  | .minus => .JSUnaryOpMinus sp
  | .typeof => .JSUnaryOpTypeof sp
  | .void => .JSUnaryOpVoid sp
  | .delete => .JSUnaryOpDelete sp
  | .preIncr => .JSUnaryOpIncr sp
  | .preDecr => .JSUnaryOpDecr sp

private def toPostfixOp : MiniPostfixOp → JSUnaryOp
  | .incr => .JSUnaryOpIncr sp
  | .decr => .JSUnaryOpDecr sp

private def toAssignOp : MiniAssignOp → JSAssignOp
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

mutual

/-- An expression in a position that requires precedence `minPrec`; the
parentheses `MiniAST` does not store are put back here, exactly as
`MiniASTPrinter` puts them back in the printed output. -/
partial def toExpressionPrec (minPrec : Nat) (e : MiniExpr) : JSExpression :=
  let d := toExpression e
  if Printer.exprPrec e < minPrec then .JSExpressionParen sp d sp else d

/-- The object of a `.` or `[]` access. -/
partial def toMemberObject (e : MiniExpr) : JSExpression :=
  match e with
  | .number r => .JSExpressionParen sp (numberExpr r.val) sp
  | e => toExpressionPrec 16 e

/-- An expression. -/
partial def toExpression : MiniExpr → JSExpression
  | .ident n => .JSIdentifier sp n.val
  | .number r => numberExpr r.val
  | .string v => .JSStringLiteral sp (encodeStringLiteral v)
  | .regex r => .JSRegEx sp r.val
  | .null => .JSLiteral sp "null"
  | .true_ => .JSLiteral sp "true"
  | .false_ => .JSLiteral sp "false"
  | .this => .JSLiteral sp "this"
  | .array els => .JSArrayLiteral sp (toArrayElements els) sp
  | .object props => .JSObjectLiteral sp (.JSCTLNone (toCommaList (props.map toProperty))) sp
  | .assign l op r =>
      .JSAssignExpression (toExpressionPrec 16 l) (toAssignOp op) (toExpressionPrec 2 r)
  | .await e => .JSAwaitExpression sp (toExpressionPrec 14 e)
  | .call f args =>
      let callee := match f with
        | .func .. => .JSExpressionParen sp (toExpression f) sp
        | f => toMemberObject f
      .JSCallExpression callee sp (toCommaList (args.map (toExpressionPrec 2))) sp
  | .dot o n => .JSMemberDot (toMemberObject o) sp (.JSIdentifier sp n.val)
  | .index o i => .JSMemberSquare (toMemberObject o) sp (toExpressionPrec 1 i) sp
  | .classExpr name heritage body =>
      .JSClassExpression sp (toIdentOpt name) (toHeritage heritage) sp
        (body.map toClassElement) sp
  | .seq l r => .JSCommaExpression (toExpressionPrec 1 l) sp (toExpressionPrec 2 r)
  | .binary l op r =>
      let p := Printer.binOpPrec op
      .JSExpressionBinary (toExpressionPrec p l) (toBinOp op) (toExpressionPrec (p + 1) r)
  | .postfix e op => .JSExpressionPostfix (toExpressionPrec 16 e) (toPostfixOp op)
  | .ternary c a b =>
      .JSExpressionTernary (toExpressionPrec 4 c) sp (toExpressionPrec 2 a) sp
        (toExpressionPrec 2 b)
  | .arrow params body =>
      .JSArrowExpression
        (.JSParenthesizedArrowParameterList sp
          (toCommaList (params.map (toExpressionPrec 2))) sp)
        sp (toArrowBody body)
  | .func _ isGen name params body =>
      -- an `async` function *expression* has no counterpart in the annotated AST
      if isGen then
        .JSGeneratorExpression sp sp (toIdentOpt name) sp
          (toCommaList (params.map (toExpressionPrec 2))) sp (toBlock body)
      else
        .JSFunctionExpression sp (toIdentOpt name) sp
          (toCommaList (params.map (toExpressionPrec 2))) sp (toBlock body)
  | .new callee args =>
      let c := if Printer.newCalleeOk callee then toExpression callee
        else .JSExpressionParen sp (toExpression callee) sp
      .JSMemberNew sp c sp (toCommaList (args.map (toExpressionPrec 2))) sp
  | .spread e => .JSSpreadExpression sp (toExpressionPrec 2 e)
  | .template tag head parts =>
      let tag := tag.map (toExpressionPrec 16)
      let headText := "`" ++ head ++ (if parts.isEmpty then "`" else "${")
      let n := parts.length
      let parts := parts.zipIdx.map fun (p, i) =>
        JSTemplatePart.JSTemplatePart (toExpressionPrec 1 p.expr) sp
          ("}" ++ p.suffix ++ (if i + 1 == n then "`" else "${"))
      .JSTemplateLiteral tag sp headText parts
  | .unary op e => .JSUnaryExpression (toUnaryOp op) (toExpressionPrec 14 e)
  | .yield e => .JSYieldExpression sp (e.map (toExpressionPrec 2))
  | .yieldFrom e => .JSYieldFromExpression sp sp (toExpressionPrec 2 e)

/-- Array elements, with the commas the annotated AST records explicitly. -/
partial def toArrayElements (els : List MiniArrayElement) : List JSArrayElement :=
  let rec go (first : Bool) : List MiniArrayElement → List JSArrayElement
    | [] => []
    | el :: rest =>
      let sep : List JSArrayElement := if first then [] else [.JSArrayComma sp]
      let this_ : List JSArrayElement := match el with
        | .elem e => [.JSArrayElement (toExpressionPrec 2 e)]
        | .hole => []
      let tail := if rest.isEmpty && el matches .hole then [JSArrayElement.JSArrayComma sp] else []
      sep ++ this_ ++ tail ++ go false rest
  go true els

partial def toPropertyName : MiniPropertyName → JSPropertyName
  | .ident n => .JSPropertyIdent sp n.val
  | .string v => .JSPropertyString sp (encodeStringLiteral v)
  | .number r => .JSPropertyNumber sp r.val
  | .computed e => .JSPropertyComputed sp (toExpressionPrec 2 e) sp

partial def toMethodDefinition (kind : MiniMethodKind) (key : MiniPropertyName)
    (params : List MiniExpr) (body : List MiniStatement) : JSMethodDefinition :=
  let ps := toCommaList (params.map (toExpressionPrec 2))
  match kind with
  | .normal => .JSMethodDefinition (toPropertyName key) sp ps sp (toBlock body)
  | .generator => .JSGeneratorMethodDefinition sp (toPropertyName key) sp ps sp (toBlock body)
  | .get => .JSPropertyAccessor (.JSAccessorGet sp) (toPropertyName key) sp ps sp (toBlock body)
  | .set => .JSPropertyAccessor (.JSAccessorSet sp) (toPropertyName key) sp ps sp (toBlock body)

partial def toProperty : MiniProperty → JSObjectProperty
  | .keyValue k v => .JSPropertyNameandValue (toPropertyName k) sp [toExpressionPrec 2 v]
  | .shorthand n => .JSPropertyIdentRef sp n.val
  | .method kind key params body => .JSObjectMethod (toMethodDefinition kind key params body)

partial def toClassElement (el : MiniClassElement) : JSClassElement :=
  let m := toMethodDefinition el.kind el.key el.params el.body
  if el.isStatic then .JSClassStaticMethod sp m else .JSClassInstanceMethod m

partial def toHeritage : Option MiniExpr → JSClassHeritage
  | none => .JSExtendsNone
  | some e => .JSExtends sp (toExpressionPrec 16 e)

partial def toArrowBody : MiniArrowBody → JSStatement
  | .expr (.object props) =>
      .JSExpressionStatement
        (.JSExpressionParen sp
          (.JSObjectLiteral sp (.JSCTLNone (toCommaList (props.map toProperty))) sp) sp)
        .JSSemiAuto
  | .expr e => .JSExpressionStatement (toExpressionPrec 2 e) .JSSemiAuto
  | .block body => .JSStatementBlock sp (body.map toStatement) sp .JSSemiAuto

partial def toBlock (body : List MiniStatement) : JSBlock :=
  .JSBlock sp (body.map toStatement) sp

partial def toDeclarator (d : MiniDeclarator) : JSExpression :=
  .JSVarInitExpression (toExpressionPrec 2 d.lhs)
    (match d.init with
     | none => .JSVarInitNone
     | some e => .JSVarInit sp (toExpressionPrec 2 e))

partial def toDeclarators (decls : NEList MiniDeclarator) : JSCommaList JSExpression :=
  toCommaList (decls.toList.map toDeclarator)

partial def toOptExprList : Option MiniExpr → JSCommaList JSExpression
  | none => .JSLNil
  | some e => .JSLOne (toExpression e)

partial def toSwitchPart : MiniSwitchCase → JSSwitchParts
  | .case test body => .JSCase sp (toExpressionPrec 2 test) sp (body.map toStatement)
  | .default body => .JSDefault sp sp (body.map toStatement)

partial def toCatch (c : MiniCatchClause) : JSTryCatch :=
  match c.guard with
  | none => .JSCatch sp sp (toExpression c.param) sp (toBlock c.body)
  | some g => .JSCatchIf sp sp (toExpression c.param) sp (toExpression g) sp (toBlock c.body)

partial def toStatement : MiniStatement → JSStatement
  | .block body => .JSStatementBlock sp (body.map toStatement) sp .JSSemiAuto
  | .break_ l => .JSBreak sp (toIdentOpt l) semi
  | .continue_ l => .JSContinue sp (toIdentOpt l) semi
  | .classDecl name heritage body =>
      .JSClass sp (toIdent name) (toHeritage heritage) sp (body.map toClassElement) sp semi
  | .decl kind decls =>
      let ds := toDeclarators decls
      match kind with
      | .var => .JSVariable sp ds semi
      | .let_ => .JSLet sp ds semi
      | .const => .JSConstant sp ds semi
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
      let o := toExpressionPrec 2 obj
      let b := toStatement body
      let op : JSBinOp := .JSBinOpIn sp
      match head with
      | .pattern e => .JSForIn sp sp (toExpressionPrec 2 e) op o sp b
      | .decl .var e => .JSForVarIn sp sp sp (toExpression e) op o sp b
      | .decl .let_ e => .JSForLetIn sp sp sp (toExpression e) op o sp b
      | .decl .const e => .JSForConstIn sp sp sp (toExpression e) op o sp b
  | .forOf head obj body =>
      let o := toExpressionPrec 2 obj
      let b := toStatement body
      let op : JSBinOp := .JSBinOpOf sp
      match head with
      | .pattern e => .JSForOf sp sp (toExpressionPrec 2 e) op o sp b
      | .decl .var e => .JSForVarOf sp sp sp (toExpression e) op o sp b
      | .decl .let_ e => .JSForLetOf sp sp sp (toExpression e) op o sp b
      | .decl .const e => .JSForConstOf sp sp sp (toExpression e) op o sp b
  | .funcDecl isAsync isGen name params body =>
      let ps := toCommaList (params.map toExpression)
      if isAsync then .JSAsyncFunction sp sp (toIdent name) sp ps sp (toBlock body) semi
      else if isGen then .JSGenerator sp sp (toIdent name) sp ps sp (toBlock body) semi
      else .JSFunction sp (toIdent name) sp ps sp (toBlock body) semi
  | .if_ cond thenS none => .JSIf sp sp (toExpression cond) sp (toStatement thenS)
  | .if_ cond thenS (some e) =>
      .JSIfElse sp sp (toExpression cond) sp (toStatement thenS) sp (toStatement e)
  | .labelled l s => .JSLabelled (toIdent l) sp (toStatement s)
  | .empty => .JSEmptyStatement sp
  | .expr e =>
      let d := toExpressionPrec 1 e
      let d := if Printer.needsStatementParens e then .JSExpressionParen sp d sp else d
      .JSExpressionStatement d semi
  | .return_ e => .JSReturn sp (e.map toExpression) semi
  | .switch disc cases =>
      .JSSwitch sp sp (toExpression disc) sp sp (cases.map toSwitchPart) sp semi
  | .throw e => .JSThrow sp (toExpression e) semi
  | .try_ body tail =>
      let blk := toBlock body
      match tail with
      | .finallyOnly f => .JSTry sp blk [] (.JSFinally sp (toBlock f))
      | .catches cs fin =>
          .JSTry sp blk (cs.toList.map toCatch)
            (match fin with
             | .none => .JSNoFinally
             | .some f => .JSFinally sp (toBlock f))
  | .while_ cond body => .JSWhile sp sp (toExpression cond) sp (toStatement body)
  | .with_ obj body => .JSWith sp sp (toExpression obj) sp (toStatement body) semi

end

/-! ## Modules -/

private def toSpecifierImport (s : MiniSpecifier) : JSImportSpecifier :=
  match s.alias_ with
  | none => .JSImportSpecifier (toIdent s.name)
  | some a => .JSImportSpecifierAs (toIdent s.name) sp (toIdent a)

private def toSpecifierExport (s : MiniSpecifier) : JSExportSpecifier :=
  match s.alias_ with
  | none => .JSExportSpecifier (toIdent s.name)
  | some a => .JSExportSpecifierAs (toIdent s.name) sp (toIdent a)

private def toImportsNamed (specs : List MiniSpecifier) : JSImportsNamed :=
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

private def toImportDeclaration : MiniImportDeclaration → JSImportDeclaration
  | .bare mod => .JSImportDeclarationBare sp (encodeStringLiteral mod.val) semi
  | .clause c =>
      .JSImportDeclaration (toImportClause c)
        (.JSFromClause sp sp (encodeStringLiteral c.mod.val)) semi

private def toExportClause (specs : List MiniSpecifier) : JSExportClause :=
  .JSExportClause sp (toCommaList (specs.map toSpecifierExport)) sp

private def toExportDeclaration : MiniExportDeclaration → JSExportDeclaration
  | .fromClause specs mod =>
      .JSExportFrom (toExportClause specs) (.JSFromClause sp sp (encodeStringLiteral mod.val))
        semi
  | .locals specs => .JSExportLocals (toExportClause specs) semi
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
