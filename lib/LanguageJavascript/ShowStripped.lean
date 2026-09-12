/-
`showStripped`: the AST written out without its `JSAnnot` data.

These functions correspond to the `ShowStripped` class of the Haskell
`language-javascript`, and produce exactly the same text, so that the tests
ported from it can be compared line by line.  They live in their own module
because they are half as long again as the tree they print.
-/
import LanguageJavascript.AST

namespace Language.JavaScript.Parser.AST

/-! ## Helpers -/

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
  | .JSIdentName _ s => "JSIdentifier " ++ singleQuote s.val
  | .JSIdentNone => "JSIdentNone"

/-- A numeric literal, shown with the name the Haskell original gives the
literal of that base and the canonical spelling of the number: `0X1f` shows
as `JSHexInteger '0x1f'`, `070` as `JSOctal '0o70'`. -/
def ssNumber (n : JSNumber) : String :=
  let name :=
    match n.base with
    | .hexadecimal => "JSHexInteger "
    | .octal | .binary => "JSOctal "
    | .decimal => "JSDecimal "
  name ++ singleQuote n.render

/-- `ssid` of the Haskell original: the name of an identifier, quoted. -/
def ssid : JSIdent → String
  | .JSIdentName _ s => singleQuote s.val
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
  | .JSBinOpNullish _ => "'??'"
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
  | .JSLogicalAndAssign _ => "'&&='"
  | .JSLogicalOrAssign _ => "'||='"
  | .JSNullishAssign _ => "'??='"

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
  | .JSBreak _ (.JSIdentName _ n) s => "JSBreak " ++ singleQuote n.val ++ commaIf (ssSemi s)
  | .JSClass ds _ n h _ xs _ _ =>
      ssDecorators ds ++ "JSClass " ++ ssid n ++ " (" ++ ssClassHeritage h ++ ") "
        ++ ssClassElements xs
  | .JSContinue _ .JSIdentNone s => "JSContinue" ++ commaIf (ssSemi s)
  | .JSContinue _ (.JSIdentName _ n) s => "JSContinue " ++ singleQuote n.val ++ commaIf (ssSemi s)
  | .JSConstant _ xs _ => "JSConstant " ++ ssExprCommaList1 xs
  | .JSUsing _ xs _ => "JSUsing " ++ ssExprCommaList1 xs
  | .JSAwaitUsing _ _ xs _ => "JSAwaitUsing " ++ ssExprCommaList1 xs
  | .JSDoWhile _ x1 _ _ x2 _ x3 =>
      "JSDoWhile (" ++ ssStatement x1 ++ ") (" ++ ssExpression x2 ++ ") (" ++ ssSemi x3 ++ ")"
  | .JSFor _ _ x1s _ x2s _ x3s _ x4 =>
      "JSFor " ++ ssExprCommaList x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForIn _ _ x1s _ x2 _ x3 =>
      "JSForIn " ++ ssExpression x1s ++ " (" ++ ssExpression x2 ++ ") (" ++ ssStatement x3 ++ ")"
  | .JSForVar _ _ _ x1s _ x2s _ x3s _ x4 =>
      "JSForVar " ++ ssExprCommaList1 x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForVarIn _ _ _ x1 _ x2 _ x3 =>
      "JSForVarIn (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForLet _ _ _ x1s _ x2s _ x3s _ x4 =>
      "JSForLet " ++ ssExprCommaList1 x1s ++ " " ++ ssExprCommaList x2s ++ " "
        ++ ssExprCommaList x3s ++ " (" ++ ssStatement x4 ++ ")"
  | .JSForLetIn _ _ _ x1 _ x2 _ x3 =>
      "JSForLetIn (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForLetOf _ _ _ x1 _ x2 _ x3 =>
      "JSForLetOf (" ++ ssExpression x1 ++ ") (" ++ ssExpression x2 ++ ") ("
        ++ ssStatement x3 ++ ")"
  | .JSForConst _ _ _ x1s _ x2s _ x3s _ x4 =>
      "JSForConst " ++ ssExprCommaList1 x1s ++ " " ++ ssExprCommaList x2s ++ " "
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
  | .JSLet _ xs _ => "JSLet " ++ ssExprCommaList1 xs
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
  | .JSVariable _ xs _ => "JSVariable " ++ ssExprCommaList1 xs
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
  | .JSClassExpression ds _ n h _ xs _ =>
      ssDecorators ds ++ "JSClassExpression " ++ ssid n ++ " (" ++ ssClassHeritage h ++ ") "
        ++ ssClassElements xs
  | .JSOptionalMemberDot ex _ n =>
      "JSOptionalMemberDot (" ++ ssExpression ex ++ "," ++ ssExpression n ++ ")"
  | .JSOptionalMemberSquare ex _ _ x _ =>
      "JSOptionalMemberSquare (" ++ ssExpression ex ++ "," ++ ssExpression x ++ ")"
  | .JSOptionalCallExpression ex _ _ xs _ =>
      "JSOptionalCallExpression (" ++ ssExpression ex ++ ",JSArguments " ++ ssExprCommaList xs
        ++ ")"
  | .JSPrivateName _ n => "JSPrivateName " ++ singleQuote n.val
  | .JSImportMeta _ _ _ => "JSImportMeta"
  | .JSNewTarget _ _ _ => "JSNewTarget"
  | .JSImportCall _ _ xs _ => "JSImportCall " ++ ssExprCommaList xs
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
  | .JSNumberLit _ s => ssNumber s
  | .JSIdentifier _ s => "JSIdentifier " ++ singleQuote s.val
  | .JSLiteral _ k => "JSLiteral " ++ singleQuote k.text.val
  | .JSMemberDot x1s _ x2 => "JSMemberDot (" ++ ssExpression x1s ++ "," ++ ssExpression x2 ++ ")"
  | .JSMemberExpression e _ a _ =>
      "JSMemberExpression (" ++ ssExpression e ++ ",JSArguments " ++ ssExprCommaList a ++ ")"
  | .JSMemberNew _ n _ s _ =>
      "JSMemberNew (" ++ ssExpression n ++ ",JSArguments " ++ ssExprCommaList s ++ ")"
  | .JSMemberSquare x1s _ x2 _ =>
      "JSMemberSquare (" ++ ssExpression x1s ++ "," ++ ssExpression x2 ++ ")"
  | .JSNewExpression _ e => "JSNewExpression " ++ ssExpression e
  | .JSObjectLiteral _ xs _ => "JSObjectLiteral " ++ ssObjectPropertyList xs
  | .JSRegEx _ s => "JSRegEx " ++ singleQuote s.render
  | .JSStringLiteral _ s => "JSStringLiteral " ++ s.render
  | .JSUnaryExpression op x =>
      "JSUnaryExpression (" ++ ssUnaryOp op ++ "," ++ ssExpression x ++ ")"
  | .JSVarInitExpression x1 x2 =>
      "JSVarInitExpression (" ++ ssExpression x1 ++ ") " ++ ssVarInitializer x2
  | .JSYieldExpression _ none => "JSYieldExpression ()"
  | .JSYieldExpression _ (some x) => "JSYieldExpression (" ++ ssExpression x ++ ")"
  | .JSYieldFromExpression _ _ x => "JSYieldFromExpression (" ++ ssExpression x ++ ")"
  | .JSSpreadExpression _ x1 => "JSSpreadExpression (" ++ ssExpression x1 ++ ")"
  | .JSTemplateLiteral none _ s ps =>
      "JSTemplateLiteral (()," ++ singleQuote (templateHeadSpelling s ps) ++ ","
        ++ ssTemplateParts ps ++ ")"
  | .JSTemplateLiteral (some t) _ s ps =>
      "JSTemplateLiteral ((" ++ ssExpression t ++ "),"
        ++ singleQuote (templateHeadSpelling s ps) ++ "," ++ ssTemplateParts ps ++ ")"

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
  | .JSPropertyNameandValue x1 _ x2 =>
      "JSPropertyNameandValue (" ++ ssPropertyName x1 ++ ") [" ++ ssExpression x2 ++ "]"
  | .JSPropertyIdentRef _ s => "JSPropertyIdentRef " ++ singleQuote s.val
  | .JSPropertyIdentRefDefault _ s _ v =>
      "JSPropertyIdentRefDefault " ++ singleQuote s.val ++ " [" ++ ssExpression v ++ "]"
  | .JSObjectSpread _ e => "JSObjectSpread (" ++ ssExpression e ++ ")"
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
  | .JSPropertyIdent _ s => "JSIdentifier " ++ singleQuote s.val
  | .JSPropertyPrivate _ s => "JSPrivateName " ++ singleQuote s.val
  | .JSPropertyString _ s => "JSIdentifier " ++ singleQuote s.render
  | .JSPropertyNumber _ s => "JSIdentifier " ++ singleQuote s.render
  | .JSPropertyComputed _ x _ => "JSPropertyComputed (" ++ ssExpression x ++ ")"

def ssArrayElement : JSArrayElement → String
  | .JSArrayElement e => ssExpression e
  | .JSArrayComma _ => "JSComma"

def ssTemplatePart (isLast : Bool) : JSTemplatePart → String
  | .JSTemplatePart e _ s =>
      "(" ++ ssExpression e ++ "," ++ singleQuote (templatePartSpelling s isLast) ++ ")"

def ssClassHeritage : JSClassHeritage → String
  | .JSExtendsNone => ""
  | .JSExtends _ x => ssExpression x

def ssClassElement : JSClassElement → String
  | .JSClassInstanceMethod ds m => ssDecorators ds ++ ssMethodDefinition m
  | .JSClassStaticMethod ds _ m =>
      ssDecorators ds ++ "JSClassStaticMethod (" ++ ssMethodDefinition m ++ ")"
  | .JSClassInstanceField ds n i _ =>
      ssDecorators ds ++ "JSClassInstanceField (" ++ ssPropertyName n ++ ") "
        ++ ssVarInitializer i
  | .JSClassStaticField ds _ n i _ =>
      ssDecorators ds ++ "JSClassStaticField (" ++ ssPropertyName n ++ ") "
        ++ ssVarInitializer i
  | .JSClassStaticBlock _ b => "JSClassStaticBlock (" ++ ssBlock b ++ ")"
  | .JSClassSemi _ => "JSClassSemi"

def ssDecorator : JSDecorator → String
  | .JSDecorator _ e => "JSDecorator (" ++ ssExpression e ++ ")"

def ssDecorators : List JSDecorator → String
  | [] => ""
  | d :: ds => ssDecorator d ++ " " ++ ssDecorators ds

def ssModuleItem : JSModuleItem → String
  | .JSModuleExportDeclaration _ x1 =>
      "JSModuleExportDeclaration (" ++ ssExportDeclaration x1 ++ ")"
  | .JSModuleImportDeclaration _ x1 =>
      "JSModuleImportDeclaration (" ++ ssImportDeclaration x1 ++ ")"
  | .JSModuleStatementListItem x1 => "JSModuleStatementListItem (" ++ ssStatement x1 ++ ")"

def ssImportDeclaration : JSImportDeclaration → String
  | .JSImportDeclaration imp from_ _ =>
      "JSImportDeclaration (" ++ ssImportClause imp ++ "," ++ ssFromClause from_ ++ ")"
  | .JSImportDeclarationBare _ m attrs _ =>
      "JSImportDeclarationBare (" ++ singleQuote m.val ++ ssImportAttributes? attrs ++ ")"

def ssImportClause : JSImportClause → String
  | .JSImportClauseDefault x => "JSImportClauseDefault (" ++ ssIdent x ++ ")"
  | .JSImportClauseNameSpace x => "JSImportClauseNameSpace (" ++ ssImportNameSpace x ++ ")"
  | .JSImportClauseNamed x => "JSImportClauseNameSpace (" ++ ssImportsNamed x ++ ")"
  | .JSImportClauseDefaultNameSpace x1 _ x2 =>
      "JSImportClauseDefaultNameSpace (" ++ ssIdent x1 ++ "," ++ ssImportNameSpace x2 ++ ")"
  | .JSImportClauseDefaultNamed x1 _ x2 =>
      "JSImportClauseDefaultNamed (" ++ ssIdent x1 ++ "," ++ ssImportsNamed x2 ++ ")"

def ssFromClause : JSFromClause → String
  | .JSFromClause _ _ m attrs =>
      "JSFromClause " ++ singleQuote m.val ++ ssImportAttributes? attrs

def ssImportAttribute : JSImportAttribute → String
  | .JSImportAttribute _ k _ _ v =>
      "JSImportAttribute (" ++ singleQuote k.val ++ "," ++ singleQuote v.val ++ ")"

def ssImportAttrCommaListAux : JSCommaList JSImportAttribute → List String → List String
  | .JSLCons xs _ x, acc => ssImportAttrCommaListAux xs (ssImportAttribute x :: acc)
  | .JSLOne x, acc => ssImportAttribute x :: acc
  | .JSLNil, acc => acc

def ssImportAttributes? : Option JSImportAttributes → String
  | none => ""
  | some (.JSImportAttributes _ _ attrs _) =>
      ",JSImportAttributes [" ++ ",".intercalate (ssImportAttrCommaListAux attrs []) ++ "]"

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
  | .JSExportAll _ from_ _ => "JSExportAll (" ++ ssFromClause from_ ++ ")"
  | .JSExportAllAs _ _ n from_ _ =>
      "JSExportAllAs (" ++ ssIdent n ++ "," ++ ssFromClause from_ ++ ")"
  | .JSExportDefault _ e _ => "JSExportDefault (" ++ ssExpression e ++ ")"
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

/-- A comma list grows at its end, so it is walked inwards onto an
accumulator: appending at every step would cost a copy of the list already
built. -/
def ssExprCommaListAux : JSCommaList JSExpression → List String → List String
  | .JSLCons l _ i, acc => ssExprCommaListAux l (ssExpression i :: acc)
  | .JSLOne i, acc => ssExpression i :: acc
  | .JSLNil, acc => acc

def ssExprCommaList (xs : JSCommaList JSExpression) : String :=
  "(" ++ commaJoin (ssExprCommaListAux xs []) ++ ")"

def ssExprCommaList1Aux : JSCommaList1 JSExpression → List String → List String
  | .JSL1Cons l _ i, acc => ssExprCommaList1Aux l (ssExpression i :: acc)
  | .JSL1One i, acc => ssExpression i :: acc

/-- The declarators of a `var`, `let` or `const`, which are a non-empty
comma list. -/
def ssExprCommaList1 (xs : JSCommaList1 JSExpression) : String :=
  "(" ++ commaJoin (ssExprCommaList1Aux xs []) ++ ")"

def ssImportSpecCommaListAux : JSCommaList JSImportSpecifier → List String → List String
  | .JSLCons l _ i, acc => ssImportSpecCommaListAux l (ssImportSpecifier i :: acc)
  | .JSLOne i, acc => ssImportSpecifier i :: acc
  | .JSLNil, acc => acc

def ssImportSpecCommaList (xs : JSCommaList JSImportSpecifier) : String :=
  "(" ++ commaJoin (ssImportSpecCommaListAux xs []) ++ ")"

def ssExportSpecCommaListAux : JSCommaList JSExportSpecifier → List String → List String
  | .JSLCons l _ i, acc => ssExportSpecCommaListAux l (ssExportSpecifier i :: acc)
  | .JSLOne i, acc => ssExportSpecifier i :: acc
  | .JSLNil, acc => acc

def ssExportSpecCommaList (xs : JSCommaList JSExportSpecifier) : String :=
  "(" ++ commaJoin (ssExportSpecCommaListAux xs []) ++ ")"

def ssObjectPropertyCommaListAux : JSCommaList JSObjectProperty → List String → List String
  | .JSLCons l _ i, acc => ssObjectPropertyCommaListAux l (ssObjectProperty i :: acc)
  | .JSLOne i, acc => ssObjectProperty i :: acc
  | .JSLNil, acc => acc

def ssObjectPropertyList : JSCommaTrailingList JSObjectProperty → String
  | .JSCTLComma xs _ => "[" ++ commaJoin (ssObjectPropertyCommaListAux xs []) ++ ",JSComma]"
  | .JSCTLNone xs => "[" ++ commaJoin (ssObjectPropertyCommaListAux xs []) ++ "]"

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
  | [x] => [ssTemplatePart true x]
  | x :: xs => ssTemplatePart false x :: ssTemplatePartsAux xs

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

end Language.JavaScript.Parser.AST
