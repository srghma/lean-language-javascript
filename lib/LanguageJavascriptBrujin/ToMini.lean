/-
Conversion of the scope safe `BrujinAST` back into the deterministic `MiniAST`.
-/
import LanguageJavascriptBrujin.AST
import LanguageJavascriptMini.Printer

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST
open Language.JavaScript.Doc

/-! ## Printing an extension

The tree is parametrised by its two extensions, so printing it needs to be
told how one is written: that is what `ExtPrinter` carries.
`printUnsafeExprExt` says how an `Expr.unsafeExt` is written and
`printUnsafeTargetExt` how a `Target.unsafeExt` is, each as a `Doc`.

The conversion to `MiniAST` needs a `MiniExpr` rather than a document, so
the class has a second pair of fields for it, `exprExtToMini` and
`targetExtToMini`.  They default to the documents above, spliced into the
tree as one atomic token — which is what an extension usually is — so an
instance only has to give the two printers; an extension which *is* a
JavaScript expression (an unknown global, say) is better served by giving
that expression, and then the conversion to `MiniAST` keeps its structure. -/

/-- The width an extension's document is rendered at when it is spliced
into the tree as a token: wide enough that it is never broken. -/
def extTokenWidth : Nat := 1000000

/-- A document spliced into a `MiniAST` tree as one atomic token: it is
printed verbatim, exactly where the extension stands, and is treated as a
primary expression, so a document that needs them has to carry its own
parentheses. -/
def rawToken (d : Doc) : MiniExpr := .ident (NEString.ofString! (Doc.render extTokenWidth d))

/-- How the two extensions of a tree are written. -/
class ExtPrinter (exprExt targetExt : Nat → Nat → Type) where
  /-- How an expression extension, `Expr.unsafeExt`, is written. -/
  printUnsafeExprExt : {c m : Nat} → exprExt c m → Doc
  /-- How a target extension, `Target.unsafeExt`, is written. -/
  printUnsafeTargetExt : {c m : Nat} → targetExt c m → Doc
  /-- The expression the conversion to `MiniAST` puts in place of an
  expression extension; by default the document above, as a token. -/
  exprExtToMini : {c m : Nat} → exprExt c m → MiniExpr := fun e => rawToken (printUnsafeExprExt e)
  /-- The expression the conversion to `MiniAST` puts in place of a target
  extension; by default the document above, as a token. -/
  targetExtToMini : {c m : Nat} → targetExt c m → MiniExpr :=
    fun e => rawToken (printUnsafeTargetExt e)

/-- A tree whose unknown names are free variables is written by writing the name. -/
instance : ExtPrinter FreeExt FreeExt where
  printUnsafeExprExt n := .text n.val
  printUnsafeTargetExt n := .text n.val
  exprExtToMini n := .ident n
  targetExtToMini n := .ident n

/-- A tree with no extension has nothing to print. -/
instance : ExtPrinter NoExt NoExt where
  printUnsafeExprExt e := e.elim
  printUnsafeTargetExt e := e.elim

class NamingScheme where
  constNameOf : (level : Nat) → (index : Nat) → NEString
  mutNameOf : (level : Nat) → (index : Nat) → NEString

@[instance_reducible] def levelNaming : NamingScheme where
  constNameOf l _ := constName l
  mutNameOf l _ := mutName l

@[instance_reducible] def indexNaming : NamingScheme where
  constNameOf _ i := idxConstName i
  mutNameOf _ i := idxMutName i

section Naming
variable [naming : NamingScheme]
-- The extensions a tree may mention, and how they are written.  Every
-- function in this section is generic in them.
variable {exprExt targetExt : Nat → Nat → Type} [extPrinter : ExtPrinter exprExt targetExt]

def cName (level index : Nat) : NEString := NamingScheme.constNameOf level index
def mName (level index : Nat) : NEString := NamingScheme.mutNameOf level index

def paramName (m arity j : Nat) : NEString := mName (m + j) (arity - 1 - j)

/-- The parameters of a function, as the names the printer gives them: one
`x` per ordinary parameter, followed by `...x` if there is a rest
parameter. -/
def paramBinders (m arity : Nat) (hasRest : Bool) : List MiniParam :=
  let k := paramCount arity hasRest
  (List.range arity).map (fun j => MiniParam.plain (.ident (paramName m k j))) ++
    (if hasRest then [MiniParam.rest (.ident (paramName m k arity))] else [])

/-- One binder is written per parameter, the rest parameter included. -/
@[simp] theorem paramBinders_length (m arity : Nat) (hasRest : Bool) :
    (paramBinders m arity hasRest).length = arity + hasRest.toNat := by
  cases hasRest <;> simp [paramBinders, paramCount]

/-- An ordinary parameter is written as a plain name. -/
theorem paramBinders_getElem_lt (m arity : Nat) (hasRest : Bool) (j : Nat) (hj : j < arity) :
    (paramBinders m arity hasRest)[j]'(by simp; omega) =
      .plain (.ident (paramName m (arity + hasRest.toNat) j)) := by
  cases hasRest <;>
    simp [paramBinders, paramCount, List.getElem_append_left, hj]

/-- The rest parameter, when there is one, is written last and as `...x`. -/
theorem paramBinders_getElem_rest (m arity : Nat) :
    (paramBinders m arity true)[arity]'(by simp) =
      .rest (.ident (paramName m (arity + 1) arity)) := by
  simp [paramBinders, paramCount, List.getElem_append_right]

mutual

def toMiniExpr {c m : Nat} (e : Expr exprExt targetExt c m) : MiniExpr :=
  match e with
  | .mutVar i => .ident (mName (mutLevel i) i.val)
  | .constVar i => .ident (cName (constLevel i) i.val)
  | .unsafeExt e => extPrinter.exprExtToMini e
  | .number n => .number n
  | .string v => .string v
  | .regex r => .regex r
  | .null => .null
  | .true_ => .true_
  | .false_ => .false_
  | .this => .this
  | .superDot n => .superDot n
  | .superIndex i => .superIndex (toMiniExpr i)
  | .superCall args => .superCall (toMiniExprs args)
  | .newTarget => .newTarget
  | .array els => .array (toMiniArrayElems els)
  | .object ps => .object (toMiniProperties ps)
  | .assign t op rhs => .assign (toMiniTarget t) op (toMiniExpr rhs)
  | .update t op isPrefix =>
      if isPrefix then
        .unary (match op with | .incr => .preIncr | .decr => .preDecr) (toMiniTarget t)
      else .postfix (toMiniTarget t) op
  | .await x => .await (toMiniExpr x)
  | .call f args => .call (toMiniExpr f) (toMiniExprs args)
  | .new f args => .new (toMiniExpr f) (toMiniExprs args)
  | .dot o n => .dot (toMiniExpr o) n
  | .index o i => .index (toMiniExpr o) (toMiniExpr i)
  | .privateDot o n => .privateDot (toMiniExpr o) n
  | .privateName n => .privateName n
  | .chain base hd tl => .chain (toMiniExpr base) ⟨toMiniChainLink hd, toMiniChainLinks tl⟩
  | .importMeta => .importMeta
  | .importCall spec opts => .importCall (toMiniExpr spec) (toMiniOptExpr opts)
  | .classAnon ds her body =>
      .classExpr (toMiniExprs ds) none (toMiniOptExpr her) (toMiniClassElems body)
  | .classSelf ds her body =>
      .classExpr (toMiniExprs ds) (some (cName c 0)) (toMiniOptExpr her)
        (toMiniClassElems body)
  | .seq a b => .seq (toMiniExpr a) (toMiniExpr b)
  | .binary a op b => .binary (toMiniExpr a) op (toMiniExpr b)
  | .ternary a b d => .ternary (toMiniExpr a) (toMiniExpr b) (toMiniExpr d)
  | .arrow arity hasRest body =>
      .arrow (paramBinders m arity hasRest) (toMiniArrowBody body)
  | .func isAsync isGen hasRest arity body =>
      .func isAsync isGen none (paramBinders m arity hasRest) (toMiniBlock body)
  | .funcSelf isAsync isGen hasRest arity body =>
      .func isAsync isGen (some (cName c 0)) (paramBinders m arity hasRest) (toMiniBlock body)
  | .spread x => .spread (toMiniExpr x)
  | .template tag head parts =>
      .template (toMiniOptExpr tag) head (toMiniTemplateParts parts)
  | .unary op x => .unary op (toMiniExpr x)
  | .yield x => .yield (toMiniOptExpr x)
  | .yieldFrom x => .yieldFrom (toMiniExpr x)

def toMiniTarget {c m : Nat} (t : Target exprExt targetExt c m) : MiniExpr :=
  match t with
  | .mut i => .ident (mName (mutLevel i) i.val)
  | .unsafeExt e => extPrinter.targetExtToMini e
  | .dot o n => .dot (toMiniExpr o) n
  | .privateDot o n => .privateDot (toMiniExpr o) n
  | .superDot n => .superDot n
  | .superIndex i => .superIndex (toMiniExpr i)
  | .index o i => .index (toMiniExpr o) (toMiniExpr i)

def toMiniChainLink {c m : Nat} : ChainLink exprExt targetExt c m → MiniChainLink
  | .dot opt n => .dot opt n
  | .privateDot opt n => .privateDot opt n
  | .index opt i => .index opt (toMiniExpr i)
  | .call opt args => .call opt (toMiniExprs args)

def toMiniChainLinks {c m : Nat} : ChainLinks exprExt targetExt c m → List MiniChainLink
  | .nil => []
  | .cons hd tl => toMiniChainLink hd :: toMiniChainLinks tl

def toMiniExprs {c m : Nat} : Exprs exprExt targetExt c m → List MiniExpr
  | .nil => []
  | .cons e r => toMiniExpr e :: toMiniExprs r

def toMiniOptExpr {c m : Nat} : OptExpr exprExt targetExt c m → Option MiniExpr
  | .none => none
  | .some e => some (toMiniExpr e)

def toMiniArrayElem {c m : Nat} : ArrayElem exprExt targetExt c m → MiniArrayElement
  | .elem e => .elem (toMiniExpr e)
  | .hole => .hole

def toMiniArrayElems {c m : Nat} : ArrayElems exprExt targetExt c m → List MiniArrayElement
  | .nil => []
  | .cons e r => toMiniArrayElem e :: toMiniArrayElems r

def toMiniTemplatePart {c m : Nat} : TemplatePart exprExt targetExt c m → MiniTemplatePart
  | .mk e s => ⟨toMiniExpr e, s⟩

def toMiniTemplateParts {c m : Nat} : TemplateParts exprExt targetExt c m → List MiniTemplatePart
  | .nil => []
  | .cons e r => toMiniTemplatePart e :: toMiniTemplateParts r

def toMiniPropName {c m : Nat} : PropName exprExt targetExt c m → MiniPropertyName
  | .ident n => .ident n
  | .private_ n => .private_ n
  | .string v => .string v
  | .number raw => .number raw
  | .computed e => .computed (toMiniExpr e)

def toMiniProperty {c m : Nat} (p : Property exprExt targetExt c m) : MiniProperty :=
  match p with
  | .keyValue k v => .keyValue (toMiniPropName k) (toMiniExpr v)
  | .spread e => .spread (toMiniExpr e)
  | .method kind key arity hasRest body =>
      .method kind (toMiniPropName key) (paramBinders m arity hasRest) (toMiniBlock body)

def toMiniProperties {c m : Nat} : Properties exprExt targetExt c m → List MiniProperty
  | .nil => []
  | .cons p r => toMiniProperty p :: toMiniProperties r

def toMiniClassElem {c m : Nat} (el : ClassElem exprExt targetExt c m) : MiniClassElement :=
  match el with
  | .method ds isStatic kind key arity hasRest body =>
      .method (toMiniExprs ds) isStatic kind (toMiniPropName key)
        (paramBinders m arity hasRest) (toMiniBlock body)
  | .field ds isStatic key init =>
      .field (toMiniExprs ds) isStatic (toMiniPropName key) (toMiniOptExpr init)
  | .staticBlock body => .staticBlock (toMiniBlock body)

def toMiniClassElems {c m : Nat} : ClassElems exprExt targetExt c m → List MiniClassElement
  | .nil => []
  | .cons e r => toMiniClassElem e :: toMiniClassElems r

def toMiniArrowBody {c m : Nat} : ArrowBody exprExt targetExt c m → MiniArrowBody
  | .expr e => .expr (toMiniExpr e)
  | .block b => .block (toMiniBlock b)

def toMiniForInit {c m dc dm : Nat} : ForInit exprExt targetExt c m dc dm → MiniForInit
  | .none => .none
  | .expr e => .expr (toMiniExpr e)
  | .constDecl init => .decl .const ⟨⟨.ident (cName c 0), some (toMiniExpr init)⟩, []⟩
  | .letDecl init => .decl .let_ ⟨⟨.ident (mName m 0), toMiniOptExpr init⟩, []⟩

def toMiniForHead {c m dc dm : Nat} : ForHead exprExt targetExt c m dc dm → MiniForHead
  | .target t => .pattern (.target (toMiniTarget t))
  | .constBind => .decl .const (.ident (cName c 0))
  | .letBind => .decl .let_ (.ident (mName m 0))

def toMiniSwitchCase {c m : Nat} : SwitchCase exprExt targetExt c m → MiniSwitchCase
  | .case t b => .case (toMiniExpr t) (toMiniBlock b)
  | .default b => .default (toMiniBlock b)

def toMiniSwitchCases {c m : Nat} : SwitchCases exprExt targetExt c m → List MiniSwitchCase
  | .nil => []
  | .cons k r => toMiniSwitchCase k :: toMiniSwitchCases r

def toMiniOptBlock {c m : Nat} : OptBlock exprExt targetExt c m → Option MiniStatement
  | .none => none
  | .some b => some (.block (toMiniBlock b))

def toMiniTryTail {c m : Nat} (tail : TryTail exprExt targetExt c m) : MiniTryTail :=
  match tail with
  | .catch_ body fin =>
      .catches ⟨⟨.ident (mName m 0), none, toMiniBlock body⟩, []⟩
        (match fin with
          | .none => .none
          | .some b => .some (toMiniBlock b))
  | .finallyOnly b => .finallyOnly (toMiniBlock b)

def toMiniStmt {c m dc dm : Nat} (s : Stmt exprExt targetExt c m dc dm) : MiniStatement :=
  match s with
  | .expr e => .expr (toMiniExpr e)
  | .constDecl init => .decl .const ⟨⟨.ident (cName c 0), some (toMiniExpr init)⟩, []⟩
  | .letDecl init => .decl .let_ ⟨⟨.ident (mName m 0), toMiniOptExpr init⟩, []⟩
  | .usingDecl isAwait init =>
      .using_ isAwait ⟨⟨.ident (cName c 0), some (toMiniExpr init)⟩, []⟩
  | .block b => .block (toMiniBlock b)
  | .if_ cond t e => .if_ (toMiniExpr cond) (.block (toMiniBlock t)) (toMiniOptBlock e)
  | .while_ cond b => .while_ (toMiniExpr cond) (.block (toMiniBlock b))
  | .doWhile b cond => .doWhile (.block (toMiniBlock b)) (toMiniExpr cond)
  | .for_ init cond step body =>
      .for_ (toMiniForInit init) (toMiniOptExpr cond) (toMiniOptExpr step)
        (.block (toMiniBlock body))
  | .forIn head obj body =>
      .forIn (toMiniForHead head) (toMiniExpr obj) (.block (toMiniBlock body))
  | .forOf head obj body =>
      .forOf (toMiniForHead head) (toMiniExpr obj) (.block (toMiniBlock body))
  | .funcDecl isAsync isGen hasRest arity body =>
      .funcDecl isAsync isGen (cName c 0) (paramBinders m arity hasRest) (toMiniBlock body)
  | .classDecl ds her body =>
      .classDecl (toMiniExprs ds) (cName c 0) (toMiniOptExpr her) (toMiniClassElems body)
  | .return_ e => .return_ (toMiniOptExpr e)
  | .throw e => .throw (toMiniExpr e)
  | .break_ l => .break_ l
  | .continue_ l => .continue_ l
  | .labelled l s' => .labelled l (toMiniStmt s')
  | .switch d cs => .switch (toMiniExpr d) (toMiniSwitchCases cs)
  | .try_ b tail => .try_ (toMiniBlock b) (toMiniTryTail tail)

def toMiniBlock {c m : Nat} : Block exprExt targetExt c m → List MiniStatement
  | .nil => []
  | .cons s r => toMiniStmt s :: toMiniBlock r

end

def importLocalNames (c : Nat) (clause : ImportClause) : List NEString :=
  (List.range clause.count).map fun j => cName (c + j) (clause.count - 1 - j)

def toMiniImport (c : Nat) (clause : ImportClause) : MiniImportClause :=
  let names := importLocalNames c clause
  let (default_, names) :=
    if clause.hasDefault then (names.head?, names.drop 1) else (none, names)
  let (namespace_, names) :=
    if clause.hasNamespace then (names.head?, names.drop 1) else (none, names)
  let named :=
    if clause.named.isEmpty then none
    else some ((clause.named.zip names).map fun (n, local_) => ⟨n, some local_⟩)
  MiniImportClause.mk! default_ namespace_ named clause.mod clause.attrs

def toMiniExportLocal {c m : Nat} : ExportLocal exprExt targetExt c m → Specifier
  | .const i exported => ⟨cName (constLevel i) i.val, some exported⟩
  | .mut i exported => ⟨mName (mutLevel i) i.val, some exported⟩

def toMiniExportLocals {c m : Nat} : ExportLocals exprExt targetExt c m → List Specifier
  | .nil => []
  | .cons e r => toMiniExportLocal e :: toMiniExportLocals r

def toMiniModuleItem {c m dc dm : Nat} : ModuleItem exprExt targetExt c m dc dm → MiniModuleItem
  | .stmt s => .stmt (toMiniStmt s)
  | .importBare mod attrs => .importDecl (.bare mod attrs)
  | .importClause clause => .importDecl (.clause (toMiniImport c clause))
  | .exportFrom specs mod attrs => .exportDecl (.fromClause specs mod attrs)
  | .exportAll alias_ mod attrs => .exportDecl (.all alias_ mod attrs)
  | .exportDefaultExpr e => .exportDecl (.defaultExpr (toMiniExpr e))
  | .exportLocals specs => .exportDecl (.locals (toMiniExportLocals specs))
  | .exportDecl s => .exportDecl (.decl (toMiniStmt s))

def toMiniModuleItems {c m : Nat} : ModuleItems exprExt targetExt c m → List MiniModuleItem
  | .nil => []
  | .cons it r => toMiniModuleItem it :: toMiniModuleItems r

def toMiniProgram (p : ModuleItems exprExt targetExt 0 0) : MiniProgram := ⟨toMiniModuleItems p⟩

end Naming

instance : NamingScheme := levelNaming

section Printing
-- The extensions of the tree being printed, and how they are written.
variable {exprExt targetExt : Nat → Nat → Type} [extPrinter : ExtPrinter exprExt targetExt]

def printProgram (p : ModuleItems exprExt targetExt 0 0) : String :=
  MiniAST.printProgram (toMiniProgram p)

def toMiniProgramIndexed (p : ModuleItems exprExt targetExt 0 0) : MiniProgram :=
  ⟨toMiniModuleItems (naming := indexNaming) p⟩

def printProgramIndexed (p : ModuleItems exprExt targetExt 0 0) : String :=
  MiniAST.printProgram (toMiniProgramIndexed p)

def printExprIndexed {c m : Nat} (e : Expr exprExt targetExt c m) : String :=
  MiniAST.printExpr (toMiniExpr (naming := indexNaming) e)

def printBlock {c m : Nat} (b : Block exprExt targetExt c m) : String :=
  MiniAST.printProgram ⟨(toMiniBlock b).map .stmt⟩

def printExpr {c m : Nat} (e : Expr exprExt targetExt c m) : String :=
  MiniAST.printExpr (toMiniExpr e)

/-- Print an expression with level-based names. -/
def printScopedExpr {c m : Nat} (e : Expr exprExt targetExt c m) : String := printExpr e

/-- Print an expression, naming variables by their de Bruijn index. -/
def printScopedExprIndexed {c m : Nat} (e : Expr exprExt targetExt c m) : String :=
  printExprIndexed e

instance {c m : Nat} : BEq (Expr exprExt targetExt c m) := ⟨fun a b => toMiniExpr a == toMiniExpr b⟩
instance {c m : Nat} : BEq (Block exprExt targetExt c m) := ⟨fun a b => toMiniBlock a == toMiniBlock b⟩
instance {c m dc dm : Nat} : BEq (Stmt exprExt targetExt c m dc dm) :=
  ⟨fun a b => toMiniStmt a == toMiniStmt b⟩
instance {c m : Nat} : BEq (ModuleItems exprExt targetExt c m) :=
  ⟨fun a b => toMiniModuleItems a == toMiniModuleItems b⟩

instance {c m : Nat} : ToString (Expr exprExt targetExt c m) := ⟨printExpr⟩
instance : ToString (ModuleItems exprExt targetExt 0 0) := ⟨printProgram⟩

end Printing

/-! ## Printing a tree whose extensions are written by hand

The functions above take how an extension is written from the `ExtPrinter`
instance; these ones take the two printers as arguments instead, which is
what a one off extension wants. -/

section PrintWith
variable {exprExt targetExt : Nat → Nat → Type}
  (printUnsafeExprExt : {c m : Nat} → exprExt c m → Doc)
  (printUnsafeTargetExt : {c m : Nat} → targetExt c m → Doc)

/-- The printer built from the two documents, each extension being written
verbatim where it stands. -/
@[instance_reducible] def extPrinterOf : ExtPrinter exprExt targetExt where
  printUnsafeExprExt := printUnsafeExprExt
  printUnsafeTargetExt := printUnsafeTargetExt

/-- Convert an expression to `MiniAST`, writing an extension with the two
given printers. -/
def toMiniExprWith [NamingScheme] {c m : Nat} (e : Expr exprExt targetExt c m) : MiniExpr :=
  letI : ExtPrinter exprExt targetExt := extPrinterOf printUnsafeExprExt printUnsafeTargetExt
  toMiniExpr e

/-- Print an expression, writing an extension with the two given
printers. -/
def printExprWith {c m : Nat} (e : Expr exprExt targetExt c m) : String :=
  letI : ExtPrinter exprExt targetExt := extPrinterOf printUnsafeExprExt printUnsafeTargetExt
  printExpr e

/-- Print an expression, naming the variables by their de Bruijn index and
writing an extension with the two given printers. -/
def printExprIndexedWith {c m : Nat} (e : Expr exprExt targetExt c m) : String :=
  letI : ExtPrinter exprExt targetExt := extPrinterOf printUnsafeExprExt printUnsafeTargetExt
  printExprIndexed e

/-- Print a block, writing an extension with the two given printers. -/
def printBlockWith {c m : Nat} (b : Block exprExt targetExt c m) : String :=
  letI : ExtPrinter exprExt targetExt := extPrinterOf printUnsafeExprExt printUnsafeTargetExt
  printBlock b

end PrintWith

end Language.JavaScript.BrujinAST
