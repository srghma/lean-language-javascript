/-
Conversion of the scope safe `BrujinAST` back into the deterministic `MiniAST`.
-/
import LanguageJavascriptBrujin.AST
import LanguageJavascriptMini.Printer

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST

class NamingScheme where
  constNameOf : (level : Nat) → (index : Nat) → NEString
  mutNameOf : (level : Nat) → (index : Nat) → NEString

def levelNaming : NamingScheme where
  constNameOf l _ := constName l
  mutNameOf l _ := mutName l

def indexNaming : NamingScheme where
  constNameOf _ i := idxConstName i
  mutNameOf _ i := idxMutName i

section Naming
variable [NamingScheme]

def cName (level index : Nat) : NEString := NamingScheme.constNameOf level index
def mName (level index : Nat) : NEString := NamingScheme.mutNameOf level index

def paramName (m arity j : Nat) : NEString := mName (m + j) (arity - 1 - j)

def paramNames (m arity : Nat) : List NEString :=
  (List.range arity).map (paramName m arity)

def paramExprs (m arity : Nat) : List MiniExpr :=
  (paramNames m arity).map .ident

mutual

partial def toMiniExpr {c m : Nat} (e : Expr c m) : MiniExpr :=
  match e with
  | .mutVar i => .ident (mName (mutLevel i) i.val)
  | .constVar i => .ident (cName (constLevel i) i.val)
  | .unsafeGlobal n => .ident n
  | .number raw => .number raw
  | .string v => .string v
  | .regex raw => .regex raw
  | .null => .null
  | .true_ => .true_
  | .false_ => .false_
  | .this => .this
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
  | .classAnon her body => .classExpr none (toMiniOptExpr her) (toMiniClassElems body)
  | .classSelf her body =>
      .classExpr (some (cName c 0)) (toMiniOptExpr her) (toMiniClassElems body)
  | .seq a b => .seq (toMiniExpr a) (toMiniExpr b)
  | .binary a op b => .binary (toMiniExpr a) op (toMiniExpr b)
  | .ternary a b d => .ternary (toMiniExpr a) (toMiniExpr b) (toMiniExpr d)
  | .arrow arity body => .arrow (paramExprs m arity) (toMiniArrowBody body)
  | .func isAsync isGen arity body =>
      .func isAsync isGen none (paramExprs m arity) (toMiniBlock body)
  | .funcSelf isAsync isGen arity body =>
      .func isAsync isGen (some (cName c 0)) (paramExprs m arity) (toMiniBlock body)
  | .spread x => .spread (toMiniExpr x)
  | .template tag head parts =>
      .template (toMiniOptExpr tag) head (toMiniTemplateParts parts)
  | .unary op x => .unary op (toMiniExpr x)
  | .yield x => .yield (toMiniOptExpr x)
  | .yieldFrom x => .yieldFrom (toMiniExpr x)

partial def toMiniTarget {c m : Nat} (t : Target c m) : MiniExpr :=
  match t with
  | .mut i => .ident (mName (mutLevel i) i.val)
  | .unsafeGlobal n => .ident n
  | .dot o n => .dot (toMiniExpr o) n
  | .index o i => .index (toMiniExpr o) (toMiniExpr i)

partial def toMiniExprs {c m : Nat} : Exprs c m → List MiniExpr
  | .nil => []
  | .cons e r => toMiniExpr e :: toMiniExprs r

partial def toMiniOptExpr {c m : Nat} : OptExpr c m → Option MiniExpr
  | .none => none
  | .some e => some (toMiniExpr e)

partial def toMiniArrayElem {c m : Nat} : ArrayElem c m → MiniArrayElement
  | .elem e => .elem (toMiniExpr e)
  | .hole => .hole

partial def toMiniArrayElems {c m : Nat} : ArrayElems c m → List MiniArrayElement
  | .nil => []
  | .cons e r => toMiniArrayElem e :: toMiniArrayElems r

partial def toMiniTemplatePart {c m : Nat} : TemplatePart c m → MiniTemplatePart
  | .mk e s => ⟨toMiniExpr e, s⟩

partial def toMiniTemplateParts {c m : Nat} : TemplateParts c m → List MiniTemplatePart
  | .nil => []
  | .cons e r => toMiniTemplatePart e :: toMiniTemplateParts r

partial def toMiniPropName {c m : Nat} : PropName c m → MiniPropertyName
  | .ident n => .ident n
  | .string v => .string v
  | .number raw => .number raw
  | .computed e => .computed (toMiniExpr e)

partial def toMiniProperty {c m : Nat} (p : Property c m) : MiniProperty :=
  match p with
  | .keyValue k v => .keyValue (toMiniPropName k) (toMiniExpr v)
  | .method kind k arity body =>
      .method kind (toMiniPropName k) (paramExprs m arity) (toMiniBlock body)

partial def toMiniProperties {c m : Nat} : Properties c m → List MiniProperty
  | .nil => []
  | .cons p r => toMiniProperty p :: toMiniProperties r

partial def toMiniClassElem {c m : Nat} (el : ClassElem c m) : MiniClassElement :=
  match el with
  | .mk isStatic kind k arity body =>
      ⟨isStatic, kind, toMiniPropName k, paramExprs m arity, toMiniBlock body⟩

partial def toMiniClassElems {c m : Nat} : ClassElems c m → List MiniClassElement
  | .nil => []
  | .cons e r => toMiniClassElem e :: toMiniClassElems r

partial def toMiniArrowBody {c m : Nat} : ArrowBody c m → MiniArrowBody
  | .expr e => .expr (toMiniExpr e)
  | .block b => .block (toMiniBlock b)

partial def toMiniForInit {c m dc dm : Nat} : ForInit c m dc dm → MiniForInit
  | .none => .none
  | .expr e => .expr (toMiniExpr e)
  | .constDecl init => .decl .const ⟨⟨.ident (cName c 0), some (toMiniExpr init)⟩, []⟩
  | .letDecl init => .decl .let_ ⟨⟨.ident (mName m 0), toMiniOptExpr init⟩, []⟩

partial def toMiniForHead {c m dc dm : Nat} : ForHead c m dc dm → MiniForHead
  | .target t => .pattern (toMiniTarget t)
  | .constBind => .decl .const (.ident (cName c 0))
  | .letBind => .decl .let_ (.ident (mName m 0))

partial def toMiniSwitchCase {c m : Nat} : SwitchCase c m → MiniSwitchCase
  | .case t b => .case (toMiniExpr t) (toMiniBlock b)
  | .default b => .default (toMiniBlock b)

partial def toMiniSwitchCases {c m : Nat} : SwitchCases c m → List MiniSwitchCase
  | .nil => []
  | .cons k r => toMiniSwitchCase k :: toMiniSwitchCases r

partial def toMiniOptBlock {c m : Nat} : OptBlock c m → Option MiniStatement
  | .none => none
  | .some b => some (.block (toMiniBlock b))

partial def toMiniTryTail {c m : Nat} (tail : TryTail c m) : MiniTryTail :=
  match tail with
  | .catch_ body fin =>
      .catches ⟨⟨.ident (mName m 0), none, toMiniBlock body⟩, []⟩
        (match fin with
          | .none => .none
          | .some b => .some (toMiniBlock b))
  | .finallyOnly b => .finallyOnly (toMiniBlock b)

partial def toMiniStmt {c m dc dm : Nat} (s : Stmt c m dc dm) : MiniStatement :=
  match s with
  | .expr e => .expr (toMiniExpr e)
  | .constDecl init => .decl .const ⟨⟨.ident (cName c 0), some (toMiniExpr init)⟩, []⟩
  | .letDecl init => .decl .let_ ⟨⟨.ident (mName m 0), toMiniOptExpr init⟩, []⟩
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
  | .funcDecl isAsync isGen arity body =>
      .funcDecl isAsync isGen (cName c 0) (paramExprs m arity) (toMiniBlock body)
  | .classDecl her body =>
      .classDecl (cName c 0) (toMiniOptExpr her) (toMiniClassElems body)
  | .return_ e => .return_ (toMiniOptExpr e)
  | .throw e => .throw (toMiniExpr e)
  | .break_ l => .break_ l
  | .continue_ l => .continue_ l
  | .labelled l s' => .labelled l (toMiniStmt s')
  | .switch d cs => .switch (toMiniExpr d) (toMiniSwitchCases cs)
  | .try_ b tail => .try_ (toMiniBlock b) (toMiniTryTail tail)

partial def toMiniBlock {c m : Nat} : Block c m → List MiniStatement
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
  MiniImportClause.mk! default_ namespace_ named clause.mod

def toMiniExportLocal {c m : Nat} : ExportLocal c m → MiniSpecifier
  | .const i exported => ⟨cName (constLevel i) i.val, some exported⟩
  | .mut i exported => ⟨mName (mutLevel i) i.val, some exported⟩

def toMiniExportLocals {c m : Nat} : ExportLocals c m → List MiniSpecifier
  | .nil => []
  | .cons e r => toMiniExportLocal e :: toMiniExportLocals r

def toMiniModuleItem {c m dc dm : Nat} : ModuleItem c m dc dm → MiniModuleItem
  | .stmt s => .stmt (toMiniStmt s)
  | .importBare mod => .importDecl (.bare mod)
  | .importClause clause => .importDecl (.clause (toMiniImport c clause))
  | .exportFrom specs mod => .exportDecl (.fromClause specs mod)
  | .exportLocals specs => .exportDecl (.locals (toMiniExportLocals specs))
  | .exportDecl s => .exportDecl (.decl (toMiniStmt s))

def toMiniModuleItems {c m : Nat} : ModuleItems c m → List MiniModuleItem
  | .nil => []
  | .cons it r => toMiniModuleItem it :: toMiniModuleItems r

def toMiniProgram (p : Program) : MiniProgram := ⟨toMiniModuleItems p.items⟩

end Naming

instance : NamingScheme := levelNaming

def printProgram (p : Program) : String :=
  MiniAST.printProgram (toMiniProgram p)

def toMiniProgramIndexed (p : Program) : MiniProgram := @toMiniProgram indexNaming p

def printProgramIndexed (p : Program) : String :=
  MiniAST.printProgram (toMiniProgramIndexed p)

def printExprIndexed {c m : Nat} (e : Expr c m) : String :=
  MiniAST.printExpr (@toMiniExpr indexNaming c m e)

def printBlock {c m : Nat} (b : Block c m) : String :=
  MiniAST.printProgram ⟨(toMiniBlock b).map .stmt⟩

def printExpr {c m : Nat} (e : Expr c m) : String :=
  MiniAST.printExpr (toMiniExpr e)

instance {c m : Nat} : BEq (Expr c m) := ⟨fun a b => toMiniExpr a == toMiniExpr b⟩
instance {c m : Nat} : BEq (Block c m) := ⟨fun a b => toMiniBlock a == toMiniBlock b⟩
instance {c m dc dm : Nat} : BEq (Stmt c m dc dm) := ⟨fun a b => toMiniStmt a == toMiniStmt b⟩
instance : BEq Program := ⟨fun a b => toMiniProgram a == toMiniProgram b⟩

instance {c m : Nat} : ToString (Expr c m) := ⟨printExpr⟩
instance : ToString Program := ⟨printProgram⟩

end Language.JavaScript.BrujinAST
