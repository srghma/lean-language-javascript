/-
Conversion of the scope safe `BrujinAST` back into the deterministic
`MiniAST`, and from there — through `MiniASTPrinter` — into JavaScript
source.

A `BrujinAST` tree has no variable *names*, so the conversion has to invent
them.  It does so from the *level* of a binding, the number of bindings of
its kind that were already in scope where it was bound: the const variable
of level `l` is called `_cl` and the mutable one `_ml` (`constName`,
`mutName`).  Since the level of a variable does not change when the scope
grows, every mention of one variable produces the same name, and a name
generated for one binder is never generated for another one in its scope.
(The one thing the generated names cannot avoid is an `unsafeGlobal` that
is *itself* called `_c0`: reading the printed program back would then bind
it.  The underscore makes that unlikely, not impossible.)

The conversion is total: every `BrujinAST` tree describes a JavaScript
program, and no information is lost apart from the names, which were not
there.  It is what gives `BrujinAST` its printer (`printProgram`) and its
equality (`BEq`, comparing the canonical renderings: two trees are equal
exactly when they are equal up to the names, which is α-equivalence).
-/
import LanguageJavascriptBrujin.AST
import LanguageJavascriptMini.Printer

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST

/-- The name of the `j`-th parameter of a function whose body is entered
with `m` mutable variables already in scope. -/
def paramName (m j : Nat) : NEString := mutName (m + j)

/-- The names of the `arity` parameters of a function entered with `m`
mutable variables in scope, in source order. -/
def paramNames (m arity : Nat) : List NEString :=
  (List.range arity).map (paramName m)

/-- The parameter list of a function, as `MiniAST` identifiers. -/
def paramExprs (m arity : Nat) : List MiniExpr :=
  (paramNames m arity).map .ident

mutual

/-- The `MiniAST` expression denoted by a `BrujinAST` one. -/
partial def toMiniExpr {c m : Nat} (e : Expr c m) : MiniExpr :=
  match e with
  | .mutVar i => .ident (mutName (mutLevel i))
  | .constVar i => .ident (constName (constLevel i))
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
      .classExpr (some (constName c)) (toMiniOptExpr her) (toMiniClassElems body)
  | .seq a b => .seq (toMiniExpr a) (toMiniExpr b)
  | .binary a op b => .binary (toMiniExpr a) op (toMiniExpr b)
  | .ternary a b d => .ternary (toMiniExpr a) (toMiniExpr b) (toMiniExpr d)
  | .arrow arity body => .arrow (paramExprs m arity) (toMiniArrowBody body)
  | .func isAsync isGen arity body =>
      .func isAsync isGen none (paramExprs m arity) (toMiniBlock body)
  | .funcSelf isAsync isGen arity body =>
      .func isAsync isGen (some (constName c)) (paramExprs m arity) (toMiniBlock body)
  | .spread x => .spread (toMiniExpr x)
  | .template tag head parts =>
      .template (toMiniOptExpr tag) head (toMiniTemplateParts parts)
  | .unary op x => .unary op (toMiniExpr x)
  | .yield x => .yield (toMiniOptExpr x)
  | .yieldFrom x => .yieldFrom (toMiniExpr x)

/-- The expression an assignment target denotes. -/
partial def toMiniTarget {c m : Nat} (t : Target c m) : MiniExpr :=
  match t with
  | .mut i => .ident (mutName (mutLevel i))
  | .unsafeGlobal n => .ident n
  | .dot o n => .dot (toMiniExpr o) n
  | .index o i => .index (toMiniExpr o) (toMiniExpr i)

/-- A list of expressions. -/
partial def toMiniExprs {c m : Nat} : Exprs c m → List MiniExpr
  | .nil => []
  | .cons e r => toMiniExpr e :: toMiniExprs r

/-- An optional expression. -/
partial def toMiniOptExpr {c m : Nat} : OptExpr c m → Option MiniExpr
  | .none => none
  | .some e => some (toMiniExpr e)

/-- An element of an array literal. -/
partial def toMiniArrayElem {c m : Nat} : ArrayElem c m → MiniArrayElement
  | .elem e => .elem (toMiniExpr e)
  | .hole => .hole

/-- The elements of an array literal. -/
partial def toMiniArrayElems {c m : Nat} : ArrayElems c m → List MiniArrayElement
  | .nil => []
  | .cons e r => toMiniArrayElem e :: toMiniArrayElems r

/-- A substitution of a template literal. -/
partial def toMiniTemplatePart {c m : Nat} : TemplatePart c m → MiniTemplatePart
  | .mk e s => ⟨toMiniExpr e, s⟩

/-- The substitutions of a template literal. -/
partial def toMiniTemplateParts {c m : Nat} : TemplateParts c m → List MiniTemplatePart
  | .nil => []
  | .cons e r => toMiniTemplatePart e :: toMiniTemplateParts r

/-- The name of a property. -/
partial def toMiniPropName {c m : Nat} : PropName c m → MiniPropertyName
  | .ident n => .ident n
  | .string v => .string v
  | .number raw => .number raw
  | .computed e => .computed (toMiniExpr e)

/-- A member of an object literal. -/
partial def toMiniProperty {c m : Nat} (p : Property c m) : MiniProperty :=
  match p with
  | .keyValue k v => .keyValue (toMiniPropName k) (toMiniExpr v)
  | .method kind k arity body =>
      .method kind (toMiniPropName k) (paramExprs m arity) (toMiniBlock body)

/-- The members of an object literal. -/
partial def toMiniProperties {c m : Nat} : Properties c m → List MiniProperty
  | .nil => []
  | .cons p r => toMiniProperty p :: toMiniProperties r

/-- A member of a class body. -/
partial def toMiniClassElem {c m : Nat} (el : ClassElem c m) : MiniClassElement :=
  match el with
  | .mk isStatic kind k arity body =>
      ⟨isStatic, kind, toMiniPropName k, paramExprs m arity, toMiniBlock body⟩

/-- The members of a class body. -/
partial def toMiniClassElems {c m : Nat} : ClassElems c m → List MiniClassElement
  | .nil => []
  | .cons e r => toMiniClassElem e :: toMiniClassElems r

/-- The body of an arrow function. -/
partial def toMiniArrowBody {c m : Nat} : ArrowBody c m → MiniArrowBody
  | .expr e => .expr (toMiniExpr e)
  | .block b => .block (toMiniBlock b)

/-- The first clause of a `for (;;)` statement. -/
partial def toMiniForInit {c m dc dm : Nat} : ForInit c m dc dm → MiniForInit
  | .none => .none
  | .expr e => .expr (toMiniExpr e)
  | .constDecl init => .decl .const ⟨⟨.ident (constName c), some (toMiniExpr init)⟩, []⟩
  | .letDecl init => .decl .let_ ⟨⟨.ident (mutName m), toMiniOptExpr init⟩, []⟩

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement. -/
partial def toMiniForHead {c m dc dm : Nat} : ForHead c m dc dm → MiniForHead
  | .target t => .pattern (toMiniTarget t)
  | .constBind => .decl .const (.ident (constName c))
  | .letBind => .decl .let_ (.ident (mutName m))

/-- One case of a `switch`. -/
partial def toMiniSwitchCase {c m : Nat} : SwitchCase c m → MiniSwitchCase
  | .case t b => .case (toMiniExpr t) (toMiniBlock b)
  | .default b => .default (toMiniBlock b)

/-- The cases of a `switch`. -/
partial def toMiniSwitchCases {c m : Nat} : SwitchCases c m → List MiniSwitchCase
  | .nil => []
  | .cons k r => toMiniSwitchCase k :: toMiniSwitchCases r

/-- An optional block, as an optional statement. -/
partial def toMiniOptBlock {c m : Nat} : OptBlock c m → Option MiniStatement
  | .none => none
  | .some b => some (.block (toMiniBlock b))

/-- What follows the block of a `try`. -/
partial def toMiniTryTail {c m : Nat} (tail : TryTail c m) : MiniTryTail :=
  match tail with
  | .catch_ body fin =>
      .catches ⟨⟨.ident (mutName m), none, toMiniBlock body⟩, []⟩
        (match fin with
          | .none => .none
          | .some b => .some (toMiniBlock b))
  | .finallyOnly b => .finallyOnly (toMiniBlock b)

/-- A statement. -/
partial def toMiniStmt {c m dc dm : Nat} (s : Stmt c m dc dm) : MiniStatement :=
  match s with
  | .expr e => .expr (toMiniExpr e)
  | .constDecl init => .decl .const ⟨⟨.ident (constName c), some (toMiniExpr init)⟩, []⟩
  | .letDecl init => .decl .let_ ⟨⟨.ident (mutName m), toMiniOptExpr init⟩, []⟩
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
      .funcDecl isAsync isGen (constName c) (paramExprs m arity) (toMiniBlock body)
  | .classDecl her body =>
      .classDecl (constName c) (toMiniOptExpr her) (toMiniClassElems body)
  | .return_ e => .return_ (toMiniOptExpr e)
  | .throw e => .throw (toMiniExpr e)
  | .break_ l => .break_ l
  | .continue_ l => .continue_ l
  | .labelled l s' => .labelled l (toMiniStmt s')
  | .switch d cs => .switch (toMiniExpr d) (toMiniSwitchCases cs)
  | .try_ b tail => .try_ (toMiniBlock b) (toMiniTryTail tail)

/-- A block, as a list of statements. -/
partial def toMiniBlock {c m : Nat} : Block c m → List MiniStatement
  | .nil => []
  | .cons s r => toMiniStmt s :: toMiniBlock r

end

/-! ## Modules -/

/-- The local names an import clause binds, in source order: the default
import, the namespace import, then the named ones.  In a scope with `c`
const variables they get the levels `c`, `c + 1`, … -/
def importLocalNames (c : Nat) (clause : ImportClause) : List NEString :=
  (List.range clause.count).map fun j => constName (c + j)

/-- The `MiniAST` import clause of a `BrujinAST` one, in a scope with `c`
const variables. -/
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

/-- One entry of an `export { ... }` clause. -/
def toMiniExportLocal {c m : Nat} : ExportLocal c m → MiniSpecifier
  | .const i exported => ⟨constName (constLevel i), some exported⟩
  | .mut i exported => ⟨mutName (mutLevel i), some exported⟩

/-- The entries of an `export { ... }` clause. -/
def toMiniExportLocals {c m : Nat} : ExportLocals c m → List MiniSpecifier
  | .nil => []
  | .cons e r => toMiniExportLocal e :: toMiniExportLocals r

/-- A top level item. -/
def toMiniModuleItem {c m dc dm : Nat} : ModuleItem c m dc dm → MiniModuleItem
  | .stmt s => .stmt (toMiniStmt s)
  | .importBare mod => .importDecl (.bare mod)
  | .importClause clause => .importDecl (.clause (toMiniImport c clause))
  | .exportFrom specs mod => .exportDecl (.fromClause specs mod)
  | .exportLocals specs => .exportDecl (.locals (toMiniExportLocals specs))
  | .exportDecl s => .exportDecl (.decl (toMiniStmt s))

/-- The top level items. -/
def toMiniModuleItems {c m : Nat} : ModuleItems c m → List MiniModuleItem
  | .nil => []
  | .cons it r => toMiniModuleItem it :: toMiniModuleItems r

/-- The `MiniAST` program a `BrujinAST` one denotes.  The variables are
given their generated names. -/
def toMiniProgram (p : Program) : MiniProgram := ⟨toMiniModuleItems p.items⟩

/-! ## Printing -/

/-- Print a program in the canonical style of `MiniASTPrinter`. -/
def printProgram (p : Program) : String :=
  MiniAST.printProgram (toMiniProgram p)

/-- Print a block of statements, as the body of a function would be printed. -/
def printBlock {c m : Nat} (b : Block c m) : String :=
  MiniAST.printProgram ⟨(toMiniBlock b).map .stmt⟩

/-- Print an expression. -/
def printExpr {c m : Nat} (e : Expr c m) : String :=
  MiniAST.printExpr (toMiniExpr e)

/-! ## Equality

Two trees are compared through their canonical renderings; since the names
are generated from the levels of the binders, this is equality up to the
names, i.e. α-equivalence. -/

instance {c m : Nat} : BEq (Expr c m) := ⟨fun a b => toMiniExpr a == toMiniExpr b⟩
instance {c m : Nat} : BEq (Block c m) := ⟨fun a b => toMiniBlock a == toMiniBlock b⟩
instance {c m dc dm : Nat} : BEq (Stmt c m dc dm) := ⟨fun a b => toMiniStmt a == toMiniStmt b⟩
instance : BEq Program := ⟨fun a b => toMiniProgram a == toMiniProgram b⟩

instance {c m : Nat} : ToString (Expr c m) := ⟨printExpr⟩
instance : ToString Program := ⟨printProgram⟩

end Language.JavaScript.BrujinAST
