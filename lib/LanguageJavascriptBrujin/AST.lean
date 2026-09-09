/-
A *scope safe* JavaScript AST: `BrujinAST`.

`MiniAST` is a deterministic tree, but it still talks about variables by
*name*, so it can describe a program that mentions a variable which is not
bound anywhere.  `BrujinAST` cannot: every tree is indexed by the scope it
lives in, a variable is a de Bruijn *index* into that scope, and the only
way to mention something that the tree does not bind is the explicit escape
hatch `Expr.unsafeGlobal`.

**Two scopes.**  JavaScript has two kinds of binding, and they behave
differently, so the tree is parametrised by *two* de Bruijn scopes:

* `c`, the number of **const** bindings in scope — `const x = ...`,
  `for (const x of ...)`, a `function f` declaration, a `class C`
  declaration, and the names bound by an `import`.  A const binding cannot
  be assigned to, which is why `Target` (the left hand side of an
  assignment or of `++`) has no constructor for it;
* `m`, the number of **mutable** bindings in scope — `let`/`var`, a
  function or arrow parameter (a parameter is a mutable cell), the binder of
  a `catch` clause, and `for (let x of ...)`.

So `Expr c m` is an expression that may use `c` const and `m` mutable
variables, `Expr.constVar (i : Fin c)` and `Expr.mutVar (i : Fin m)` being
the two ways of naming one.

**Index convention.**  Index `0` always denotes the *most recently* bound
variable of its kind, and a scope grows on the left: entering one new const
binding takes `Expr c m` to `Expr (c + 1) m`, under which the new variable
is `constVar 0` and what used to be `constVar i` is `constVar (i + 1)`.
Where several variables are bound at once (the parameters of a function,
the names of an import) they are bound left to right, so the *last*
parameter has index `0`.

**Statements bind.**  A statement can extend the scope of the statements
that follow it, so a block is a telescope rather than a list: `Stmt c m dc
dm` is a statement in scope `(c, m)` which adds `dc` const and `dm` mutable
bindings, and `Block.cons` puts the rest of the block in scope
`(c + dc, m + dm)`.

**Lexical scoping.**  The body of a function, of a loop or of a block still
sees the enclosing scope: the body of a function of arity `k` in scope
`(c, m)` is a `Block c (m + k)`.

**What it deliberately cannot express.**  Destructuring patterns and
default parameter values (a binder is a plain variable), `with` (its scope
is dynamic), object literal shorthand (`{x}` — the name is gone, so it is
written as a key/value pair), a `catch` clause without a binder or with the
non standard `if` guard, and `var` hoisting: `var` is treated as
`let`, and a name used before the statement that binds it is not in scope,
so it has to be written as `unsafeGlobal`.

Because the lists inside the tree are indexed by the scope, they cannot be
`List (Expr c m)`: Lean rejects a nested inductive whose parameters mention
a local variable.  Each of them is therefore its own inductive (`Exprs`,
`Properties`, …) with `toList`/`ofList` functions next to it; `OptExpr` and
`OptBlock` play the part of `Option` for the same reason.
-/
import LanguageJavascriptMini.AST

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST

/-! ## Imports

An `import` binds a number of const variables that depends on its clause,
so the clause is described by an ordinary structure and the number of names
it binds by a function on it. -/

/-- `import def, * as ns, { a, b as c } from "mod";`, with the *local* names
removed: they are de Bruijn binders.  Only the names of the imported
bindings, which belong to the other module, are still strings. -/
structure ImportClause where
  /-- The module the names come from. -/
  mod : NEString
  /-- Whether there is a default import, `import def from "mod"`. -/
  hasDefault : Bool
  /-- Whether there is a namespace import, `import * as ns from "mod"`. -/
  hasNamespace : Bool
  /-- The names of the named imports, `import { a, b as c } from "mod"`;
  the entry is the name `a` respectively `b` exported by the module. -/
  named : List NEString
  /-- An import has to bind something. -/
  binds : hasDefault = true ∨ hasNamespace = true ∨ named ≠ []
deriving DecidableEq

namespace ImportClause

instance : Inhabited ImportClause :=
  ⟨{ mod := default, hasDefault := true, hasNamespace := false, named := [],
     binds := Or.inl rfl }⟩

/-- The number of const bindings the import introduces. -/
def count (i : ImportClause) : Nat :=
  (if i.hasDefault then 1 else 0) + (if i.hasNamespace then 1 else 0) + i.named.length

/-- Build an import clause, checking that it binds a name. -/
def mk? (mod : NEString) (hasDefault hasNamespace : Bool) (named : List NEString) :
    Option ImportClause :=
  if h : hasDefault = true ∨ hasNamespace = true ∨ named ≠ [] then
    some ⟨mod, hasDefault, hasNamespace, named, h⟩
  else
    none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (mod : NEString) (hasDefault hasNamespace : Bool) (named : List NEString) :
    ImportClause :=
  (mk? mod hasDefault hasNamespace named).getD default

end ImportClause

/-! ## The syntax tree -/

mutual

/-- Expressions in a scope of `c` const and `m` mutable variables. -/
inductive Expr : Nat → Nat → Type where
  /-- A mutable variable: a `let`/`var`, a parameter or a `catch` binder.
  Index `0` is the most recently bound one. -/
  | mutVar {c m : Nat} (i : Fin m) : Expr c m
  /-- A const variable: a `const`, a `function`/`class` declaration or an
  imported name.  Index `0` is the most recently bound one. -/
  | constVar {c m : Nat} (i : Fin c) : Expr c m
  /-- The escape hatch: a name that the tree does not bind — a global, or a
  function declared elsewhere in the file. -/
  | unsafeGlobal {c m : Nat} (name : NEString) : Expr c m
  /-- A numeric literal, in its normalised spelling. -/
  | number {c m : Nat} (raw : NEString) : Expr c m
  /-- A string literal, holding the characters it denotes. -/
  | string {c m : Nat} (value : String) : Expr c m
  /-- A regular expression literal, including the slashes and the flags. -/
  | regex {c m : Nat} (raw : NEString) : Expr c m
  | null {c m : Nat} : Expr c m
  | true_ {c m : Nat} : Expr c m
  | false_ {c m : Nat} : Expr c m
  | this {c m : Nat} : Expr c m
  /-- `[a, , b]` -/
  | array {c m : Nat} (elements : ArrayElems c m) : Expr c m
  /-- `{ a: 1 }` -/
  | object {c m : Nat} (properties : Properties c m) : Expr c m
  /-- `target op rhs`, for an assignment operator `op`.  The target cannot
  be a const variable. -/
  | assign {c m : Nat} (target : Target c m) (op : MiniAssignOp) (rhs : Expr c m) : Expr c m
  /-- `x++`, `++x`, `x--`, `--x`; `isPrefix` selects the prefix form. -/
  | update {c m : Nat} (target : Target c m) (op : MiniPostfixOp) (isPrefix : Bool) : Expr c m
  | await {c m : Nat} (expr : Expr c m) : Expr c m
  /-- `callee(args)` -/
  | call {c m : Nat} (callee : Expr c m) (args : Exprs c m) : Expr c m
  /-- `new callee(args)` -/
  | new {c m : Nat} (callee : Expr c m) (args : Exprs c m) : Expr c m
  /-- `obj.name` -/
  | dot {c m : Nat} (obj : Expr c m) (name : NEString) : Expr c m
  /-- `obj[idx]` -/
  | index {c m : Nat} (obj : Expr c m) (idx : Expr c m) : Expr c m
  /-- An anonymous class expression. -/
  | classAnon {c m : Nat} (heritage : OptExpr c m) (body : ClassElems c m) : Expr c m
  /-- A named class expression; the name is a const binding visible in the
  body of the class, and is `constVar 0` there. -/
  | classSelf {c m : Nat} (heritage : OptExpr c m) (body : ClassElems (c + 1) m) : Expr c m
  /-- The comma operator, `lhs, rhs`. -/
  | seq {c m : Nat} (lhs : Expr c m) (rhs : Expr c m) : Expr c m
  | binary {c m : Nat} (lhs : Expr c m) (op : MiniBinOp) (rhs : Expr c m) : Expr c m
  /-- `cond ? thenE : elseE` -/
  | ternary {c m : Nat} (cond : Expr c m) (thenE : Expr c m) (elseE : Expr c m) : Expr c m
  /-- `(p₁, …, pₖ) => body`; the parameters are mutable bindings, the last
  one being `mutVar 0`. -/
  | arrow {c m : Nat} (arity : Nat) (body : ArrowBody c (m + arity)) : Expr c m
  /-- An anonymous function expression. -/
  | func {c m : Nat} (isAsync : Bool) (isGenerator : Bool) (arity : Nat)
      (body : Block c (m + arity)) : Expr c m
  /-- A named function expression; the name is a const binding visible in
  the body, where it is `constVar 0`. -/
  | funcSelf {c m : Nat} (isAsync : Bool) (isGenerator : Bool) (arity : Nat)
      (body : Block (c + 1) (m + arity)) : Expr c m
  /-- `...expr` -/
  | spread {c m : Nat} (expr : Expr c m) : Expr c m
  /-- A template literal: an optional tag, the text before the first
  substitution, and one part per substitution. -/
  | template {c m : Nat} (tag : OptExpr c m) (head : String) (parts : TemplateParts c m) :
      Expr c m
  | unary {c m : Nat} (op : MiniUnaryOp) (expr : Expr c m) : Expr c m
  /-- `yield expr` -/
  | yield {c m : Nat} (expr : OptExpr c m) : Expr c m
  /-- `yield* expr` -/
  | yieldFrom {c m : Nat} (expr : Expr c m) : Expr c m

/-- The left hand side of an assignment or of an increment.  A const
variable is not one of the possibilities — that is what `const` means. -/
inductive Target : Nat → Nat → Type where
  /-- A mutable variable. -/
  | mut {c m : Nat} (i : Fin m) : Target c m
  /-- An unbound name; the escape hatch, as for expressions. -/
  | unsafeGlobal {c m : Nat} (name : NEString) : Target c m
  /-- `obj.name = ...` -/
  | dot {c m : Nat} (obj : Expr c m) (name : NEString) : Target c m
  /-- `obj[idx] = ...` -/
  | index {c m : Nat} (obj : Expr c m) (idx : Expr c m) : Target c m

/-- A list of expressions in one scope. -/
inductive Exprs : Nat → Nat → Type where
  | nil {c m : Nat} : Exprs c m
  | cons {c m : Nat} (hd : Expr c m) (tl : Exprs c m) : Exprs c m

/-- An optional expression; `Option` cannot be used, see the module note. -/
inductive OptExpr : Nat → Nat → Type where
  | none {c m : Nat} : OptExpr c m
  | some {c m : Nat} (expr : Expr c m) : OptExpr c m

/-- An element of an array literal; `hole` is an elision, as in `[1, , 2]`. -/
inductive ArrayElem : Nat → Nat → Type where
  | elem {c m : Nat} (expr : Expr c m) : ArrayElem c m
  | hole {c m : Nat} : ArrayElem c m

/-- The elements of an array literal. -/
inductive ArrayElems : Nat → Nat → Type where
  | nil {c m : Nat} : ArrayElems c m
  | cons {c m : Nat} (hd : ArrayElem c m) (tl : ArrayElems c m) : ArrayElems c m

/-- The `${...}` substitution of a template literal together with the text
following it. -/
inductive TemplatePart : Nat → Nat → Type where
  | mk {c m : Nat} (expr : Expr c m) (suffix : String) : TemplatePart c m

/-- The substitutions of a template literal. -/
inductive TemplateParts : Nat → Nat → Type where
  | nil {c m : Nat} : TemplateParts c m
  | cons {c m : Nat} (hd : TemplatePart c m) (tl : TemplateParts c m) : TemplateParts c m

/-- The name of a property or a method. -/
inductive PropName : Nat → Nat → Type where
  | ident {c m : Nat} (name : NEString) : PropName c m
  /-- A quoted name, holding the characters it denotes. -/
  | string {c m : Nat} (value : String) : PropName c m
  | number {c m : Nat} (raw : NEString) : PropName c m
  /-- `[expr]` -/
  | computed {c m : Nat} (expr : Expr c m) : PropName c m

/-- A member of an object literal.  There is no shorthand: `{x}` is a
key/value pair whose value is the variable. -/
inductive Property : Nat → Nat → Type where
  | keyValue {c m : Nat} (key : PropName c m) (value : Expr c m) : Property c m
  | method {c m : Nat} (kind : MiniMethodKind) (key : PropName c m) (arity : Nat)
      (body : Block c (m + arity)) : Property c m

/-- The members of an object literal. -/
inductive Properties : Nat → Nat → Type where
  | nil {c m : Nat} : Properties c m
  | cons {c m : Nat} (hd : Property c m) (tl : Properties c m) : Properties c m

/-- A member of a class body. -/
inductive ClassElem : Nat → Nat → Type where
  | mk {c m : Nat} (isStatic : Bool) (kind : MiniMethodKind) (key : PropName c m)
      (arity : Nat) (body : Block c (m + arity)) : ClassElem c m

/-- The members of a class body. -/
inductive ClassElems : Nat → Nat → Type where
  | nil {c m : Nat} : ClassElems c m
  | cons {c m : Nat} (hd : ClassElem c m) (tl : ClassElems c m) : ClassElems c m

/-- The body of an arrow function. -/
inductive ArrowBody : Nat → Nat → Type where
  | expr {c m : Nat} (expr : Expr c m) : ArrowBody c m
  | block {c m : Nat} (body : Block c m) : ArrowBody c m

/-- The first clause of a `for (;;)` statement; it may bind a variable,
which is in scope in the condition, the step and the body. -/
inductive ForInit : Nat → Nat → Nat → Nat → Type where
  | none {c m : Nat} : ForInit c m 0 0
  | expr {c m : Nat} (expr : Expr c m) : ForInit c m 0 0
  /-- `for (const x = e; ...)` -/
  | constDecl {c m : Nat} (init : Expr c m) : ForInit c m 1 0
  /-- `for (let x = e; ...)` -/
  | letDecl {c m : Nat} (init : OptExpr c m) : ForInit c m 0 1

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement. -/
inductive ForHead : Nat → Nat → Nat → Nat → Type where
  /-- `for (x of ...)`, assigning to something that already exists. -/
  | target {c m : Nat} (target : Target c m) : ForHead c m 0 0
  /-- `for (const x of ...)` -/
  | constBind {c m : Nat} : ForHead c m 1 0
  /-- `for (let x of ...)` -/
  | letBind {c m : Nat} : ForHead c m 0 1

/-- One `case`/`default` of a `switch`. -/
inductive SwitchCase : Nat → Nat → Type where
  | case {c m : Nat} (test : Expr c m) (body : Block c m) : SwitchCase c m
  | default {c m : Nat} (body : Block c m) : SwitchCase c m

/-- The cases of a `switch`. -/
inductive SwitchCases : Nat → Nat → Type where
  | nil {c m : Nat} : SwitchCases c m
  | cons {c m : Nat} (hd : SwitchCase c m) (tl : SwitchCases c m) : SwitchCases c m

/-- An optional block. -/
inductive OptBlock : Nat → Nat → Type where
  | none {c m : Nat} : OptBlock c m
  | some {c m : Nat} (body : Block c m) : OptBlock c m

/-- What follows the block of a `try`.  A `try` needs a `catch` or a
`finally`, which this makes structurally impossible to violate. -/
inductive TryTail : Nat → Nat → Type where
  /-- `catch (e) { ... }`; the binder is a mutable variable, `mutVar 0` in
  the body of the clause. -/
  | catch_ {c m : Nat} (body : Block c (m + 1)) (fin : OptBlock c m) : TryTail c m
  /-- No `catch` clause, only a `finally`. -/
  | finallyOnly {c m : Nat} (body : Block c m) : TryTail c m

/-- A statement in scope `(c, m)` that binds `dc` further const and `dm`
further mutable variables for the statements that follow it. -/
inductive Stmt : Nat → Nat → Nat → Nat → Type where
  /-- An expression statement. -/
  | expr {c m : Nat} (expr : Expr c m) : Stmt c m 0 0
  /-- `const x = init;` -/
  | constDecl {c m : Nat} (init : Expr c m) : Stmt c m 1 0
  /-- `let x = init;` (`var` is converted to this). -/
  | letDecl {c m : Nat} (init : OptExpr c m) : Stmt c m 0 1
  /-- A nested block; what it binds does not escape it. -/
  | block {c m : Nat} (body : Block c m) : Stmt c m 0 0
  | if_ {c m : Nat} (cond : Expr c m) (thenB : Block c m) (elseB : OptBlock c m) : Stmt c m 0 0
  | while_ {c m : Nat} (cond : Expr c m) (body : Block c m) : Stmt c m 0 0
  | doWhile {c m : Nat} (body : Block c m) (cond : Expr c m) : Stmt c m 0 0
  | for_ {c m dc dm : Nat} (init : ForInit c m dc dm) (cond : OptExpr (c + dc) (m + dm))
      (step : OptExpr (c + dc) (m + dm)) (body : Block (c + dc) (m + dm)) : Stmt c m 0 0
  | forIn {c m dc dm : Nat} (head : ForHead c m dc dm) (obj : Expr c m)
      (body : Block (c + dc) (m + dm)) : Stmt c m 0 0
  | forOf {c m dc dm : Nat} (head : ForHead c m dc dm) (obj : Expr c m)
      (body : Block (c + dc) (m + dm)) : Stmt c m 0 0
  /-- `function f(...) { ... }`; `f` is a const binding, and it is in scope
  in the body of the function, where it is `constVar 0`. -/
  | funcDecl {c m : Nat} (isAsync : Bool) (isGenerator : Bool) (arity : Nat)
      (body : Block (c + 1) (m + arity)) : Stmt c m 1 0
  /-- `class C { ... }`; `C` is a const binding, in scope in the body. -/
  | classDecl {c m : Nat} (heritage : OptExpr c m) (body : ClassElems (c + 1) m) : Stmt c m 1 0
  | return_ {c m : Nat} (expr : OptExpr c m) : Stmt c m 0 0
  | throw {c m : Nat} (expr : Expr c m) : Stmt c m 0 0
  | break_ {c m : Nat} (label : Option NEString) : Stmt c m 0 0
  | continue_ {c m : Nat} (label : Option NEString) : Stmt c m 0 0
  /-- A labelled statement.  The statement carrying the label may not bind
  anything, which is exactly what a label is used with. -/
  | labelled {c m : Nat} (label : NEString) (stmt : Stmt c m 0 0) : Stmt c m 0 0
  | switch {c m : Nat} (disc : Expr c m) (cases : SwitchCases c m) : Stmt c m 0 0
  | try_ {c m : Nat} (body : Block c m) (tail : TryTail c m) : Stmt c m 0 0

/-- A block: a telescope of statements, each of which may extend the scope
of the ones that follow it. -/
inductive Block : Nat → Nat → Type where
  | nil {c m : Nat} : Block c m
  | cons {c m dc dm : Nat} (hd : Stmt c m dc dm) (tl : Block (c + dc) (m + dm)) : Block c m

/-- One entry of an `export { a as b }` clause: which local variable is
exported, and under which name. -/
inductive ExportLocal : Nat → Nat → Type where
  | const {c m : Nat} (i : Fin c) (exported : NEString) : ExportLocal c m
  | mut {c m : Nat} (i : Fin m) (exported : NEString) : ExportLocal c m

/-- The entries of an `export { ... }` clause. -/
inductive ExportLocals : Nat → Nat → Type where
  | nil {c m : Nat} : ExportLocals c m
  | cons {c m : Nat} (hd : ExportLocal c m) (tl : ExportLocals c m) : ExportLocals c m

/-- A top level item: a statement, or an `import`/`export` declaration.
Like a statement it may extend the scope of what follows it. -/
inductive ModuleItem : Nat → Nat → Nat → Nat → Type where
  | stmt {c m dc dm : Nat} (stmt : Stmt c m dc dm) : ModuleItem c m dc dm
  /-- `import "mod";`, which binds nothing. -/
  | importBare {c m : Nat} (mod : NEString) : ModuleItem c m 0 0
  /-- `import ... from "mod";`; the names it binds are const bindings, bound
  left to right, so the last of them is `constVar 0`. -/
  | importClause {c m : Nat} (clause : ImportClause) : ModuleItem c m clause.count 0
  /-- `export { a as b } from "mod";` -/
  | exportFrom {c m : Nat} (specs : List MiniSpecifier) (mod : NEString) : ModuleItem c m 0 0
  /-- `export { x as name };` -/
  | exportLocals {c m : Nat} (specs : ExportLocals c m) : ModuleItem c m 0 0
  /-- `export <declaration>` -/
  | exportDecl {c m dc dm : Nat} (stmt : Stmt c m dc dm) : ModuleItem c m dc dm

/-- The top level items of a program, as a telescope. -/
inductive ModuleItems : Nat → Nat → Type where
  | nil {c m : Nat} : ModuleItems c m
  | cons {c m dc dm : Nat} (hd : ModuleItem c m dc dm) (tl : ModuleItems (c + dc) (m + dm)) :
      ModuleItems c m

end

/-- A whole program: top level items in the empty scope. -/
structure Program where
  /-- The top level items. -/
  items : ModuleItems 0 0

/-! ## Default values -/

instance {c m : Nat} : Inhabited (Expr c m) := ⟨.null⟩
instance {c m : Nat} : Inhabited (Target c m) := ⟨.unsafeGlobal default⟩
instance {c m : Nat} : Inhabited (Exprs c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (OptExpr c m) := ⟨.none⟩
instance {c m : Nat} : Inhabited (ArrayElem c m) := ⟨.hole⟩
instance {c m : Nat} : Inhabited (ArrayElems c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (TemplatePart c m) := ⟨.mk default ""⟩
instance {c m : Nat} : Inhabited (TemplateParts c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (PropName c m) := ⟨.ident default⟩
instance {c m : Nat} : Inhabited (Property c m) := ⟨.keyValue default default⟩
instance {c m : Nat} : Inhabited (Properties c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (ClassElems c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (Block c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (OptBlock c m) := ⟨.none⟩
instance {c m : Nat} : Inhabited (ClassElem c m) := ⟨.mk false .normal default 0 .nil⟩
instance {c m : Nat} : Inhabited (ArrowBody c m) := ⟨.block .nil⟩
instance {c m : Nat} : Inhabited (ForInit c m 0 0) := ⟨.none⟩
instance {c m : Nat} : Inhabited (ForHead c m 0 0) := ⟨.target default⟩
instance {c m : Nat} : Inhabited (SwitchCase c m) := ⟨.default .nil⟩
instance {c m : Nat} : Inhabited (SwitchCases c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (TryTail c m) := ⟨.finallyOnly .nil⟩
instance {c m : Nat} : Inhabited (Stmt c m 0 0) := ⟨.expr default⟩
instance {c m : Nat} : Inhabited (ExportLocals c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (ModuleItem c m 0 0) := ⟨.stmt default⟩
instance {c m : Nat} : Inhabited (ModuleItems c m) := ⟨.nil⟩
instance : Inhabited Program := ⟨⟨.nil⟩⟩

/-! ## Lists -/

namespace Exprs
def toList {c m : Nat} : Exprs c m → List (Expr c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (Expr c m) → Exprs c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
@[simp] theorem toList_ofList {c m : Nat} (l : List (Expr c m)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, toList, ih]
end Exprs

namespace ArrayElems
def toList {c m : Nat} : ArrayElems c m → List (ArrayElem c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ArrayElem c m) → ArrayElems c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
@[simp] theorem toList_ofList {c m : Nat} (l : List (ArrayElem c m)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, toList, ih]
end ArrayElems

namespace TemplateParts
def toList {c m : Nat} : TemplateParts c m → List (TemplatePart c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (TemplatePart c m) → TemplateParts c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end TemplateParts

namespace Properties
def toList {c m : Nat} : Properties c m → List (Property c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (Property c m) → Properties c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end Properties

namespace ClassElems
def toList {c m : Nat} : ClassElems c m → List (ClassElem c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ClassElem c m) → ClassElems c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end ClassElems

namespace SwitchCases
def toList {c m : Nat} : SwitchCases c m → List (SwitchCase c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (SwitchCase c m) → SwitchCases c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end SwitchCases

namespace ExportLocals
def toList {c m : Nat} : ExportLocals c m → List (ExportLocal c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ExportLocal c m) → ExportLocals c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end ExportLocals

namespace OptExpr
def toOption {c m : Nat} : OptExpr c m → Option (Expr c m)
  | OptExpr.none => Option.none
  | OptExpr.some e => Option.some e
def ofOption {c m : Nat} : Option (Expr c m) → OptExpr c m
  | Option.none => OptExpr.none
  | Option.some e => OptExpr.some e
end OptExpr

namespace OptBlock
def toOption {c m : Nat} : OptBlock c m → Option (Block c m)
  | OptBlock.none => Option.none
  | OptBlock.some b => Option.some b
def ofOption {c m : Nat} : Option (Block c m) → OptBlock c m
  | Option.none => OptBlock.none
  | Option.some b => OptBlock.some b
end OptBlock

/-! ## Casting along an equality of scopes -/

def Expr.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m') (e : Expr c m) : Expr c' m' :=
  hc ▸ hm ▸ e

def OptExpr.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m') (e : OptExpr c m) : OptExpr c' m' :=
  hc ▸ hm ▸ e

def Block.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m') (b : Block c m) : Block c' m' :=
  hc ▸ hm ▸ b

def ModuleItems.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m') (b : ModuleItems c m) : ModuleItems c' m' :=
  hc ▸ hm ▸ b

/-! ## Names of the variables -/

def constLevel {c : Nat} (i : Fin c) : Nat := c - 1 - i.val
def mutLevel {m : Nat} (i : Fin m) : Nat := m - 1 - i.val

def constIndex? (c l : Nat) : Option (Fin c) :=
  if h : l < c then some ⟨c - 1 - l, by omega⟩ else none

def mutIndex? (m l : Nat) : Option (Fin m) :=
  if h : l < m then some ⟨m - 1 - l, by omega⟩ else none

@[simp] theorem constIndex?_constLevel {c : Nat} (i : Fin c) :
    constIndex? c (constLevel i) = some i := by
  have h := i.isLt
  simp only [constIndex?, constLevel]
  rw [dif_pos (by omega)]
  exact congrArg some (Fin.ext (by simp; omega))

@[simp] theorem mutIndex?_mutLevel {m : Nat} (i : Fin m) :
    mutIndex? m (mutLevel i) = some i := by
  have h := i.isLt
  simp only [mutIndex?, mutLevel]
  rw [dif_pos (by omega)]
  exact congrArg some (Fin.ext (by simp; omega))

def constName (l : Nat) : NEString := ⟨"_c" ++ toString l, by simp⟩
def mutName (l : Nat) : NEString := ⟨"_m" ++ toString l, by simp⟩

/-! ### Index based names -/

def idxConstName (i : Nat) : NEString := ⟨"c#" ++ toString i, by simp⟩
def idxMutName (i : Nat) : NEString := ⟨"l#" ++ toString i, by simp⟩
def idxConstIdent (i : Nat) : NEString := ⟨"_brujinConst_" ++ toString i, by simp⟩
def idxMutIdent (i : Nat) : NEString := ⟨"_brujinMut_" ++ toString i, by simp⟩

def idxIdent? (n : NEString) : Option (Bool × Nat) :=
  let s := n.val
  if s.startsWith "_brujinConst_" then
    ((s.drop "_brujinConst_".length).toNat?).map fun i => (true, i)
  else if s.startsWith "_brujinMut_" then
    ((s.drop "_brujinMut_".length).toNat?).map fun i => (false, i)
  else none

end Language.JavaScript.BrujinAST
