/-
A *scope safe* JavaScript AST: `BrujinAST`.

`MiniAST` is a deterministic tree, but it still talks about variables by
*name*, so it can describe a program that mentions a variable which is not
bound anywhere.  `BrujinAST` cannot: every tree is indexed by the scope it
lives in, a variable is a de Bruijn *index* into that scope, and the only
way to mention something that the tree does not bind is the explicit escape
hatch `Expr.unsafeExt` — an *extension*, which for the usual instantiation
of the tree is an unknown global, `Expr.unsafeGlobal`.

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
sees the enclosing scope: the body of a function of `k` parameters in scope
`(c, m)` is a `Block exprExt targetExt c (m + k)`.

**Parameters.**  A function, a method or an arrow carries its `arity`, the
number of ordinary parameters, and a flag `hasRest` saying whether a rest
parameter `...xs` follows them.  The scope of the body therefore grows by
`arity + hasRest.toNat`, the rest parameter being the last binder and so
`mutVar 0`.  A rest parameter can only be written where JavaScript allows
one — last — because that is the only place the type can put it.

**The extensions.**  The tree takes two parameters, `exprExt` and
`targetExt`, each a family `Nat → Nat → Type` indexed by the scope: the
*extensions*, what the user wants a tree to be able to mention besides
what the tree describes itself.  `Expr exprExt targetExt c m` is an
expression in the scope `(c, m)` which may use an `exprExt c m` through
`Expr.unsafeExt`, and a `Target` may use a `targetExt c m` the same way.
Everything downstream — the conversion to `MiniAST`, the printer, the
optimizer — is generic in the two, the printer taking the two functions
`printUnsafeExprExt` and `printUnsafeTargetExt` which say how an extension
is written.

**The globals.**  `GlobalExt g`, the extension `{n : NEString // n ∈ g}`,
recovers the escape hatch the tree used to have built in: a name that the
tree does not bind, drawn from the set `g`.  `Global.Expr c m g` is the
tree instantiated that way and `Expr.unsafeGlobal name mem` builds the
escape hatch, carrying `mem : name ∈ g`, so a name that is not in `g`
cannot be written down at all.

The set is *shared* by every constructor rather than accumulated at each
node, so it is an upper bound: a subtree of `Global.Expr c m g` may well
mention fewer globals than `g`.  That is what makes it usable — the index
of a subtree is the index of the tree, so nothing has to be reassociated
when two subtrees are put together.

Every name the tree does not bind goes in `g`, whatever it is: `Math`,
`JSON` and `Array` are recorded there exactly like `console`, `Date` or
`fetch`.  The type therefore lists every free name of the tree.

`Program` and `ScopedExpr` pair a tree with the set it was built against,
so that a whole program remains an ordinary type: two programs which name
different globals still have the same type.  `OfMini` computes that set,
exactly, by converting twice — see `ConvM` there.

**Private names.**  `#x` is not a variable: it is resolved against the
class the expression occurs in, not against a scope, so a private name is a
plain `NEString` and is *not* recorded in `g`.

**`super` and `new.target`.**  `super.x`, `super[i]` and `super(...)` are
nodes of their own (`Expr.superDot`, `Expr.superIndex`, `Expr.superCall`,
and the first two also as a `Target`): the home object of the method the
expression occurs in is not a variable, so it is not resolved against a
scope and not recorded in `g`.  Those three forms are the only ones
JavaScript allows, so there is no node for `super` on its own.
`new.target` is a node too.

**Modern syntax.**  An optional chain is one node — a base expression and
the links written after it, each saying whether it is written `?.` — so
`a?.b.c` and `(a?.b).c` are different trees; `??` and `??=` are the
`coalesce` operators; a class body holds methods, fields (static or not,
each with its decorators) and static initialisation blocks, and a class
itself carries its decorators; `import.meta` and the dynamic
`import(specifier, options)` are nodes of their own; an object literal
may spread another object; `using x = e;` and `await using x = e;` bind a
const variable (what they bind cannot be assigned to); a label may carry a
statement that binds, which is what a labelled function declaration needs;
and a module item may be `export * [as ns] from "m"`,
`export default <expression>` or an `import`/`export ... from` carrying
import attributes.

**What it deliberately cannot express.**  Destructuring patterns and
default parameter values (a binder is a plain variable, though a rest
parameter is one and is recorded as such), `with` (its scope
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

**What it depends on.**  This module does not import another tree.  The
leaf types it shares with the deterministic tree — the operators,
`MethodKind`, `Specifier` and `ImportAttr` — come from
`LanguageJavascript.Common`, and the refined ones — `NEString`, `NEList`,
`JSNumber`, `RegExpLit` — from `LanguageJavascript.Types`; both are in
`Language.JavaScript`, the parent of this namespace, so they are in scope
without an `open`.  Only `OfMini` and `ToMini`, which convert between the
two trees, mention `MiniAST`.
-/
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Data.Finset.Insert
-- import Mathlib.Data.Finset.Union
import LanguageJavascript.Common

namespace Language.JavaScript.BrujinAST

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
  /-- The import attributes, `with { type: "json" }`. -/
  attrs : List ImportAttr := []
  /-- An import has to bind something. -/
  binds : hasDefault = true ∨ hasNamespace = true ∨ named ≠ []
deriving DecidableEq

namespace ImportClause

instance : Inhabited ImportClause :=
  ⟨{ mod := default, hasDefault := true, hasNamespace := false, named := [], attrs := [],
     binds := Or.inl rfl }⟩

/-- The number of const bindings the import introduces. -/
def count (i : ImportClause) : Nat :=
  (if i.hasDefault then 1 else 0) + (if i.hasNamespace then 1 else 0) + i.named.length

/-- Build an import clause, checking that it binds a name. -/
def mk? (mod : NEString) (hasDefault hasNamespace : Bool) (named : List NEString)
    (attrs : List ImportAttr := []) : Option ImportClause :=
  if h : hasDefault = true ∨ hasNamespace = true ∨ named ≠ [] then
    some ⟨mod, hasDefault, hasNamespace, named, attrs, h⟩
  else
    none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (mod : NEString) (hasDefault hasNamespace : Bool) (named : List NEString)
    (attrs : List ImportAttr := []) : ImportClause :=
  (mk? mod hasDefault hasNamespace named attrs).getD default

end ImportClause

/-! ## Parameters

A function, a method or an arrow does not name its parameters — they are de
Bruijn binders, `mutVar (arity - 1) … mutVar 0` in the body.  What it does
record is `arity`, how many ordinary parameters there are, and `hasRest`,
whether a rest parameter `...xs` follows them; the body then lives in a
scope `arity + hasRest.toNat` larger, the rest parameter being the last
binder.  `paramCount` is that total. -/

/-- The number of binders `arity` ordinary parameters followed by an
optional rest parameter introduce. -/
def paramCount (arity : Nat) (hasRest : Bool) : Nat := arity + hasRest.toNat

/-! ## Extensions

The tree is parametrised by two families of types, `exprExt c m` and
`targetExt c m`, the *extensions*: whatever the user wants a tree to be
able to mention besides what the tree itself describes.  `Expr.unsafeExt`
and `Target.unsafeExt` are the only ways to use one, and because an
extension is indexed by the scope `(c, m)` it may itself refer to the
variables in scope.

`GlobalExt g` is the extension this file used to have built in: an unknown
global, a name that the tree does not bind, drawn from a fixed set `g`.  A
tree of type `Expr (GlobalExt g) (GlobalExt g) c m` therefore lists every
unknown name it may mention in its type, exactly as before; the
abbreviations in the `Global` namespace below name those instantiations,
and `Expr.unsafeGlobal` / `Target.unsafeGlobal` build one.

`NoExt` is the other end: a tree with no extension at all, which mentions
nothing it does not bind. -/

/-- The extension of a tree whose escape hatch is an unknown global drawn
from `g`: a name together with the proof that it is one of `g`. -/
abbrev GlobalExt (g : Finset NEString) : Nat → Nat → Type := fun _ _ => {n : NEString // n ∈ g}

/-- The empty extension: a tree with no escape hatch. -/
abbrev NoExt : Nat → Nat → Type := fun _ _ => Empty

/-- An extension which does not depend on the scope it lives in, and so can
be moved to any other scope.  `GlobalExt g` is one — a global is a name, and
a name means the same thing in every scope — and so is `NoExt`.  It is what
the transformations that change the scope of a tree (`Strengthen`, and
through it the optimizer) ask of an extension; an extension which does
mention the variables in scope cannot be one, and such a tree cannot be
strengthened or optimized. -/
class ExtInvariant (ext : Nat → Nat → Type) where
  /-- Move an extension to another scope. -/
  castScope : {c m c' m' : Nat} → ext c m → ext c' m'

instance globalExtInvariant {g : Finset NEString} : ExtInvariant (GlobalExt g) where
  castScope e := e

instance : ExtInvariant NoExt where
  castScope e := e.elim

/-! ## The syntax tree -/

mutual

/-- Expressions in a scope of `c` const and `m` mutable variables. -/
inductive Expr (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  /-- A mutable variable: a `let`/`var`, a parameter or a `catch` binder.
  Index `0` is the most recently bound one. -/
  | mutVar {c m : Nat} (i : Fin m) : Expr exprExt targetExt c m
  /-- A const variable: a `const`, a `function`/`class` declaration or an
  imported name.  Index `0` is the most recently bound one. -/
  | constVar {c m : Nat} (i : Fin c) : Expr exprExt targetExt c m
  /-- The escape hatch: an *extension*, anything the tree itself cannot
  describe.  What one is, is up to the user: instantiating `exprExt` with
  `GlobalExt g` gives back the previous escape hatch, a name the tree does
  not bind drawn from the set `g`. -/
  | unsafeExt {c m : Nat} (ext : exprExt c m) :
      Expr exprExt targetExt c m
  /-- A numeric literal, as the number it denotes. -/
  | number {c m : Nat} (value : JSNumber) : Expr exprExt targetExt c m
  /-- A string literal, holding the characters it denotes. -/
  | string {c m : Nat} (value : String) : Expr exprExt targetExt c m
  /-- A regular expression literal: its pattern and its flags. -/
  | regex {c m : Nat} (re : RegExpLit) : Expr exprExt targetExt c m
  | null {c m : Nat} : Expr exprExt targetExt c m
  | true_ {c m : Nat} : Expr exprExt targetExt c m
  | false_ {c m : Nat} : Expr exprExt targetExt c m
  | this {c m : Nat} : Expr exprExt targetExt c m
  /-- `super.name`.  The home object of the method the expression occurs
  in is not a variable, so `super` is a node of its own and is not
  recorded in `g`; and since `super` is only an expression as a member
  access or a call, there is no node for `super` on its own. -/
  | superDot {c m : Nat} (name : NEString) : Expr exprExt targetExt c m
  /-- `super[idx]` -/
  | superIndex {c m : Nat} (idx : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `super(args)`, the call to the constructor of the parent class. -/
  | superCall {c m : Nat} (args : Exprs exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `new.target` -/
  | newTarget {c m : Nat} : Expr exprExt targetExt c m
  /-- `[a, , b]` -/
  | array {c m : Nat} (elements : ArrayElems exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `{ a: 1 }` -/
  | object {c m : Nat} (properties : Properties exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `target op rhs`, for an assignment operator `op`.  The target cannot
  be a const variable. -/
  | assign {c m : Nat} (target : Target exprExt targetExt c m) (op : AssignOp) (rhs : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `x++`, `++x`, `x--`, `--x`; `isPrefix` selects the prefix form. -/
  | update {c m : Nat} (target : Target exprExt targetExt c m) (op : PostfixOp) (isPrefix : Bool) : Expr exprExt targetExt c m
  | await {c m : Nat} (expr : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `callee(args)` -/
  | call {c m : Nat} (callee : Expr exprExt targetExt c m) (args : Exprs exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `new callee(args)` -/
  | new {c m : Nat} (callee : Expr exprExt targetExt c m) (args : Exprs exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `obj.name` -/
  | dot {c m : Nat} (obj : Expr exprExt targetExt c m) (name : NEString) : Expr exprExt targetExt c m
  /-- `obj[idx]` -/
  | index {c m : Nat} (obj : Expr exprExt targetExt c m) (idx : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `obj.#name`, the access to a private class member.  A private name is
  not a variable: it is looked up in the class the expression occurs in, so
  it is a plain `NEString` and is not tracked in `g`. -/
  | privateDot {c m : Nat} (obj : Expr exprExt targetExt c m) (name : NEString) : Expr exprExt targetExt c m
  /-- A private name on its own, which only `#x in obj` allows. -/
  | privateName {c m : Nat} (name : NEString) : Expr exprExt targetExt c m
  /-- An optional chain, `a?.b`, `a?.[i]` or `f?.(x)`: a base expression
  followed by one or more links, written here as a first link and the rest.
  The whole chain is one node, so that `(a?.b).c`, which evaluates `.c`
  even when `a` is nullish, is a different tree from `a?.b.c`. -/
  | chain {c m : Nat} (base : Expr exprExt targetExt c m) (hd : ChainLink exprExt targetExt c m)
      (tl : ChainLinks exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `import.meta` -/
  | importMeta {c m : Nat} : Expr exprExt targetExt c m
  /-- A dynamic import, `import(specifier)` or `import(specifier, options)`. -/
  | importCall {c m : Nat} (specifier : Expr exprExt targetExt c m)
      (options : OptExpr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- An anonymous class expression. -/
  | classAnon {c m : Nat} (decorators : Exprs exprExt targetExt c m)
      (heritage : OptExpr exprExt targetExt c m) (body : ClassElems exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- A named class expression; the name is a const binding visible in the
  body of the class, and is `constVar 0` there.  The decorators are
  evaluated outside the class, so they do not see that name. -/
  | classSelf {c m : Nat} (decorators : Exprs exprExt targetExt c m)
      (heritage : OptExpr exprExt targetExt c m) (body : ClassElems exprExt targetExt (c + 1) m) : Expr exprExt targetExt c m
  /-- The comma operator, `lhs, rhs`. -/
  | seq {c m : Nat} (lhs : Expr exprExt targetExt c m) (rhs : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  | binary {c m : Nat} (lhs : Expr exprExt targetExt c m) (op : BinOp) (rhs : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `cond ? thenE : elseE` -/
  | ternary {c m : Nat} (cond : Expr exprExt targetExt c m) (thenE : Expr exprExt targetExt c m) (elseE : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `(p₁, …, pₙ) => body`; the parameters are mutable bindings, the last
  one being `mutVar 0`, and the rest parameter, if any, is that last one. -/
  | arrow {c m : Nat} (arity : Nat) (hasRest : Bool)
      (body : ArrowBody exprExt targetExt c (m + arity + hasRest.toNat)) : Expr exprExt targetExt c m
  /-- An anonymous function expression. -/
  | func {c m : Nat} (isAsync isGenerator hasRest : Bool)
      (arity : Nat) (body : Block exprExt targetExt c (m + arity + hasRest.toNat)) : Expr exprExt targetExt c m
  /-- A named function expression; the name is a const binding visible in
  the body, where it is `constVar 0`. -/
  | funcSelf {c m : Nat} (isAsync isGenerator hasRest : Bool)
      (arity : Nat) (body : Block exprExt targetExt (c + 1) (m + arity + hasRest.toNat)) : Expr exprExt targetExt c m
  /-- `...expr` -/
  | spread {c m : Nat} (expr : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- A template literal: an optional tag, the text before the first
  substitution, and one part per substitution. -/
  | template {c m : Nat} (tag : OptExpr exprExt targetExt c m) (head : String) (parts : TemplateParts exprExt targetExt c m) :
      Expr exprExt targetExt c m
  | unary {c m : Nat} (op : UnaryOp) (expr : Expr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `yield expr` -/
  | yield {c m : Nat} (expr : OptExpr exprExt targetExt c m) : Expr exprExt targetExt c m
  /-- `yield* expr` -/
  | yieldFrom {c m : Nat} (expr : Expr exprExt targetExt c m) : Expr exprExt targetExt c m

/-- The left hand side of an assignment or of an increment.  A const
variable is not one of the possibilities — that is what `const` means. -/
inductive Target (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  /-- A mutable variable. -/
  | mut {c m : Nat} (i : Fin m) : Target exprExt targetExt c m
  /-- An extension used as an assignment target; the escape hatch, as for
  expressions, but drawn from `targetExt`. -/
  | unsafeExt {c m : Nat} (ext : targetExt c m) :
      Target exprExt targetExt c m
  /-- `obj.name = ...` -/
  | dot {c m : Nat} (obj : Expr exprExt targetExt c m) (name : NEString) : Target exprExt targetExt c m
  /-- `obj.#name = ...`, an assignment to a private class member. -/
  | privateDot {c m : Nat} (obj : Expr exprExt targetExt c m) (name : NEString) : Target exprExt targetExt c m
  /-- `super.name = ...` -/
  | superDot {c m : Nat} (name : NEString) : Target exprExt targetExt c m
  /-- `super[idx] = ...` -/
  | superIndex {c m : Nat} (idx : Expr exprExt targetExt c m) : Target exprExt targetExt c m
  /-- `obj[idx] = ...` -/
  | index {c m : Nat} (obj : Expr exprExt targetExt c m) (idx : Expr exprExt targetExt c m) : Target exprExt targetExt c m

/-- One link of an optional chain: a member access or a call, `optional`
saying whether it is written with `?.`. -/
inductive ChainLink (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  /-- `.name` or `?.name` -/
  | dot {c m : Nat} (optional : Bool) (name : NEString) : ChainLink exprExt targetExt c m
  /-- `.#name` or `?.#name` -/
  | privateDot {c m : Nat} (optional : Bool) (name : NEString) :
      ChainLink exprExt targetExt c m
  /-- `[idx]` or `?.[idx]` -/
  | index {c m : Nat} (optional : Bool) (idx : Expr exprExt targetExt c m) : ChainLink exprExt targetExt c m
  /-- `(args)` or `?.(args)` -/
  | call {c m : Nat} (optional : Bool) (args : Exprs exprExt targetExt c m) : ChainLink exprExt targetExt c m

/-- The links of an optional chain after the first one. -/
inductive ChainLinks (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : ChainLinks exprExt targetExt c m
  | cons {c m : Nat} (hd : ChainLink exprExt targetExt c m) (tl : ChainLinks exprExt targetExt c m) :
      ChainLinks exprExt targetExt c m

/-- A list of expressions in one scope. -/
inductive Exprs (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : Exprs exprExt targetExt c m
  | cons {c m : Nat} (hd : Expr exprExt targetExt c m) (tl : Exprs exprExt targetExt c m) : Exprs exprExt targetExt c m

/-- An optional expression; `Option` cannot be used, see the module note. -/
inductive OptExpr (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | none {c m : Nat} : OptExpr exprExt targetExt c m
  | some {c m : Nat} (expr : Expr exprExt targetExt c m) : OptExpr exprExt targetExt c m

/-- An element of an array literal; `hole` is an elision, as in `[1, , 2]`. -/
inductive ArrayElem (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | elem {c m : Nat} (expr : Expr exprExt targetExt c m) : ArrayElem exprExt targetExt c m
  | hole {c m : Nat} : ArrayElem exprExt targetExt c m

/-- The elements of an array literal. -/
inductive ArrayElems (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : ArrayElems exprExt targetExt c m
  | cons {c m : Nat} (hd : ArrayElem exprExt targetExt c m) (tl : ArrayElems exprExt targetExt c m) : ArrayElems exprExt targetExt c m

/-- The `${...}` substitution of a template literal together with the text
following it. -/
inductive TemplatePart (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | mk {c m : Nat} (expr : Expr exprExt targetExt c m) (suffix : String) : TemplatePart exprExt targetExt c m

/-- The substitutions of a template literal. -/
inductive TemplateParts (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : TemplateParts exprExt targetExt c m
  | cons {c m : Nat} (hd : TemplatePart exprExt targetExt c m) (tl : TemplateParts exprExt targetExt c m) : TemplateParts exprExt targetExt c m

/-- The name of a property or a method. -/
inductive PropName (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | ident {c m : Nat} (name : NEString) : PropName exprExt targetExt c m
  /-- A private name, `#x`, without its `#`; only a class member has one. -/
  | private_ {c m : Nat} (name : NEString) : PropName exprExt targetExt c m
  /-- A quoted name, holding the characters it denotes. -/
  | string {c m : Nat} (value : String) : PropName exprExt targetExt c m
  /-- A numeric name, as the number it denotes. -/
  | number {c m : Nat} (value : JSNumber) : PropName exprExt targetExt c m
  /-- `[expr]` -/
  | computed {c m : Nat} (expr : Expr exprExt targetExt c m) : PropName exprExt targetExt c m

/-- A member of an object literal.  There is no shorthand: `{x}` is a
key/value pair whose value is the variable. -/
inductive Property (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | keyValue {c m : Nat} (key : PropName exprExt targetExt c m) (value : Expr exprExt targetExt c m) : Property exprExt targetExt c m
  /-- `{ ...rest }`, which copies the properties of another object. -/
  | spread {c m : Nat} (expr : Expr exprExt targetExt c m) : Property exprExt targetExt c m
  | method {c m : Nat} (kind : MethodKind) (key : PropName exprExt targetExt c m)
      (arity : Nat) (hasRest : Bool) (body : Block exprExt targetExt c (m + arity + hasRest.toNat)) :
      Property exprExt targetExt c m

/-- The members of an object literal. -/
inductive Properties (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : Properties exprExt targetExt c m
  | cons {c m : Nat} (hd : Property exprExt targetExt c m) (tl : Properties exprExt targetExt c m) : Properties exprExt targetExt c m

/-- A member of a class body: a method, a field or a static block. -/
inductive ClassElem (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  /-- A method, a generator, a getter or a setter. -/
  | method {c m : Nat} (decorators : Exprs exprExt targetExt c m) (isStatic : Bool)
      (kind : MethodKind) (key : PropName exprExt targetExt c m) (arity : Nat) (hasRest : Bool)
      (body : Block exprExt targetExt c (m + arity + hasRest.toNat)) : ClassElem exprExt targetExt c m
  /-- A field, `x = 1;`, `#x;` or `static x = 1;`. -/
  | field {c m : Nat} (decorators : Exprs exprExt targetExt c m) (isStatic : Bool)
      (key : PropName exprExt targetExt c m) (init : OptExpr exprExt targetExt c m) : ClassElem exprExt targetExt c m
  /-- A static initialisation block, `static { ... }`. -/
  | staticBlock {c m : Nat} (body : Block exprExt targetExt c m) : ClassElem exprExt targetExt c m

/-- The members of a class body. -/
inductive ClassElems (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : ClassElems exprExt targetExt c m
  | cons {c m : Nat} (hd : ClassElem exprExt targetExt c m) (tl : ClassElems exprExt targetExt c m) : ClassElems exprExt targetExt c m

/-- The body of an arrow function. -/
inductive ArrowBody (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | expr {c m : Nat} (expr : Expr exprExt targetExt c m) : ArrowBody exprExt targetExt c m
  | block {c m : Nat} (body : Block exprExt targetExt c m) : ArrowBody exprExt targetExt c m

/-- The first clause of a `for (;;)` statement; it may bind a variable,
which is in scope in the condition, the step and the body. -/
inductive ForInit (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Nat → Nat → Type where
  | none {c m : Nat} : ForInit exprExt targetExt c m 0 0
  | expr {c m : Nat} (expr : Expr exprExt targetExt c m) : ForInit exprExt targetExt c m 0 0
  /-- `for (const x = e; ...)` -/
  | constDecl {c m : Nat} (init : Expr exprExt targetExt c m) : ForInit exprExt targetExt c m 1 0
  /-- `for (let x = e; ...)` -/
  | letDecl {c m : Nat} (init : OptExpr exprExt targetExt c m) : ForInit exprExt targetExt c m 0 1

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement. -/
inductive ForHead (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Nat → Nat → Type where
  /-- `for (x of ...)`, assigning to something that already exists. -/
  | target {c m : Nat} (target : Target exprExt targetExt c m) : ForHead exprExt targetExt c m 0 0
  /-- `for (const x of ...)` -/
  | constBind {c m : Nat} : ForHead exprExt targetExt c m 1 0
  /-- `for (let x of ...)` -/
  | letBind {c m : Nat} : ForHead exprExt targetExt c m 0 1

/-- One `case`/`default` of a `switch`. -/
inductive SwitchCase (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | case {c m : Nat} (test : Expr exprExt targetExt c m) (body : Block exprExt targetExt c m) : SwitchCase exprExt targetExt c m
  | default {c m : Nat} (body : Block exprExt targetExt c m) : SwitchCase exprExt targetExt c m

/-- The cases of a `switch`. -/
inductive SwitchCases (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : SwitchCases exprExt targetExt c m
  | cons {c m : Nat} (hd : SwitchCase exprExt targetExt c m) (tl : SwitchCases exprExt targetExt c m) : SwitchCases exprExt targetExt c m

/-- An optional block. -/
inductive OptBlock (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | none {c m : Nat} : OptBlock exprExt targetExt c m
  | some {c m : Nat} (body : Block exprExt targetExt c m) : OptBlock exprExt targetExt c m

/-- What follows the block of a `try`.  A `try` needs a `catch` or a
`finally`, which this makes structurally impossible to violate. -/
inductive TryTail (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  /-- `catch (e) { ... }`; the binder is a mutable variable, `mutVar 0` in
  the body of the clause. -/
  | catch_ {c m : Nat} (body : Block exprExt targetExt c (m + 1)) (fin : OptBlock exprExt targetExt c m) : TryTail exprExt targetExt c m
  /-- No `catch` clause, only a `finally`. -/
  | finallyOnly {c m : Nat} (body : Block exprExt targetExt c m) : TryTail exprExt targetExt c m

/-- A statement in scope `(c, m)` that binds `dc` further const and `dm`
further mutable variables for the statements that follow it. -/
inductive Stmt (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Nat → Nat → Type where
  /-- An expression statement. -/
  | expr {c m : Nat} (expr : Expr exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  /-- `const x = init;` -/
  | constDecl {c m : Nat} (init : Expr exprExt targetExt c m) : Stmt exprExt targetExt c m 1 0
  /-- `let x = init;` (`var` is converted to this). -/
  | letDecl {c m : Nat} (init : OptExpr exprExt targetExt c m) : Stmt exprExt targetExt c m 0 1
  /-- `using x = init;` and `await using x = init;`, the explicit resource
  management declarations; `isAwait` selects the second.  What they bind
  cannot be assigned to, so it is a const binding. -/
  | usingDecl {c m : Nat} (isAwait : Bool) (init : Expr exprExt targetExt c m) :
      Stmt exprExt targetExt c m 1 0
  /-- A nested block; what it binds does not escape it. -/
  | block {c m : Nat} (body : Block exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | if_ {c m : Nat} (cond : Expr exprExt targetExt c m) (thenB : Block exprExt targetExt c m) (elseB : OptBlock exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | while_ {c m : Nat} (cond : Expr exprExt targetExt c m) (body : Block exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | doWhile {c m : Nat} (body : Block exprExt targetExt c m) (cond : Expr exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | for_ {c m dc dm : Nat} (init : ForInit exprExt targetExt c m dc dm) (cond : OptExpr exprExt targetExt (c + dc) (m + dm))
      (step : OptExpr exprExt targetExt (c + dc) (m + dm)) (body : Block exprExt targetExt (c + dc) (m + dm)) : Stmt exprExt targetExt c m 0 0
  | forIn {c m dc dm : Nat} (head : ForHead exprExt targetExt c m dc dm) (obj : Expr exprExt targetExt c m)
      (body : Block exprExt targetExt (c + dc) (m + dm)) : Stmt exprExt targetExt c m 0 0
  | forOf {c m dc dm : Nat} (head : ForHead exprExt targetExt c m dc dm) (obj : Expr exprExt targetExt c m)
      (body : Block exprExt targetExt (c + dc) (m + dm)) : Stmt exprExt targetExt c m 0 0
  /-- `function f(...) { ... }`; `f` is a const binding, and it is in scope
  in the body of the function, where it is `constVar 0`. -/
  | funcDecl {c m : Nat} (isAsync isGenerator hasRest : Bool)
      (arity : Nat) (body : Block exprExt targetExt (c + 1) (m + arity + hasRest.toNat)) : Stmt exprExt targetExt c m 1 0
  /-- `class C { ... }`; `C` is a const binding, in scope in the body. -/
  | classDecl {c m : Nat} (decorators : Exprs exprExt targetExt c m)
      (heritage : OptExpr exprExt targetExt c m) (body : ClassElems exprExt targetExt (c + 1) m) : Stmt exprExt targetExt c m 1 0
  | return_ {c m : Nat} (expr : OptExpr exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | throw {c m : Nat} (expr : Expr exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | break_ {c m : Nat} (label : Option NEString) : Stmt exprExt targetExt c m 0 0
  | continue_ {c m : Nat} (label : Option NEString) : Stmt exprExt targetExt c m 0 0
  /-- A labelled statement.  A label may carry a declaration — a labelled
  function declaration, `l: function f () {}`, is the usual case — so what
  the statement binds is what the labelled statement binds. -/
  | labelled {c m dc dm : Nat} (label : NEString)
      (stmt : Stmt exprExt targetExt c m dc dm) : Stmt exprExt targetExt c m dc dm
  | switch {c m : Nat} (disc : Expr exprExt targetExt c m) (cases : SwitchCases exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0
  | try_ {c m : Nat} (body : Block exprExt targetExt c m) (tail : TryTail exprExt targetExt c m) : Stmt exprExt targetExt c m 0 0

/-- A block: a telescope of statements, each of which may extend the scope
of the ones that follow it. -/
inductive Block (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : Block exprExt targetExt c m
  | cons {c m dc dm : Nat} (hd : Stmt exprExt targetExt c m dc dm) (tl : Block exprExt targetExt (c + dc) (m + dm)) : Block exprExt targetExt c m

/-- One entry of an `export { a as b }` clause: which local variable is
exported, and under which name. -/
inductive ExportLocal (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | const {c m : Nat} (i : Fin c) (exported : NEString) : ExportLocal exprExt targetExt c m
  | mut {c m : Nat} (i : Fin m) (exported : NEString) : ExportLocal exprExt targetExt c m

/-- The entries of an `export { ... }` clause. -/
inductive ExportLocals (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : ExportLocals exprExt targetExt c m
  | cons {c m : Nat} (hd : ExportLocal exprExt targetExt c m) (tl : ExportLocals exprExt targetExt c m) : ExportLocals exprExt targetExt c m

/-- A top level item: a statement, or an `import`/`export` declaration.
Like a statement it may extend the scope of what follows it. -/
inductive ModuleItem (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Nat → Nat → Type where
  | stmt {c m dc dm : Nat} (stmt : Stmt exprExt targetExt c m dc dm) : ModuleItem exprExt targetExt c m dc dm
  /-- `import "mod";`, which binds nothing. -/
  | importBare {c m : Nat} (mod : NEString)
      (attrs : List ImportAttr) : ModuleItem exprExt targetExt c m 0 0
  /-- `import ... from "mod";`; the names it binds are const bindings, bound
  left to right, so the last of them is `constVar 0`. -/
  | importClause {c m : Nat} (clause : ImportClause) : ModuleItem exprExt targetExt c m clause.count 0
  /-- `export { a as b } from "mod";` -/
  | exportFrom {c m : Nat} (specs : List Specifier) (mod : NEString)
      (attrs : List ImportAttr) : ModuleItem exprExt targetExt c m 0 0
  /-- `export * from "mod";` and `export * as ns from "mod";`; `alias_` is
  the `ns` of the second form.  Neither binds a name in this module. -/
  | exportAll {c m : Nat} (alias_ : Option NEString) (mod : NEString)
      (attrs : List ImportAttr) : ModuleItem exprExt targetExt c m 0 0
  /-- `export default <expression>;` -/
  | exportDefaultExpr {c m : Nat} (expr : Expr exprExt targetExt c m) : ModuleItem exprExt targetExt c m 0 0
  /-- `export { x as name };` -/
  | exportLocals {c m : Nat} (specs : ExportLocals exprExt targetExt c m) : ModuleItem exprExt targetExt c m 0 0
  /-- `export <declaration>` -/
  | exportDecl {c m dc dm : Nat} (stmt : Stmt exprExt targetExt c m dc dm) : ModuleItem exprExt targetExt c m dc dm

/-- The top level items of a program, as a telescope. -/
inductive ModuleItems (exprExt targetExt : Nat → Nat → Type) : Nat → Nat → Type where
  | nil {c m : Nat} : ModuleItems exprExt targetExt c m
  | cons {c m dc dm : Nat} (hd : ModuleItem exprExt targetExt c m dc dm) (tl : ModuleItems exprExt targetExt (c + dc) (m + dm)) :
      ModuleItems exprExt targetExt c m

end

variable {exprExt targetExt : Nat → Nat → Type}

/-! ## Trees whose extension is an unknown global

The instantiation of the tree at `GlobalExt g`: a tree in the scope
`(c, m)` whose unknown globals are among `g`, which is what the tree was
before it took its extensions as parameters.  `Program`, `OfMini` and the
optimizer all work with these. -/

namespace Global

/-- `Expr` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Expr (c m : Nat) (g : Finset NEString) := BrujinAST.Expr (GlobalExt g) (GlobalExt g) c m

/-- `Target` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Target (c m : Nat) (g : Finset NEString) := BrujinAST.Target (GlobalExt g) (GlobalExt g) c m

/-- `ChainLink` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ChainLink (c m : Nat) (g : Finset NEString) := BrujinAST.ChainLink (GlobalExt g) (GlobalExt g) c m

/-- `ChainLinks` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ChainLinks (c m : Nat) (g : Finset NEString) := BrujinAST.ChainLinks (GlobalExt g) (GlobalExt g) c m

/-- `Exprs` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Exprs (c m : Nat) (g : Finset NEString) := BrujinAST.Exprs (GlobalExt g) (GlobalExt g) c m

/-- `OptExpr` whose escape hatch is an unknown global drawn from `g`. -/
abbrev OptExpr (c m : Nat) (g : Finset NEString) := BrujinAST.OptExpr (GlobalExt g) (GlobalExt g) c m

/-- `ArrayElem` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ArrayElem (c m : Nat) (g : Finset NEString) := BrujinAST.ArrayElem (GlobalExt g) (GlobalExt g) c m

/-- `ArrayElems` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ArrayElems (c m : Nat) (g : Finset NEString) := BrujinAST.ArrayElems (GlobalExt g) (GlobalExt g) c m

/-- `TemplatePart` whose escape hatch is an unknown global drawn from `g`. -/
abbrev TemplatePart (c m : Nat) (g : Finset NEString) := BrujinAST.TemplatePart (GlobalExt g) (GlobalExt g) c m

/-- `TemplateParts` whose escape hatch is an unknown global drawn from `g`. -/
abbrev TemplateParts (c m : Nat) (g : Finset NEString) := BrujinAST.TemplateParts (GlobalExt g) (GlobalExt g) c m

/-- `PropName` whose escape hatch is an unknown global drawn from `g`. -/
abbrev PropName (c m : Nat) (g : Finset NEString) := BrujinAST.PropName (GlobalExt g) (GlobalExt g) c m

/-- `Property` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Property (c m : Nat) (g : Finset NEString) := BrujinAST.Property (GlobalExt g) (GlobalExt g) c m

/-- `Properties` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Properties (c m : Nat) (g : Finset NEString) := BrujinAST.Properties (GlobalExt g) (GlobalExt g) c m

/-- `ClassElem` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ClassElem (c m : Nat) (g : Finset NEString) := BrujinAST.ClassElem (GlobalExt g) (GlobalExt g) c m

/-- `ClassElems` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ClassElems (c m : Nat) (g : Finset NEString) := BrujinAST.ClassElems (GlobalExt g) (GlobalExt g) c m

/-- `ArrowBody` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ArrowBody (c m : Nat) (g : Finset NEString) := BrujinAST.ArrowBody (GlobalExt g) (GlobalExt g) c m

/-- `SwitchCase` whose escape hatch is an unknown global drawn from `g`. -/
abbrev SwitchCase (c m : Nat) (g : Finset NEString) := BrujinAST.SwitchCase (GlobalExt g) (GlobalExt g) c m

/-- `SwitchCases` whose escape hatch is an unknown global drawn from `g`. -/
abbrev SwitchCases (c m : Nat) (g : Finset NEString) := BrujinAST.SwitchCases (GlobalExt g) (GlobalExt g) c m

/-- `OptBlock` whose escape hatch is an unknown global drawn from `g`. -/
abbrev OptBlock (c m : Nat) (g : Finset NEString) := BrujinAST.OptBlock (GlobalExt g) (GlobalExt g) c m

/-- `TryTail` whose escape hatch is an unknown global drawn from `g`. -/
abbrev TryTail (c m : Nat) (g : Finset NEString) := BrujinAST.TryTail (GlobalExt g) (GlobalExt g) c m

/-- `Block` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Block (c m : Nat) (g : Finset NEString) := BrujinAST.Block (GlobalExt g) (GlobalExt g) c m

/-- `ExportLocal` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ExportLocal (c m : Nat) (g : Finset NEString) := BrujinAST.ExportLocal (GlobalExt g) (GlobalExt g) c m

/-- `ExportLocals` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ExportLocals (c m : Nat) (g : Finset NEString) := BrujinAST.ExportLocals (GlobalExt g) (GlobalExt g) c m

/-- `ModuleItems` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ModuleItems (c m : Nat) (g : Finset NEString) := BrujinAST.ModuleItems (GlobalExt g) (GlobalExt g) c m

/-- `ForInit` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ForInit (c m : Nat) (g : Finset NEString) (dc dm : Nat) :=
  BrujinAST.ForInit (GlobalExt g) (GlobalExt g) c m dc dm

/-- `ForHead` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ForHead (c m : Nat) (g : Finset NEString) (dc dm : Nat) :=
  BrujinAST.ForHead (GlobalExt g) (GlobalExt g) c m dc dm

/-- `Stmt` whose escape hatch is an unknown global drawn from `g`. -/
abbrev Stmt (c m : Nat) (g : Finset NEString) (dc dm : Nat) :=
  BrujinAST.Stmt (GlobalExt g) (GlobalExt g) c m dc dm

/-- `ModuleItem` whose escape hatch is an unknown global drawn from `g`. -/
abbrev ModuleItem (c m : Nat) (g : Finset NEString) (dc dm : Nat) :=
  BrujinAST.ModuleItem (GlobalExt g) (GlobalExt g) c m dc dm

end Global

/-- An unknown global, as an expression: the escape hatch of the tree
instantiated at `GlobalExt g`. -/
abbrev Expr.unsafeGlobal {c m : Nat} {g : Finset NEString} (name : NEString) (mem : name ∈ g) :
    Global.Expr c m g := .unsafeExt ⟨name, mem⟩

/-- An unknown global, as an assignment target. -/
abbrev Target.unsafeGlobal {c m : Nat} {g : Finset NEString} (name : NEString) (mem : name ∈ g) :
    Global.Target c m g := .unsafeExt ⟨name, mem⟩

/-- A whole program: top level items in the empty scope, together with the
set of unknown globals they mention.  The set is a field rather than a
parameter so that `Program` is an ordinary type: two programs which name
different globals still have the same type. -/
structure Program where
  /-- The unknown globals the program mentions. -/
  globals : Finset NEString
  /-- The top level items. -/
  items : Global.ModuleItems 0 0 globals

/-- An expression in the scope `(c, m)`, together with the set of unknown
globals it mentions. -/
structure ScopedExpr (c m : Nat) where
  /-- The unknown globals the expression mentions. -/
  globals : Finset NEString
  /-- The expression. -/
  expr : Global.Expr c m globals

/-! ## Default values -/

instance {c m : Nat} : Inhabited (Expr exprExt targetExt c m) := ⟨.null⟩
instance {c m : Nat} : Inhabited (Target exprExt targetExt c m) := ⟨.dot .null default⟩
instance {c m : Nat} : Inhabited (Exprs exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (OptExpr exprExt targetExt c m) := ⟨.none⟩
instance {c m : Nat} : Inhabited (ArrayElem exprExt targetExt c m) := ⟨.hole⟩
instance {c m : Nat} : Inhabited (ArrayElems exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (TemplatePart exprExt targetExt c m) := ⟨.mk default ""⟩
instance {c m : Nat} : Inhabited (TemplateParts exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (PropName exprExt targetExt c m) := ⟨.ident default⟩
instance {c m : Nat} : Inhabited (Property exprExt targetExt c m) := ⟨.keyValue default default⟩
instance {c m : Nat} : Inhabited (Properties exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (ClassElems exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (Block exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (OptBlock exprExt targetExt c m) := ⟨.none⟩
instance {c m : Nat} : Inhabited (ClassElem exprExt targetExt c m) :=
  ⟨.method .nil false .normal default 0 false .nil⟩
instance {c m : Nat} : Inhabited (ChainLink exprExt targetExt c m) := ⟨.dot true default⟩
instance {c m : Nat} : Inhabited (ChainLinks exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (ArrowBody exprExt targetExt c m) := ⟨.block .nil⟩
instance {c m : Nat} : Inhabited (ForInit exprExt targetExt c m 0 0) := ⟨.none⟩
instance {c m : Nat} : Inhabited (ForHead exprExt targetExt c m 0 0) := ⟨.target default⟩
instance {c m : Nat} : Inhabited (SwitchCase exprExt targetExt c m) := ⟨.default .nil⟩
instance {c m : Nat} : Inhabited (SwitchCases exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (TryTail exprExt targetExt c m) := ⟨.finallyOnly .nil⟩
instance {c m : Nat} : Inhabited (Stmt exprExt targetExt c m 0 0) := ⟨.expr default⟩
instance {c m : Nat} : Inhabited (ExportLocals exprExt targetExt c m) := ⟨.nil⟩
instance {c m : Nat} : Inhabited (ModuleItem exprExt targetExt c m 0 0) := ⟨.stmt default⟩
instance {c m : Nat} : Inhabited (ModuleItems exprExt targetExt c m) := ⟨.nil⟩
instance : Inhabited Program := ⟨⟨∅, .nil⟩⟩
instance {c m : Nat} : Inhabited (ScopedExpr c m) := ⟨⟨∅, .null⟩⟩

/-! ## Lists -/

namespace Exprs
def toList {c m : Nat} : Exprs exprExt targetExt c m → List (Expr exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (Expr exprExt targetExt c m) → Exprs exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
@[simp] theorem toList_ofList {c m : Nat} (l : List (Expr exprExt targetExt c m)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, toList, ih]
end Exprs

namespace ChainLinks
def toList {c m : Nat} : ChainLinks exprExt targetExt c m → List (ChainLink exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ChainLink exprExt targetExt c m) → ChainLinks exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
@[simp] theorem toList_ofList {c m : Nat} (l : List (ChainLink exprExt targetExt c m)) :
    (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, toList, ih]
end ChainLinks

namespace ArrayElems
def toList {c m : Nat} : ArrayElems exprExt targetExt c m → List (ArrayElem exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ArrayElem exprExt targetExt c m) → ArrayElems exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
@[simp] theorem toList_ofList {c m : Nat} (l : List (ArrayElem exprExt targetExt c m)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, toList, ih]
end ArrayElems

namespace TemplateParts
def toList {c m : Nat} : TemplateParts exprExt targetExt c m → List (TemplatePart exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (TemplatePart exprExt targetExt c m) → TemplateParts exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end TemplateParts

namespace Properties
def toList {c m : Nat} : Properties exprExt targetExt c m → List (Property exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (Property exprExt targetExt c m) → Properties exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end Properties

namespace ClassElems
def toList {c m : Nat} : ClassElems exprExt targetExt c m → List (ClassElem exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ClassElem exprExt targetExt c m) → ClassElems exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end ClassElems

namespace SwitchCases
def toList {c m : Nat} : SwitchCases exprExt targetExt c m → List (SwitchCase exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (SwitchCase exprExt targetExt c m) → SwitchCases exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end SwitchCases

namespace ExportLocals
def toList {c m : Nat} : ExportLocals exprExt targetExt c m → List (ExportLocal exprExt targetExt c m)
  | .nil => []
  | .cons e r => e :: toList r
def ofList {c m : Nat} : List (ExportLocal exprExt targetExt c m) → ExportLocals exprExt targetExt c m
  | [] => .nil
  | e :: r => .cons e (ofList r)
end ExportLocals

namespace OptExpr
def toOption {c m : Nat} : OptExpr exprExt targetExt c m → Option (Expr exprExt targetExt c m)
  | OptExpr.none => Option.none
  | OptExpr.some e => Option.some e
def ofOption {c m : Nat} : Option (Expr exprExt targetExt c m) → OptExpr exprExt targetExt c m
  | Option.none => OptExpr.none
  | Option.some e => OptExpr.some e
end OptExpr

namespace OptBlock
def toOption {c m : Nat} : OptBlock exprExt targetExt c m → Option (Block exprExt targetExt c m)
  | OptBlock.none => Option.none
  | OptBlock.some b => Option.some b
def ofOption {c m : Nat} : Option (Block exprExt targetExt c m) → OptBlock exprExt targetExt c m
  | Option.none => OptBlock.none
  | Option.some b => OptBlock.some b
end OptBlock

/-! ## Casting along an equality of scopes -/

def Expr.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m')
    (e : Expr exprExt targetExt c m) : Expr exprExt targetExt c' m' :=
  hc ▸ hm ▸ e

def OptExpr.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m')
    (e : OptExpr exprExt targetExt c m) : OptExpr exprExt targetExt c' m' :=
  hc ▸ hm ▸ e

def Block.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m')
    (b : Block exprExt targetExt c m) : Block exprExt targetExt c' m' :=
  hc ▸ hm ▸ b

def ModuleItems.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m')
    (b : ModuleItems exprExt targetExt c m) : ModuleItems exprExt targetExt c' m' :=
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
