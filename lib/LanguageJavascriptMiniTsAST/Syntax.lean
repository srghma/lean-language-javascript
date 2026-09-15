import MiniAST.Syntax

/-!
# The TypeScript syntax tree

A TypeScript syntax tree: the JavaScript tree of `MiniAST`, with the
TypeScript syntax added to it — the type expressions, type annotations,
type parameters and type arguments, the member modifiers, and the
TypeScript declarations (`interface`, `type`, `enum`, `declare`,
`namespace`, `import`/`export type`).

The component types that carry no TypeScript syntax (non-empty strings
and lists, numeric and regular expression literals, the operators, the
JSX names) are the ones of `Language.JavaScript`; this file reuses them
rather than repeating them.

A TypeScript file is read here as prettier reads one: with JSX enabled,
which is what prettier's `typescript` parser does.  The angle bracket
type assertion `<T>x`, which that reading rules out, is therefore not
part of the tree; `x as T` is.
-/

namespace Language.TypeScript.MiniTsAST

open Language.JavaScript

/-! ## TypeScript modifiers -/

/-- The accessibility modifier of a class member or of a parameter
property. -/
inductive TsAccessibility where
  | public_
  | protected_
  | private_
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword an accessibility modifier is written with. -/
def TsAccessibility.text : TsAccessibility → String
  | .public_ => "public"
  | .protected_ => "protected"
  | .private_ => "private"

/-- The modifiers a member of a class may be written with, in the order
prettier writes them: `declare`, the accessibility, `static`,
`override`, `abstract`, `readonly`. -/
structure TsMemberMods where
  /-- `declare x: number;` -/
  isDeclare : Bool := false
  /-- `public`, `protected` or `private`. -/
  accessibility : Option TsAccessibility := none
  /-- `static` -/
  isStatic : Bool := false
  /-- `override` -/
  isOverride : Bool := false
  /-- `abstract` -/
  isAbstract : Bool := false
  /-- `readonly` -/
  isReadonly : Bool := false
deriving Repr, BEq, DecidableEq, Inhabited

/-- The modifiers a parameter may be written with.  A parameter written
with one of them is a parameter property: it declares a member of the
class as well as a parameter of its constructor. -/
structure TsParamMods where
  /-- `public`, `protected` or `private`. -/
  accessibility : Option TsAccessibility := none
  /-- `override` -/
  isOverride : Bool := false
  /-- `readonly` -/
  isReadonly : Bool := false
deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether any modifier is written, which makes the parameter a
parameter property. -/
def TsParamMods.isEmpty (m : TsParamMods) : Bool :=
  m.accessibility.isNone && !m.isOverride && !m.isReadonly

/-- The variance annotation of a type parameter. -/
inductive TsVariance where
  /-- `in T` -/
  | in_
  /-- `out T` -/
  | out_
  /-- `in out T` -/
  | inOut
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keywords a variance annotation is written with. -/
def TsVariance.text : TsVariance → String
  | .in_ => "in"
  | .out_ => "out"
  | .inOut => "in out"

/-- What a mapped type does to the `readonly` or `?` modifier of the
properties it maps. -/
inductive TsMappedMod where
  /-- The modifier is written as it stands: `readonly`, `?`. -/
  | keep
  /-- `+readonly`, `+?` -/
  | add
  /-- `-readonly`, `-?` -/
  | remove
deriving Repr, BEq, DecidableEq, Inhabited

/-- What kind of member of an interface, or of an object type, a method
signature is. -/
inductive TsMethodSigKind where
  /-- `m(): void` -/
  | normal
  /-- `get p(): number` -/
  | get
  /-- `set p(v: number)` -/
  | set
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Imports and exports -/

/-- One `name`, `name as alias` or `type name` of an import or export
clause. -/
structure TsSpecifier where
  /-- `import { type A }`, the type only form of the specifier. -/
  isType : Bool := false
  /-- The exported name. -/
  name : NEString
  /-- The local name, when it differs. -/
  alias_ : Option NEString := none
deriving Repr, BEq, DecidableEq, Inhabited

/-- The name of a namespace, or of a type, possibly read through a
namespace: `A`, `A.B.C`. -/
inductive TsEntityName where
  | ident (name : NEString)
  /-- `obj.name` -/
  | qualified (obj : TsEntityName) (name : NEString)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The name a `namespace`/`module` declaration declares. -/
inductive TsNamespaceName where
  /-- `namespace N`, `namespace N.M` -/
  | qualified (names : NEList NEString)
  /-- `module "foo"` -/
  | str (value : String)
  /-- `declare global` -/
  | global
deriving Repr, BEq, DecidableEq, Inhabited

/-- The right hand side of an `import x = ...` declaration. -/
inductive TsImportEqualsRhs where
  /-- `import fs = require("fs");` -/
  | require (mod : String)
  /-- `import A = B.C;` -/
  | entity (name : TsEntityName)
deriving Repr, BEq, DecidableEq, Inhabited

/-- `import def, * as ns, { a, b as c } from "mod";`.  Each of the three
clauses is optional, but at least one of them has to be there. -/
structure MiniImportClause where
  /-- `import type ... from "mod"`, the type only form. -/
  isType : Bool := false
  /-- The default import, `import def from "mod"`. -/
  default_ : Option NEString
  /-- The namespace import, `import * as ns from "mod"`. -/
  namespace_ : Option NEString
  /-- The named imports, `import { a, b as c } from "mod"`. -/
  named : Option (List TsSpecifier)
  /-- The module the names come from. -/
  mod : NEString
  /-- The import attributes, `with { type: "json" }`. -/
  attrs : List ImportAttr := []
  /-- An import must bind something. -/
  binds : default_.isSome ∨ namespace_.isSome ∨ named.isSome
deriving DecidableEq

instance : Inhabited MiniImportClause :=
  ⟨{ isType := false, default_ := some default, namespace_ := .none, named := .none,
     mod := default, attrs := [], binds := Or.inl rfl }⟩

namespace MiniImportClause

/-- Build an import clause, checking that it binds something. -/
def mk? (default_ namespace_ : Option NEString) (named : Option (List TsSpecifier))
    (mod : NEString) (attrs : List ImportAttr := []) (isType : Bool := false) :
    Option MiniImportClause :=
  if h : default_.isSome ∨ namespace_.isSome ∨ named.isSome then
    some ⟨isType, default_, namespace_, named, mod, attrs, h⟩
  else
    Option.none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (default_ namespace_ : Option NEString) (named : Option (List TsSpecifier))
    (mod : NEString) (attrs : List ImportAttr := []) (isType : Bool := false) :
    MiniImportClause :=
  (mk? default_ namespace_ named mod attrs isType).getD default

end MiniImportClause

/-- An `import` declaration. -/
inductive MiniImportDeclaration where
  /-- `import "mod";`, possibly with import attributes. -/
  | bare (mod : NEString) (attrs : List ImportAttr)
  /-- `import ... from "mod";` -/
  | clause (clause : MiniImportClause)
  /-- `import fs = require("fs");` and `import A = B.C;`; `isExport`
  writes it as `export import A = B.C;`. -/
  | equals (isExport : Bool) (name : NEString) (rhs : TsImportEqualsRhs)
deriving DecidableEq, Inhabited

/-! ## The syntax tree -/

mutual

/-- Expressions. -/
inductive MiniExpr where
  /-- An identifier. -/
  | ident (name : NEString)
  /-- A numeric literal, as the number it denotes. -/
  | number (value : JSNumber)
  /-- A string literal, holding the characters it denotes (not the source text). -/
  | string (value : String)
  /-- A regular expression literal: its pattern and its flags. -/
  | regex (re : RegExpLit)
  | null
  | true_
  | false_
  | this
  /-- `super.name`, the only forms `super` may be written in being a
  member access and a call; `super` on its own is not an expression. -/
  | superDot (name : NEString)
  /-- `super[idx]` -/
  | superIndex (idx : MiniExpr)
  /-- `super(args)`, the call to the constructor of the parent class. -/
  | superCall (args : List MiniExpr)
  /-- `new.target` -/
  | newTarget
  /-- `[a, , b]` -/
  | array (elements : List MiniArrayElement)
  /-- `{ a: 1 }` -/
  | object (properties : List MiniProperty)
  /-- `lhs op rhs`, for an assignment operator `op`. -/
  | assign (lhs : MiniExpr) (op : AssignOp) (rhs : MiniExpr)
  /-- A destructuring assignment, `[a, b] = xs` or `({ a } = o)`: the left
  hand side is a pattern rather than an expression. -/
  | assignPattern (lhs : MiniPattern) (rhs : MiniExpr)
  | await (expr : MiniExpr)
  /-- `callee(args)`, and `callee<T>(args)` when `typeArgs` is not empty. -/
  | call (callee : MiniExpr) (typeArgs : List MiniTsType) (args : List MiniExpr)
  /-- `obj.name` -/
  | dot (obj : MiniExpr) (name : NEString)
  /-- `obj.#name`, the access to a private class member. -/
  | privateDot (obj : MiniExpr) (name : NEString)
  /-- A private name used on its own, which only `#x in obj` allows. -/
  | privateName (name : NEString)
  /-- `obj[index]` -/
  | index (obj : MiniExpr) (idx : MiniExpr)
  /-- An optional chain expression. -/
  | chain (base : MiniExpr) (links : NEList MiniChainLink)
  /-- `import.meta` -/
  | importMeta
  /-- A dynamic import, `import(specifier)` or `import(specifier, options)`. -/
  | importCall (specifier : MiniExpr) (options : Option MiniExpr)
  /-- `class name extends heritage { body }` used as an expression. -/
  | classExpr (decorators : List MiniExpr) (name : Option NEString)
      (typeParams : List MiniTsTypeParam) (heritage : Option MiniClassHeritage)
      (implements_ : List MiniTsHeritage) (body : List MiniClassElement)
  /-- The comma operator, `lhs, rhs`. -/
  | seq (lhs : MiniExpr) (rhs : MiniExpr)
  | binary (lhs : MiniExpr) (op : BinOp) (rhs : MiniExpr)
  | postfix (expr : MiniExpr) (op : PostfixOp)
  /-- `cond ? thenE : elseE` -/
  | ternary (cond : MiniExpr) (thenE : MiniExpr) (elseE : MiniExpr)
  /-- `(params) => body`, and `async (params) => body` when `isAsync` is
  set. -/
  | arrow (isAsync : Bool) (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (retType : Option MiniTsType) (body : MiniArrowBody)
  /-- A function expression; `isAsync` and `isGenerator` select `async` and `*`. -/
  | func (isAsync : Bool) (isGenerator : Bool) (name : Option NEString)
      (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (retType : Option MiniTsType) (body : List MiniStatement)
  /-- `new callee(args)`, and `new callee<T>(args)` when `typeArgs` is
  not empty. -/
  | new (callee : MiniExpr) (typeArgs : List MiniTsType) (args : List MiniExpr)
  /-- `...expr` -/
  | spread (expr : MiniExpr)
  /-- A template literal: an optional tag, the type arguments the tag is
  read at (`` tag<T>`…` ``, which only a tagged template may carry), the
  text before the first substitution, and one part per substitution. -/
  | template (tag : Option MiniExpr) (typeArgs : List MiniTsType) (head : String)
      (parts : List MiniTemplatePart)
  | unary (op : UnaryOp) (expr : MiniExpr)
  /-- `yield expr` -/
  | yield (expr : Option MiniExpr)
  /-- `yield* expr` -/
  | yieldFrom (expr : MiniExpr)
  /-- A JSX element or fragment, `<div />` or `<>...</>`. -/
  | jsx (node : MiniJSXNode)
  /-- `expr as T`, and `expr as const` when the type is the reference
  `const`. -/
  | asExpr (expr : MiniExpr) (type : MiniTsType)
  /-- `expr satisfies T` -/
  | satisfies (expr : MiniExpr) (type : MiniTsType)
  /-- `expr!`, the non-null assertion. -/
  | nonNull (expr : MiniExpr)
  /-- `f<T>`, an instantiation expression: a generic function read at a
  type, with no call. -/
  | instantiation (expr : MiniExpr) (typeArgs : List MiniTsType)

-- ### Types

/-- A type expression. -/
inductive MiniTsType where
  /-- A type read by name, `Foo`, `A.B<T>`; the predefined types
  (`string`, `any`, `void`, `never`, `undefined`, `null`, …) are
  references too. -/
  | ref (name : TsEntityName) (args : List MiniTsType)
  /-- `this` -/
  | this
  /-- A string literal type, holding the characters it denotes. -/
  | strLit (value : String)
  /-- A numeric literal type. -/
  | numLit (value : JSNumber)
  /-- A negated numeric literal type, `-1`. -/
  | negNumLit (value : JSNumber)
  /-- `T[]` -/
  | array (elem : MiniTsType)
  /-- `T[K]`, an indexed access type. -/
  | indexed (obj : MiniTsType) (index : MiniTsType)
  /-- `A | B | C`; a union is written with at least two members. -/
  | union (types : List MiniTsType)
  /-- `A & B & C` -/
  | intersection (types : List MiniTsType)
  /-- `(a: A) => B` -/
  | fn (typeParams : List MiniTsTypeParam) (params : List MiniParam) (ret : MiniTsType)
  /-- `new (a: A) => B`, and `abstract new (a: A) => B`. -/
  | ctor (isAbstract : Bool) (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (ret : MiniTsType)
  /-- `typeof x`, and `typeof x<T>`. -/
  | typeQuery (name : TsEntityName) (args : List MiniTsType)
  /-- `keyof T` -/
  | keyof (type : MiniTsType)
  /-- `readonly T[]`, `readonly [A, B]` -/
  | readonlyOp (type : MiniTsType)
  /-- `unique symbol` -/
  | uniqueSymbol
  /-- `infer U`, and `infer U extends C`. -/
  | infer_ (name : NEString) (constraint : Option MiniTsType)
  /-- `C extends E ? T : F` -/
  | conditional (check : MiniTsType) (extends_ : MiniTsType) (trueType : MiniTsType)
      (falseType : MiniTsType)
  /-- `{ a: A; b(): B }`, an object type. -/
  | objectType (members : List MiniTsTypeMember)
  /-- A mapped type, `{ readonly [K in Keys as N]?: T }`. -/
  | mapped (readonlyMod : Option TsMappedMod) (key : NEString) (constraint : MiniTsType)
      (as_ : Option MiniTsType) (optionalMod : Option TsMappedMod) (value : Option MiniTsType)
  /-- `[A, b?: B, ...C[]]` -/
  | tuple (elems : List MiniTsTupleElem)
  /-- A template literal type: the text before the first substitution,
  and one part per substitution. -/
  | templateLit (head : String) (parts : List MiniTsTemplatePart)
  /-- `import("mod")`, `import("mod").A<T>`, `typeof import("mod")` when
  `isTypeof` is set, and `import("mod", { with: { type: "json" } })` when
  the import attributes are written. -/
  | importType (isTypeof : Bool) (mod : String) (attrs : List ImportAttr)
      (qualifier : Option TsEntityName) (args : List MiniTsType)
  /-- A type predicate written as the return type of a function:
  `x is T`, `asserts x`, `asserts x is T`, `this is T`. -/
  | predicate (asserts : Bool) (param : NEString) (type : Option MiniTsType)

/-- One element of a tuple type. -/
inductive MiniTsTupleElem where
  /-- `A` -/
  | elem (type : MiniTsType)
  /-- `A?` -/
  | optional (type : MiniTsType)
  /-- `...A` -/
  | rest (type : MiniTsType)
  /-- `a: A`, `a?: A` and `...a: A`, the labelled forms. -/
  | named (name : NEString) (isOptional : Bool) (isRest : Bool) (type : MiniTsType)

/-- The `${...}` substitution of a template literal type together with
the text following it. -/
structure MiniTsTemplatePart where
  /-- The substituted type. -/
  type : MiniTsType
  /-- The template text following the substitution. -/
  suffix : String

/-- One member of an interface, or of an object type. -/
inductive MiniTsTypeMember where
  /-- `readonly a?: A` -/
  | property (isReadonly : Bool) (key : MiniPropertyName) (isOptional : Bool)
      (type : Option MiniTsType)
  /-- `m?<T>(a: A): B`, `get p(): B`, `set p(v: A)` -/
  | method (kind : TsMethodSigKind) (key : MiniPropertyName) (isOptional : Bool)
      (typeParams : List MiniTsTypeParam) (params : List MiniParam) (ret : Option MiniTsType)
  /-- `<T>(a: A): B`, a call signature. -/
  | callSig (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (ret : Option MiniTsType)
  /-- `new <T>(a: A): B`, a construct signature. -/
  | ctorSig (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (ret : Option MiniTsType)
  /-- `readonly [k: string]: A`, an index signature. -/
  | indexSig (isReadonly : Bool) (name : NEString) (keyType : MiniTsType)
      (valueType : MiniTsType)

/-- A type parameter, `const in out T extends C = D`. -/
structure MiniTsTypeParam where
  /-- `const T`, a type parameter whose inference is `const`. -/
  isConst : Bool
  /-- `in T`, `out T`, `in out T`. -/
  variance : Option TsVariance
  /-- The name. -/
  name : NEString
  /-- `T extends C` -/
  constraint : Option MiniTsType
  /-- `T = D` -/
  default_ : Option MiniTsType

/-- One entry of the `extends` clause of an interface, or of the
`implements` clause of a class: a name and its type arguments. -/
structure MiniTsHeritage where
  /-- The name. -/
  name : TsEntityName
  /-- The type arguments. -/
  args : List MiniTsType

/-- The `extends` clause of a class: an expression and its type
arguments. -/
structure MiniClassHeritage where
  /-- The base class. -/
  expr : MiniExpr
  /-- The type arguments, `extends Base<T>`. -/
  typeArgs : List MiniTsType

-- ### JSX

/-- A JSX element or fragment. -/
inductive MiniJSXNode where
  /-- `<name attrs>children</name>`, and `<name attrs />` when `children`
  is `none`; `typeArgs` holds the type arguments a component may be read
  at, `<Comp<string> />`. -/
  | element (name : JSXName) (typeArgs : List MiniTsType)
      (attrs : List MiniJSXAttribute) (children : Option (List MiniJSXChild))
  /-- `<>children</>` -/
  | fragment (children : List MiniJSXChild)

/-- One attribute of a JSX element. -/
inductive MiniJSXAttribute where
  /-- `name`, `name="value"` or `name={expr}`. -/
  | attr (name : JSXName) (value : Option MiniJSXAttrValue)
  /-- `{...expr}` -/
  | spread (expr : MiniExpr)

/-- The value of a JSX attribute. -/
inductive MiniJSXAttrValue where
  /-- `name="value"`, holding the characters the value denotes. -/
  | string (value : String)
  /-- `name={expr}` -/
  | expr (e : MiniExpr)
  /-- `name=<x />`, an element written as the value with no braces. -/
  | node (n : MiniJSXNode)

/-- One child of a JSX element. -/
inductive MiniJSXChild where
  /-- Text.  It holds the characters it denotes; the characters a parser
  would read as markup are written as entities, and every run of
  whitespace in it is meaningful, as a run written on one line is: it is
  printed as `{" "}` where the line breaks there. -/
  | text (value : String)
  /-- `{expr}` -/
  | expr (e : MiniExpr)
  /-- `{}`, a substitution with nothing in it, which a source may hold
  where a comment stands between the braces. -/
  | emptyExpr
  /-- A nested element or fragment. -/
  | node (n : MiniJSXNode)

-- ### The rest of the tree

/-- One link of an optional chain: a member access or a call, `optional`
saying whether it is written with `?.`. -/
inductive MiniChainLink where
  /-- `.name` or `?.name` -/
  | dot (optional : Bool) (name : NEString)
  /-- `.#name` or `?.#name` -/
  | privateDot (optional : Bool) (name : NEString)
  /-- `[idx]` or `?.[idx]` -/
  | index (optional : Bool) (idx : MiniExpr)
  /-- `(args)` or `?.(args)`, with the type arguments of the call. -/
  | call (optional : Bool) (typeArgs : List MiniTsType) (args : List MiniExpr)
  /-- `!`, the non-null assertion written on a link of the chain. -/
  | nonNull

/-- A binding pattern. -/
inductive MiniPattern where
  /-- `x` -/
  | ident (name : NEString)
  /-- `[a, , b, ...r]` -/
  | array (elements : List MiniArrayPatternElem)
  /-- `{ a, b: c, ...r }`; `rest` is the `...r`, if there is one. -/
  | object (props : List MiniObjectPatternProp) (rest : Option MiniPattern)
  /-- `pat = value`: the value is used when what is matched is `undefined`. -/
  | withDefault (pat : MiniPattern) (value : MiniExpr)
  /-- A target which is not a binding, as in `[o.p] = xs`: the expression
  the value is assigned to.  A declaration cannot have one. -/
  | target (expr : MiniExpr)

/-- One element of an array pattern. -/
inductive MiniArrayPatternElem where
  /-- An elision, as in `[a, , b]`. -/
  | hole
  | elem (pat : MiniPattern)
  /-- `...rest`, which JavaScript only allows last. -/
  | rest (pat : MiniPattern)

/-- One property of an object pattern, `{ key: value }`; `{ a }` is the
property whose key is `a` and whose value is the pattern `a`. -/
structure MiniObjectPatternProp where
  /-- The property read from the object. -/
  key : MiniPropertyName
  /-- The pattern the property is matched against. -/
  value : MiniPattern

/-- A parameter of a function, an arrow or a method: a pattern, or a rest
parameter, which JavaScript only allows last.  A parameter carries its
type annotation, its decorators, and a parameter of a constructor may
carry the modifiers that make it a parameter property. -/
inductive MiniParam where
  /-- An ordinary parameter, `x`, `x?: T`, `x: T = 1` or `{ a, b }: T`;
  `decorators` holds the decorators a parameter of a class method may be
  written with, `@Inject() x: T`. -/
  | plain (decorators : List MiniExpr) (mods : TsParamMods) (pat : MiniPattern)
      (isOptional : Bool) (type : Option MiniTsType)
  /-- `...rest: T[]`, and `@Dec() ...rest: T[]`. -/
  | rest (decorators : List MiniExpr) (pat : MiniPattern) (type : Option MiniTsType)

/-- An element of an array literal; `hole` is an elision, as in `[1, , 2]`. -/
inductive MiniArrayElement where
  | elem (expr : MiniExpr)
  | hole

/-- The body of an arrow function. -/
inductive MiniArrowBody where
  | expr (expr : MiniExpr)
  | block (body : List MiniStatement)

/-- The `${...}` substitution of a template literal together with the text
following it. -/
structure MiniTemplatePart where
  /-- The substituted expression. -/
  expr : MiniExpr
  /-- The template text following the substitution. -/
  suffix : String

/-- The name of a property or method. -/
inductive MiniPropertyName where
  | ident (name : NEString)
  /-- A private name, `#x`, without its `#`; only a class member has one. -/
  | private_ (name : NEString)
  /-- A quoted name, holding the characters it denotes. -/
  | string (value : String)
  /-- A numeric name, as the number it denotes. -/
  | number (value : JSNumber)
  /-- `[expr]` -/
  | computed (expr : MiniExpr)

/-- A member of an object literal. -/
inductive MiniProperty where
  | keyValue (key : MiniPropertyName) (value : MiniExpr)
  /-- `{ x }` -/
  | shorthand (name : NEString)
  /-- `{ ...rest }` -/
  | spread (expr : MiniExpr)
  | method (kind : MethodKind) (key : MiniPropertyName)
      (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (retType : Option MiniTsType) (body : List MiniStatement)

/-- A member of a class body: a method, a field, an index signature or a
static block. -/
inductive MiniClassElement where
  /-- A method, a generator, a getter or a setter.  A method with no
  body is an overload signature, or the member of an abstract class
  declared with no implementation. -/
  | method (decorators : List MiniExpr) (mods : TsMemberMods) (kind : MethodKind)
      (key : MiniPropertyName) (isOptional : Bool) (typeParams : List MiniTsTypeParam)
      (params : List MiniParam) (retType : Option MiniTsType)
      (body : Option (List MiniStatement))
  /-- A field, `x = 1;`, `#x;` or `static x = 1;`; `isAccessor` writes it
  with the `accessor` keyword, as `accessor x = 1;`, and `isDefinite`
  with the definite assignment assertion, as `x!: number;`. -/
  | field (decorators : List MiniExpr) (mods : TsMemberMods) (isAccessor : Bool)
      (key : MiniPropertyName) (isOptional : Bool) (isDefinite : Bool)
      (type : Option MiniTsType) (init : Option MiniExpr)
  /-- An index signature, `[k: string]: number;`. -/
  | indexSig (mods : TsMemberMods) (name : NEString) (keyType : MiniTsType)
      (valueType : MiniTsType)
  /-- A static initialisation block, `static { ... }`. -/
  | staticBlock (body : List MiniStatement)

/-- One declarator of a `var`/`let`/`const` statement. -/
structure MiniDeclarator where
  /-- The name, or destructuring pattern, being bound. -/
  lhs : MiniPattern
  /-- The definite assignment assertion, `let x!: number;`. -/
  definite : Bool
  /-- The type annotation, if any. -/
  type : Option MiniTsType
  /-- The initialiser, if any. -/
  init : Option MiniExpr

/-- One member of an `enum`. -/
structure MiniTsEnumMember where
  /-- The name of the member. -/
  key : MiniPropertyName
  /-- The value, if it is written. -/
  init : Option MiniExpr

/-- The first clause of a `for (;;)` statement. -/
inductive MiniForInit where
  | none
  | expr (expr : MiniExpr)
  | decl (kind : VarKind) (decls : NEList MiniDeclarator)

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement:
either an assignment to something which already exists, or a declaration. -/
inductive MiniForHead where
  | pattern (lhs : MiniPattern)
  | decl (kind : VarKind) (lhs : MiniPattern)
  /-- `for (using x of xs)` and `for await (await using x of xs)`, the
  explicit resource management binders; `isAwait` selects the second. -/
  | usingDecl (isAwait : Bool) (lhs : MiniPattern)

/-- One `case`/`default` of a `switch`. -/
inductive MiniSwitchCase where
  | case (test : MiniExpr) (body : List MiniStatement)
  | default (body : List MiniStatement)

/-- The `catch` clause of a `try`; `guard` is the (non standard) `if` guard. -/
structure MiniCatchClause where
  /-- The bound exception. -/
  param : MiniPattern
  /-- The type annotation of the bound exception, `catch (e: unknown)`. -/
  type : Option MiniTsType
  /-- The guard of a `catch (e if cond)` clause. -/
  guard : Option MiniExpr
  /-- The body. -/
  body : List MiniStatement

/-- The `finally` clause of a `try`. -/
inductive MiniFinallyClause where
  | none
  | some (body : List MiniStatement)

/-- What follows the block of a `try`.  A `try` needs at least one `catch`
or a `finally`, which this makes structurally impossible to violate. -/
inductive MiniTryTail where
  /-- At least one `catch` clause, and possibly a `finally`. -/
  | catches (catches : NEList MiniCatchClause) (fin : MiniFinallyClause)
  /-- No `catch` clause, only a `finally`. -/
  | finallyOnly (body : List MiniStatement)

/-- Statements. -/
inductive MiniStatement where
  | block (body : List MiniStatement)
  | break_ (label : Option NEString)
  | continue_ (label : Option NEString)
  /-- `class name extends heritage implements … { body }` as a
  declaration. -/
  | classDecl (decorators : List MiniExpr) (isAbstract : Bool) (name : NEString)
      (typeParams : List MiniTsTypeParam) (heritage : Option MiniClassHeritage)
      (implements_ : List MiniTsHeritage) (body : List MiniClassElement)
  /-- `var`/`let`/`const` declaration; it declares at least one name. -/
  | decl (kind : VarKind) (decls : NEList MiniDeclarator)
  /-- `using x = e;` and `await using x = e;`, the explicit resource
  management declarations; `isAwait` selects the second. -/
  | using_ (isAwait : Bool) (decls : NEList MiniDeclarator)
  /-- `debugger;` -/
  | debugger
  | doWhile (body : MiniStatement) (cond : MiniExpr)
  | for_ (init : MiniForInit) (cond : Option MiniExpr) (step : Option MiniExpr)
      (body : MiniStatement)
  | forIn (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  /-- `for (head of obj) body`, and `for await (head of obj) body` when
  `isAwait` is set. -/
  | forOf (isAwait : Bool) (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  /-- A function declaration.  A declaration with no body is an overload
  signature, `function f(a: string): void;`. -/
  | funcDecl (isAsync : Bool) (isGenerator : Bool) (name : NEString)
      (typeParams : List MiniTsTypeParam) (params : List MiniParam)
      (retType : Option MiniTsType) (body : Option (List MiniStatement))
  | if_ (cond : MiniExpr) (thenS : MiniStatement) (elseS : Option MiniStatement)
  | labelled (label : NEString) (stmt : MiniStatement)
  | empty
  /-- An expression statement. -/
  | expr (expr : MiniExpr)
  | return_ (expr : Option MiniExpr)
  | switch (disc : MiniExpr) (cases : List MiniSwitchCase)
  | throw (expr : MiniExpr)
  | try_ (body : List MiniStatement) (tail : MiniTryTail)
  | while_ (cond : MiniExpr) (body : MiniStatement)
  | with_ (obj : MiniExpr) (body : MiniStatement)
  /-- `type Name<T> = T;` -/
  | typeAlias (name : NEString) (typeParams : List MiniTsTypeParam) (type : MiniTsType)
  /-- `interface Name<T> extends A, B { … }` -/
  | interface_ (name : NEString) (typeParams : List MiniTsTypeParam)
      (extends_ : List MiniTsHeritage) (members : List MiniTsTypeMember)
  /-- `enum E { A = 1 }`, and `const enum E { … }` when `isConst` is set. -/
  | enum_ (isConst : Bool) (name : NEString) (members : List MiniTsEnumMember)
  /-- `namespace N.M { … }`, `module "foo" { … }` and `global { … }`;
  `isModuleKeyword` writes a named namespace with the `module` keyword.
  A body of `none` writes the declaration with no body at all,
  `declare module "foo";`, which TypeScript only allows for an ambient
  module named by a string. -/
  | namespaceDecl (isModuleKeyword : Bool) (name : TsNamespaceName)
      (body : Option (List MiniModuleItem))
  /-- `declare <declaration>`, the ambient form of a declaration. -/
  | declare_ (stmt : MiniStatement)

/-- An `export` declaration. -/
inductive MiniExportDeclaration where
  /-- `export { a } from "mod";`, possibly with import attributes;
  `isType` writes it as `export type { a } from "mod";`. -/
  | fromClause (isType : Bool) (specs : List TsSpecifier) (mod : NEString)
      (attrs : List ImportAttr)
  /-- `export { a };`, and `export type { a };`. -/
  | locals (isType : Bool) (specs : List TsSpecifier)
  /-- `export * from "mod";` and `export * as ns from "mod";`; `alias_` is
  the `ns` of the second form, and `isType` writes it as
  `export type * from "mod";`. -/
  | all (isType : Bool) (alias_ : Option NEString) (mod : NEString) (attrs : List ImportAttr)
  /-- `export default <expression>;` -/
  | defaultExpr (expr : MiniExpr)
  /-- `export default <declaration>`, for the declarations that are no
  expression: an `interface`, and an `abstract class`. -/
  | defaultDecl (stmt : MiniStatement)
  /-- `export <declaration>` -/
  | decl (stmt : MiniStatement)
  /-- `export = expr;`, the TypeScript export assignment. -/
  | assign (expr : MiniExpr)
  /-- `export as namespace N;` -/
  | asNamespace (name : NEString)

/-- A top level item: a statement, or an `import`/`export` declaration. -/
inductive MiniModuleItem where
  | stmt (stmt : MiniStatement)
  | importDecl (decl : MiniImportDeclaration)
  | exportDecl (decl : MiniExportDeclaration)

end

/-! ## Default values -/

instance : Inhabited MiniExpr := ⟨.null⟩
instance : Inhabited MiniTsType := ⟨.ref (.ident default) []⟩
instance : Inhabited MiniTsTupleElem := ⟨.elem default⟩
instance : Inhabited MiniTsTemplatePart := ⟨⟨default, ""⟩⟩
instance : Inhabited MiniTsTypeMember := ⟨.property false (.ident default) false none⟩
instance : Inhabited MiniTsTypeParam := ⟨⟨false, none, default, none, none⟩⟩
instance : Inhabited MiniTsHeritage := ⟨⟨.ident default, []⟩⟩
instance : Inhabited MiniClassHeritage := ⟨⟨default, []⟩⟩
instance : Inhabited MiniStatement := ⟨.empty⟩
instance : Inhabited MiniPattern := ⟨.ident default⟩
instance : Inhabited MiniArrayPatternElem := ⟨.hole⟩
instance : Inhabited MiniObjectPatternProp := ⟨⟨.ident default, .ident default⟩⟩
instance : Inhabited MiniChainLink := ⟨.dot true default⟩
instance : Inhabited MiniJSXNode := ⟨.fragment []⟩
instance : Inhabited MiniJSXAttribute := ⟨.attr (.ident default) none⟩
instance : Inhabited MiniJSXAttrValue := ⟨.string ""⟩
instance : Inhabited MiniJSXChild := ⟨.text ""⟩
instance : Inhabited MiniParam := ⟨.plain [] {} (.ident default) false none⟩
instance : Inhabited MiniArrayElement := ⟨.hole⟩
instance : Inhabited MiniArrowBody := ⟨.block []⟩
instance : Inhabited MiniTemplatePart := ⟨⟨default, ""⟩⟩
instance : Inhabited MiniPropertyName := ⟨.ident default⟩
instance : Inhabited MiniProperty := ⟨.shorthand default⟩
instance : Inhabited MiniClassElement := ⟨.staticBlock []⟩
instance : Inhabited MiniDeclarator := ⟨⟨.ident default, false, none, none⟩⟩
instance : Inhabited MiniTsEnumMember := ⟨⟨.ident default, none⟩⟩
instance : Inhabited MiniForInit := ⟨.none⟩
instance : Inhabited MiniForHead := ⟨.pattern default⟩
instance : Inhabited MiniSwitchCase := ⟨.default []⟩
instance : Inhabited MiniCatchClause := ⟨⟨.ident default, none, none, []⟩⟩
instance : Inhabited MiniFinallyClause := ⟨.none⟩
instance : Inhabited MiniTryTail := ⟨.finallyOnly []⟩
instance : Inhabited MiniExportDeclaration := ⟨.locals false []⟩
instance : Inhabited MiniModuleItem := ⟨.stmt default⟩

/-- A whole program: a list of top level items. -/
structure MiniProgram where
  /-- The top level items. -/
  items : List MiniModuleItem
deriving Inhabited

/-! ## Equality -/

deriving instance BEq for MiniExpr, MiniStatement, MiniModuleItem, MiniTsType

instance : BEq MiniProgram := ⟨fun a b => a.items == b.items⟩

/-! ## Convenience -/

namespace MiniParam

/-- An ordinary parameter with no decorators, no modifiers, no `?` and
no type. -/
def simple (pat : MiniPattern) : MiniParam := .plain [] {} pat false none

/-- An ordinary parameter with a type annotation. -/
def typed (pat : MiniPattern) (type : MiniTsType) : MiniParam :=
  .plain [] {} pat false (some type)

/-- The decorators the parameter is written with. -/
def decorators : MiniParam → List MiniExpr
  | .plain ds _ _ _ _ | .rest ds _ _ => ds

end MiniParam

end Language.TypeScript.MiniTsAST
