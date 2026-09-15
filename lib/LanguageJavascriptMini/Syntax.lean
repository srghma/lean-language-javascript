import MiniAST.Doc


/-! ## Refined component types -/

namespace Language.JavaScript

/-! ## Non-empty strings -/

/-- A string that is known not to be empty. -/
structure NEString where
  /-- The characters of the string. -/
  val : String
  /-- The proof that makes the type non-trivial. -/
  ne : val ≠ ""
deriving DecidableEq

namespace NEString

instance : Inhabited NEString := ⟨⟨"_", by decide⟩⟩
instance : Repr NEString := ⟨fun s _ => repr s.val⟩
instance : ToString NEString := ⟨fun s => s.val⟩
instance : Hashable NEString := ⟨fun s => hash s.val⟩

/-- The non-empty string `s`, or `none` if `s` is empty. -/
def ofString? (s : String) : Option NEString :=
  if h : s ≠ "" then some ⟨s, h⟩ else none

/-- The non-empty string `s`; a placeholder if `s` is empty. -/
def ofString! (s : String) : NEString :=
  if h : s ≠ "" then ⟨s, h⟩ else default

end NEString

/-! ## Non-empty lists -/

/-- A list that is known not to be empty. -/
structure NEList (α : Type) where
  /-- The first element. -/
  hd : α
  /-- The remaining elements. -/
  tl : List α
deriving Repr, BEq, DecidableEq, Inhabited

namespace NEList

variable {α β : Type}

/-- The elements, as an ordinary list. -/
def toList (l : NEList α) : List α := l.hd :: l.tl

/-- A non-empty list from a list, or `none` if it is empty. -/
def ofList? : List α → Option (NEList α)
  | [] => none
  | a :: as => some ⟨a, as⟩

/-- A non-empty list from a list; a singleton placeholder if it is empty. -/
def ofList! [Inhabited α] : List α → NEList α
  | [] => ⟨default, []⟩
  | a :: as => ⟨a, as⟩

end NEList

/-! ## Numeric literals -/

/-- The base a numeric literal is written in. -/
inductive NumBase where
  /-- `0b1010` -/
  | binary
  /-- `0o17`, and the legacy `017` -/
  | octal
  /-- `17`, `1.5`, `1e3` -/
  | decimal
  /-- `0xff` -/
  | hexadecimal
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace NumBase

/-- The radix: 2, 8, 10 or 16. -/
def radix : NumBase → Nat
  | .binary => 2
  | .octal => 8
  | .decimal => 10
  | .hexadecimal => 16

/-- The `0b`/`0o`/`0x` prefix a literal in this base is written with; base
ten literals have none. -/
def prefixText : NumBase → String
  | .binary => "0b"
  | .octal => "0o"
  | .decimal => ""
  | .hexadecimal => "0x"

end NumBase

/-- A JavaScript numeric literal: decimal, radix (base 2/8/16), or BigInt. -/
inductive JSNumber where
  /-- A base ten literal denoting exactly `mantissa * 10 ^ exponent`. -/
  | decimal (mantissa : Nat) (exponent : Int)
  /-- A literal in base two, eight or sixteen. -/
  | radix (base : NumBase) (value : Nat)
  /-- A `BigInt` literal, written in `base`. -/
  | bigint (base : NumBase) (value : Nat)
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace JSNumber

/-- Strip the trailing zeros of a base ten mantissa, moving them into the exponent. -/
private def stripZerosAux : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | fuel + 1, m, e => if m % 10 == 0 then stripZerosAux fuel (m / 10) (e + 1) else (m, e)

/-- Strip the trailing zeros of a base ten mantissa, moving them into the
exponent. -/
private def stripZeros (m : Nat) (e : Int) : Nat × Int :=
  if m == 0 then (0, 0) else stripZerosAux m m e

/-- The canonical form of a literal: the mantissa of a base ten literal has
no trailing zeros, zero is `decimal 0 0`, and a base ten `radix` literal is
a `decimal` one. -/
def normalize : JSNumber → JSNumber
  | .decimal m e => let (m', e') := stripZeros m e; .decimal m' e'
  | .radix .decimal v => let (m', e') := stripZeros v 0; .decimal m' e'
  | .radix b v => .radix b v
  | .bigint b v => .bigint b v

/-- The literal denoting the natural number `n` in base ten. -/
def ofNat (n : Nat) : JSNumber := normalize (.decimal n 0)

instance : OfNat JSNumber n := ⟨ofNat n⟩

/-! ### Rendering -/

/-- The character a digit of value `d < 16` is written with. -/
def digitChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)

/-- The digits of `n` in base `base`, most significant first. -/
def digitsAux (base : Nat) : Nat → Nat → String → String
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      let rest := n / base
      let acc := if rest == 0 then acc else digitsAux base fuel rest acc
      acc.push (digitChar (n % base))

/-- The spelling of `n` in base `base`. -/
def digitsOf (base : Nat) (n : Nat) : String :=
  if n == 0 then "0" else digitsAux base (n + 1) n ""

private def repeatChar (c : Char) (n : Nat) : String := String.pushn "" c n

/-- Render a base ten literal. -/
private def renderDecimal (mantissa : Nat) (exponent : Int) : String :=
  if mantissa == 0 then "0"
  else
    let s := digitsOf 10 mantissa
    let k : Int := Int.ofNat s.length
    -- the value is `0.s * 10 ^ n`
    let n : Int := k + exponent
    if k ≤ n && n ≤ 21 then
      s ++ repeatChar '0' (n - k).toNat
    else if 0 < n && n ≤ 21 then
      -- a digit is one byte wide, so the point falls at the byte index `n`
      String.Pos.Raw.extract s ⟨0⟩ ⟨n.toNat⟩ ++ "." ++
        String.Pos.Raw.extract s ⟨n.toNat⟩ ⟨s.utf8ByteSize⟩
    else if -6 < n && n ≤ 0 then
      "0." ++ repeatChar '0' (-n).toNat ++ s
    else
      let head := String.Pos.Raw.extract s ⟨0⟩ ⟨1⟩
      let tail := String.Pos.Raw.extract s ⟨1⟩ ⟨s.utf8ByteSize⟩
      let e := n - 1
      (if tail.isEmpty then head else head ++ "." ++ tail) ++ "e" ++
        (if e < 0 then "-" ++ toString (-e) else toString e)

/-- The canonical spelling of the literal.  Letters are lower case, there
are no superfluous zeros, and the value is not changed. -/
def render (x : JSNumber) : String :=
  match x.normalize with
  | .decimal m e => renderDecimal m e
  | .radix b v => b.prefixText ++ digitsOf b.radix v
  | .bigint b v => b.prefixText ++ digitsOf b.radix v ++ "n"


instance : ToString JSNumber := ⟨render⟩

end JSNumber

/-! ## Regular expression literals -/

/-- The flags of a regular expression literal. -/
structure RegExpFlags where
  /-- `d`, `hasIndices`. -/
  hasIndices : Bool := false
  /-- `g`, `global`.  A global regular expression object is stateful. -/
  global : Bool := false
  /-- `i`, `ignoreCase`. -/
  ignoreCase : Bool := false
  /-- `m`, `multiline`. -/
  multiline : Bool := false
  /-- `s`, `dotAll`. -/
  dotAll : Bool := false
  /-- `u`, `unicode`. -/
  unicode : Bool := false
  /-- `v`, `unicodeSets`. -/
  unicodeSets : Bool := false
  /-- `y`, `sticky`.  A sticky regular expression object is stateful. -/
  sticky : Bool := false
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace RegExpFlags

/-- The flags, in the canonical order `dgimsuvy`. -/
def render (f : RegExpFlags) : String :=
  (if f.hasIndices then "d" else "") ++
  (if f.global then "g" else "") ++
  (if f.ignoreCase then "i" else "") ++
  (if f.multiline then "m" else "") ++
  (if f.dotAll then "s" else "") ++
  (if f.unicode then "u" else "") ++
  (if f.unicodeSets then "v" else "") ++
  (if f.sticky then "y" else "")

instance : ToString RegExpFlags := ⟨render⟩

end RegExpFlags

/-- A regular expression literal: the pattern between the slashes, and the
flags after the closing one. -/
structure RegExpLit where
  /-- The pattern, without the delimiting slashes.  It cannot be empty:
  `//` starts a comment, and an empty pattern is written `/(?:)/`. -/
  source : NEString
  /-- The flags. -/
  flags : RegExpFlags := {}
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace RegExpLit

/-- The literal, as it is written in source: `/source/flags`. -/
def render (r : RegExpLit) : String :=
  "/" ++ r.source.val ++ "/" ++ r.flags.render

instance : ToString RegExpLit := ⟨render⟩

end RegExpLit

/-! ## Component types -/

/-! ## Operators -/

/-- Binary operators. -/
inductive BinOp where
  | and | or
  /-- `??`, the nullish coalescing operator. -/
  | coalesce
  | bitAnd | bitOr | bitXor
  | eq | neq | strictEq | strictNeq
  | lt | le | gt | ge
  | lsh | rsh | ursh
  | plus | minus | times | divide | mod
  | inOp | instanceOf
deriving Repr, BEq, DecidableEq, Inhabited

/-- Prefix operators. -/
inductive UnaryOp where
  | not | tilde | plus | minus
  | typeof | void | delete
  | preIncr | preDecr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Postfix operators. -/
inductive PostfixOp where
  | incr | decr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Assignment operators. -/
inductive AssignOp where
  | assign
  | plus | minus | times | divide | mod
  | lsh | rsh | ursh
  | bitAnd | bitXor | bitOr
  /-- `&&=` -/
  | logicalAnd
  /-- `||=` -/
  | logicalOr
  /-- `??=` -/
  | coalesce
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword introducing a variable declaration. -/
inductive VarKind where
  | var | let_ | const
deriving Repr, BEq, DecidableEq, Inhabited

/-- What kind of method a member of an object or class literal is. -/
inductive MethodKind where
  /-- `m() {}` -/
  | normal
  /-- `*m() {}` -/
  | generator
  /-- `async m() {}` -/
  | async
  /-- `async *m() {}` -/
  | asyncGenerator
  /-- `get m() {}` -/
  | get
  /-- `set m(v) {}` -/
  | set
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Import and export clauses -/

/-- One `name` or `name as alias` of an import or export clause. -/
structure Specifier where
  /-- The exported name. -/
  name : NEString
  /-- The local name, when it differs. -/
  alias_ : Option NEString
deriving Repr, BEq, DecidableEq, Inhabited

/-- One import attribute, e.g. `type: "json"`. -/
structure ImportAttr where
  /-- The key. -/
  key : String
  /-- The value. -/
  value : String
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## JSX names -/

/-- The name of a JSX element, or of one of its attributes: a plain name,
a member of a name (`Foo.Bar`, which only an element has), or a namespaced
name (`svg:path`). -/
inductive JSXName where
  /-- `div`, `Foo`, `data-id` -/
  | ident (name : NEString)
  /-- `Foo.Bar` -/
  | member (obj : JSXName) (name : NEString)
  /-- `svg:path` -/
  | namespaced (ns : NEString) (name : NEString)
deriving Repr, BEq, DecidableEq, Inhabited

namespace JSXName

/-- The name, as it is written in source. -/
def render : JSXName → String
  | .ident n => n.val
  | .member o n => o.render ++ "." ++ n.val
  | .namespaced ns n => ns.val ++ ":" ++ n.val

instance : ToString JSXName := ⟨render⟩

end JSXName

end Language.JavaScript

namespace Language.JavaScript.MiniAST

/-! ## Imports -/

/-- `import def, * as ns, { a, b as c } from "mod";`.  Each of the three
clauses is optional, but at least one of them has to be there. -/
structure MiniImportClause where
  /-- The default import, `import def from "mod"`. -/
  default_ : Option NEString
  /-- The namespace import, `import * as ns from "mod"`. -/
  namespace_ : Option NEString
  /-- The named imports, `import { a, b as c } from "mod"`. -/
  named : Option (List Specifier)
  /-- The module the names come from. -/
  mod : NEString
  /-- The import attributes, `with { type: "json" }`. -/
  attrs : List ImportAttr := []
  /-- An import must bind something. -/
  binds : default_.isSome ∨ namespace_.isSome ∨ named.isSome
deriving DecidableEq

instance : Inhabited MiniImportClause :=
  ⟨{ default_ := some default, namespace_ := .none, named := .none, mod := default,
     attrs := [], binds := Or.inl rfl }⟩

namespace MiniImportClause

/-- Build an import clause, checking that it binds something. -/
def mk? (default_ namespace_ : Option NEString) (named : Option (List Specifier))
    (mod : NEString) (attrs : List ImportAttr := []) : Option MiniImportClause :=
  if h : default_.isSome ∨ namespace_.isSome ∨ named.isSome then
    some ⟨default_, namespace_, named, mod, attrs, h⟩
  else
    Option.none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (default_ namespace_ : Option NEString) (named : Option (List Specifier))
    (mod : NEString) (attrs : List ImportAttr := []) : MiniImportClause :=
  (mk? default_ namespace_ named mod attrs).getD default

end MiniImportClause

/-- An `import` declaration. -/
inductive MiniImportDeclaration where
  /-- `import "mod";`, possibly with import attributes. -/
  | bare (mod : NEString) (attrs : List ImportAttr)
  /-- `import ... from "mod";` -/
  | clause (clause : MiniImportClause)
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
  /-- `callee(args)` -/
  | call (callee : MiniExpr) (args : List MiniExpr)
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
      (heritage : Option MiniExpr) (body : List MiniClassElement)
  /-- The comma operator, `lhs, rhs`. -/
  | seq (lhs : MiniExpr) (rhs : MiniExpr)
  | binary (lhs : MiniExpr) (op : BinOp) (rhs : MiniExpr)
  | postfix (expr : MiniExpr) (op : PostfixOp)
  /-- `cond ? thenE : elseE` -/
  | ternary (cond : MiniExpr) (thenE : MiniExpr) (elseE : MiniExpr)
  /-- `(params) => body`, and `async (params) => body` when `isAsync` is
  set. -/
  | arrow (isAsync : Bool) (params : List MiniParam) (body : MiniArrowBody)
  /-- A function expression; `isAsync` and `isGenerator` select `async` and `*`. -/
  | func (isAsync : Bool) (isGenerator : Bool) (name : Option NEString)
      (params : List MiniParam) (body : List MiniStatement)
  /-- `new callee(args)` -/
  | new (callee : MiniExpr) (args : List MiniExpr)
  /-- `...expr` -/
  | spread (expr : MiniExpr)
  /-- A template literal: an optional tag, the text before the first
  substitution, and one part per substitution. -/
  | template (tag : Option MiniExpr) (head : String) (parts : List MiniTemplatePart)
  | unary (op : UnaryOp) (expr : MiniExpr)
  /-- `yield expr` -/
  | yield (expr : Option MiniExpr)
  /-- `yield* expr` -/
  | yieldFrom (expr : MiniExpr)
  /-- A JSX element or fragment, `<div />` or `<>...</>`. -/
  | jsx (node : MiniJSXNode)

/-- A JSX element or fragment. -/
inductive MiniJSXNode where
  /-- `<name attrs>children</name>`, and `<name attrs />` when `children`
  is `none`. -/
  | element (name : JSXName) (attrs : List MiniJSXAttribute)
      (children : Option (List MiniJSXChild))
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

/-- One link of an optional chain: a member access or a call, `optional`
saying whether it is written with `?.`. -/
inductive MiniChainLink where
  /-- `.name` or `?.name` -/
  | dot (optional : Bool) (name : NEString)
  /-- `.#name` or `?.#name` -/
  | privateDot (optional : Bool) (name : NEString)
  /-- `[idx]` or `?.[idx]` -/
  | index (optional : Bool) (idx : MiniExpr)
  /-- `(args)` or `?.(args)` -/
  | call (optional : Bool) (args : List MiniExpr)

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
parameter, which JavaScript only allows last. -/
inductive MiniParam where
  /-- An ordinary parameter, `x`, `x = 1` or `{ a, b }`. -/
  | plain (pat : MiniPattern)
  /-- `...rest` -/
  | rest (pat : MiniPattern)

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
  | method (kind : MethodKind) (key : MiniPropertyName) (params : List MiniParam)
      (body : List MiniStatement)

/-- A member of a class body: a method, a field or a static block. -/
inductive MiniClassElement where
  /-- A method, a generator, a getter or a setter. -/
  | method (decorators : List MiniExpr) (isStatic : Bool) (kind : MethodKind)
      (key : MiniPropertyName) (params : List MiniParam) (body : List MiniStatement)
  /-- A field, `x = 1;`, `#x;` or `static x = 1;`; `isAccessor` writes it
  with the `accessor` keyword, as `accessor x = 1;`. -/
  | field (decorators : List MiniExpr) (isStatic : Bool) (isAccessor : Bool)
      (key : MiniPropertyName) (init : Option MiniExpr)
  /-- A static initialisation block, `static { ... }`. -/
  | staticBlock (body : List MiniStatement)

/-- One declarator of a `var`/`let`/`const` statement. -/
structure MiniDeclarator where
  /-- The name, or destructuring pattern, being bound. -/
  lhs : MiniPattern
  /-- The initialiser, if any. -/
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
  /-- `class name extends heritage { body }` as a declaration. -/
  | classDecl (decorators : List MiniExpr) (name : NEString) (heritage : Option MiniExpr)
      (body : List MiniClassElement)
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
  | funcDecl (isAsync : Bool) (isGenerator : Bool) (name : NEString)
      (params : List MiniParam) (body : List MiniStatement)
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

/-- An `export` declaration. -/
inductive MiniExportDeclaration where
  /-- `export { a } from "mod";`, possibly with import attributes. -/
  | fromClause (specs : List Specifier) (mod : NEString) (attrs : List ImportAttr)
  /-- `export { a };` -/
  | locals (specs : List Specifier)
  /-- `export * from "mod";` and `export * as ns from "mod";`; `alias_` is
  the `ns` of the second form. -/
  | all (alias_ : Option NEString) (mod : NEString) (attrs : List ImportAttr)
  /-- `export default <expression>;` -/
  | defaultExpr (expr : MiniExpr)
  /-- `export <declaration>` -/
  | decl (stmt : MiniStatement)

/-- A top level item: a statement, or an `import`/`export` declaration. -/
inductive MiniModuleItem where
  | stmt (stmt : MiniStatement)
  | importDecl (decl : MiniImportDeclaration)
  | exportDecl (decl : MiniExportDeclaration)

end

/-! ## Default values -/

instance : Inhabited MiniExpr := ⟨.null⟩
instance : Inhabited MiniStatement := ⟨.empty⟩
instance : Inhabited MiniPattern := ⟨.ident default⟩
instance : Inhabited MiniArrayPatternElem := ⟨.hole⟩
instance : Inhabited MiniObjectPatternProp := ⟨⟨.ident default, .ident default⟩⟩
instance : Inhabited MiniChainLink := ⟨.dot true default⟩
instance : Inhabited MiniJSXNode := ⟨.fragment []⟩
instance : Inhabited MiniJSXAttribute := ⟨.attr (.ident default) none⟩
instance : Inhabited MiniJSXAttrValue := ⟨.string ""⟩
instance : Inhabited MiniJSXChild := ⟨.text ""⟩
instance : Inhabited MiniParam := ⟨.plain (.ident default)⟩
instance : Inhabited MiniArrayElement := ⟨.hole⟩
instance : Inhabited MiniArrowBody := ⟨.block []⟩
instance : Inhabited MiniTemplatePart := ⟨⟨default, ""⟩⟩
instance : Inhabited MiniPropertyName := ⟨.ident default⟩
instance : Inhabited MiniProperty := ⟨.shorthand default⟩
instance : Inhabited MiniClassElement := ⟨.staticBlock []⟩
instance : Inhabited MiniDeclarator := ⟨⟨.ident default, none⟩⟩
instance : Inhabited MiniForInit := ⟨.none⟩
instance : Inhabited MiniForHead := ⟨.pattern default⟩
instance : Inhabited MiniSwitchCase := ⟨.default []⟩
instance : Inhabited MiniCatchClause := ⟨⟨.ident default, none, []⟩⟩
instance : Inhabited MiniFinallyClause := ⟨.none⟩
instance : Inhabited MiniTryTail := ⟨.finallyOnly []⟩
instance : Inhabited MiniExportDeclaration := ⟨.locals []⟩
instance : Inhabited MiniModuleItem := ⟨.stmt default⟩

/-- A whole program: a list of top level items. -/
structure MiniProgram where
  /-- The top level items. -/
  items : List MiniModuleItem
deriving Inhabited

/-! ## Equality -/

deriving instance BEq for MiniExpr, MiniStatement, MiniModuleItem

instance : BEq MiniProgram := ⟨fun a b => a.items == b.items⟩

/-! ## String literals -/

/-- Push the spelling of `c` in a literal quoted with `quote` onto `acc`. -/
private def pushEscaped (quote : Char) (acc : String) (c : Char) : String :=
  if c == quote then (acc.push '\\').push quote
  else if c == '\\' then (acc.push '\\').push '\\'
  else if c == '\n' then (acc.push '\\').push 'n'
  else if c == '\r' then (acc.push '\\').push 'r'
  else if c == '\t' then (acc.push '\\').push 't'
  else if c.toNat == 8 then (acc.push '\\').push 'b'
  else if c.toNat == 12 then (acc.push '\\').push 'f'
  else if c.toNat == 11 then (acc.push '\\').push 'v'
  else if c.toNat < 0x20 || c.toNat == 0x7F then
    let hex := Nat.toDigits 16 c.toNat
    let acc := (acc.push '\\').push 'x'
    let acc := if hex.length == 1 then acc.push '0' else acc
    hex.foldl (fun acc d => acc.push d) acc
  else acc.push c

/-- The quote a literal holding `value` is written with, given the quote
that is preferred (prettier's `singleQuote` chooses which that is): the
preferred one, unless the value holds more of it than of the other, in
which case writing the other escapes fewer characters. -/
def quoteFor (preferred : Char) (value : String) : Char :=
  let other := if preferred == '"' then '\'' else '"'
  let (pref, alt) :=
    value.foldl (fun (n : Nat × Nat) c =>
      if c == preferred then (n.1 + 1, n.2) else if c == other then (n.1, n.2 + 1) else n) (0, 0)
  if pref > alt then other else preferred

/-- Render a string value as a JavaScript literal, preferring `preferred`
as its quote. -/
def encodeStringLiteralQuoted (preferred : Char) (value : String) : String :=
  let quote := quoteFor preferred value
  (value.foldl (pushEscaped quote) (String.singleton quote)).push quote

/-- Render a string value as a JavaScript literal, with double quotes
preferred, which is prettier's default. -/
def encodeStringLiteral (value : String) : String :=
  encodeStringLiteralQuoted '"' value

/-! ## JSX text and attribute values -/

/-- Render the text of a JSX child, which holds the characters it denotes,
as it is written between the tags: the characters a parser would read as
markup, or as an entity, are written as entities themselves. -/
def encodeJSXText (value : String) : String :=
  value.foldl (fun acc c =>
    if c == '&' then acc ++ "&amp;"
    else if c == '<' then acc ++ "&lt;"
    else if c == '>' then acc ++ "&gt;"
    else if c == '{' then acc ++ "&#123;"
    else if c == '}' then acc ++ "&#125;"
    else acc.push c) ""

/-- Render the value of a JSX attribute as a quoted literal.  The quote is
the one that has to be written as an entity the fewer times, double quotes
when it is a draw, as prettier chooses it; the occurrences of that quote,
and every ampersand, are written as entities. -/
def encodeJSXAttrStringQuoted (preferred : Char) (value : String) : String :=
  let quote := quoteFor preferred value
  let body := value.foldl (fun acc c =>
    if c == '&' then acc ++ "&amp;"
    else if c == quote then acc ++ (if quote == '"' then "&quot;" else "&apos;")
    else acc.push c) ""
  (String.singleton quote ++ body).push quote

/-- Render the value of a JSX attribute with double quotes preferred,
which is prettier's default. -/
def encodeJSXAttrString (value : String) : String :=
  encodeJSXAttrStringQuoted '"' value

/-! ## Template literal text -/

/-- Render the text of a template literal, which holds the characters it
denotes, as it is written between the backticks: a backslash, a backtick
and the `${` which would start a substitution are escaped, and so is a
carriage return, which a parser would otherwise read as a line feed.  A
line feed itself stands as it is: a template literal may span lines. -/
def encodeTemplateText (value : String) : String :=
  go value.toList ""
where
  /-- The characters still to be written, and what has been written. -/
  go : List Char → String → String
    | [], acc => acc
    | '\\' :: cs, acc => go cs ((acc.push '\\').push '\\')
    | '`' :: cs, acc => go cs ((acc.push '\\').push '`')
    | '\r' :: cs, acc => go cs ((acc.push '\\').push 'r')
    | '$' :: '{' :: cs, acc => go cs (((acc.push '\\').push '$').push '{')
    | c :: cs, acc => go cs (acc.push c)

end Language.JavaScript.MiniAST
