/-
A *deterministic* JavaScript AST.

`RequestProject.JavaScript.AST` is a faithful port of the Haskell
`language-javascript` AST: every node carries a `JSAnnot` recording the
source position and the comments and whitespace that preceded the token, so
that the printer can reproduce the layout of the input.  Two programs which
differ only in layout (`import  def  from 'mod'` versus `import def from
"mod"`) have *different* ASTs there.

`MiniAST` is the opposite: it stores only the meaning of the program.

* there are no annotations, so no positions, no comments and no whitespace;
* redundant syntax is normalised away — parentheses (the printer puts them
  back where the precedence requires them), automatic versus explicit
  semicolons, `new X` versus `new X()`, and the two spellings of a call;
* string literals hold their *decoded* value rather than the source text,
  and numeric literals are normalised.

Consequently the AST is *deterministic*: two sources that mean the same
thing give equal `MiniAST` values, and `MiniASTPrinter` turns a value back
into one canonical, opinionated rendering of it.

The types are also more precise than the annotated ones: a name is an
`NEString`, a string which carries a proof that it is not `""`; a numeric
literal is a `JSNumber` and a string literal holds the characters it
denotes; a `var` statement holds an `NEList` of declarators, which cannot
be empty; what a parameter, a declarator, the head of a `for ... of` or the
binder of a `catch` binds is a `MiniPattern` — a name, a destructuring
pattern, or either of those with a default value — rather than an arbitrary
expression, and a parameter is a `MiniParam`, a pattern which may be the
rest parameter; a `try` statement cannot be written without a `catch` and a
`finally`; `super` is only expressible in the three forms JavaScript allows
it in, `super.x`, `super[i]` and `super(...)`, each of which is a node of
its own; and every node with a single shape is a `structure` rather than
a one constructor inductive.
-/

import LanguageJavascript.Common

namespace Language.JavaScript.MiniAST

/-! ## Component types

`NEString`, `NEList`, `JSNumber` and `RegExpLit` are the refined types of
`Language.JavaScript.Types`, and the operators, `VarKind`, `MethodKind`,
`Specifier` and `ImportAttr` — the leaf types this tree shares with the
scope safe tree — are those of `Language.JavaScript.Common`.  Both live in
`Language.JavaScript`, the parent namespace of this one, so they are in
scope without an `open`. -/

/-! ## Imports

An `import` declaration is not recursive, so — unlike the syntax tree
below — its invariant can be stated as a proof carrying field. -/

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
  /-- An optional chain: a base expression followed by one or more links,
  at least one of which is optional (`a?.b`, `a?.[i]`, `f?.(x)`).  The
  whole chain is one node, so that the difference between `(a?.b).c` and
  `a?.b.c` — the first evaluates `.c` even when `a` is nullish — is
  recorded. -/
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
  /-- `(params) => body` -/
  | arrow (params : List MiniParam) (body : MiniArrowBody)
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

/-- A binding pattern: what a parameter, a declarator, the head of a
`for ... of` or the binder of a `catch` binds.  It is a grammar of its own
rather than an arbitrary expression, so a default value and a destructuring
pattern are first class. -/
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
  /-- A field, `x = 1;`, `#x;` or `static x = 1;`. -/
  | field (decorators : List MiniExpr) (isStatic : Bool) (key : MiniPropertyName)
      (init : Option MiniExpr)
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
  | doWhile (body : MiniStatement) (cond : MiniExpr)
  | for_ (init : MiniForInit) (cond : Option MiniExpr) (step : Option MiniExpr)
      (body : MiniStatement)
  | forIn (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  | forOf (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
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

/-! ## Default values

As for the annotated AST, `Inhabited` cannot be derived for the mutually
recursive types, so the instances are given by hand. -/

instance : Inhabited MiniExpr := ⟨.null⟩
instance : Inhabited MiniStatement := ⟨.empty⟩
instance : Inhabited MiniPattern := ⟨.ident default⟩
instance : Inhabited MiniArrayPatternElem := ⟨.hole⟩
instance : Inhabited MiniObjectPatternProp := ⟨⟨.ident default, .ident default⟩⟩
instance : Inhabited MiniChainLink := ⟨.dot true default⟩
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

/-! ## Equality

The point of the deterministic AST is that equal programs give equal values,
so the tree carries `BEq`. -/

deriving instance BEq for MiniExpr, MiniStatement, MiniModuleItem

instance : BEq MiniProgram := ⟨fun a b => a.items == b.items⟩

/-! ## String literals

A `MiniExpr.string` holds the characters the literal denotes, so that
`'a\n'` and `"a\u000a"` give the same node.  `decodeStringLiteral` performs
that decoding and `encodeStringLiteral` produces a literal again. -/

/-! A literal is decoded, and a value encoded, *in place*: the source is
read by byte index and the result is built by pushing characters onto it, so
neither string is ever turned into a list of characters, and no intermediate
list or string is built.

Every scanning function takes a `fuel` argument bounding the number of
characters left to read; the number of bytes left is always enough, since
every step consumes at least one byte. -/

private def isHighSurrogate (n : Nat) : Bool := 0xD800 ≤ n && n ≤ 0xDBFF
private def isLowSurrogate (n : Nat) : Bool := 0xDC00 ≤ n && n ≤ 0xDFFF

/-- The value of the `count` hexadecimal digits of `raw` at the byte index
`p`, and the index just after them; `none` if there are fewer than `count`
characters left, or one of them is not a digit. -/
private def hexRun? (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → Nat → Option (Nat × String.Pos.Raw)
  | 0, p, acc => some (acc, p)
  | count + 1, p, acc =>
      if stop ≤ p.byteIdx then none
      else
        match JSNumber.digitVal? (String.Pos.Raw.get raw p) with
        | none => none
        | some d => hexRun? raw stop count (String.Pos.Raw.next raw p) (16 * acc + d)

/-- The value of the hexadecimal digits of `raw` from the byte index `p` up
to a `}`, and the index just after the `}`; `none` if there is no digit, a
character which is not one, or no closing brace. -/
private def hexBrace? (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → Nat → Bool → Option (Nat × String.Pos.Raw)
  | 0, _, _, _ => none
  | fuel + 1, p, acc, any =>
      if stop ≤ p.byteIdx then none
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '}' then (if any then some (acc, q) else none)
        else
          match JSNumber.digitVal? c with
          | none => none
          | some d => hexBrace? raw stop fuel q (16 * acc + d) true

/-- The escape sequence written in `raw` at the byte index `p`, `bs` being
the index of the backslash which starts it: the characters it denotes,
pushed onto `acc`, and the index just after the sequence.  An unknown escape
stands for the escaped character itself, and an escape denoting no character
at all stands for the text it is written with. -/
private def decodeEscapeAt (raw : String) (stop : Nat) (bs p : String.Pos.Raw) (acc : String) :
    String × String.Pos.Raw :=
  -- the character of code `n`, or the source text of the escape if there is
  -- no such character
  let plain (n : Nat) (rest : String.Pos.Raw) : String × String.Pos.Raw :=
    if n.isValidChar then (acc.push (Char.ofNat n), rest)
    else (acc ++ String.Pos.Raw.extract raw bs rest, rest)
  let verbatim (rest : String.Pos.Raw) : String × String.Pos.Raw :=
    (acc ++ String.Pos.Raw.extract raw bs rest, rest)
  if stop ≤ p.byteIdx then (acc, p)
  else
    let c := String.Pos.Raw.get raw p
    let q := String.Pos.Raw.next raw p
    if c == 'n' then (acc.push '\n', q)
    else if c == 't' then (acc.push '\t', q)
    else if c == 'r' then (acc.push '\r', q)
    else if c == 'b' then (acc.push (Char.ofNat 8), q)
    else if c == 'f' then (acc.push (Char.ofNat 12), q)
    else if c == 'v' then (acc.push (Char.ofNat 11), q)
    else if c == '\n' then (acc, q)                       -- line continuation
    else if c == '\r' then
      if q.byteIdx < stop && String.Pos.Raw.get raw q == '\n' then
        (acc, String.Pos.Raw.next raw q)
      else (acc, q)
    else if c == 'x' then
      match hexRun? raw stop 2 q 0 with
      | some (n, r) => plain n r
      | none => (acc.push 'x', q)
    else if c == 'u' then
      if q.byteIdx < stop && String.Pos.Raw.get raw q == '{' then
        match hexBrace? raw stop stop (String.Pos.Raw.next raw q) 0 false with
        | some (n, r) => plain n r
        | none => (acc.push 'u', q)
      else
        match hexRun? raw stop 4 q 0 with
        | some (n, r) =>
            if isHighSurrogate n then
              -- combine with a following low surrogate, if there is one
              let r1 := String.Pos.Raw.next raw r
              let r2 := String.Pos.Raw.next raw r1
              if r.byteIdx < stop && String.Pos.Raw.get raw r == '\\' &&
                  r1.byteIdx < stop && String.Pos.Raw.get raw r1 == 'u' then
                match hexRun? raw stop 4 r2 0 with
                | some (m, r') =>
                    if isLowSurrogate m then
                      plain (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)) r'
                    else verbatim r
                | none => verbatim r
              else verbatim r
            else plain n r
        | none => (acc.push 'u', q)
    else if c == '0' then
      if q.byteIdx < stop && '0' ≤ String.Pos.Raw.get raw q &&
          String.Pos.Raw.get raw q ≤ '9' then (acc.push '0', q)
      else (acc.push (Char.ofNat 0), q)
    else (acc.push c, q)

/-- Decode the text of `raw` between the byte index `p` and `stop`, pushing
the characters it denotes onto `acc`. -/
private def decodeFrom (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → String → String
  | 0, _, acc => acc
  | fuel + 1, p, acc =>
      if stop ≤ p.byteIdx then acc
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '\\' then
          let (acc, r) := decodeEscapeAt raw stop p q acc
          decodeFrom raw stop fuel r acc
        else decodeFrom raw stop fuel q (acc.push c)

/-- Decode a JavaScript string literal, given with its surrounding quotes,
into the characters it denotes. -/
def decodeStringLiteral (raw : String) : String :=
  let size := raw.utf8ByteSize
  if size == 0 then ""
  else
    let q := String.Pos.Raw.get raw ⟨0⟩
    if q == '"' || q == '\'' then
      -- a quote is one byte wide, so the body starts at index one
      let close := String.Pos.Raw.prev raw ⟨size⟩
      if 0 < close.byteIdx && String.Pos.Raw.get raw close == q then
        decodeFrom raw close.byteIdx size ⟨1⟩ ""
      else decodeFrom raw size size ⟨1⟩ ""
    else decodeFrom raw size size ⟨0⟩ ""

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

/-- Render a string value as a JavaScript literal.  As `prettier` does,
double quotes are used unless that would need more escaping.

The value is read twice by byte index — once to count the quotes it holds,
once to write it out — and never becomes a list of characters. -/
def encodeStringLiteral (value : String) : String :=
  let (doubles, singles) :=
    value.foldl (fun (n : Nat × Nat) c =>
      if c == '"' then (n.1 + 1, n.2) else if c == '\'' then (n.1, n.2 + 1) else n) (0, 0)
  let quote := if doubles > singles then '\'' else '"'
  (value.foldl (pushEscaped quote) (String.singleton quote)).push quote

/-! ## Numeric literals

A numeric literal is a `JSNumber` rather than the text it was written with,
so a literal in this tree is a number and two spellings of the same number
give the same tree.  `JSNumber.parse?` reads a source spelling and
`JSNumber.render` produces the canonical one; both live in
`Language.JavaScript.Types`. -/

end Language.JavaScript.MiniAST
