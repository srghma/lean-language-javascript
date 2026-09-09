/-
A *deterministic* JavaScript AST.

`RequestProject.JavaScript.AST` is a faithful port of the Haskell
`language-javascript` AST: every node carries a `JSAnnot` recording the
source position and the comments and whitespace that preceded the token, so
that the printer can reproduce the input character for character.  Two
programs which differ only in layout (`import  def  from 'mod'` versus
`import def from "mod"`) have *different* ASTs there.

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
`NEString`, a string which carries a proof that it is not `""`; a `var`
statement holds an `NEList` of declarators, which cannot be empty; a `try`
statement cannot be written without a `catch` and a `finally`; and every
node with a single shape is a `structure` rather than a one constructor
inductive.
-/

namespace Language.JavaScript.MiniAST

/-! ## Refined component types -/

/-- A string that is known not to be empty.  Identifiers, labels, module
names, numeric literals and the like use it, so that a `MiniAST` value
cannot describe a program with a nameless name. -/
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

/-- The non-empty string `s`, or `none` if `s` is empty. -/
def ofString? (s : String) : Option NEString :=
  if h : s ≠ "" then some ⟨s, h⟩ else none

/-- The non-empty string `s`; a placeholder if `s` is empty. -/
def ofString! (s : String) : NEString :=
  if h : s ≠ "" then ⟨s, h⟩ else default

@[simp] theorem val_ofString! {s : String} (h : s ≠ "") : (ofString! s).val = s := by
  simp [ofString!, h]

end NEString

/-- A list that is known not to be empty.  The invariant is structural — the
first element is a field — so `NEList.toList_ne_nil` is available wherever a
proof of non-emptiness is wanted.  (A subtype `{l : List α // l ≠ []}`
cannot be used here: the AST nests these lists inside its own recursive
types, and Lean does not allow a nested inductive whose parameters mention
the nested type.) -/
structure NEList (α : Type) where
  /-- The first element. -/
  hd : α
  /-- The remaining elements. -/
  tl : List α
deriving Repr, BEq, DecidableEq, Inhabited

namespace NEList

/-- The elements, as an ordinary list. -/
def toList (l : NEList α) : List α := l.hd :: l.tl

@[simp] theorem toList_ne_nil (l : NEList α) : l.toList ≠ [] := by
  simp [toList]

/-- A non-empty list from a list, or `none` if it is empty. -/
def ofList? : List α → Option (NEList α)
  | [] => none
  | a :: as => some ⟨a, as⟩

/-- A non-empty list from a list; a singleton placeholder if it is empty. -/
def ofList! [Inhabited α] : List α → NEList α
  | [] => ⟨default, []⟩
  | a :: as => ⟨a, as⟩

@[simp] theorem toList_ofList! [Inhabited α] (a : α) (as : List α) :
    (ofList! (a :: as)).toList = a :: as := rfl

/-- Map a function over the elements. -/
def map (f : α → β) (l : NEList α) : NEList β := ⟨f l.hd, l.tl.map f⟩

/-- The number of elements. -/
def length (l : NEList α) : Nat := l.tl.length + 1

end NEList

/-! ## Operators -/

/-- Binary operators. -/
inductive MiniBinOp where
  | and | or
  | bitAnd | bitOr | bitXor
  | eq | neq | strictEq | strictNeq
  | lt | le | gt | ge
  | lsh | rsh | ursh
  | plus | minus | times | divide | mod
  | inOp | instanceOf
deriving Repr, BEq, DecidableEq, Inhabited

/-- Prefix operators. -/
inductive MiniUnaryOp where
  | not | tilde | plus | minus
  | typeof | void | delete
  | preIncr | preDecr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Postfix operators. -/
inductive MiniPostfixOp where
  | incr | decr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Assignment operators. -/
inductive MiniAssignOp where
  | assign
  | plus | minus | times | divide | mod
  | lsh | rsh | ursh
  | bitAnd | bitXor | bitOr
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword introducing a variable declaration. -/
inductive MiniVarKind where
  | var | let_ | const
deriving Repr, BEq, DecidableEq, Inhabited

/-- What kind of method a member of an object or class literal is. -/
inductive MiniMethodKind where
  | normal | generator | get | set
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Imports

An `import` declaration is not recursive, so — unlike the types above — its
invariant can be stated as a proof carrying field. -/

/-- One `name` or `name as alias` of an import or export clause. -/
structure MiniSpecifier where
  /-- The exported name. -/
  name : NEString
  /-- The local name, when it differs. -/
  alias_ : Option NEString
deriving Repr, BEq, DecidableEq, Inhabited

/-- `import def, * as ns, { a, b as c } from "mod";`.  Each of the three
clauses is optional, but at least one of them has to be there. -/
structure MiniImportClause where
  /-- The default import, `import def from "mod"`. -/
  default_ : Option NEString
  /-- The namespace import, `import * as ns from "mod"`. -/
  namespace_ : Option NEString
  /-- The named imports, `import { a, b as c } from "mod"`. -/
  named : Option (List MiniSpecifier)
  /-- The module the names come from. -/
  mod : NEString
  /-- An import must bind something. -/
  binds : default_.isSome ∨ namespace_.isSome ∨ named.isSome
deriving DecidableEq

instance : Inhabited MiniImportClause :=
  ⟨{ default_ := some default, namespace_ := .none, named := .none, mod := default,
     binds := Or.inl rfl }⟩

namespace MiniImportClause

/-- Build an import clause, checking that it binds something. -/
def mk? (default_ namespace_ : Option NEString) (named : Option (List MiniSpecifier))
    (mod : NEString) : Option MiniImportClause :=
  if h : default_.isSome ∨ namespace_.isSome ∨ named.isSome then
    some ⟨default_, namespace_, named, mod, h⟩
  else
    Option.none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (default_ namespace_ : Option NEString) (named : Option (List MiniSpecifier))
    (mod : NEString) : MiniImportClause :=
  (mk? default_ namespace_ named mod).getD default

end MiniImportClause

/-- An `import` declaration. -/
inductive MiniImportDeclaration where
  /-- `import "mod";` -/
  | bare (mod : NEString)
  /-- `import ... from "mod";` -/
  | clause (clause : MiniImportClause)
deriving DecidableEq, Inhabited

/-! ## The syntax tree -/

mutual

/-- Expressions. -/
inductive MiniExpr where
  /-- An identifier. -/
  | ident (name : NEString)
  /-- A numeric literal, in its normalised source spelling. -/
  | number (raw : NEString)
  /-- A string literal, holding the characters it denotes (not the source text). -/
  | string (value : String)
  /-- A regular expression literal, including the slashes and the flags. -/
  | regex (raw : NEString)
  | null
  | true_
  | false_
  | this
  /-- `[a, , b]` -/
  | array (elements : List MiniArrayElement)
  /-- `{ a: 1 }` -/
  | object (properties : List MiniProperty)
  /-- `lhs op rhs`, for an assignment operator `op`. -/
  | assign (lhs : MiniExpr) (op : MiniAssignOp) (rhs : MiniExpr)
  | await (expr : MiniExpr)
  /-- `callee(args)` -/
  | call (callee : MiniExpr) (args : List MiniExpr)
  /-- `obj.name` -/
  | dot (obj : MiniExpr) (name : NEString)
  /-- `obj[index]` -/
  | index (obj : MiniExpr) (idx : MiniExpr)
  /-- `class name extends heritage { body }` used as an expression. -/
  | classExpr (name : Option NEString) (heritage : Option MiniExpr)
      (body : List MiniClassElement)
  /-- The comma operator, `lhs, rhs`. -/
  | seq (lhs : MiniExpr) (rhs : MiniExpr)
  | binary (lhs : MiniExpr) (op : MiniBinOp) (rhs : MiniExpr)
  | postfix (expr : MiniExpr) (op : MiniPostfixOp)
  /-- `cond ? thenE : elseE` -/
  | ternary (cond : MiniExpr) (thenE : MiniExpr) (elseE : MiniExpr)
  /-- `(params) => body` -/
  | arrow (params : List MiniExpr) (body : MiniArrowBody)
  /-- A function expression; `isAsync` and `isGenerator` select `async` and `*`. -/
  | func (isAsync : Bool) (isGenerator : Bool) (name : Option NEString)
      (params : List MiniExpr) (body : List MiniStatement)
  /-- `new callee(args)` -/
  | new (callee : MiniExpr) (args : List MiniExpr)
  /-- `...expr` -/
  | spread (expr : MiniExpr)
  /-- A template literal: an optional tag, the text before the first
  substitution, and one part per substitution. -/
  | template (tag : Option MiniExpr) (head : String) (parts : List MiniTemplatePart)
  | unary (op : MiniUnaryOp) (expr : MiniExpr)
  /-- `yield expr` -/
  | yield (expr : Option MiniExpr)
  /-- `yield* expr` -/
  | yieldFrom (expr : MiniExpr)

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
  /-- A quoted name, holding the characters it denotes. -/
  | string (value : String)
  | number (raw : NEString)
  /-- `[expr]` -/
  | computed (expr : MiniExpr)

/-- A member of an object literal. -/
inductive MiniProperty where
  | keyValue (key : MiniPropertyName) (value : MiniExpr)
  /-- `{ x }` -/
  | shorthand (name : NEString)
  | method (kind : MiniMethodKind) (key : MiniPropertyName) (params : List MiniExpr)
      (body : List MiniStatement)

/-- A member of a class body. -/
structure MiniClassElement where
  /-- Whether the member is `static`. -/
  isStatic : Bool
  /-- Plain method, generator, getter or setter. -/
  kind : MiniMethodKind
  /-- The name of the member. -/
  key : MiniPropertyName
  /-- The parameter list. -/
  params : List MiniExpr
  /-- The body. -/
  body : List MiniStatement

/-- One declarator of a `var`/`let`/`const` statement. -/
structure MiniDeclarator where
  /-- The name, or destructuring pattern, being bound. -/
  lhs : MiniExpr
  /-- The initialiser, if any. -/
  init : Option MiniExpr

/-- The first clause of a `for (;;)` statement. -/
inductive MiniForInit where
  | none
  | expr (expr : MiniExpr)
  | decl (kind : MiniVarKind) (decls : NEList MiniDeclarator)

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement. -/
inductive MiniForHead where
  | pattern (lhs : MiniExpr)
  | decl (kind : MiniVarKind) (lhs : MiniExpr)

/-- One `case`/`default` of a `switch`. -/
inductive MiniSwitchCase where
  | case (test : MiniExpr) (body : List MiniStatement)
  | default (body : List MiniStatement)

/-- The `catch` clause of a `try`; `guard` is the (non standard) `if` guard. -/
structure MiniCatchClause where
  /-- The bound exception. -/
  param : MiniExpr
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
  | classDecl (name : NEString) (heritage : Option MiniExpr) (body : List MiniClassElement)
  /-- `var`/`let`/`const` declaration; it declares at least one name. -/
  | decl (kind : MiniVarKind) (decls : NEList MiniDeclarator)
  | doWhile (body : MiniStatement) (cond : MiniExpr)
  | for_ (init : MiniForInit) (cond : Option MiniExpr) (step : Option MiniExpr)
      (body : MiniStatement)
  | forIn (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  | forOf (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  | funcDecl (isAsync : Bool) (isGenerator : Bool) (name : NEString)
      (params : List MiniExpr) (body : List MiniStatement)
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
  /-- `export { a } from "mod";` -/
  | fromClause (specs : List MiniSpecifier) (mod : NEString)
  /-- `export { a };` -/
  | locals (specs : List MiniSpecifier)
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
instance : Inhabited MiniArrayElement := ⟨.hole⟩
instance : Inhabited MiniArrowBody := ⟨.block []⟩
instance : Inhabited MiniTemplatePart := ⟨⟨default, ""⟩⟩
instance : Inhabited MiniPropertyName := ⟨.ident default⟩
instance : Inhabited MiniProperty := ⟨.shorthand default⟩
instance : Inhabited MiniClassElement := ⟨⟨false, .normal, default, [], []⟩⟩
instance : Inhabited MiniDeclarator := ⟨⟨default, none⟩⟩
instance : Inhabited MiniForInit := ⟨.none⟩
instance : Inhabited MiniForHead := ⟨.pattern default⟩
instance : Inhabited MiniSwitchCase := ⟨.default []⟩
instance : Inhabited MiniCatchClause := ⟨⟨default, none, []⟩⟩
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

private def hexDigitVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hexDigitsVal? : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => do let a ← acc; let d ← hexDigitVal? c; pure (16 * a + d))
      (some 0)

private def isHighSurrogate (n : Nat) : Bool := 0xD800 ≤ n && n ≤ 0xDBFF
private def isLowSurrogate (n : Nat) : Bool := 0xDC00 ≤ n && n ≤ 0xDFFF

/-- The escape sequence `\c...` at the head of `cs` (which does not include
the backslash): the characters it denotes and the rest of the input.  An
unknown escape stands for the escaped character itself. -/
private partial def decodeEscape (cs : List Char) : List Char × List Char :=
  let plain (n : Nat) (rest : List Char) (raw : List Char) : List Char × List Char :=
    if n.isValidChar then ([Char.ofNat n], rest) else (raw, rest)
  match cs with
  | [] => ([], [])
  | 'n' :: r => (['\n'], r)
  | 't' :: r => (['\t'], r)
  | 'r' :: r => (['\r'], r)
  | 'b' :: r => ([Char.ofNat 8], r)
  | 'f' :: r => ([Char.ofNat 12], r)
  | 'v' :: r => ([Char.ofNat 11], r)
  | '\n' :: r => ([], r)                       -- line continuation
  | '\r' :: '\n' :: r => ([], r)
  | '\r' :: r => ([], r)
  | 'x' :: a :: b :: r =>
      match hexDigitsVal? [a, b] with
      | some n => plain n r ['\\', 'x', a, b]
      | none => (['x'], a :: b :: r)
  | 'u' :: '{' :: r =>
      let digits := r.takeWhile (· ≠ '}')
      let rest := r.dropWhile (· ≠ '}')
      match hexDigitsVal? digits, rest with
      | some n, '}' :: r' => plain n r' (['\\', 'u', '{'] ++ digits ++ ['}'])
      | _, _ => (['u'], '{' :: r)
  | 'u' :: a :: b :: c :: d :: r =>
      let raw := ['\\', 'u', a, b, c, d]
      match hexDigitsVal? [a, b, c, d] with
      | some n =>
          if isHighSurrogate n then
            -- combine with a following low surrogate, if there is one
            match r with
            | '\\' :: 'u' :: a' :: b' :: c' :: d' :: r' =>
                match hexDigitsVal? [a', b', c', d'] with
                | some m =>
                    if isLowSurrogate m then
                      plain (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)) r'
                        (raw ++ ['\\', 'u', a', b', c', d'])
                    else (raw, r)
                | none => (raw, r)
            | _ => (raw, r)
          else plain n r raw
      | none => (['u'], a :: b :: c :: d :: r)
  | '0' :: r =>
      match r with
      | d :: _ => if '0' ≤ d && d ≤ '9' then (['0'], r) else ([Char.ofNat 0], r)
      | [] => ([Char.ofNat 0], [])
  | c :: r => ([c], r)

private partial def decodeChars : List Char → List Char
  | [] => []
  | '\\' :: cs =>
      let (out, rest) := decodeEscape cs
      out ++ decodeChars rest
  | c :: cs => c :: decodeChars cs

/-- Decode a JavaScript string literal, given with its surrounding quotes,
into the characters it denotes. -/
def decodeStringLiteral (raw : String) : String :=
  let cs := raw.toList
  let cs :=
    match cs with
    | q :: rest =>
        if q == '"' || q == '\'' then
          match rest.reverse with
          | q' :: body => if q' == q then body.reverse else rest
          | [] => rest
        else cs
    | [] => cs
  String.ofList (decodeChars cs)

private def escapeChar (quote : Char) (c : Char) : String :=
  if c == quote then "\\" ++ String.singleton quote
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat == 8 then "\\b"
  else if c.toNat == 12 then "\\f"
  else if c.toNat == 11 then "\\v"
  else if c.toNat < 0x20 || c.toNat == 0x7F then
    let hex := String.ofList (Nat.toDigits 16 c.toNat)
    "\\x" ++ (if hex.length == 1 then "0" ++ hex else hex)
  else String.singleton c

/-- Render a string value as a JavaScript literal.  As `prettier` does,
double quotes are used unless that would need more escaping. -/
def encodeStringLiteral (value : String) : String :=
  let cs := value.toList
  let doubles := (cs.filter (· == '"')).length
  let singles := (cs.filter (· == '\'')).length
  let quote := if doubles > singles then '\'' else '"'
  String.singleton quote ++ String.join (cs.map (escapeChar quote))
    ++ String.singleton quote

/-! ## Numeric literals

Numeric literals keep their spelling (a hexadecimal literal is not turned
into a decimal one), but the spelling is normalised the way `prettier`
normalises it. -/

private def stripTrailingFractionZeros (s : String) : String :=
  match s.splitOn "." with
  | [intPart, frac] =>
      let digits := frac.toList
      let trimmed := (digits.reverse.dropWhile (· == '0')).reverse
      let frac' := if trimmed.isEmpty then (if digits.isEmpty then [] else ['0']) else trimmed
      if frac'.isEmpty then intPart else intPart ++ "." ++ String.ofList frac'
  | _ => s

/-- Normalise a numeric literal: lower case, no leading `+` or superfluous
zeros in the exponent, a digit before the decimal point, no trailing dot and
no extraneous trailing zeros in the fraction. -/
def normalizeNumber (raw : String) : String :=
  let s := raw.toLower
  if s.startsWith "0x" || s.startsWith "0b" || s.startsWith "0o" then s
  else
    let (mantissa, exponent) :=
      match s.splitOn "e" with
      | [m] => (m, "")
      | [m, e] => (m, e)
      | _ => (s, "")
    -- a digit before the decimal point
    let mantissa := if mantissa.startsWith "." then "0" ++ mantissa else mantissa
    let mantissa := stripTrailingFractionZeros mantissa
    let mantissa :=
      if mantissa.endsWith "." then String.ofList (mantissa.toList.dropLast) else mantissa
    if exponent == "" then mantissa
    else
      let expChars := exponent.toList
      let (sign, digits) :=
        match expChars with
        | '-' :: r => ("-", r)
        | '+' :: r => ("", r)
        | r => ("", r)
      let digits := String.ofList (digits.dropWhile (· == '0'))
      let digits := if digits == "" then "0" else digits
      if digits == "0" then mantissa else mantissa ++ "e" ++ sign ++ digits

end Language.JavaScript.MiniAST
