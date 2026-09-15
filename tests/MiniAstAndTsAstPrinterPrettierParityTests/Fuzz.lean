import MiniAST

/-!
# A generator of random sample programs

A small deterministic generator of `MiniAST` programs, used to compare the
printer's output with prettier's on many more shapes than the hand written
corpus covers.  The generated programs stay inside the part of the
language whose meaning does not depend on the context, so that every one
of them parses: `return` is only generated inside a function, `break` and
`continue` only inside a loop, and every declaration gets a fresh name.
-/

namespace Language.JavaScript.MiniAST.Fuzz

open Language.JavaScript

/-- The state of the generator: a seed and a counter of fresh names. -/
structure St where
  /-- The seed of the pseudo random number generator. -/
  seed : UInt64
  /-- The number of fresh names handed out so far. -/
  fresh : Nat
deriving Inhabited

/-- One step of a linear congruential generator. -/
def step (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A pseudo random number below `n`, and the state that follows. -/
def rand (st : St) (n : Nat) : Nat × St :=
  let s := step st.seed
  let v := (s >>> 33).toNat
  (if n == 0 then 0 else v % n, { st with seed := s })

/-- A fresh name, and the state that follows. -/
def freshName (st : St) (prefix_ : String) : String × St :=
  (prefix_ ++ toString st.fresh, { st with fresh := st.fresh + 1 })

/-- The identifiers the generator picks from. -/
def names : Array String :=
  #["a", "bb", "value", "item", "index", "result", "handler", "theCollection",
    "computeTheValue", "theConfigurationObject", "aLongIdentifierNameNumberZero",
    "theVeryLongNameForAVariableHere", "f", "g", "xs",
    -- names of the lengths in between, so that a line falls just short of
    -- the eightieth column as often as it falls just past it
    "abc", "abcd", "node8", "target9", "iterator", "collection", "currentValue",
    "theHandlerName", "theIteratorOfTheList", "aVeryVeryLongIdentifierNameHere"]

/-- The strings the generator picks from.  Several of them hold a
character a literal has to escape, so that the spelling the printer picks
for a string is exercised too. -/
def strings : Array String :=
  #["", "ok", "a string", "it's", "say \"hi\"", "a rather long string literal here",
    "tab\there", "x", "a-key", "three words here",
    "a string of a length which is somewhere in the middle",
    "a\\b", "both ' and \"", "two '' and one \"", "line\nbreak", "nul\u0000here",
    "café", "a`b", "${x}", "class", "1a"]

/-- The texts the generator writes between the backticks of a template
literal.  Several of them hold a character which has to be escaped there. -/
def templateTexts : Array String :=
  #["", "a", "value ", "a rather long piece of template text", "` tick", "\\ slash",
    "${ dollar", "two\nlines", "café", " and "]

/-- The names the generator reads a property off with, which unlike an
identifier may be a reserved word. -/
def memberNames : Array String :=
  #["value", "length", "name", "class", "default", "function", "new", "in", "true",
    "constructor", "theRatherLongPropertyName", "café"]

/-- The names of the JSX elements the generator picks from. -/
def jsxNames : Array String :=
  #["div", "span", "p", "li", "Foo", "MyComponent", "TheVeryLongComponentNameHere", "br"]

/-- The names of the JSX attributes the generator picks from. -/
def jsxAttrNames : Array String :=
  #["id", "className", "onClick", "value", "data-id", "key", "href",
    "theRatherLongAttributeNameHere"]

/-- The texts the generator writes between the tags of a JSX element.
Several of them begin or end with whitespace, which decides where a
`{" "}` has to be written, and one holds the characters that are written
as entities. -/
def jsxTexts : Array String :=
  #["hello", "hello world", " padded ", "a b c", "x", "text ", " text", "a < b & c > d",
    "one two three four five six seven eight nine ten eleven twelve thirteen",
    "the quick brown fox jumps over the lazy dog",
    "{braces}", "café naïve", "全角の文字", "aVeryLongWordWithoutAnySpacesInItAtAllWhatsoever",
    "two  spaces", "\n", " ", "  a  b  ", "\n  a\n  b\n", "a\tb",
    -- text whose characters are the ones an entity stands for, and text
    -- which spells an entity out: both are written as entities themselves
    "&amp; and &#123;", "a\u00a0b", "quotes ' and \"", "&nbsp;"]

/-- A name from `names`. -/
def genName (st : St) : String × St :=
  let (k, st) := rand st names.size
  (names[k]!, st)

/-- A name to read a property off with. -/
def genMemberName (st : St) : String × St :=
  let (k, st) := rand st (memberNames.size + names.size)
  (if k < memberNames.size then memberNames[k]! else names[k - memberNames.size]!, st)

/-- A text to write between the backticks of a template literal. -/
def genTemplateText (st : St) : String × St :=
  let (k, st) := rand st templateTexts.size
  (templateTexts[k]!, st)

/-- A non-empty string. -/
def nes (x : String) : NEString := NEString.ofString! x

/-- An identifier expression. -/
def ident (x : String) : MiniExpr := .ident (nes x)

/-- The binary operators the generator picks from. -/
def binOps : Array BinOp :=
  #[.plus, .minus, .times, .divide, .mod, .and, .or, .coalesce, .eq, .strictEq,
    .lt, .ge, .bitAnd, .bitOr, .lsh, .inOp, .instanceOf]

/-- The unary operators the generator picks from. -/
def unOps : Array UnaryOp := #[.not, .minus, .plus, .tilde, .typeof, .void]

/-- The assignment operators the generator picks from. -/
def assignOps : Array AssignOp :=
  #[.plus, .minus, .times, .bitOr, .lsh, .logicalAnd, .logicalOr, .coalesce]

/-- The numeric literals the generator picks from. -/
def numbers : Array JSNumber :=
  #[.decimal 0 0, .decimal 15 (-1), .decimal 1 21, .decimal 1 (-7), .decimal 123456 (-3),
    .radix .hexadecimal 255, .radix .binary 10, .radix .octal 15,
    .bigint .decimal 12, .bigint .hexadecimal 255, .decimal 1000 0]

/-- The numeric literals the generator writes a property name with.  A
`BigInt` literal is not one of them: a property name may not be written
with the trailing `n`. -/
def keyNumbers : Array JSNumber :=
  #[.decimal 0 0, .decimal 15 (-1), .decimal 1 21, .decimal 123456 (-3),
    .radix .hexadecimal 255, .radix .binary 10, .decimal 1000 0]

/-- The regular expression literals the generator picks from. -/
def regexes : Array MiniExpr :=
  #[.regex ⟨NEString.ofString! "ab+c", {}⟩,
    .regex ⟨NEString.ofString! "^[a-z]+$", { global := true, ignoreCase := true }⟩]

/-- Whether the statement is a declaration.  A place which takes a single
statement, such as the body of an `if` or of a loop, does not allow one. -/
def isDeclarationStmt : MiniStatement → Bool
  | .decl .. | .using_ .. | .classDecl .. | .funcDecl .. => true
  | .labelled _ s => isDeclarationStmt s
  | _ => false

/-- The statement, in a block if it is a declaration, so that it may stand
where a single statement is expected. -/
def asSingleStmt (s : MiniStatement) : MiniStatement :=
  if isDeclarationStmt s then .block [s] else s

mutual

/-- A random expression of depth at most `d`. -/
partial def genExpr (d : Nat) (st : St) : MiniExpr × St :=
  if d == 0 then genAtom st else
    let (k, st) := rand st 85
    match k with
    | 0 | 1 => genAtom st
    | 2 =>
        let (l, st) := genExpr (d - 1) st
        let (r, st) := genExpr (d - 1) st
        let (i, st) := rand st binOps.size
        (.binary l binOps[i]! r, st)
    | 3 =>
        let (c, st) := genExpr (d - 1) st
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        (.ternary c a b, st)
    | 4 =>
        let (f, st) := genName st
        let (args, st) := genExprs (d - 1) st
        (.call (ident f) args, st)
    | 5 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genMemberName st
        (.dot o (nes n), st)
    | 6 =>
        let (o, st) := genExpr (d - 1) st
        let (i, st) := genExpr 0 st
        (.index o i, st)
    | 7 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genMemberName st
        let (args, st) := genExprs (d - 1) st
        (.call (.dot o (nes n)) args, st)
    | 8 =>
        let (ps, st) := genParams st
        let (b, st) := genExpr (d - 1) st
        let (a, st) := rand st 3
        (.arrow (a == 0) ps (.expr b), st)
    | 9 =>
        let (ps, st) := genParams st
        let (body, st) := genStmts (d - 1) true false st
        let (a, st) := rand st 3
        (.arrow (a == 0) ps (.block body), st)
    | 10 =>
        let (props, st) := genProps (d - 1) st
        (.object props, st)
    | 11 =>
        let (els, st) := genExprs (d - 1) st
        (.array (els.map MiniArrayElement.elem), st)
    | 12 =>
        let (i, st) := rand st unOps.size
        let (e, st) := genExpr (d - 1) st
        (.unary unOps[i]! e, st)
    | 13 =>
        let (n, st) := genName st
        let (e, st) := genExpr (d - 1) st
        (.assign (ident n) .assign e, st)
    | 14 =>
        let (n, st) := genName st
        let (args, st) := genExprs (d - 1) st
        (.new (ident n) args, st)
    | 15 =>
        let (e, st) := genExpr (d - 1) st
        let (s, st) := genTemplateText st
        let (suffix, st) := genTemplateText st
        (.template none s [⟨e, suffix⟩], st)
    | 16 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genMemberName st
        let (m, st) := genMemberName st
        (.chain o ⟨.dot true (nes n), [.dot false (nes m)]⟩, st)
    | 17 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genName st
        let (args, st) := genExprs (d - 1) st
        (.chain o ⟨.dot true (nes n), [.call false args]⟩, st)
    | 18 =>
        let (ps, st) := genParams st
        let (ps', st) := genParams st
        let (b, st) := genExpr (d - 1) st
        let (a, st) := rand st 4
        (.arrow (a == 0 || a == 1) ps (.expr (.arrow (a == 0) ps' (.expr b))), st)
    | 19 =>
        let (n, st) := genName st
        let (e, st) := genExpr (d - 1) st
        (.assign (.dot (ident n) (nes "property")) .plus e, st)
    | 20 =>
        let (f, st) := genName st
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        (.call (ident f) [a, .spread b], st)
    | 21 =>
        let (ps, st) := genParams st
        let (body, st) := genStmts (d - 1) true false st
        (.func false false none ps body, st)
    -- a compound or logical assignment
    | 22 =>
        let (n, st) := genName st
        let (i, st) := rand st assignOps.size
        let (e, st) := genExpr (d - 1) st
        (.assign (ident n) assignOps[i]! e, st)
    -- a tagged template literal
    | 23 =>
        let (f, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (s, st) := genTemplateText st
        let (suffix, st) := genTemplateText st
        (.template (some (ident f)) s [⟨e, suffix⟩], st)
    -- a regular expression literal, possibly with a method called on it
    | 24 =>
        let (i, st) := rand st regexes.size
        let (k, st) := rand st 2
        let re := regexes[i]!
        if k == 0 then (re, st)
        else
          let (e, st) := genExpr (d - 1) st
          (.call (.dot re (nes "test")) [e], st)
    -- a longer optional chain
    | 25 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genName st
        let (args, st) := genExprs (d - 1) st
        let (m, st) := rand st 100
        (.chain o ⟨.dot true (nes n), [.call true args, .index true (.number (JSNumber.ofNat m))]⟩,
          st)
    -- an `await` inside the asynchronous function it belongs to
    | 26 =>
        let (e, st) := genExpr (d - 1) st
        (.call (.func true false none [] [.return_ (some (.await e))]) [], st)
    -- a `yield` inside the generator it belongs to
    | 27 =>
        let (e, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        (.call (.func false true none [] [.expr (if k == 0 then .yield (some e) else .yieldFrom e)])
          [], st)
    -- a class expression
    | 28 =>
        let (base, st) := genName st
        let (prop, st) := genMemberName st
        let (elems, st) := genClassElements (d - 1) st
        let (k, st) := rand st 3
        let heritage : Option MiniExpr :=
          match k with
          | 0 => none
          | 1 => some (ident base)
          | _ => some (.dot (ident base) (nes prop))
        (.classExpr [] none heritage elems, st)
    -- the comma operator
    | 29 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        (.seq a b, st)
    -- a member chain of three calls, and a `new` of a member callee
    | 30 =>
        let (o, st) := genName st
        let (n1, st) := genName st
        let (n2, st) := genName st
        let (n3, st) := genName st
        let (a1, st) := genExprs (d - 1) st
        let (a2, st) := genExprs (d - 1) st
        let (k, st) := rand st 2
        if k == 0 then
          (.call (.dot (.call (.dot (.call (.dot (ident o) (nes n1)) a1) (nes n2)) a2) (nes n3)) [],
            st)
        else (.new (.dot (ident o) (nes n1)) a1, st)
    -- a dynamic `import()`, with or without import attributes
    | 31 =>
        let (m, st) := freshName st "mod"
        let (k, st) := rand st 2
        if k == 0 then (.importCall (.string m) none, st)
        else
          (.importCall (.string m)
            (some (.object [.keyValue (.ident (nes "with"))
              (.object [.keyValue (.ident (nes "type")) (.string "json")])])), st)
    -- `import.meta`, on its own or with a property read off it
    | 32 =>
        let (n, st) := genName st
        let (k, st) := rand st 2
        ((if k == 0 then .importMeta else .dot .importMeta (nes n)), st)
    -- `super` inside a method of the class it belongs to
    | 33 =>
        let (base, st) := genName st
        let (m, st) := genName st
        let (n, st) := genName st
        let (s, st) := genString st
        let (args, st) := genExprs (d - 1) st
        let (k, st) := rand st 4
        let body : List MiniStatement :=
          match k with
          | 0 => [.return_ (some (.call (.superDot (nes n)) args))]
          | 1 => [.return_ (some (.superDot (nes n)))]
          | 2 => [.return_ (some (.superIndex (.string s)))]
          | _ => [.expr (.superCall args)]
        let key : MiniPropertyName :=
          if k == 3 then .ident (nes "constructor") else .ident (nes m)
        (.classExpr [] none (some (ident base))
          [.method [] false .normal key [] body], st)
    -- `new.target` inside the function it belongs to
    | 34 =>
        (.call (.func false false none [] [.return_ (some .newTarget)]) [], st)
    -- the private name of a class, read off `this` and tested with `in`
    | 35 =>
        let (fld, st) := freshName st "field"
        let (m, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        let body : List MiniStatement :=
          if k == 0 then [.return_ (some (.privateDot .this (nes fld)))]
          else [.return_ (some (.binary (.privateName (nes fld)) .inOp (ident "item")))]
        (.classExpr [] none none
          [ .field [] false false (.private_ (nes fld)) (some e),
            .method [] false .normal (.ident (nes m)) [.plain (.ident (nes "item"))] body ], st)
    -- a variable incremented, before or after it is read
    | 36 =>
        let (n, st) := genName st
        let (k, st) := rand st 4
        ((match k with
          | 0 => .postfix (ident n) .incr
          | 1 => .postfix (ident n) .decr
          | 2 => .unary .preIncr (ident n)
          | _ => .unary .preDecr (ident n)), st)
    -- a property deleted, and the `void` of an expression
    | 37 =>
        let (n, st) := genName st
        let (m, st) := genName st
        let (k, st) := rand st 2
        ((if k == 0 then .unary .delete (.dot (ident n) (nes m))
          else .unary .delete (.index (ident n) (.string m))), st)
    -- a numeric literal of one of the shapes the language allows
    | 38 =>
        let (i, st) := rand st numbers.size
        (.number numbers[i]!, st)
    -- an object literal whose names are written in the other ways
    | 39 =>
        let (s, st) := genString st
        let (n, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (f, st) := genExpr (d - 1) st
        (.object [.keyValue (.string s) e, .keyValue (.number (JSNumber.ofNat 2)) f,
          .keyValue (.computed (ident n)) .null], st)
    -- the accessors of an object literal
    | 40 =>
        let (n, st) := genName st
        let (e, st) := genExpr (d - 1) st
        (.object [.method .get (.ident (nes n)) [] [.return_ (some e)],
          .method .set (.ident (nes n)) [.plain (.ident (nes "value"))] [],
          .method .generator (.ident (nes "gen")) [] []], st)
    -- an array literal with an elision in it
    | 41 =>
        let (els, st) := genExprs (d - 1) st
        let (e, st) := genExpr (d - 1) st
        (.array (.hole :: .elem e :: els.map MiniArrayElement.elem ++ [.hole]), st)
    -- a destructuring assignment
    | 42 =>
        let (x, st) := genName st
        let (y, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then
            .assignPattern (.array [.elem (.ident (nes x)), .hole,
              .rest (.ident (nes y))]) e
          else
            .assignPattern (.object [⟨.ident (nes x), .ident (nes x)⟩]
              (some (.ident (nes y)))) e), st)
    -- the comma operator, of three operands
    | 43 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (c, st) := genExpr (d - 1) st
        (.seq a (.seq b c), st)
    -- a template literal of two substitutions, possibly tagged
    | 44 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (s, st) := genTemplateText st
        let (mid, st) := genTemplateText st
        let (f, st) := genName st
        let (k, st) := rand st 2
        (.template (if k == 0 then none else some (ident f)) s
          [⟨a, mid⟩, ⟨b, ""⟩], st)
    -- a `new` of no arguments, and a `new` of a `new`
    | 45 =>
        let (n, st) := genName st
        let (args, st) := genExprs (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .new (ident n) [] else .new (.new (ident n) args) []), st)
    -- a function expression of a name, and an arrow of a rest parameter
    | 46 =>
        let (f, st) := freshName st "fn"
        let (body, st) := genStmts (d - 1) true false st
        let (e, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .func false false (some (nes f)) [] body
          else .arrow false [.plain (.object [⟨.ident (nes "a"), .ident (nes "a")⟩] none),
            .rest (.ident (nes "rest"))] (.expr e)), st)
    -- a class expression whose members are decorated
    | 47 =>
        let (n, st) := genName st
        let (e, st) := genExpr 0 st
        (.classExpr [ident "logged"] none none
          [.method [ident "bound"] false .normal (.ident (nes n)) [] [],
           .field [.call (ident "inject") [e]] true false (.ident (nes "service")) none], st)
    -- an optional chain that reads an index and calls a method
    | 48 =>
        let (o, st) := genExpr (d - 1) st
        let (n, st) := genName st
        let (m, st) := rand st 100
        (.chain o ⟨.index true (.number (JSNumber.ofNat m)),
          [.dot false (nes n), .call true []]⟩, st)
    -- a chained ternary, and a ternary that stands as an argument
    | 49 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (c, st) := genExpr (d - 1) st
        let (e, st) := genExpr (d - 1) st
        let (f, st) := genName st
        let (k, st) := rand st 3
        ((match k with
          | 0 => .ternary a b (.ternary c e (ident f))
          | 1 => .ternary (.ternary a b c) e (ident f)
          | _ => .call (ident f) [.ternary a b c, e]), st)
    -- a chain of logical operators, and a comparison inside one
    | 50 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (c, st) := genExpr (d - 1) st
        let (k, st) := rand st 3
        ((match k with
          | 0 => .binary (.binary a .and b) .or c
          | 1 => .binary a .and (.binary b .or c)
          | _ => .binary (.binary a .strictEq b) .and
              (.binary (.unary .typeof c) .neq (.string "undefined"))), st)
    -- a call whose last argument is a function or an object literal
    | 51 =>
        let (f, st) := genName st
        let (a, st) := genExpr (d - 1) st
        let (ps, st) := genParams st
        let (body, st) := genStmts (d - 1) true false st
        let (props, st) := genProps (d - 1) st
        let (k, st) := rand st 3
        ((match k with
          | 0 => .call (ident f) [a, .arrow false ps (.block body)]
          | 1 => .call (ident f) [a, .object props]
          | _ => .call (ident f) [a, .func false false none ps body]), st)
    -- a call whose first argument is a function
    | 52 =>
        let (f, st) := genName st
        let (body, st) := genStmts (d - 1) true false st
        let (els, st) := genExprs (d - 1) st
        (.call (ident f) [.arrow false [] (.block body), .array (els.map MiniArrayElement.elem)], st)
    -- an arrow whose body is an object literal
    | 53 =>
        let (ps, st) := genParams st
        let (props, st) := genProps (d - 1) st
        (.arrow false ps (.expr (.object props)), st)
    -- a chain of string concatenations
    | 54 =>
        let (s1, st) := genString st
        let (a, st) := genExpr (d - 1) st
        let (s2, st) := genString st
        let (b, st) := genExpr (d - 1) st
        (.binary (.binary (.binary (.string s1) .plus a) .plus (.string s2)) .plus b, st)
    -- an object literal of a nested array and a nested object
    | 55 =>
        let (props, st) := genProps (d - 1) st
        let (els, st) := genExprs (d - 1) st
        let (n, st) := genName st
        (.object [.keyValue (.ident (nes n)) (.array (els.map MiniArrayElement.elem)),
          .keyValue (.ident (nes "nested")) (.object props)], st)
    -- a `new` of a member callee, with a call or a member read off it
    | 56 =>
        let (o, st) := genName st
        let (n, st) := genName st
        let (m, st) := genName st
        let (args, st) := genExprs (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .call (.dot (.new (.dot (ident o) (nes n)) args) (nes m)) []
          else .dot (.new (ident o) args) (nes m)), st)
    -- an assignment whose right hand side is a member chain
    | 57 =>
        let (x, st) := genName st
        let (o, st) := genName st
        let (n1, st) := genName st
        let (n2, st) := genName st
        let (args, st) := genExprs (d - 1) st
        (.assign (.dot (ident x) (nes "property")) .assign
          (.call (.dot (.call (.dot (ident o) (nes n1)) args) (nes n2)) []), st)
    -- the comma operator where it has to be parenthesised
    | 58 =>
        let (f, st) := genName st
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .call (ident f) [.seq a b] else .arrow false [] (.expr (.seq a b))), st)
    -- a prefix operator applied to an operator expression
    | 59 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (k, st) := rand st 3
        ((match k with
          | 0 => .unary .not (.binary a .and b)
          | 1 => .unary .minus (.binary a .plus b)
          | _ => .binary (.unary .typeof a) .strictEq (.string "function")), st)
    -- a template literal of a nested template, and one of an operator
    -- expression inside its substitution
    | 60 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (s, st) := genTemplateText st
        let (k, st) := rand st 2
        ((if k == 0 then
            .template none s [⟨a, " "⟩, ⟨.template none "inner " [⟨b, ""⟩], ""⟩]
          else .template none "" [⟨.binary a .plus b, s⟩]), st)
    -- an array of many short elements, which prettier fills a line with
    | 61 =>
        let (n, st) := rand st 30
        let (k, st) := rand st 3
        let els : List MiniArrayElement :=
          (List.range (n + 6)).map fun i =>
            match k with
            | 0 => .elem (.number (JSNumber.ofNat (i * 37)))
            | 1 => .elem (.number (.decimal (i * 15) (-1)))
            | _ => .elem (.unary .minus (.number (JSNumber.ofNat i)))
        (.array els, st)
    -- an object literal of many properties
    | 62 =>
        let (n, st) := rand st 5
        let (e, st) := genExpr (d - 1) st
        let props : List MiniProperty :=
          (List.range (n + 3)).map fun i =>
            .keyValue (.ident (nes (names[i % names.size]!.append (toString i))))
              (.number (JSNumber.ofNat i))
        (.object (props ++ [.keyValue (.ident (nes "last")) e]), st)
    -- a call of many arguments
    | 63 =>
        let (f, st) := genName st
        let (n, st) := rand st 4
        let (e, st) := genExpr (d - 1) st
        let args : List MiniExpr :=
          (List.range (n + 3)).map fun i => ident (names[i % names.size]!)
        (.call (ident f) (args ++ [e]), st)
    -- a chain of property reads, with no call in it
    | 64 =>
        let (o, st) := genExpr (d - 1) st
        let (n1, st) := genMemberName st
        let (n2, st) := genMemberName st
        let (n3, st) := genMemberName st
        (.dot (.dot (.dot o (nes n1)) (nes n2)) (nes n3), st)
    -- a `super[...]` lookup, inside the method of the class it belongs to
    | 65 =>
        let (base, st) := genName st
        let (m, st) := genName st
        let (s, st) := genString st
        let (k, st) := rand st 2
        let idx : MiniExpr := if k == 0 then .string s else .number (JSNumber.ofNat 3)
        (.classExpr [] none (some (ident base))
          [.method [] false .normal (.ident (nes m)) []
            [.return_ (some (.superIndex idx))]], st)
    -- an `await` of several shapes, inside the asynchronous function it
    -- belongs to
    | 66 =>
        let (e, st) := genExpr (d - 1) st
        let (n, st) := genMemberName st
        let (k, st) := rand st 7
        let inner : MiniExpr :=
          match k with
          | 0 => .await (.await e)
          | 1 => .dot (.await e) (nes n)
          | 2 => .binary (.await e) .or (.await (ident "item"))
          | 3 => .array [.elem (.spread (.await e))]
          -- an `await` at the left edge of the operand of another one
          | 4 => .await (.dot (.await e) (nes n))
          | 5 => .await (.call (.await e) [ident "item"])
          | _ => .await (.binary (ident "item") .plus (.dot (.await e) (nes n)))
        (.call (.func true false none [] [.return_ (some inner)]) [], st)
    -- a parenthesised optional chain, read off or called
    | 67 =>
        let (o, st) := genName st
        let (n, st) := genName st
        let (m, st) := genMemberName st
        let (args, st) := genExprs (d - 1) st
        let chain : MiniExpr := .chain (ident o) ⟨.dot true (nes n), []⟩
        let (k, st) := rand st 3
        ((match k with
          | 0 => .dot chain (nes m)
          | 1 => .call chain args
          | _ => .new chain args), st)
    -- an array of object literals, and one of arrays
    | 68 =>
        let (props, st) := genProps (d - 1) st
        let (els, st) := genExprs (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then
            .array [.elem (.object props), .elem (.object props)]
          else
            .array [.elem (.array (els.map MiniArrayElement.elem)),
              .elem (.array (els.map MiniArrayElement.elem))]), st)
    -- a chain of three curried arrow functions
    | 69 =>
        let (x, st) := genName st
        let (y, st) := genName st
        let (z, st) := genName st
        let (b, st) := genExpr (d - 1) st
        (.arrow false [.plain (.ident (nes x))]
          (.expr (.arrow false [.plain (.ident (nes y))]
            (.expr (.arrow false [.plain (.ident (nes z))] (.expr b))))), st)
    -- a template literal read off, and one tagged by a member chain
    | 70 =>
        let (o, st) := genName st
        let (n, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (s, st) := genTemplateText st
        let (k, st) := rand st 2
        ((if k == 0 then .dot (.template none s [⟨e, ""⟩]) (nes "length")
          else .template (some (.dot (ident o) (nes n))) s [⟨e, ""⟩]), st)
    -- a class of private members, including a private accessor pair
    | 71 =>
        let (fld, st) := freshName st "field"
        let (acc, st) := freshName st "field"
        let (m, st) := freshName st "method"
        let (e, st) := genExpr (d - 1) st
        (.classExpr [] none none
          [ .field [] false false (.private_ (nes fld)) none,
            .method [] false .normal (.private_ (nes m)) [] [.return_ (some e)],
            .method [] false .get (.private_ (nes acc)) []
              [.return_ (some (.privateDot .this (nes fld)))],
            .method [] false .set (.private_ (nes acc)) [.plain (.ident (nes "value"))] [] ], st)
    -- a numeric literal read off, and one used as a property name
    | 72 =>
        let (i, st) := rand st keyNumbers.size
        let (e, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .call (.dot (.number (.decimal 5 0)) (nes "toFixed")) []
          else .object [.keyValue (.number keyNumbers[i]!) e]), st)
    -- a spread of an expression which needs parentheses
    | 73 =>
        let (f, st) := genName st
        let (x, st) := genName st
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (k, st) := rand st 3
        ((match k with
          | 0 => .call (ident f) [.spread (.ternary a b (ident x))]
          | 1 => .array [.elem (.spread (.assign (ident x) .assign a))]
          | _ => .object [.spread (.binary a .or b)]), st)
    -- the accessors of an object literal, of a computed and of a quoted name
    | 74 =>
        let (n, st) := genName st
        let (s, st) := genString st
        let (e, st) := genExpr (d - 1) st
        (.object [.method .get (.computed (ident n)) [] [.return_ (some e)],
          .method .set (.string s) [.plain (.ident (nes "value"))] []], st)
    -- a `new` whose callee is a call or a member of one
    | 75 =>
        let (f, st) := genName st
        let (n, st) := genMemberName st
        let (args, st) := genExprs (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .new (.call (ident f) []) args
          else .new (.dot (.call (ident f) []) (nes n)) args), st)
    -- the comma operator where it stands in an arrow body or an element
    | 76 =>
        let (a, st) := genExpr (d - 1) st
        let (b, st) := genExpr (d - 1) st
        let (ps, st) := genParams st
        let (k, st) := rand st 2
        ((if k == 0 then .arrow false ps (.expr (.seq a b))
          else .array [.elem (.seq a b)]), st)
    -- a destructuring assignment into a nested pattern
    | 77 =>
        let (x, st) := genName st
        let (y, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (f, st) := genAtom st
        (.assignPattern
          (.object [⟨.string "a key",
              .array [.elem (.withDefault (.ident (nes x)) f), .hole,
                .rest (.ident (nes y))]⟩] none) e, st)
    -- a `require` of a module, and the `define` of one
    | 78 =>
        let (m, st) := freshName st "a/rather/long/module/path/"
        let (n, st) := genMemberName st
        let (body, st) := genStmts (d - 1) true false st
        let (k, st) := rand st 6
        ((match k with
          | 0 => .call (ident "require") [.string m]
          | 1 => .dot (.call (ident "require") [.string m]) (nes n)
          | 2 => .call (.dot (ident "require") (nes "resolve")) [.string m]
          | 3 => .call (ident "require") [.string m, .arrow false [] (.block body)]
          | 4 => .call (ident "define")
              [.array [.elem (.string m)], .arrow false [.plain (.ident (nes "item"))] (.block body)]
          | _ => .call (ident "define")
              [.string m, .array [.elem (.string m)], .arrow false [] (.block body)]), st)
    -- a call of a test framework, and one which only looks like it
    | 79 =>
        let (name, st) := freshName st "the name of the test number "
        let (body, st) := genStmts (d - 1) true false st
        let (k, st) := rand st 6
        let fn : MiniExpr := .arrow false [] (.block body)
        ((match k with
          | 0 => .call (ident "describe") [.string name, fn]
          | 1 => .call (.dot (ident "it") (nes "only")) [.string name,
              .func false false none [] body]
          | 2 => .call (ident "test") [.string name,
              .arrow false [.plain (.ident (nes "done"))] (.block body), .number (JSNumber.ofNat 2500)]
          | 3 => .call (ident "beforeEach") [.call (ident "inject") [fn]]
          | 4 => .call (ident "it") [.template none name [], .call (ident "fakeAsync") [fn]]
          | _ => .call (ident "describeTheThing") [.string name, fn]), st)
    -- a member chain of a random head and of random links
    | 80 =>
        let (head, st) := genChainHead d st
        let (n, st) := rand st 5
        genChainLinks (n + 1) d head st
    -- a JSX element on its own
    | 81 =>
        let (n, st) := genJsxNode d st
        (.jsx n, st)
    -- a JSX element in the places one is usually written
    | 82 =>
        let (n, st) := genJsxNode (d - 1) st
        let (e, st) := genExpr (d - 1) st
        let (f, st) := genName st
        let (k, st) := rand st 6
        ((match k with
          | 0 => .arrow false [.plain (.ident (nes "props"))] (.expr (.jsx n))
          | 1 => .ternary e (.jsx n) .null
          | 2 => .binary e .and (.jsx n)
          | 3 => .call (ident f) [.jsx n]
          | 4 => .array [.elem (.jsx n), .elem e]
          | _ => .object [.keyValue (.ident (nes "icon")) (.jsx n)]), st)
    -- the list of elements a call of `map` builds
    | 83 =>
        let (n, st) := genJsxNode (d - 1) st
        let (m, st) := genJsxNode (d - 1) st
        let (xs, st) := genName st
        let (k, st) := rand st 2
        let body : MiniExpr :=
          .call (.dot (ident xs) (nes "map"))
            [.arrow false [.plain (.ident (nes "item"))] (.expr (.jsx m))]
        ((match k with
          | 0 => .jsx (.element (.ident (nes "ul")) [] (some [.expr body]))
          | _ => .jsx (.element (.ident (nes "div")) [.attr (.ident (nes "className"))
              (some (.string "a-long-class-name"))]
              (some [.node n, .text " ", .expr body]))), st)
    -- an assignment of an assignment, and one to an index
    | _ =>
        let (x, st) := genName st
        let (y, st) := genName st
        let (e, st) := genExpr (d - 1) st
        let (k, st) := rand st 2
        ((if k == 0 then .assign (ident x) .assign (.assign (ident y) .assign e)
          else .assign (.index (ident x) (.string y)) .divide e), st)

/-- A head a member chain may start from: the shapes prettier's layout
tells apart, from `this` and a short name to a call and a literal. -/
partial def genChainHead (d : Nat) (st : St) : MiniExpr × St :=
  let (k, st) := rand st 10
  match k with
  | 0 => (.this, st)
  | 1 => (ident "z", st)
  | 2 => (ident "_", st)
  | 3 => (ident "theConfigurationObject", st)
  | 4 => (ident "TheFactoryName", st)
  | 5 =>
      let (args, st) := genExprs (d - 1) st
      (.call (ident "computeTheValue") args, st)
  | 6 => (.call (ident "require") [.string "a/module/path"], st)
  | 7 => (.object [.shorthand (nes "a")], st)
  | 8 => (.array [.elem (.number (JSNumber.ofNat 1))], st)
  | _ => (.template none "text" [], st)

/-- `n` further links of a member chain, read off `e`. -/
partial def genChainLinks (n d : Nat) (e : MiniExpr) (st : St) : MiniExpr × St :=
  match n with
  | 0 => (e, st)
  | n + 1 =>
      let (k, st) := rand st 6
      let (nm, st) := genMemberName st
      let (args, st) := genExprs (d - 1) st
      let next : MiniExpr :=
        match k with
        | 0 | 1 => .dot e (nes nm)
        | 2 => .index e (.number (JSNumber.ofNat 0))
        | 3 | 4 => .call (.dot e (nes nm)) args
        | _ => .call e args
      genChainLinks n d next st

/-- Between one and three members of a class. -/
partial def genClassElements (d : Nat) (st : St) : List MiniClassElement × St :=
  let (n, st) := rand st 3
  genClassElementList (n + 1) d st

/-- Exactly `n` members of a class. -/
partial def genClassElementList (n d : Nat) (st : St) : List MiniClassElement × St :=
  match n with
  | 0 => ([], st)
  | n + 1 =>
      let (k, st) := rand st 10
      let (key, st) := genName st
      let (elem, st) : MiniClassElement × St :=
        match k with
        | 0 =>
            let (ps, st) := genParams st
            let (body, st) := genStmts d true false st
            (.method [] false .normal (.ident (nes key)) ps body, st)
        | 1 =>
            let (body, st) := genStmts d true false st
            (.method [] true .normal (.ident (nes key)) [] body, st)
        | 2 =>
            let (body, st) := genStmts d true false st
            (.method [] false .get (.ident (nes key)) [] body, st)
        | 3 =>
            let (body, st) := genStmts d true false st
            (.method [] false .set (.ident (nes key)) [.plain (.ident (nes "value"))] body, st)
        | 4 =>
            let (body, st) := genStmts d true false st
            (.method [] false .generator (.ident (nes key)) [] body, st)
        | 8 =>
            let (ps, st) := genParams st
            let (body, st) := genStmts d true false st
            let (j, st) := rand st 2
            (.method [] (j == 0) .async (.ident (nes key)) ps body, st)
        | 9 =>
            let (body, st) := genStmts d true false st
            (.method [] false .asyncGenerator (.ident (nes key)) [] body, st)
        | 5 =>
            let (e, st) := genExpr d st
            let (j, st) := rand st 3
            (.field [] false (j == 0) (.ident (nes key)) (some e), st)
        | 6 =>
            -- a private name may be declared only once in its class, so it
            -- is taken from the fresh names rather than from `names`
            let (priv, st) := freshName st "field"
            let (e, st) := genExpr d st
            let (j, st) := rand st 3
            (.field [] true (j == 0) (.private_ (nes priv)) (some e), st)
        | _ =>
            let (body, st) := genStmts d false false st
            (.staticBlock body, st)
      let (rest, st) := genClassElementList n d st
      (elem :: rest, st)

/-- A random binding pattern. -/
partial def genPattern (st : St) : MiniPattern × St :=
  let (k, st) := rand st 5
  let (x, st) := genName st
  let (y, st) := genName st
  match k with
  | 0 => (.object [⟨.ident (nes x), .ident (nes x)⟩] none, st)
  | 1 => (.object [⟨.ident (nes x), .ident (nes y)⟩] (some (.ident (nes "rest"))), st)
  | 2 => (.array [.elem (.ident (nes x)), .hole, .rest (.ident (nes y))], st)
  | 3 =>
      let (e, st) := genAtom st
      (.array [.elem (.withDefault (.ident (nes x)) e)], st)
  | _ => (.ident (nes x), st)

/-- A random leaf expression. -/
partial def genAtom (st : St) : MiniExpr × St :=
  let (k, st) := rand st 8
  match k with
  | 0 | 1 | 2 =>
      let (n, st) := genName st
      (ident n, st)
  | 3 =>
      let (m, st) := rand st 1000
      (.number (JSNumber.ofNat m), st)
  | 4 =>
      let (s, st) := genString st
      (.string s, st)
  | 5 => (.true_, st)
  | 6 => (.null, st)
  | _ => (.number (.decimal 15 (-1)), st)

/-- A random string literal value. -/
partial def genString (st : St) : String × St :=
  let (k, st) := rand st strings.size
  (strings[k]!, st)

/-- Between zero and three random expressions. -/
partial def genExprs (d : Nat) (st : St) : List MiniExpr × St :=
  let (n, st) := rand st 4
  genExprList n d st

/-- Exactly `n` random expressions. -/
partial def genExprList (n d : Nat) (st : St) : List MiniExpr × St :=
  match n with
  | 0 => ([], st)
  | n + 1 =>
      let (e, st) := genExpr d st
      let (rest, st) := genExprList n d st
      (e :: rest, st)

/-- Between zero and two random parameters. -/
partial def genParams (st : St) : List MiniParam × St :=
  let (n, st) := rand st 3
  genParamList n st

/-- Exactly `n` random parameters. -/
partial def genParamList (n : Nat) (st : St) : List MiniParam × St :=
  match n with
  | 0 => ([], st)
  | n + 1 =>
      let (k, st) := rand st 6
      let (x, st) := genName st
      let (p, st) : MiniParam × St :=
        match k with
        | 0 => (.plain (.object [⟨.ident (nes x), .ident (nes x)⟩] none), st)
        | 1 =>
            let (e, st) := genAtom st
            (.plain (.withDefault (.ident (nes x)) e), st)
        | _ => (.plain (.ident (nes x)), st)
      let (rest, st) := genParamList n st
      -- a rest parameter may only come last
      let p := match p, rest with
        | .plain (.ident n), [] => if k == 5 then .rest (.ident n) else .plain (.ident n)
        | p, _ => p
      (p :: rest, st)

/-- Between one and three random properties of an object literal. -/
partial def genProps (d : Nat) (st : St) : List MiniProperty × St :=
  let (n, st) := rand st 3
  genPropList (n + 1) d st

/-- Exactly `n` random properties. -/
partial def genPropList (n d : Nat) (st : St) : List MiniProperty × St :=
  match n with
  | 0 => ([], st)
  | n + 1 =>
      let (k, st) := rand st 8
      let (key, st) := genName st
      let (member, st) := genMemberName st
      let (prop, st) : MiniProperty × St :=
        match k with
        | 0 =>
            let (e, st) := genExpr d st
            (.spread e, st)
        | 1 => (.shorthand (nes key), st)
        | 2 =>
            let (ps, st) := genParams st
            let (body, st) := genStmts d true false st
            (.method .normal (.ident (nes key)) ps body, st)
        | 3 =>
            let (s, st) := genString st
            let (e, st) := genExpr d st
            (.keyValue (.string s) e, st)
        | 6 =>
            let (ps, st) := genParams st
            let (body, st) := genStmts d true false st
            (.method .async (.ident (nes key)) ps body, st)
        | 7 =>
            let (body, st) := genStmts d true false st
            (.method .asyncGenerator (.ident (nes key)) [] body, st)
        | _ =>
            let (e, st) := genExpr d st
            (.keyValue (.ident (nes member)) e, st)
      let (rest, st) := genPropList n d st
      (prop :: rest, st)

/-- Between one and three random statements. -/
partial def genStmts (d : Nat) (inFunction inLoop : Bool) (st : St) :
    List MiniStatement × St :=
  let (n, st) := rand st 3
  genStmtList (n + 1) d inFunction inLoop st

/-- Exactly `n` random statements. -/
partial def genStmtList (n d : Nat) (inFunction inLoop : Bool) (st : St) :
    List MiniStatement × St :=
  match n with
  | 0 => ([], st)
  | n + 1 =>
      let (s, st) := genStmt d inFunction inLoop st
      let (rest, st) := genStmtList n d inFunction inLoop st
      (s :: rest, st)

/-- A random statement of depth at most `d`. -/
partial def genStmt (d : Nat) (inFunction inLoop : Bool) (st : St) :
    MiniStatement × St :=
  let (k, st) := rand st (if d == 0 then 3 else 50)
  match k with
  | 0 =>
      let (e, st) := genExpr d st
      (.expr e, st)
  | 1 =>
      let (x, st) := freshName st "value"
      let (e, st) := genExpr d st
      (.decl .const ⟨⟨.ident (nes x), some e⟩, []⟩, st)
  | 2 =>
      if inFunction then
        let (e, st) := genExpr d st
        (.return_ (some e), st)
      else
        let (e, st) := genExpr d st
        (.expr e, st)
  | 3 =>
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      (.if_ c (.block body) none, st)
  | 4 =>
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      let (alt, st) := genStmts (d - 1) inFunction inLoop st
      (.if_ c (.block body) (some (.block alt)), st)
  | 5 =>
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      (.while_ c (.block body), st)
  | 6 =>
      let (x, st) := freshName st "item"
      let (o, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      let (j, st) := rand st 4
      let head : MiniForHead :=
        if j == 0 then .usingDecl false (.ident (nes x)) else .decl .const (.ident (nes x))
      (.forOf false head o (.block body), st)
  | 7 =>
      let (x, st) := freshName st "index"
      let (limit, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      (.for_ (.decl .let_ ⟨⟨.ident (nes x), some (.number (JSNumber.ofNat 0))⟩, []⟩)
        (some (.binary (ident x) .lt limit)) (some (.postfix (ident x) .incr))
        (.block body), st)
  | 8 =>
      let (fn, st) := freshName st "helper"
      let (ps, st) := genParams st
      let (body, st) := genStmts (d - 1) true false st
      (.funcDecl false false (nes fn) ps body, st)
  | 9 =>
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      let (handler, st) := genStmts (d - 1) inFunction inLoop st
      (.try_ body (.catches ⟨⟨.ident (nes "error"), none, handler⟩, []⟩ .none), st)
  | 10 =>
      let (e, st) := genExpr (d - 1) st
      (.throw e, st)
  | 11 =>
      let (disc, st) := genExpr (d - 1) st
      let (a, st) := genExpr 0 st
      let (body, st) := genStmts (d - 1) inFunction true st
      (.switch disc [.case a body, .default []], st)
  | 12 =>
      if inLoop then (.break_ none, st)
      else
        let (e, st) := genExpr d st
        (.expr e, st)
  | 13 =>
      let (cls, st) := freshName st "TheClass"
      let (m, st) := genName st
      let (ps, st) := genParams st
      let (body, st) := genStmts (d - 1) true false st
      (.classDecl [] (nes cls) none
        [.method [] false .normal (.ident (nes m)) ps body], st)
  | 14 =>
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      (.block body, st)
  | 15 =>
      let (x, st) := freshName st "value"
      let (e, st) := genExpr d st
      (.decl .let_ ⟨⟨.ident (nes x), some e⟩, []⟩, st)
  | 16 =>
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      (.doWhile (.block body) c, st)
  | 17 =>
      let (x, st) := freshName st "key"
      let (o, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      (.forIn (.decl .const (.ident (nes x))) o (.block body), st)
  -- a labelled loop, and a `break` or a `continue` that names it
  | 18 =>
      let (lbl, st) := freshName st "outer"
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      let (k, st) := rand st 2
      let jump : MiniStatement :=
        if k == 0 then .break_ (some (nes lbl)) else .continue_ (some (nes lbl))
      (.labelled (nes lbl) (.while_ c (.block (body ++ [jump]))), st)
  -- a declaration that destructures
  | 19 =>
      let (pat, st) := genPattern st
      let (e, st) := genExpr (d - 1) st
      (.decl .const ⟨⟨pat, some e⟩, []⟩, st)
  | 20 =>
      let (cls, st) := freshName st "TheClass"
      let (base, st) := genName st
      let (prop, st) := genMemberName st
      let (elems, st) := genClassElements (d - 1) st
      let (k, st) := rand st 4
      -- a superclass which is a property read is the one prettier may put
      -- on a line of its own
      let heritage : Option MiniExpr :=
        match k with
        | 0 => none
        | 1 => some (ident base)
        | 2 => some (.dot (ident base) (nes prop))
        | _ => some (.index (.dot (ident base) (nes prop)) (.string "key"))
      (.classDecl [] (nes cls) heritage elems, st)
  | 21 =>
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      let (fin, st) := genStmts (d - 1) inFunction inLoop st
      let (k, st) := rand st 2
      if k == 0 then (.try_ body (.finallyOnly fin), st)
      else
        let (pat, st) := genPattern st
        (.try_ body (.catches ⟨⟨pat, none, fin⟩, []⟩ .none), st)
  -- a `switch` of several cases
  | 22 =>
      let (disc, st) := genExpr (d - 1) st
      let (a, st) := genExpr 0 st
      let (b, st) := genExpr 0 st
      let (body, st) := genStmts (d - 1) inFunction true st
      let (other, st) := genStmts (d - 1) inFunction true st
      (.switch disc [.case a body, .default other, .case b []], st)
  -- a declaration of several names, and one of a `var`
  | 23 =>
      let (x, st) := freshName st "value"
      let (y, st) := freshName st "value"
      let (e, st) := genExpr (d - 1) st
      let (f, st) := genExpr (d - 1) st
      let (k, st) := rand st 2
      if k == 0 then
        (.decl .var ⟨⟨.ident (nes x), some e⟩, [⟨.ident (nes y), some f⟩]⟩, st)
      else (.decl .let_ ⟨⟨.ident (nes x), none⟩, [⟨.ident (nes y), some f⟩]⟩, st)
  -- an `if` whose branches are not blocks
  | 24 =>
      let (c, st) := genExpr (d - 1) st
      let (a, st) := genStmt (d - 1) inFunction inLoop st
      let (b, st) := genStmt (d - 1) inFunction inLoop st
      let (k, st) := rand st 3
      let a := asSingleStmt a
      let b := asSingleStmt b
      ((match k with
        | 0 => .if_ c a none
        | 1 => .if_ c a (some b)
        | _ => .if_ c (.block [a]) (some b)), st)
  -- a loop whose body is not a block
  | 25 =>
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmt (d - 1) inFunction true st
      let (k, st) := rand st 3
      let body := asSingleStmt body
      ((match k with
        | 0 => .while_ c body
        | 1 => .doWhile body c
        | _ => .while_ c .empty), st)
  -- a `using` declaration, which disposes of what it binds.  It stands in
  -- a block, since a script may not have one at its top level
  | 26 =>
      let (x, st) := freshName st "resource"
      let (y, st) := freshName st "resource"
      let (e, st) := genExpr (d - 1) st
      let (f, st) := genExpr (d - 1) st
      let (k, st) := rand st 2
      ((if k == 0 then .block [.using_ false ⟨⟨.ident (nes x), some e⟩, []⟩]
        else .block [.using_ false
          ⟨⟨.ident (nes x), some e⟩, [⟨.ident (nes y), some f⟩]⟩]), st)
  -- a labelled statement which is not a loop
  | 27 =>
      let (lbl, st) := freshName st "block"
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      (.labelled (nes lbl) (.block (body ++ [.break_ (some (nes lbl))])), st)
  -- the head of a `for (;;)`, where an `in` has to be parenthesised
  | 28 =>
      let (x, st) := freshName st "index"
      let (s, st) := genString st
      let (o, st) := genExpr 0 st
      let (body, st) := genStmts (d - 1) inFunction true st
      let (k, st) := rand st 2
      let init : MiniForInit :=
        if k == 0 then .expr (.binary (.string s) .inOp o)
        else .decl .let_ ⟨⟨.ident (nes x), some (.binary (.string s) .inOp o)⟩, []⟩
      (.for_ init none none (.block body), st)
  -- a `for ... of` and a `for ... in` which assign to something that
  -- already exists
  | 29 =>
      let (x, st) := freshName st "item"
      let (o, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction true st
      let (k, st) := rand st 2
      let decl : MiniStatement := .decl .let_ ⟨⟨.ident (nes x), none⟩, []⟩
      let loop : MiniStatement :=
        if k == 0 then .forOf false (.pattern (.ident (nes x))) o (.block body)
        else .forIn (.pattern (.ident (nes x))) o (.block body)
      (.block [decl, loop], st)
  -- a declaration which destructures into a nested pattern
  | 30 =>
      let (x, st) := freshName st "value"
      let (y, st) := freshName st "value"
      let (e, st) := genExpr (d - 1) st
      let (f, st) := genAtom st
      (.decl .const
        ⟨⟨.object [⟨.string "a key", .array [.elem (.withDefault (.ident (nes x)) f), .hole]⟩,
            ⟨.computed (.string "k"), .ident (nes y)⟩] none,
          some e⟩, []⟩, st)
  -- a class of a static block and of a field of a computed name
  | 31 =>
      let (cls, st) := freshName st "TheClass"
      let (n, st) := genName st
      let (e, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) false false st
      (.classDecl [ident "logged"] (nes cls) none
        [.staticBlock body, .field [] false false (.computed (.string n)) (some e),
         .method [] false .get (.private_ (nes "count")) [] [.return_ (some (.number 0))]], st)
  -- an empty statement, which prettier drops
  | 32 =>
      let (e, st) := genExpr (d - 1) st
      let (k, st) := rand st 2
      ((if k == 0 then .empty else .block [.empty, .expr e, .empty]), st)
  -- a `with` statement, which only a script may have
  | 33 =>
      let (o, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      (.with_ o (.block body), st)
  -- an `await using` declaration, inside the asynchronous function it
  -- belongs to
  | 34 =>
      let (fn, st) := freshName st "helper"
      let (x, st) := freshName st "resource"
      let (e, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) true false st
      (.funcDecl true false (nes fn) []
        (.using_ true ⟨⟨.ident (nes x), some e⟩, []⟩ :: body), st)
  -- a `switch` of an empty case, of a case whose body is a block, and of
  -- a `default` which is not last
  | 35 =>
      let (disc, st) := genExpr (d - 1) st
      let (a, st) := genExpr 0 st
      let (b, st) := genExpr 0 st
      let (body, st) := genStmts (d - 1) inFunction true st
      let (other, st) := genStmts (d - 1) inFunction true st
      (.switch disc [.case a [], .case b [.block body, .break_ none], .default other], st)
  -- a function which returns an operator expression
  | 36 =>
      let (fn, st) := freshName st "helper"
      let (a, st) := genExpr (d - 1) st
      let (b, st) := genExpr (d - 1) st
      let (c, st) := genExpr (d - 1) st
      let (k, st) := rand st 2
      (.funcDecl false false (nes fn) []
        [.return_ (some (if k == 0 then .binary (.binary a .plus b) .times c
          else .ternary a b c))], st)
  -- a class whose parent is an expression, and whose constructor calls it
  | 37 =>
      let (cls, st) := freshName st "TheClass"
      let (base, st) := genName st
      let (args, st) := genExprs (d - 1) st
      let (ps, st) := genParams st
      let (body, st) := genStmts (d - 1) true false st
      (.classDecl [] (nes cls) (some (.call (ident "mixin") [ident base]))
        [.method [] false .normal (.ident (nes "constructor")) ps
          (.expr (.superCall args) :: body)], st)
  -- an asynchronous function declaration, and a generator one
  | 38 =>
      let (fn, st) := freshName st "helper"
      let (e, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) true false st
      let (k, st) := rand st 2
      ((if k == 0 then .funcDecl true false (nes fn) [] (.expr (.await e) :: body)
        else .funcDecl false true (nes fn) [] (.expr (.yield (some e)) :: body)), st)
  -- a `throw` of a newly built error, and an assignment statement
  | 39 =>
      let (e, st) := genExpr (d - 1) st
      let (n, st) := genName st
      let (k, st) := rand st 2
      ((if k == 0 then .throw (.new (ident "Error") [.template none "bad " [⟨e, ""⟩]])
        else .expr (.assign (.dot (ident n) (nes "property")) .assign e)), st)
  -- a function of many parameters
  | 40 =>
      let (fn, st) := freshName st "helper"
      let (n, st) := rand st 4
      let (body, st) := genStmts (d - 1) true false st
      let ps : List MiniParam :=
        (List.range (n + 3)).map fun i => .plain (.ident (nes (names[i % names.size]!)))
      (.funcDecl false false (nes fn) ps body, st)
  -- a class of several members
  | 41 =>
      let (cls, st) := freshName st "TheClass"
      let (n1, st) := genName st
      let (n2, st) := genName st
      let (e, st) := genExpr (d - 1) st
      -- a static block may hold no `return`
      let (body, st) := genStmts (d - 1) false false st
      (.classDecl [] (nes cls) none
        [.field [] false false (.ident (nes n1)) (some e),
         .method [] false .get (.ident (nes n2)) [] [.return_ (some (ident n1))],
         .method [] false .set (.ident (nes n2)) [.plain (.ident (nes "value"))] [],
         .staticBlock body], st)
  -- a `for (;;)` whose head is empty, or whose update is a comma operator
  | 43 =>
      let (x, st) := freshName st "index"
      let (body, st) := genStmts (d - 1) inFunction true st
      let (k, st) := rand st 3
      let decl : MiniStatement := .decl .let_ ⟨⟨.ident (nes x), some (.number 0)⟩, []⟩
      ((match k with
        | 0 => .block [.for_ .none none none (.block (body ++ [.break_ none]))]
        | 1 => .block [decl,
            .for_ .none (some (.binary (ident x) .lt (.number 10)))
              (some (.seq (.postfix (ident x) .incr) (.assign (ident x) .plus (.number 0))))
              (.block body)]
        | _ => .block [decl,
            .for_ (.expr (.assign (ident x) .assign (.number 0))) none none
              (.block (body ++ [.break_ none]))]), st)
  -- a chain of `else if`, and an `if` whose branch is an empty statement
  | 44 =>
      let (a, st) := genExpr (d - 1) st
      let (b, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      let (other, st) := genStmts (d - 1) inFunction inLoop st
      let (k, st) := rand st 2
      ((if k == 0 then
          .if_ a (.block body) (some (.if_ b (.block other) (some (.block []))))
        else .if_ a .empty (some (.block other))), st)
  -- a class of private members, of a private accessor pair and of a
  -- static private method
  | 45 =>
      let (cls, st) := freshName st "TheClass"
      let (fld, st) := freshName st "field"
      let (acc, st) := freshName st "field"
      let (m, st) := freshName st "method"
      let (e, st) := genExpr (d - 1) st
      (.classDecl [] (nes cls) none
        [ .field [] false false (.private_ (nes fld)) (some e),
          .method [] true .normal (.private_ (nes m)) [] [],
          .method [] false .get (.private_ (nes acc)) []
            [.return_ (some (.privateDot .this (nes fld)))],
          .method [] false .set (.private_ (nes acc)) [.plain (.ident (nes "value"))] [] ], st)
  -- a declaration of several declarators which destructure
  | 46 =>
      let (x, st) := freshName st "value"
      let (y, st) := freshName st "value"
      let (pat, st) := genPattern st
      let (e, st) := genExpr (d - 1) st
      let (f, st) := genExpr (d - 1) st
      (.decl .const ⟨⟨pat, some e⟩,
        [⟨.ident (nes x), some f⟩, ⟨.array [.elem (.ident (nes y))], some (.array [])⟩]⟩, st)
  -- a `do ... while` and a loop whose body is a single statement, and a
  -- label around a label
  | 47 =>
      let (lbl, st) := freshName st "outer"
      let (inner, st) := freshName st "inner"
      let (c, st) := genExpr (d - 1) st
      let (body, st) := genStmt (d - 1) inFunction true st
      let (k, st) := rand st 3
      let body := asSingleStmt body
      ((match k with
        | 0 => .labelled (nes lbl) (.labelled (nes inner)
            (.while_ c (.block [.break_ (some (nes lbl))])))
        | 1 => .doWhile body c
        | _ => .forOf false (.decl .const (.ident (nes "item"))) c body), st)
  -- a `debugger` statement, alone or as the body of a loop or of an `if`
  | 48 =>
      let (c, st) := genExpr (d - 1) st
      let (k, st) := rand st 4
      ((match k with
        | 0 => .debugger
        | 1 => .block [.debugger, .expr c]
        | 2 => .if_ c .debugger (some .debugger)
        | _ => .while_ c .debugger), st)
  -- an asynchronous function of a `for await (... of ...)` loop
  | 49 =>
      let (fn, st) := freshName st "consume"
      let (x, st) := freshName st "item"
      let (o, st) := genExpr (d - 1) st
      let (body, st) := genStmts (d - 1) true true st
      let (k, st) := rand st 3
      let loop : MiniStatement :=
        match k with
        | 0 => .forOf true (.usingDecl true (.ident (nes x))) o (.block body)
        | 1 => .forOf true (.pattern (.ident (nes x))) o (.block [.expr (.await (.ident (nes x)))])
        | _ => .forOf true (.decl .let_ (.array [.elem (.ident (nes x))])) o (.block body)
      (.funcDecl true false (nes fn) [] [loop], st)
  -- a `try` of a `catch` and a `finally`, and one of a `finally` only
  | _ =>
      let (body, st) := genStmts (d - 1) inFunction inLoop st
      let (handler, st) := genStmts (d - 1) inFunction inLoop st
      let (fin, st) := genStmts (d - 1) inFunction inLoop st
      let (pat, st) := genPattern st
      (.try_ body (.catches ⟨⟨pat, none, handler⟩, []⟩ (.some fin)), st)

/-- A random attribute of a JSX element. -/
partial def genJsxAttr (d : Nat) (st : St) : MiniJSXAttribute × St :=
  let (k, st) := rand st 12
  let (n, st) := rand st jsxAttrNames.size
  let (ns, st) := rand st 8
  -- now and then a namespaced name, `xlink:href`
  let name : JSXName :=
    if ns == 0 then .namespaced (nes "xlink") (nes jsxAttrNames[n]!)
    else .ident (nes jsxAttrNames[n]!)
  match k with
  | 0 => (.attr name none, st)
  | 1 | 2 | 3 =>
      let (i, st) := rand st strings.size
      (.attr name (some (.string strings[i]!)), st)
  | 9 =>
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      (.spread e, st)
  -- an element written as the value of an attribute, between braces and
  -- written straight after the `=`
  | 10 =>
      if d == 0 then (.attr name none, st)
      else
        let (m, st) := genJsxNode (d - 1) st
        let (b, st) := rand st 3
        -- a fragment written as the value, which has no tag to hold it
        let m := if b == 2 then MiniJSXNode.fragment [.text "text"] else m
        (.attr name (some (if b == 0 then .node m else .expr (.jsx m))), st)
  | _ =>
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      (.attr name (some (.expr e)), st)

/-- Up to three random attributes of a JSX element. -/
partial def genJsxAttrs (d : Nat) (st : St) : List MiniJSXAttribute × St :=
  let (n, st) := rand st 4
  go n st
where
  go : Nat → St → List MiniJSXAttribute × St
    | 0, st => ([], st)
    | k + 1, st =>
        let (a, st) := genJsxAttr d st
        let (rest, st) := go k st
        (a :: rest, st)

/-- A random child of a JSX element. -/
partial def genJsxChild (d : Nat) (st : St) : MiniJSXChild × St :=
  let (k, st) := rand st 11
  match k with
  | 0 | 1 | 2 | 3 =>
      let (i, st) := rand st jsxTexts.size
      (.text jsxTexts[i]!, st)
  | 4 => (.expr (.string " "), st)
  -- `{}`, a substitution with nothing in it
  | 7 => (.emptyExpr, st)
  -- a nested fragment
  | 10 =>
      if d == 0 then (.text "x", st)
      else
        let (kids, st) := genJsxChildren (d - 1) st
        (.node (.fragment kids), st)
  | 5 | 6 =>
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      let (s, st) := rand st 8
      -- now and then `{...children}` rather than `{children}`
      (.expr (if s == 0 then .spread e else e), st)
  | _ =>
      if d == 0 then
        let (i, st) := rand st jsxTexts.size
        (.text jsxTexts[i]!, st)
      else
        let (n, st) := genJsxNode (d - 1) st
        (.node n, st)

/-- Up to three random children of a JSX element. -/
partial def genJsxChildren (d : Nat) (st : St) : List MiniJSXChild × St :=
  let (n, st) := rand st 4
  go n st
where
  go : Nat → St → List MiniJSXChild × St
    | 0, st => ([], st)
    | k + 1, st =>
        let (c, st) := genJsxChild d st
        let (rest, st) := go k st
        (c :: rest, st)

/-- A random JSX element or fragment. -/
partial def genJsxNode (d : Nat) (st : St) : MiniJSXNode × St :=
  let (k, st) := rand st 12
  if k == 0 then
    let (kids, st) := genJsxChildren d st
    (.fragment kids, st)
  else
    let (i, st) := rand st jsxNames.size
    let (m, st) := rand st 4
    let name : JSXName :=
      match m with
      | 0 => .member (.ident (nes "Foo")) (nes jsxNames[i]!)
      | 1 => .namespaced (nes "svg") (nes "path")
      -- a name read through two members, `Foo.Bar.Baz`
      | 2 => .member (.member (.ident (nes "Foo")) (nes "Bar")) (nes jsxNames[i]!)
      | _ => .ident (nes jsxNames[i]!)
    let (attrs, st) := genJsxAttrs d st
    let (c, st) := rand st 3
    if c == 0 then (.element name attrs none, st)
    else
      let (kids, st) := genJsxChildren d st
      (.element name attrs (some kids), st)

end

/-- A random `import` or `export` declaration.  Every name it binds, and
every name it exports, is a fresh one, so that no program declares or
exports the same name twice.  Only the first item of a program may be a
default export, since a module may have at most one. -/
def genModuleItem (d : Nat) (allowDefault : Bool) (st : St) : MiniModuleItem × St :=
  let (k, st) := rand st 10
  let k := if k == 7 && !allowDefault then 6 else k
  let (m, st) := freshName st "mod"
  match k with
  | 0 => (.importDecl (.bare (nes m) []), st)
  | 1 =>
      let (j, st) := rand st 3
      let attrs : List ImportAttr :=
        match j with
        | 0 => [⟨"type", "json"⟩]
        | 1 => [⟨"other", "a rather long attribute value here"⟩]
        | _ => [⟨"type", "json"⟩, ⟨"other", "value"⟩, ⟨"a key", "third"⟩]
      (.importDecl (.bare (nes m) attrs), st)
  | 2 =>
      let (x, st) := freshName st "imported"
      let (y, st) := freshName st "imported"
      let (z, st) := freshName st "imported"
      (.importDecl (.clause (MiniImportClause.mk! (some (nes x)) none
        (some [⟨nes "name", some (nes y)⟩, ⟨nes z, none⟩]) (nes m))), st)
  | 3 =>
      let (ns, st) := freshName st "imported"
      let (x, st) := freshName st "imported"
      let (j, st) := rand st 3
      -- a namespace import, an empty list of names, and one beside a
      -- default import, which prettier writes without it
      ((match j with
        | 0 => .importDecl (.clause (MiniImportClause.mk! none (some (nes ns)) none (nes m)))
        | 1 => .importDecl (.clause (MiniImportClause.mk! none none (some []) (nes m)))
        | _ => .importDecl (.clause (MiniImportClause.mk! (some (nes x)) none (some [])
            (nes m)))), st)
  | 4 =>
      let (ns, st) := freshName st "exported"
      let (j, st) := rand st 2
      (.exportDecl (.all (if j == 0 then none else some (nes ns)) (nes m) []), st)
  | 5 =>
      let (x, st) := freshName st "exported"
      (.exportDecl (.fromClause [⟨nes "name", some (nes x)⟩] (nes m) []), st)
  | 6 =>
      let (x, st) := freshName st "value"
      let (e, st) := genExpr d st
      (.exportDecl (.decl (.decl .const ⟨⟨.ident (nes x), some e⟩, []⟩)), st)
  -- `export default <expression>`
  | 7 =>
      let (e, st) := genExpr d st
      (.exportDecl (.defaultExpr e), st)
  -- `export { a as b };`, of names which are declared right before it
  | 8 =>
      let (x, st) := freshName st "value"
      let (y, st) := freshName st "exported"
      (.exportDecl (.locals [⟨nes x, some (nes y)⟩]), st)
  -- `export function`, and a named import of import attributes
  | _ =>
      let (k, st) := rand st 2
      if k == 0 then
        let (fn, st) := freshName st "exportedHelper"
        let (ps, st) := genParams st
        let (body, st) := genStmts d true false st
        (.exportDecl (.decl (.funcDecl false false (nes fn) ps body)), st)
      else
        let (x, st) := freshName st "imported"
        (.importDecl (.clause (MiniImportClause.mk! none none
          (some [⟨nes "name", some (nes x)⟩]) (nes m) [⟨"type", "json"⟩])), st)

/-- Exactly `n` random `import` or `export` declarations. -/
def genModuleItems (n d : Nat) (st : St) : List MiniModuleItem × St :=
  go n true st
where
  go : Nat → Bool → St → List MiniModuleItem × St
    | 0, _, st => ([], st)
    | n + 1, allowDefault, st =>
        let (item, st) := genModuleItem d allowDefault st
        let isDefault := match item with
          | .exportDecl (.defaultExpr _) => true
          | _ => false
        let (rest, st) := go n (allowDefault && !isDefault) st
        (item :: rest, st)

/-- A random program of `count` statements, each of depth at most `depth`,
preceded by up to two `import` or `export` declarations. -/
def genProgram (depth count : Nat) (st : St) : MiniProgram × St :=
  let (n, st) := rand st 3
  let (items, st) := genModuleItems n depth st
  let (stmts, st) := genStmtList count depth false false st
  (⟨items ++ stmts.map MiniModuleItem.stmt⟩, st)

/-! ## Programs built around JSX

The generator above writes a JSX element only now and then, among every
other shape of expression.  The one here writes nothing else: every
statement of a program it builds holds a JSX element, in one of the
positions a component writes one in.  It is what exercises the JSX layout
rules at a useful rate. -/

/-- A random statement built around a JSX element. -/
def genJsxStmt (d : Nat) (st : St) : MiniStatement × St :=
  let (k, st) := rand st 29
  let (node, st) := genJsxNode d st
  let (other, st) := genJsxNode (if d == 0 then 0 else d - 1) st
  let j : MiniExpr := .jsx node
  let j2 : MiniExpr := .jsx other
  match k with
  -- `const x = <jsx>;`
  | 0 =>
      let (x, st) := freshName st "element"
      (.decl .const ⟨⟨.ident (nes x), some j⟩, []⟩, st)
  -- `function C(props) { return <jsx>; }`
  | 1 =>
      let (f, st) := freshName st "Component"
      (.funcDecl false false (nes f) [.plain (.ident (nes "props"))] [.return_ (some j)], st)
  -- `const C = (props) => <jsx>;`
  | 2 =>
      let (f, st) := freshName st "Component"
      (.decl .const ⟨⟨.ident (nes f),
        some (.arrow false [.plain (.ident (nes "props"))] (.expr j))⟩, []⟩, st)
  -- `render(<jsx>, document.getElementById("root"));`
  | 3 =>
      (.expr (.call (ident "render")
        [j, .call (.dot (ident "document") (nes "getElementById")) [.string "root"]]), st)
  -- a JSX element standing alone as an expression statement
  | 4 => (.expr j, st)
  -- a conditional whose branches are elements
  | 5 =>
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      let (x, st) := freshName st "element"
      (.decl .const ⟨⟨.ident (nes x), some (.ternary e j j2)⟩, []⟩, st)
  -- an element written as the right operand of `&&`, inside a return
  | 6 =>
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      let (f, st) := freshName st "Component"
      (.funcDecl false false (nes f) [] [.return_ (some (.binary e .and j))], st)
  -- an array and an object holding elements
  | 7 =>
      let (x, st) := freshName st "elements"
      (.decl .const ⟨⟨.ident (nes x), some (.array [.elem j, .elem j2])⟩, []⟩, st)
  | 8 =>
      let (x, st) := freshName st "icons"
      (.decl .const ⟨⟨.ident (nes x),
        some (.object [.keyValue (.ident (nes "icon")) j,
          .keyValue (.ident (nes "label")) j2])⟩, []⟩, st)
  -- an element whose child is the list a call of `map` builds
  | 9 =>
      let (xs, st) := genName st
      let (x, st) := freshName st "list"
      let body : MiniExpr :=
        .call (.dot (ident xs) (nes "map"))
          [.arrow false [.plain (.ident (nes "item"))] (.expr j2)]
      (.decl .const ⟨⟨.ident (nes x),
        some (.jsx (.element (.ident (nes "ul")) [] (some [.expr body, .node node])))⟩, []⟩, st)
  -- an element written as the value of an attribute of another
  | 10 =>
      let (x, st) := freshName st "element"
      (.decl .const ⟨⟨.ident (nes x),
        some (.jsx (.element (.ident (nes "Layout"))
          [.attr (.ident (nes "header")) (some (.expr j)),
           .attr (.ident (nes "footer")) (some (.expr j2))] none))⟩, []⟩, st)
  -- a chain of arrow functions ending in an element
  | 11 =>
      let (f, st) := freshName st "render"
      (.decl .const ⟨⟨.ident (nes f),
        some (.arrow false [.plain (.ident (nes "props"))]
          (.expr (.arrow false [.plain (.ident (nes "state"))] (.expr j))))⟩, []⟩, st)
  -- an element read through a member access
  | 12 =>
      let (x, st) := freshName st "props"
      (.decl .const ⟨⟨.ident (nes x), some (.dot j (nes "props"))⟩, []⟩, st)
  -- an element returned from a call of a hook
  | 13 =>
      let (x, st) := freshName st "memo"
      (.decl .const ⟨⟨.ident (nes x),
        some (.call (ident "useMemo") [.arrow false [] (.expr j), .array []])⟩, []⟩, st)
  -- an element written inside a fragment, beside text and a substitution
  | 14 =>
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      let (x, st) := freshName st "element"
      (.decl .const ⟨⟨.ident (nes x),
        some (.jsx (.fragment [.node node, .text " and ", .expr e, .node other]))⟩, []⟩, st)
  -- an element assigned to something that already exists
  | 15 =>
      let (x, st) := genName st
      (.expr (.assign (.ident (nes x)) .assign j), st)
  -- an element written in a template literal, and one thrown
  | 16 =>
      let (x, st) := freshName st "markup"
      (.decl .const ⟨⟨.ident (nes x), some (.template none "before " [⟨j, " after"⟩])⟩, []⟩, st)
  | 17 => (.throw j, st)
  -- an element as the default value of a parameter, and as a class field
  | 18 =>
      let (f, st) := freshName st "Component"
      (.funcDecl false false (nes f)
        [.plain (.withDefault (.ident (nes "fallback")) j)] [.return_ (some j2)], st)
  | 19 =>
      let (c, st) := freshName st "Widget"
      (.classDecl [] (nes c) none
        [.field [] false false (.ident (nes "defaultContent")) (some j),
         .method [] false .normal (.ident (nes "render")) [] [.return_ (some j2)]], st)
  -- an element written in the body of an arrow function which is the
  -- argument of a call standing in a `{ }` of another element
  | 20 =>
      let (x, st) := freshName st "element"
      let (e, st) := genExpr (if d == 0 then 0 else d - 1) st
      (.decl .const ⟨⟨.ident (nes x),
        some (.jsx (.element (.ident (nes "div")) []
          (some [.expr (.call (ident "useCallback")
            [.arrow false [] (.expr (.seq j e))])])))⟩, []⟩, st)
  -- an element as the operand of a unary operator, and of a `typeof`
  | 21 => (.expr (.unary .not j), st)
  -- an element read through an optional chain, and one awaited
  | 22 =>
      let (x, st) := freshName st "props"
      (.decl .const ⟨⟨.ident (nes x),
        some (.chain j ⟨.dot true (nes "props"), []⟩)⟩, []⟩, st)
  -- an element written as the tag of a template literal, and one called
  | 23 =>
      let (x, st) := freshName st "markup"
      (.decl .const ⟨⟨.ident (nes x), some (.template (some j) "text " [⟨j2, ""⟩])⟩, []⟩, st)
  | 24 => (.expr (.call j [j2]), st)
  -- an element in the head of a statement, where a leftmost `<` asks for
  -- parentheses of its own
  | 25 => (.if_ j (.block [.expr j2]) (some (.block [])), st)
  | 26 =>
      let (b, st) := rand st 3
      match b with
      | 0 => (.while_ j (.block [.expr j2]), st)
      | 1 => (.doWhile (.block [.expr j2]) j, st)
      | _ => (.switch j [.case j2 [.break_ none]], st)
  -- an element in the head of a `for`, and one written as a computed key
  | 27 =>
      let (b, st) := rand st 2
      if b == 0 then (.forOf false (.decl .const (.ident (nes "item"))) j (.block [.expr j2]), st)
      else (.for_ (.expr j) (some j2) (some j) (.block []), st)
  | 28 =>
      let (x, st) := freshName st "table"
      (.decl .const ⟨⟨.ident (nes x),
        some (.object [.keyValue (.computed j) j2])⟩, []⟩, st)
  -- an element among the arguments of a call whose last argument is a function
  | _ =>
      let (f, st) := genName st
      (.expr (.call (ident f) [j, .arrow false [.plain (.ident (nes "event"))] (.expr j2)]), st)

/-- Exactly `n` random statements built around JSX elements. -/
def genJsxStmtList (n d : Nat) (st : St) : List MiniStatement × St :=
  match n with
  | 0 => ([], st)
  | n + 1 =>
      let (s, st) := genJsxStmt d st
      let (rest, st) := genJsxStmtList n d st
      (s :: rest, st)

/-- A random program of `count` statements, each built around a JSX
element of depth at most `depth`. -/
def genJsxProgram (depth count : Nat) (st : St) : MiniProgram × St :=
  let (stmts, st) := genJsxStmtList count depth st
  (⟨stmts.map MiniModuleItem.stmt⟩, st)

/-- `n` random programs built around JSX elements, from the seed `seed`. -/
def jsxPrograms (n depth count : Nat) (seed : UInt64) : List MiniProgram :=
  go n { seed := seed, fresh := 0 } []
where
  go : Nat → St → List MiniProgram → List MiniProgram
    | 0, _, acc => acc.reverse
    | k + 1, st, acc =>
        let (p, st) := genJsxProgram depth count st
        go k st (p :: acc)

/-- `n` random programs, from the seed `seed`. -/
def programs (n depth count : Nat) (seed : UInt64) : List MiniProgram :=
  go n { seed := seed, fresh := 0 } []
where
  go : Nat → St → List MiniProgram → List MiniProgram
    | 0, _, acc => acc.reverse
    | k + 1, st, acc =>
        let (p, st) := genProgram depth count st
        go k st (p :: acc)

end Language.JavaScript.MiniAST.Fuzz
