import Tests.Corpus14

/-!
# Samples of the parentheses a leftmost token asks for

Programs which exercise the places where an expression needs parentheses
because of the token it starts with, or because of what stands around it:
an optional chain which is called or is the callee of a `new`, a numeric
literal read a property off, an object literal or a function expression
where a statement starts, and the identifier `let` where a declaration
could stand, which prettier parenthesises on its own rather than
parenthesising the statement.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An optional chain of one link. -/
def optionalDot (base : MiniExpr) (name : String) : MiniExpr :=
  .chain base ⟨.dot true (nes name), []⟩

/-- `let[0]`, the read that makes `let` a keyword. -/
def letIndex : MiniExpr := .index (v "let") (num 0)

/-- `let.x`, which is a read of the variable named `let`. -/
def letDot : MiniExpr := .dot (v "let") (nes "x")

/-- The samples. -/
def samples15 : List Sample :=
  [ { name := "chain-called", prog := ⟨[es (.call (optionalDot (v "a") "b") [])]⟩ }
  , { name := "chain-new", prog := ⟨[es (.new (optionalDot (v "a") "b") [])]⟩ }
  , { name := "chain-deleted", prog := ⟨[es (.unary .delete (optionalDot (v "a") "b"))]⟩ }
  , { name := "chain-member", prog := ⟨[es (.dot (optionalDot (v "a") "b") (nes "c"))]⟩ }
  , { name := "chain-assigned"
      prog := ⟨[es (.assign (v "x") .assign (optionalDot (v "a") "b"))]⟩ }
  , { name := "number-callee", prog := ⟨[es (.call (.dot (num 5) (nes "toFixed")) [])]⟩ }
  , { name := "number-decimal-callee"
      prog := ⟨[es (.call (.dot (.number (.decimal 15 (-1))) (nes "toFixed")) [])]⟩ }
  , { name := "bigint-callee"
      prog := ⟨[es (.call (.dot (.number (.bigint .decimal 5)) (nes "toString")) [])]⟩ }
  , { name := "new-no-args", prog := ⟨[es (.new (v "Foo") [])]⟩ }
  , { name := "new-of-call", prog := ⟨[es (.new (.call (v "f") []) [])]⟩ }
  , { name := "new-of-member-call"
      prog := ⟨[es (.new (.dot (.call (v "f") []) (nes "C")) [])]⟩ }
  , { name := "new-of-chain", prog := ⟨[es (.new (optionalDot (v "a") "B") [])]⟩ }
  -- statements whose first token would be read as something else
  , { name := "statement-object", prog := ⟨[es (.object [.shorthand (nes "a")])]⟩ }
  , { name := "statement-function", prog := ⟨[es (.func false false none [] [])]⟩ }
  , { name := "statement-class", prog := ⟨[es (.classExpr [] none none [])]⟩ }
  , { name := "statement-arrow-object"
      prog := ⟨[es (.arrow false [] (.expr (.object [.shorthand (nes "a")])))]⟩ }
  -- names which are keywords elsewhere
  , { name := "name-async", prog := ⟨[st (constDecl "async" (v "of"))]⟩ }
  , { name := "name-get-set"
      prog := ⟨[st (.classDecl [] (nes "A") none
                  [.method [] false .get (.ident (nes "get")) [] [],
                   .method [] false .set (.ident (nes "set")) [par "value"] [],
                   .method [] true .normal (.ident (nes "async")) [] [],
                   .field [] true false (.ident (nes "static")) (some (num 1))])]⟩ }
  , { name := "method-named-constructor"
      prog := ⟨[es (.object [.method .normal (.ident (nes "constructor")) [] []])]⟩ }
  , { name := "yield-no-argument"
      prog := ⟨[es (.call (.func false true none [] [.expr (.yield none)]) [])]⟩ }
  , { name := "yield-in-ternary"
      prog := ⟨[es (.call (.func false true none []
                  [.expr (.ternary (v "a") (.yield (some (v "b"))) (num 0))]) [])]⟩ }
  , { name := "await-in-unary"
      prog := ⟨[es (.call (.func true false none []
                  [.expr (.unary .not (.await (v "a")))]) [])]⟩ }
  , { name := "for-init-in"
      prog := ⟨[st (.for_ (.expr (.binary (.string "a") .inOp (v "o"))) none none (.block []))]⟩ }
  -- the identifier `let`, which is parenthesised where a `[` would make
  -- it the keyword of a declaration
  , { name := "let-index-statement"
      prog := ⟨[es (.assign letIndex .assign (num 1))]⟩ }
  , { name := "let-index-statement-member"
      prog := ⟨[es (.assign (.dot letIndex (nes "y")) .assign (num 1))]⟩ }
  , { name := "let-index-statement-binary"
      prog := ⟨[es (.binary letIndex .plus (num 1))]⟩ }
  , { name := "let-index-statement-ternary"
      prog := ⟨[es (.ternary letIndex (v "a") (v "bb"))]⟩ }
  , { name := "let-dot-statement"
      prog := ⟨[es (.assign letDot .assign (num 1))]⟩ }
  -- where the identifier is not the leftmost token it keeps no parentheses
  , { name := "let-index-argument", prog := ⟨[es (call "f" [letIndex])]⟩ }
  , { name := "let-index-assigned"
      prog := ⟨[es (.assign (v "a") .assign letIndex)]⟩ }
  , { name := "let-index-condition", prog := ⟨[st (.while_ letIndex .empty)]⟩ }
  , { name := "let-index-pattern"
      prog := ⟨[es (.assignPattern (.array [.elem (.target letIndex)]) (v "xs"))]⟩ }
  , { name := "let-index-unary", prog := ⟨[es (.unary .typeof letIndex)]⟩ }
  -- the head of a `for (;;)`
  , { name := "let-index-for-init"
      prog := ⟨[st (.for_ (.expr (.assign letIndex .assign (num 1))) none none .empty)]⟩ }
  , { name := "let-dot-for-init"
      prog := ⟨[st (.for_ (.expr (.assign letDot .assign (num 1))) none none .empty)]⟩ }
  , { name := "let-index-for-test"
      prog := ⟨[st (.for_ .none (some letIndex) none .empty)]⟩ }
  , { name := "object-for-init"
      prog := ⟨[st (.for_ (.expr (.object [.shorthand (nes "a")])) none none .empty)]⟩ }
  -- the binder of a `for ... in` and of a `for ... of`, which may not
  -- start with `let` at all
  , { name := "let-for-of", prog := ⟨[st (.forOf false (.pattern (p "let")) (v "xs") .empty)]⟩ }
  , { name := "let-for-in", prog := ⟨[st (.forIn (.pattern (p "let")) (v "xs") .empty)]⟩ }
  , { name := "let-dot-for-of"
      prog := ⟨[st (.forOf false (.pattern (.target letDot)) (v "xs") .empty)]⟩ }
  , { name := "let-index-for-of"
      prog := ⟨[st (.forOf false (.pattern (.target letIndex)) (v "xs") .empty)]⟩ }
  , { name := "let-index-member-for-of"
      prog := ⟨[st (.forOf false (.pattern (.target (.dot letIndex (nes "y")))) (v "xs") .empty)]⟩ }
  , { name := "plain-target-for-of"
      prog := ⟨[st (.forOf false (.pattern (.target (.dot (v "o") (nes "p")))) (v "xs") .empty)]⟩ }
  , { name := "plain-ident-for-of"
      prog := ⟨[st (.forOf false (.pattern (p "item")) (v "xs") .empty)]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
