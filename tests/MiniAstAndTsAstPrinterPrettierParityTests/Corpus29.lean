import Tests.Corpus28

/-!
# Samples of the statements and of the whole program

The samples here cover the places where a statement is written on its own:
the directives at the head of a program or of a function body, the empty
statement, the declarations of several names, and the statements whose
first token needs care.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples. -/
def samples29 : List Sample :=
  [ -- a string statement, which a parser reads as a directive
    { name := "directive-prologue"
      prog := ⟨[es (.string "use strict"), es (.string "a"), st (constDecl "x" (num 1))]⟩ }
  , { name := "directive-quotes"
      prog := ⟨[es (.string "it's"), es (.string "say \"hi\""),
                es (.string "both ' and \"")]⟩ }
  , { name := "directive-escapes"
      prog := ⟨[es (.string "a\nb"), es (.string "tab\there")]⟩ }
  , { name := "directive-in-function"
      prog := ⟨[st (.funcDecl false false (nes "theFunctionName") []
                  [.expr (.string "use strict"), .expr (call "f" [])])]⟩ }
  , { name := "statement-first-tokens"
      prog := ⟨[es (.array [.elem (num 1)]),
                es (.template none "text" []),
                es (.unary .plus (v "a")),
                es (.regex ⟨nes "ab+c", {}⟩),
                es (.call (.arrow false [] (.expr (num 1))) [])]⟩ }
  , { name := "empty-program"
      prog := ⟨[]⟩ }
  , { name := "only-empty-statements"
      prog := ⟨[st .empty, st .empty]⟩ }
  , { name := "declarations-without-semicolon"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none []),
                st (.funcDecl false false (nes "theFunctionName") [] []),
                es (.classExpr [] none none []),
                es (.func false false none [] [])]⟩ }
  , { name := "empty-blocks-and-bodies"
      prog := ⟨[st (.block []), st (.block [.empty]),
                st (.while_ (v "a") .empty),
                st (.if_ (v "a") .empty (some .empty))]⟩ }
  , { name := "var-of-many-declarators"
      prog := ⟨[st (.decl .var ⟨⟨p "aLongIdentifierNameNumberZero", some (num 1)⟩,
                  [⟨p "aLongIdentifierNameNumberOne", some (num 2)⟩,
                   ⟨p "aLongIdentifierNameNumberTwo", some (num 3)⟩]⟩),
                st (.decl .let_ ⟨⟨p "a", none⟩, [⟨p "bb", none⟩]⟩),
                st (.decl .let_ ⟨⟨p "a", some (num 1)⟩, [⟨p "bb", none⟩]⟩)]⟩ }
  , -- a `using` of several names breaks like any other declaration
    { name := "using-of-many-declarators"
      prog := ⟨[st (.block [.using_ false ⟨⟨p "theResourceName", some (call "open" [])⟩,
                  [⟨p "theOtherResourceName", some (call "open" [])⟩]⟩]),
                st (.funcDecl true false (nes "theFunctionName") []
                  [.using_ true ⟨⟨p "theResourceName", some (call "open" [])⟩,
                    [⟨p "theOtherResourceName", some (call "open" [])⟩]⟩])]⟩ }
  , { name := "for-with-empty-body"
      prog := ⟨[st (.for_ (.decl .let_ ⟨⟨p "i", some (num 0)⟩, []⟩)
                  (some (.binary (v "i") .lt (num 10))) (some (.postfix (v "i") .incr)) .empty)]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
