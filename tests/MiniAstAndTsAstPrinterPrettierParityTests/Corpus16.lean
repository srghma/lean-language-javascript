import Tests.Corpus15

/-!
# Samples of `super[...]` and of what `export default` may be followed by

A `super[...]` lookup breaks inside its brackets like any other computed
member access.  An expression written after `export default` is
parenthesised when its leftmost token opens a function or a class
expression, which it does not when the subexpression that holds it is
parenthesised itself.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A long string, which makes a member lookup overflow the line. -/
def longString : String := "a string of a length which is somewhere in the middle"

/-- A method of a class, whose body returns `e`. -/
def returning (name : String) (e : MiniExpr) : MiniClassElement :=
  .method [] false .normal (.ident (nes name)) [] [.return_ (some e)]

/-- An anonymous function expression. -/
def anonFn : MiniExpr := .func false false none [] []

/-- The samples. -/
def samples16 : List Sample :=
  [ { name := "super-index-long"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [returning "item" (.superIndex (.string longString))])]⟩ }
  , { name := "super-index-long-nested"
      prog := ⟨[st (.block [.block [.classDecl [] (nes "A") (some (v "B"))
                  [returning "item" (.superIndex (.string longString))]]])]⟩ }
  , { name := "super-index-short"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [returning "item" (.superIndex (.string "a"))])]⟩ }
  , { name := "super-index-number"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [returning "item" (.superIndex (num 0))])]⟩ }
  , { name := "super-index-expression"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [returning "item" (.superIndex (.binary (v (longName 0)) .plus
                    (v (longName 1))))])]⟩ }
  , { name := "super-index-member"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [returning "item" (.dot (.superIndex (.string longString)) (nes "x"))])]⟩ }
  -- `export default`, where the leftmost token may not open a function or
  -- a class
  , { name := "export-default-sequence-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.seq anonFn (v "a")))]⟩ }
  , { name := "export-default-member-of-sequence"
      prog := ⟨[.exportDecl (.defaultExpr (.dot (.seq anonFn (v "a")) (nes "b")))]⟩ }
  , { name := "export-default-call-of-sequence"
      prog := ⟨[.exportDecl (.defaultExpr (.call (.seq anonFn (v "a")) []))]⟩ }
  , { name := "export-default-call-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.call anonFn []))]⟩ }
  , { name := "export-default-member-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.dot anonFn (nes "x")))]⟩ }
  , { name := "export-default-index-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.index anonFn (num 0)))]⟩ }
  , { name := "export-default-ternary-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.ternary anonFn (v "a") (v "bb")))]⟩ }
  , { name := "export-default-binary-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.binary anonFn .plus (v "a")))]⟩ }
  , { name := "export-default-assign-of-member-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.assign (.dot anonFn (nes "x")) .assign (v "a")))]⟩ }
  , { name := "export-default-tagged-template-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.template (some anonFn) "t" []))]⟩ }
  , { name := "export-default-await-of-function"
      prog := ⟨[.exportDecl (.defaultExpr (.unary .typeof anonFn))]⟩ }
  , { name := "export-default-sequence-plain"
      prog := ⟨[.exportDecl (.defaultExpr (.seq (v "a") (v "bb")))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
