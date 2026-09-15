import Tests.Corpus21

/-!
# Samples of `export default` and of nested optional chains

An expression written after `export default` whose leftmost token opens a
function or a class would be read as a declaration, so it is written in
parentheses.  Finding that leftmost token means knowing where the printer
writes parentheses of its own: an optional chain which is the base of
another one keeps none when the link that follows it is optional, since
the two then merge into one chain.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An empty class expression. -/
def emptyClass : MiniExpr := .classExpr [] none none []

/-- An empty function expression. -/
def emptyFunc : MiniExpr := .func false false none [] []

/-- The samples. -/
def samples22 : List Sample :=
  [ { name := "export-default-class-member"
      prog := ⟨[.exportDecl (.defaultExpr (.dot emptyClass (nes "x")))]⟩ }
  , { name := "export-default-class-chain"
      prog := ⟨[.exportDecl (.defaultExpr (.chain emptyClass
                  ⟨.dot true (nes "bb"), [.dot false (nes "value")]⟩))]⟩ }
  , { name := "export-default-class-index"
      prog := ⟨[.exportDecl (.defaultExpr (.index emptyClass (.string "k")))]⟩ }
  , { name := "export-default-function-member"
      prog := ⟨[.exportDecl (.defaultExpr (.dot emptyFunc (nes "name")))]⟩ }
  , { name := "export-default-function-call"
      prog := ⟨[.exportDecl (.defaultExpr (.call emptyFunc []))]⟩ }
  , { name := "export-default-class-binary"
      prog := ⟨[.exportDecl (.defaultExpr (.binary emptyClass .plus (num 1)))]⟩ }
  , { name := "export-default-class-ternary"
      prog := ⟨[.exportDecl (.defaultExpr (.ternary emptyClass (num 1) (num 2)))]⟩ }
  , { name := "export-default-function-template"
      prog := ⟨[.exportDecl (.defaultExpr (.template (some emptyFunc) "a" []))]⟩ }
  , { name := "export-default-class-of-heritage-chain"
      prog := ⟨[.exportDecl (.defaultExpr (.chain
                  (.classExpr [] none (some (v "Base"))
                    [.method [] false .normal (.ident (nes "m")) [] []])
                  ⟨.dot true (nes "bb"), []⟩))]⟩ }
  , { name := "export-default-chain-in-member"
      prog := ⟨[.exportDecl (.defaultExpr (.dot (.chain emptyClass
                  ⟨.dot true (nes "bb"), []⟩) (nes "iterator")))]⟩ }
  , { name := "export-default-chain-in-call"
      prog := ⟨[.exportDecl (.defaultExpr (.call (.chain emptyClass
                  ⟨.dot true (nes "bb"), []⟩) []))]⟩ }
  , { name := "export-default-nested-chain-class"
      prog := ⟨[.exportDecl (.defaultExpr (.chain (.chain emptyClass
                  ⟨.dot true (nes "bb"), [.dot false (nes "true")]⟩)
                  ⟨.dot true (nes "value"), [.dot false (nes "iterator")]⟩))]⟩ }
  , { name := "export-default-class-sequence"
      prog := ⟨[.exportDecl (.defaultExpr (.seq emptyClass (num 1)))]⟩ }
  , { name := "chain-in-member-statement"
      prog := ⟨[es (.dot (.chain (v "a") ⟨.dot true (nes "bb"), []⟩) (nes "value"))]⟩ }
  , { name := "nested-chain-merged"
      prog := ⟨[es (.chain (.chain (v "a") ⟨.dot true (nes "bb"), []⟩)
                  ⟨.dot true (nes "c"), []⟩)]⟩ }
  , { name := "nested-chain-parenthesised"
      prog := ⟨[es (.chain (.chain (v "a") ⟨.dot true (nes "bb"), []⟩)
                  ⟨.dot false (nes "c"), [.call false []]⟩)]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
