import Tests.Corpus10

/-!
# Samples of the assignment layouts

Programs which exercise the choice of layout prettier makes for an
assignment, a declarator or a property whose right hand side is itself an
assignment, and the difference a `BigInt` literal makes there: prettier
keeps a numeric literal on the line of the operator, but not a `BigInt`
one.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A `BigInt` literal in base ten. -/
def bigNum (k : Nat) : MiniExpr := .number (.bigint .decimal k)

/-- A statement wrapped in `n` nested blocks, which indents it by `2 * n`
columns. -/
def nestBlocks : Nat → MiniStatement → MiniStatement
  | 0, s => s
  | n + 1, s => nestBlocks n (.block [s])

/-- A very long identifier, to make a line just overflow. -/
def veryLongName : String :=
  "itemWithARatherLongNameForTheTest"

/-- The samples. -/
def samples11 : List Sample :=
  [ { name := "declarator-assign-bigint"
      prog := ⟨[st (constDecl "aVariableWithARatherLongName"
                  (.assign (v veryLongName) .coalesce (bigNum 12)))]⟩ }
  , { name := "declarator-assign-number"
      prog := ⟨[st (constDecl "aVariableWithARatherLongName"
                  (.assign (v veryLongName) .coalesce (num 123)))]⟩ }
  , { name := "declarator-pattern-assign-bigint"
      prog := ⟨[st (.decl .const
                  ⟨⟨.object [⟨.ident (nes "theVeryLongNameForAVariableHere"), p "result"⟩]
                      (some (p "rest")),
                    some (.assign (v "item") .coalesce (bigNum 12))⟩, []⟩)]⟩ }
  , { name := "assign-bigint"
      prog := ⟨[es (.assign (v (longName 0)) .assign (bigNum 1234567890)),
                es (.assign (.dot (v (longName 0)) (nes (longName 1))) .plus
                  (bigNum 1234567890)),
                es (.assign (.dot (v (longName 0)) (nes (longName 1))) .plus
                  (num 1234567890))]⟩ }
  , { name := "property-bigint"
      prog := ⟨[es (.object [.keyValue (.ident (nes (longName 0))) (bigNum 1234567890),
                  .keyValue (.ident (nes (longName 1))) (num 1234567890)])]⟩ }
  , { name := "hug-number-array"
      prog := ⟨[es (call (longName 0) [v "theCollection",
                  .array [.elem (num 1234567890123456789012345678),
                    .elem (.unary .minus (num 2234567890123456789012345678))]]),
                es (call (longName 0) [v "theCollection",
                  .array [.elem (v (longName 2)), .elem (v (longName 3))]]),
                es (call (longName 0) [v "theCollection",
                  .array [.elem (bigNum 1234567890123456789012345678),
                    .elem (bigNum 2234567890123456789012345678)]]),
                es (call (longName 0) [v "theCollection",
                  .array [.hole, .elem (num 1234567890123456789012345678),
                    .elem (num 2234567890123456789012345678)]]),
                es (call (longName 0)
                  [.array [.elem (num 1234567890123456789012345678),
                    .elem (num 2234567890123456789012345678),
                    .elem (num 3234567890123456789012345678)]])]⟩ }
  , { name := "logical-chain-object"
      prog := ⟨[st (.decl .let_ ⟨⟨p "value15445",
                  some (.binary (.unary .typeof (call "theCollection" [v "xs", .spread (v "theCollection")]))
                    .coalesce
                    (.binary (.object [.keyValue (.string "say \"hi\"") .true_,
                        .keyValue (.number 2) .null,
                        .keyValue (.computed (v "theConfigurationObject")) .null])
                      .coalesce
                      (.arrow false [.plain (.object [⟨.ident (nes "theVeryLongNameForAVariableHere"),
                          p "theVeryLongNameForAVariableHere"⟩] none)] (.expr .true_))))⟩, []⟩)]⟩ }
  , { name := "arrow-chain-assign-for"
      prog := ⟨[st (.forOf false (.decl .const (p "item21250"))
                  (.dot (.assignPattern
                      (.object [⟨.ident (nes "theVeryLongNameForAVariableHere"),
                        p "theVeryLongNameForAVariableHere"⟩] (some (p "theCollection")))
                      (.arrow false [] (.expr (.arrow false [par "value",
                        .plain (.withDefault (p "g") (v "g"))]
                        (.expr (.unary .minus (.string "tab\there")))))))
                    (nes "handler"))
                  (.block []))]⟩ }
  , { name := "pattern-property-break"
      prog := ⟨[st (.funcDecl false false (nes "f")
                  [.plain (.object [⟨.ident (nes "theVeryLongNameForAVariableHere"),
                      p (longName 0)⟩] (some (p "rest")))] []),
                es (.assignPattern
                  (.object [⟨.ident (nes "ab"), p (longName 0)⟩,
                    ⟨.ident (nes "theVeryLongNameForAVariableHere"),
                      .target (.dot (v (longName 1)) (nes (longName 2)))⟩] none)
                  (v "o")),
                st (.funcDecl false false (nes "h")
                  [.plain (.object [⟨.ident (nes "theVeryLongNameForAVariableHere"),
                      .withDefault (p (longName 0)) (num 1)⟩] none)] [])]⟩ }
  , { name := "optional-chain-call-base"
      prog := ⟨[es (.chain (.call (.func false false none [] [.expr (v "theStatementInside")]) [])
                  ⟨.dot true (nes "value"),
                   [.dot false (nes "result"), .index true (num 14),
                    .dot false (nes "theConfigurationObject"), .call true [],
                    .dot true (nes "bb"), .call false [v "xs"]]⟩),
                es (.chain (call "gg" [])
                  ⟨.dot true (nes (longName 0)),
                   [.dot false (nes (longName 1)), .call false [],
                    .dot false (nes "secondMethodCall"), .call false [],
                    .dot false (nes "third"), .call false []]⟩),
                es (.chain (.call (.dot (v "gg") (nes "hh")) [])
                  ⟨.dot true (nes (longName 0)),
                   [.dot false (nes (longName 1)), .call false [],
                    .dot false (nes "secondMethodCall"), .call false [],
                    .dot false (nes "third"), .call false []]⟩)]⟩ }
  , { name := "short-unary-argument"
      prog := ⟨[st (nestBlocks 5 (.expr (.object
                  [.keyValue (.ident (nes "theVeryLongNameForAVariableHere"))
                      (call "theVeryLongNameForAVariableHere" [.unary .not (num 615)]),
                   .keyValue (.ident (nes "index")) (num 1)]))),
                st (nestBlocks 5 (.expr (.object
                  [.keyValue (.ident (nes "theVeryLongNameForAVariableHere"))
                      (call "theVeryLongNameForAVariableHere"
                        [.unary .typeof (v "theCollection")]),
                   .keyValue (.ident (nes "index")) (num 1)]))),
                st (nestBlocks 5 (.expr (.object
                  [.keyValue (.ident (nes "theVeryLongNameForAVariableHere"))
                      (call "theVeryLongNameForAVariableHere" [.dot (v "a") (nes "b")]),
                   .keyValue (.ident (nes "index")) (num 1)])))]⟩ }
  , { name := "chain-base-member-chain"
      prog := ⟨[st (nestBlocks 6 (.decl .let_ ⟨⟨p "value4289",
                  some (.chain
                    (.chain (v "bb")
                      ⟨.index true (num 71),
                       [.dot false (nes "f"), .call true [], .call true [],
                        .dot true (nes "value"), .call true [], .index true (num 51)]⟩)
                    ⟨.dot false (nes "item"),
                     [.index true (num 12), .dot false (nes "bb"), .call true []]⟩)⟩,
                  []⟩))]⟩ }
  , { name := "declarator-bigint"
      prog := ⟨[st (constDecl (longName 0) (bigNum 123456789012345678901234567890)),
                st (constDecl (longName 1) (num 123456789012345678901234567890))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
