import Tests.Corpus36

/-!
# JSX in a chain of logical operators

Prettier keeps an element written as the last operand of a chain of `&&`
or `||` on the line of the operator, and writes the element itself over
the lines that follow.  A chain that leans to the right is rebalanced
before that rule is applied: `a && (b && <x />)` is written exactly as
`a && b && <x />` is, since a parser reads the two the same way.  The
samples here pin both down, at the top level and inside the `{ }` of an
attribute, where the room left on the line makes the difference visible.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A call whose argument list has to break. -/
private def longCall : MiniExpr :=
  .call (v "aVeryVeryLongIdentifierNameHere")
    [v "a", v "bb", v "value", v "item", v "index",
     .call (.func false false none [] [.return_ (some .newTarget)]) []]

/-- A conjunction whose last operand is an element. -/
private def andWithElement : MiniExpr :=
  .binary (.index (.string "nul\x00here") (num 74)) .and
    (.binary (v "theConfigurationObject") .and
    (el "Foo.p" [eattr "key" (v "computeTheValue"),
      eattr "theRatherLongAttributeNameHere" (.number (.decimal 15 (-1)))]
      (some [.expr (v "iterator"), .text "hello"])))

/-- An optional chain long enough to break. -/
private def optionalTail : MiniExpr :=
  .chain (v "result")
    ⟨MiniChainLink.dot true (nes "theConfigurationObject"),
     [MiniChainLink.call true [.null, v "theVeryLongNameForAVariableHere", num 151],
      MiniChainLink.index true (num 99)]⟩

/-- The chain of the sample: a broken call, then the conjunction that ends
in an element, then the optional chain. -/
private def brokenChain : MiniExpr :=
  .binary (.binary (.binary longCall .and (.assign (.index (v "g") (.string "currentValue")) .divide
      (.dot (.dot (.dot (v "g") (nes "name")) (nes "result")) (nes "index"))))
    .or andWithElement) .or optionalTail

/-- The same chain, nested to the right: `A || (B || C)`. -/
private def brokenChainRight : MiniExpr :=
  .binary (.binary longCall .and (.assign (.index (v "g") (.string "currentValue")) .divide
      (.dot (.dot (.dot (v "g") (nes "name")) (nes "result")) (nes "index"))))
    .or (.binary andWithElement .or optionalTail)

/-- The samples. -/
def samples37 : List Sample :=
  [ { name := "jsx-logical-jsx-tail"
      prog := ⟨[st (constDecl "y" (.binary (.binary (.index (.string "nul\x00here") (num 74)) .and
                  (v "theConfigurationObject")) .and
                  (el "Foo.p" [eattr "key" (v "computeTheValue"),
                    eattr "theRatherLongAttributeNameHere" (.number (.decimal 15 (-1)))]
                    (some [.expr (v "iterator"), .text "hello"]))))]⟩ }
  , { name := "jsx-logical-jsx-tail-nested"
      prog := ⟨[st (constDecl "x" (.binary (.binary (v "aaa") .or
                  (.binary (.binary (.index (.string "nul\x00here") (num 74)) .and
                    (v "theConfigurationObject")) .and
                    (el "Foo.p" [eattr "key" (v "computeTheValue"),
                      eattr "theRatherLongAttributeNameHere" (.number (.decimal 15 (-1)))]
                      (some [.expr (v "iterator"), .text "hello"])))) .or (v "bbb")))]⟩ }
  , { name := "jsx-logical-jsx-in-attr"
      prog := ⟨[es (el "br"
                  [eattr "theRatherLongAttributeNameHere"
                    (.binary (.binary (v "aaa") .or
                      (.binary (.binary (.index (.string "nul\x00here") (num 74)) .and
                        (v "theConfigurationObject")) .and
                        (el "Foo.p" [eattr "key" (v "computeTheValue"),
                          eattr "theRatherLongAttributeNameHere" (.number (.decimal 15 (-1)))]
                          (some [.expr (v "iterator"), .text "hello"])))) .or (v "bbb")),
                   sattr "onClick" "x"]
                  (some []))]⟩ }
  , { name := "jsx-logical-jsx-after-broken"
      prog := ⟨[es (el "br"
                  [eattr "theRatherLongAttributeNameHere" brokenChain,
                   sattr "onClick" "x"]
                  (some []))]⟩ }
  , { name := "jsx-logical-jsx-after-broken-right"
      prog := ⟨[st (constDecl "props679"
                  (.dot (el "br"
                    [eattr "theRatherLongAttributeNameHere" brokenChainRight,
                     sattr "onClick" "x"]
                    (some [])) (nes "props")))]⟩ }
  , { name := "jsx-logical-jsx-after-broken-indented"
      prog := ⟨[st (constDecl "props679"
                  (.dot (el "br"
                    [eattr "theRatherLongAttributeNameHere" brokenChain,
                     sattr "onClick" "x"]
                    (some [])) (nes "props")))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
