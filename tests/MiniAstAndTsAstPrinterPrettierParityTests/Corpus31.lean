import Tests.Corpus30

/-!
# Samples of the chains an optional chain is written around

An optional chain is laid out with the member chain layout only from the
call that holds it: a base which is a call of a call, or a call of a test
framework, whose arguments keep their line, is printed on its own, and the
member accesses written inside such a base take a line of their own rather
than the line of their object.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- `it.only("the name of the test", function () { ... })` -/
def testCallSample : MiniExpr :=
  .call (.dot (v "it") (nes "only"))
    [.string "the name of the test number 23209",
      .func false false none [] [.expr (.number (.decimal 15 (-1))),
        .decl .const ⟨⟨p "value23210", some (v "value")⟩, []⟩]]

/-- The statement wrapped in `n` nested blocks, which shifts it right. -/
def inNestedBlocks (n : Nat) (s : MiniStatement) : MiniStatement :=
  match n with
  | 0 => s
  | k + 1 => inNestedBlocks k (.block [s])

/-- `(aVeryVeryLongIdentifierNameHere?.result).theIteratorOfTheList?.a(...)` -/
def parenthesisedChainSample : MiniExpr :=
  .chain (.dot (.chain (v "aVeryVeryLongIdentifierNameHere") ⟨.dot true (nes "result"), []⟩)
            (nes "theIteratorOfTheList"))
    ⟨.dot true (nes "a"),
      [.call false [.binary (.binary (.binary (.string "say \"hi\"") .plus
          (v "theConfigurationObject")) .plus (.string "1a")) .plus
          (.number (.decimal 15 (-1)))]]⟩

/-- The samples. -/
def samples31 : List Sample :=
  ((List.range 4).map fun n =>
    { name := s!"chain-of-parenthesised-chain-{n}"
      prog := ⟨[st (inNestedBlocks n
                  (.expr (.assign (.dot (v "computeTheValue") (nes "property")) .plus
                    parenthesisedChainSample)))]⟩ })
  ++ ((List.range 4).map fun n =>
    { name := s!"chain-of-test-call-{n}"
      prog := ⟨[st (inNestedBlocks n
                  (.expr (.assign (v "theObject") .assign
                    (.object [.keyValue (.ident (nes "computeTheValue"))
                      (.chain testCallSample
                        ⟨.dot true (nes "constructor"), [.dot false (nes "item")]⟩)]))))]⟩ })
  ++ ((List.range 4).map fun n =>
    { name := s!"members-of-test-call-{n}"
      prog := ⟨[st (inNestedBlocks n
                  (.expr (.assign (.dot (v "collection") (nes "property")) .assign
                    (.chain (.dot (.dot (.dot testCallSample (nes "node8")) (nes "xs"))
                        (nes "theConfigurationObject"))
                      ⟨.dot true (nes "abc"), [.dot false (nes "length")]⟩))))]⟩ })
  ++ ((List.range 3).map fun n =>
    { name := s!"members-of-curried-chain-{n}"
      prog := ⟨[st (inNestedBlocks n
                  (.expr (.chain (.dot (.call (.call (.dot (.call (.dot (.dot (v "this")
                              (nes "xs")) (nes "collection")) []) (nes "node8")) [])
                          [.object [.spread (.binary (v "currentValue") .or (v "result"))]])
                        (nes "new"))
                      ⟨.dot true (nes "g"), [.dot false (nes "f")]⟩)))]⟩ })
  ++ [ -- the same test call written on its own, and read through by a call
       { name := "test-call-plain"
         prog := ⟨[es testCallSample]⟩ }
     , { name := "test-call-read-through-by-a-call"
         prog := ⟨[es (.chain testCallSample
                     ⟨.dot true (nes "then"), [.call false [v "theHandler"]]⟩)]⟩ } ]

end Language.JavaScript.MiniAST.Corpus
