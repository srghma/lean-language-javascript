import Tests.Corpus3

/-!
# Arrow function sample programs

Samples that exercise the layout prettier gives to arrow functions: the
chains of arrows, the bodies it keeps on the line of the `=>`, and the
arrows that stand in an argument, a callee, a property or a `return`.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An arrow function of one parameter, with an expression body. -/
def arrow1 (x : String) (body : MiniExpr) : MiniExpr := arrowExpr [x] body

/-- The samples. -/
def samples4 : List Sample :=
  [ { name := "arrow-ternary-body-short"
      prog := ⟨[st (constDecl "f" (arrow1 "a" (.ternary (v "a") (v "b") (v "c"))))]⟩ }
  , { name := "arrow-ternary-body-long"
      prog := ⟨[st (constDecl "chooseTheValue"
                  (arrow1 (longName 0)
                    (.ternary (v (longName 1)) (v (longName 2)) (v (longName 3)))))]⟩ }
  , { name := "arrow-ternary-body-object"
      prog := ⟨[st (constDecl "g" (arrow1 "a"
                  (.ternary (v "a") (.object [kv "x" (num 1)]) (v "c"))))]⟩ }
  , { name := "arrow-ternary-body-object-long"
      prog := ⟨[st (constDecl "chooseTheOtherValue"
                  (arrow1 (longName 0)
                    (.ternary (v (longName 1)) (.object [kv "xxxxxx" (num 1)])
                      (v (longName 3)))))]⟩ }
  , { name := "arrow-sequence-body"
      prog := ⟨[st (constDecl "h" (arrow1 "a" (.seq (v "b") (v "c"))))]⟩ }
  , { name := "arrow-array-body-long"
      prog := ⟨[st (constDecl "collectThemAll"
                  (arrow1 (longName 0)
                    (.array [.elem (v (longName 1)), .elem (v (longName 2)),
                      .elem (v (longName 3))])))]⟩ }
  , { name := "arrow-chain-two"
      prog := ⟨[st (constDecl "adder" (arrow1 "a" (arrow1 "b" (.binary (v "a") .plus (v "b")))))]⟩ }
  , { name := "arrow-chain-block-body"
      prog := ⟨[st (constDecl "makeHandlerForTheComponent"
                  (arrow1 (longName 0) (.arrow false [par (longName 1)]
                    (.block [.return_ (some (call "combineAllOfThem"
                      [v (longName 0), v (longName 1)]))]))))]⟩ }
  , { name := "arrow-chain-object-body"
      prog := ⟨[st (constDecl "makeTheRecordOfEverything"
                  (arrow1 (longName 0) (arrow1 (longName 1)
                    (.object [kv "first" (v (longName 0)), kv "second" (v (longName 1))]))))]⟩ }
  , { name := "arrow-chain-destructured-param"
      prog := ⟨[st (constDecl "f"
                  (.arrow false [.plain (.object [⟨.ident (nes "a"), p "a"⟩] none)]
                    (.expr (arrow1 "b" (.binary (v "a") .plus (v "b"))))))]⟩ }
  , { name := "arrow-chain-default-param"
      prog := ⟨[st (constDecl "f"
                  (.arrow false [.plain (.withDefault (p "a") (num 1))]
                    (.expr (arrow1 "b" (.binary (v "a") .plus (v "b"))))))]⟩ }
  , { name := "arrow-chain-in-call"
      prog := ⟨[es (call "registerTheHandler"
                  [arrow1 (longName 0) (arrow1 (longName 1)
                    (call "combineAllOfThem" [v (longName 0), v (longName 1)]))])]⟩ }
  , { name := "arrow-chain-in-call-short"
      prog := ⟨[es (call "register" [arrow1 "a" (arrow1 "b" (v "c")), v "x"])]⟩ }
  , { name := "arrow-chain-callee"
      prog := ⟨[es (.call (.call (arrow1 "a" (arrow1 "b" (.binary (v "a") .plus (v "b"))))
                  [num 1]) [num 2])]⟩ }
  , { name := "arrow-chain-property"
      prog := ⟨[st (constDecl "handlers" (.object
                  [kv "onTheFirstEvent" (arrow1 (longName 0) (arrow1 (longName 1)
                    (call "dispatchIt" [v (longName 0), v (longName 1)])))]))]⟩ }
  , { name := "arrow-chain-return"
      prog := ⟨[st (.funcDecl false false (nes "makeIt") []
                  [.return_ (some (arrow1 (longName 0) (arrow1 (longName 1)
                    (call "combineAllOfThem" [v (longName 0), v (longName 1)]))))])]⟩ }
  , { name := "arrow-chain-in-binary"
      prog := ⟨[st (constDecl "maybeTheHandler"
                  (.binary (v "providedHandlerFunction") .or
                    (arrow1 (longName 0) (arrow1 (longName 1) (v "undefinedValueHere")))))]⟩ }
  , { name := "arrow-chain-in-array"
      prog := ⟨[st (constDecl "theListOfHandlers" (.array
                  [.elem (arrow1 (longName 0) (arrow1 (longName 1)
                    (call "combineAllOfThem" [v (longName 0), v (longName 1)])))]))]⟩ }
  , { name := "arrow-chain-four"
      prog := ⟨[st (constDecl "deeplyCurriedFunction"
                  (arrow1 (longName 0) (arrow1 (longName 1) (arrow1 (longName 2)
                    (arrow1 (longName 3) (call "combineAllOfThem"
                      [v (longName 0), v (longName 1), v (longName 2), v (longName 3)]))))))]⟩ }
  , { name := "arrow-chain-assign"
      prog := ⟨[es (.assign (v "theExportedHandlerFunction") .assign
                  (arrow1 (longName 0) (arrow1 (longName 1)
                    (call "combineAllOfThem" [v (longName 0), v (longName 1)]))))]⟩ }
  , { name := "arrow-chain-arg-and-more"
      prog := ⟨[es (call "combineAllOfThem"
                  [v (longName 0), arrow1 (longName 1) (arrow1 (longName 2) (v "result"))])]⟩ }
  , { name := "arrow-in-ternary-branch"
      prog := ⟨[st (constDecl "theChosenHandler" (.ternary (v "conditionHolds")
                  (arrow1 (longName 0) (v "firstResultValue"))
                  (arrow1 (longName 1) (v "secondResultValue"))))]⟩ }
  , { name := "arrow-in-async-function"
      prog := ⟨[st (.funcDecl true false (nes "run") []
                  [constDecl "data" (.await (call "loadTheThing" [])),
                   constDecl "f" (arrow1 "a" (call "processIt" [v "a", v "data"]))])]⟩ }
  , { name := "arrow-rest-param-chain"
      prog := ⟨[st (constDecl "f" (.arrow false [.rest (p "args")]
                  (.expr (arrow1 "b" (call "useThem" [v "args", v "b"])))))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
