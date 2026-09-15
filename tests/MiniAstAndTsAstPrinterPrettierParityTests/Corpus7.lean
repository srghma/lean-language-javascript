import Tests.Corpus6

/-!
# Samples found by fuzzing

Programs whose layout the printer once wrote differently from prettier;
they are kept here so that the cases stay covered.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An arrow function with two parameters whose body is a `try`, so that
it is always broken. -/
def brokenArrow : MiniExpr :=
  .arrow false [par (longName 0), .rest (p "value")]
    (.block [ .try_ [.return_ (some (num 185)), constDecl "value4244" .null]
        (.catches ⟨⟨p "error", none,
            [constDecl "value4245" (num 2), .expr (v "computeTheValue"),
             .expr (v "g")]⟩, []⟩ .none) ])

/-- The samples. -/
def samples7 : List Sample :=
  -- The call hugs its first argument, whose parameter list then keeps the
  -- line of the `(`; the line is too long for that, so the member chain
  -- breaks instead
  [ { name := "chain-hug-first-arg-too-wide"
      prog := ⟨[es (dotCall (dotCall (.string "ok") "g"
                  [.assign (v "f") .assign (v "index"), .index (v "bb") (num 52)])
                "result" [brokenArrow, .dot (.dot (v "f") (nes "index")) (nes "theCollection")])]⟩ }
  , { name := "chain-hug-first-arg-optional"
      prog := ⟨[es (.chain (.string "ok")
                  ⟨ .dot true (nes "g"),
                    [ .call true [.assign (v "f") .assign (v "index"),
                        .index (v "bb") (num 52)],
                      .dot true (nes "result"),
                      .call true [brokenArrow,
                        .chain (v "f")
                          ⟨.dot true (nes "index"), [.dot false (nes "theCollection")]⟩] ] ⟩)]⟩ }
  , { name := "hug-first-arg-short-chain"
      prog := ⟨[es (dotCall (dotCall (.string "ok") "g" [v "x"]) "result"
                  [brokenArrow, v "tail"])]⟩ }
  -- a function expression hugged as the first argument keeps the layout
  -- of its own parameter list, unlike an arrow function
  , { name := "hug-first-arg-function-params"
      prog := ⟨[st (constDecl "value5313"
                  (.chain (v "value")
                    ⟨ .dot true (nes "theConfigurationObject"),
                      [ .call false
                          [ .func false false none [par "item", par (longName 0)]
                              [.expr (call "body" [])],
                            .string "" ] ] ⟩))]⟩ }
  -- the operator chain of a binary expression inside a conditional is
  -- indented when the conditional is an argument of a call or of a `new`,
  -- or the expression of a `return`, and is not indented elsewhere
  , { name := "ternary-binary-indent-call-arg"
      prog := ⟨[es (call "f" [.ternary (v "test")
                  (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                  (v "other")])]⟩ }
  , { name := "ternary-binary-indent-new-arg"
      prog := ⟨[es (.new (v "F") [.ternary (v "test")
                  (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                  (v "other")])]⟩ }
  , { name := "ternary-binary-indent-return"
      prog := ⟨[st (.funcDecl false false (nes "q") []
                  [.return_ (some (.ternary (v "test")
                    (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                    (v "other")))])]⟩ }
  , { name := "ternary-binary-indent-assignment"
      prog := ⟨[es (.assign (v "xyz") .assign (.ternary (v "test")
                  (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                  (v "other")))]⟩ }
  , { name := "ternary-binary-indent-array-element"
      prog := ⟨[es (.array [.elem (.ternary (v "test")
                  (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                  (v "other"))])]⟩ }
  , { name := "ternary-binary-indent-spread-arg"
      prog := ⟨[es (call "q" [.spread (.ternary (v "test")
                  (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                  (v "other"))])]⟩ }
  , { name := "ternary-binary-indent-member-object"
      prog := ⟨[es (dotCall (.ternary (v "test")
                  (.binary (v (longName 0)) .strictEq (v (longName 0 ++ longName 0)))
                  (v "other")) "m" [])]⟩ }
  -- a tab in a template literal takes no column of the line, so the head
  -- of the `for` fits on one line
  , { name := "tab-in-template-width"
      prog := ⟨[st (.block [.for_
                  (.decl .let_ ⟨⟨p "index2169", some (num 0)⟩, []⟩)
                  (some (.binary (v "index2169") .lt
                    (.template none "tab\there" [⟨v "theCollection", "!"⟩])))
                  (some (.postfix (v "index2169") .incr))
                  (.block [.expr (v "body")])])]⟩ }
  , { name := "tab-in-template-index-width"
      prog := ⟨[st (.block [.expr (.index
                  (.chain (.template none "tab\there"
                      [⟨.string "a rather long string literal here", "!"⟩])
                    ⟨.dot true (nes "theCollection"), [.dot false (nes "item")]⟩)
                  (v "value"))])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
