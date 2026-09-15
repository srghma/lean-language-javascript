import Tests.Corpus7

/-!
# Further samples found by fuzzing

Programs whose layout the printer once wrote differently from prettier;
they are kept here so that the cases stay covered.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples. -/
def samples8 : List Sample :=
  -- the right hand side of an assignment that prettier lays out as a
  -- member chain stays on the line of the `=`, and the chain breaks
  [ { name := "assign-member-chain-stays-on-line"
      prog := ⟨[st (constDecl "value8931"
                  (dotCall (dotCall (dotCall (v (longName 0)) (longName 0) [])
                      "bb" [num 468]) "result" []))]⟩ }
  , { name := "assign-member-chain-stays-on-line-args"
      prog := ⟨[st (.decl .let_ ⟨⟨p "value8548",
                  some (dotCall (dotCall (dotCall (v "index") "computeTheValue" [])
                      "theCollection" [.null]) "theVeryLongNameForAVariableHere" [])⟩, []⟩)]⟩ }
  -- an object literal, a function or a class expression at the start of
  -- an expression statement takes parentheses of its own, even when the
  -- statement is parenthesised as well
  , { name := "sequence-statement-object-first"
      prog := ⟨[es (.seq (.object [.keyValue (.ident (nes "result")) (v "a"),
                  .spread (v "result")]) (v "handler"))]⟩ }
  , { name := "sequence-statement-function-first"
      prog := ⟨[es (.seq (.func false false none [] [.expr (v "a")]) (v "g"))]⟩ }
  , { name := "sequence-statement-class-first"
      prog := ⟨[es (.seq (.classExpr [] none none []) (v "g"))]⟩ }
  -- an object literal at the start of the sequence expression that is the
  -- body of an arrow function needs no parentheses: the body has them
  , { name := "arrow-sequence-body-object-first"
      prog := ⟨[es (.assign (v "xs") .assign
                  (.arrow false [par "index", par "theVeryLongNameForAVariableHere"]
                    (.expr (.seq (.object [.keyValue (.ident (nes "computeTheValue")) (v "bb")])
                      (call "result" [v "a", .spread (v "result")])))))]⟩ }
  -- a tagged template is not a short enough second argument for the first
  -- argument of the call to be hugged
  , { name := "hug-first-arg-tagged-template"
      prog := ⟨[es (dotCall (v "theCollection") "handler"
                  [arrowBlock ["value"] [.expr (v "theVeryLongNameForAVariableHere")],
                    .template (some (v "computeTheValue")) "tab\there" [⟨num 401, "!"⟩]])]⟩ }
  -- the superclass of a class assigned to something is parenthesised when
  -- it does not fit on the line of the `extends`
  , { name := "class-expr-assigned-superclass"
      prog := ⟨[es (.assign (v "index") .lsh
                  (.classExpr [] none (some (v (longName 0 ++ longName 1)))
                    [.method [] false .normal (.ident (nes "index")) [] [.expr (v "a")]]))]⟩ }
  -- the member accesses that trail an assigned member chain keep the line
  -- of the chain
  , { name := "assigned-chain-trailing-members"
      prog := ⟨[st (.decl .let_ ⟨⟨p "value979",
                  some (.assign (v "xs") .logicalAnd
                    (.chain (dotCall (dotCall (dotCall (v "index") "computeTheValue" [])
                          "bb" [.new (v "value") [.true_]]) "index" [])
                      ⟨.dot true (nes "g"), [.dot false (nes "item")]⟩))⟩, []⟩)]⟩ }
  -- the signatures of a chain of arrow functions at the end of a chain of
  -- assignments are always broken
  , { name := "assign-chain-tail-arrow-chain"
      prog := ⟨[st (constDecl "value2748"
                  (.assign (v "xs") .plus
                    (.assign (v "theCollection") .minus
                      (.arrow false [par "theConfigurationObject"]
                        (.expr (.arrow false [] (.expr (v "theCollection"))))))))]⟩ }
  -- a conditional expression in the base of a chain that is the argument
  -- of `yield*` is indented inside the parentheses it needs
  , { name := "yield-star-ternary-chain-base"
      prog := ⟨[st (.funcDecl false true (nes "gen") []
                  [.expr (.yieldFrom
                    (.chain (.ternary
                        (.call (.func false true none [] [.expr (.yield (some (v "computeTheValue")))]) [])
                        (.new (v "a") [num 206, v "handler"])
                        (call "value" [.null, .spread (num 2)]))
                      ⟨.dot true (nes "f"),
                        [.call false [v (longName 0), v (longName 1)]]⟩))])]⟩ }
  -- the call at the end of an optional chain is a call: one with more
  -- than one argument is not a short enough second argument for the first
  -- argument to be hugged, and one with arguments keeps the member access
  -- that follows it on its line
  , { name := "hug-first-arg-optional-call-second"
      prog := ⟨[es (call (longName 0)
                  [arrowBlock [] [.expr (.true_), .return_ (some (num 2))],
                    .chain (num 15) ⟨.dot true (nes "bb"), [.call false [.true_, .true_]]⟩])]⟩ }
  , { name := "optional-call-trailing-member"
      prog := ⟨[st (constDecl "value5994"
                  (.dot (.chain (v "f")
                      ⟨.dot true (nes "result"),
                        [.call false [.null, v "theConfigurationObject", str "say \"hi\""]]⟩)
                    (nes "theVeryLongNameForAVariableHere")))]⟩ }
  -- a chain of the same logical operator that leans to the right is laid
  -- out as the chain that leans to the left
  , { name := "logical-chain-leaning-right"
      prog := ⟨[st (.decl .let_ ⟨⟨p "value1503",
                  some (.binary (v (longName 0 ++ longName 1)) .and
                    (.binary (.assign (.dot (v "item") (nes "property")) .plus
                        (.arrow false [par "item"] (.expr (num 872)))) .and
                      (v "item")))⟩, []⟩)]⟩ }
  -- a dynamic `import()` is call-like: a simple one is a short enough
  -- second argument for the first argument of the call to be hugged, and
  -- it does not make a member chain break
  , { name := "hug-first-arg-import-call"
      prog := ⟨[es (dotCall (.arrow false [] (.expr (.arrow false [par "computeTheValue"] (.expr (num 227)))))
                  "index"
                  [.arrow false [.plain (.withDefault (p "g") .null), par "theCollection"]
                      (.block [constDecl "value259" (str "say \"hi\"")]),
                    .importCall (str "mod260") none])]⟩ }
  , { name := "member-chain-import-argument"
      prog := ⟨[es (dotCall (dotCall (dotCall (v "f") "index"
                      [.importCall (str "mod1353") none]) "a" []) (longName 0) [])]⟩ }
  -- an `import()` that carries options is laid out like any other call,
  -- except that it takes no trailing comma
  , { name := "import-call-options-break"
      prog := ⟨[st (.decl .const
                  ⟨⟨.object [⟨.ident (nes "theVeryLongNameForAVariableHere"),
                        p "computeTheValue"⟩] (some (p "rest")),
                    some (.dot (.importCall (str "mod1332")
                        (some (.object [.keyValue (.ident (nes "with"))
                          (.object [.keyValue (.ident (nes "type")) (str "json")])])))
                      (nes "handler"))⟩, []⟩)]⟩ }
  , { name := "import-call-options-flat"
      prog := ⟨[es (.importCall (str "m")
                  (some (.object [.keyValue (.ident (nes "with"))
                    (.object [.keyValue (.ident (nes "type")) (str "json")])])))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
