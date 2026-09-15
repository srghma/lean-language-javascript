import Tests.Corpus16

/-!
# Samples of member chains, of the arguments a call expands, and of arrows

Programs which exercise the heuristics prettier uses to lay out a chain of
member accesses and calls, the argument of a call it expands in place
rather than breaking the whole argument list, and a chain of arrow
functions.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A call of the method `name` on `obj`. -/
def methodCall (obj : MiniExpr) (name : String) (args : List MiniExpr := []) : MiniExpr :=
  .call (.dot obj (nes name)) args

/-- A long argument, to make a call overflow the line. -/
def longStringArg : MiniExpr := .string "a rather long string literal here"

/-- An arrow of one parameter and an expression body. -/
def arrowOf (x : String) (body : MiniExpr) : MiniExpr := .arrow false [par x] (.expr body)

/-- The samples. -/
def samples17 : List Sample :=
  -- member chains
  [ { name := "chain-two-groups"
      prog := ⟨[es (methodCall (methodCall (v "theConfigurationObject") "filter" [v "predicate"])
                  "map" [v "transform"])]⟩ }
  , { name := "chain-three-groups"
      prog := ⟨[es (methodCall (methodCall (methodCall (v "theConfigurationObject") "filter"
                  [v "predicate"]) "map" [v "transform"]) "reduce" [v "combine"])]⟩ }
  , { name := "chain-three-groups-long"
      prog := ⟨[es (methodCall (methodCall (methodCall (v "theConfigurationObject") "filter"
                  [longStringArg]) "map" [longStringArg]) "reduce" [longStringArg])]⟩ }
  , { name := "chain-short-base"
      prog := ⟨[es (methodCall (methodCall (methodCall (v "z") "filter" [longStringArg])
                  "map" [longStringArg]) "reduce" [longStringArg])]⟩ }
  , { name := "chain-this-base"
      prog := ⟨[es (methodCall (methodCall (methodCall .this "filter" [longStringArg])
                  "map" [longStringArg]) "reduce" [longStringArg])]⟩ }
  , { name := "chain-factory-base"
      prog := ⟨[es (methodCall (methodCall (.call (v "factory") []) "filter" [longStringArg])
                  "map" [longStringArg])]⟩ }
  , { name := "chain-capitalised-base"
      prog := ⟨[es (methodCall (methodCall (methodCall (v "TheFactory") "filter"
                  [longStringArg]) "map" [longStringArg]) "reduce" [longStringArg])]⟩ }
  , { name := "chain-require-base"
      prog := ⟨[es (methodCall (methodCall (.call (v "require") [.string "the-module"])
                  "filter" [longStringArg]) "map" [longStringArg])]⟩ }
  , { name := "chain-computed-links"
      prog := ⟨[es (methodCall (.index (methodCall (v "theConfigurationObject") "filter"
                  [longStringArg]) (num 0)) "map" [longStringArg])]⟩ }
  , { name := "chain-no-arguments"
      prog := ⟨[es (methodCall (methodCall (methodCall (methodCall
                  (v "theConfigurationObject") "first") "second") "third") "fourth")]⟩ }
  , { name := "chain-with-function-argument"
      prog := ⟨[es (methodCall (methodCall (v "theConfigurationObject") "filter"
                  [longStringArg]) "forEach"
                  [.arrow false [par "item"] (.block [.expr (call "handle" [v "item"])])])]⟩ }
  , { name := "chain-of-properties"
      prog := ⟨[es (.dot (.dot (.dot (v "theConfigurationObject") (nes (longName 0)))
                  (nes (longName 1))) (nes (longName 2)))]⟩ }
  , { name := "chain-assigned"
      prog := ⟨[st (constDecl (longName 0)
                  (methodCall (methodCall (methodCall (v "theCollection") "filter"
                    [longStringArg]) "map" [longStringArg]) "reduce" [longStringArg]))]⟩ }
  , { name := "chain-returned"
      prog := ⟨[st (.funcDecl false false (nes "f") []
                  [.return_ (some (methodCall (methodCall (methodCall (v "theCollection")
                    "filter" [longStringArg]) "map" [longStringArg]) "reduce"
                    [longStringArg]))])]⟩ }
  , { name := "chain-in-condition"
      prog := ⟨[st (.if_ (methodCall (methodCall (methodCall (v "theCollection") "filter"
                  [longStringArg]) "map" [longStringArg]) "some" [longStringArg])
                  (.block []) none)]⟩ }
  , { name := "chain-argument-of-call"
      prog := ⟨[es (call "wrap" [methodCall (methodCall (methodCall (v "theCollection")
                  "filter" [longStringArg]) "map" [longStringArg]) "reduce"
                  [longStringArg]])]⟩ }
  , { name := "chain-call-of-call"
      prog := ⟨[es (.call (.call (.call (v "curriedFunctionWithALongName") [longStringArg])
                  [longStringArg]) [longStringArg])]⟩ }
  , { name := "chain-new-base"
      prog := ⟨[es (methodCall (methodCall (.new (v "TheCollectionClass") [longStringArg])
                  "filter" [longStringArg]) "map" [longStringArg])]⟩ }
  -- the argument a call expands in place
  , { name := "hug-last-arrow"
      prog := ⟨[es (call "theFunctionWithALongName"
                  [longStringArg,
                   .arrow false [par "item"] (.block [.expr (call "handle" [v "item"])])])]⟩ }
  , { name := "hug-last-object"
      prog := ⟨[es (call "theFunctionWithALongName"
                  [longStringArg, .object [.keyValue (.ident (nes (longName 0))) (num 1),
                    .keyValue (.ident (nes (longName 1))) (num 2)]])]⟩ }
  , { name := "hug-last-array"
      prog := ⟨[es (call "theFunctionWithALongName"
                  [longStringArg, .array [.elem (v (longName 0)), .elem (v (longName 1))]])]⟩ }
  , { name := "hug-first-function"
      prog := ⟨[es (call "theFunctionWithALongName"
                  [.arrow false [] (.block [.expr (call "handle" [v "item"])]),
                   .array [.elem (v (longName 0)), .elem (v (longName 1))]])]⟩ }
  , { name := "hug-sole-arrow"
      prog := ⟨[es (call "theFunctionWithALongName"
                  [.arrow false [par (longName 0), par (longName 1)]
                    (.block [.expr (call "handle" [v "item"])])])]⟩ }
  , { name := "hug-sole-object-pattern-param"
      prog := ⟨[es (call "theFunction"
                  [.arrow false [.plain (.object [⟨.ident (nes (longName 0)), .ident (nes (longName 0))⟩,
                      ⟨.ident (nes (longName 1)), .ident (nes (longName 1))⟩] none)]
                    (.block [])])]⟩ }
  , { name := "hook-with-deps"
      prog := ⟨[es (call "useEffect"
                  [.arrow false [] (.block [.expr (call "handle" [v "theConfigurationObject"])]),
                   .array [.elem (v "theConfigurationObject")]])]⟩ }
  , { name := "function-composition"
      prog := ⟨[es (call "compose"
                  [arrowOf "a" (v "a"), arrowOf "bb" (v "bb"), arrowOf "value" (v "value"),
                   arrowOf "item" (v "item")])]⟩ }
  -- chains of arrow functions, and the layouts of an assignment
  , { name := "arrow-chain-short"
      prog := ⟨[st (constDecl "f" (arrowOf "a" (arrowOf "bb" (v "a"))))]⟩ }
  , { name := "arrow-chain-long"
      prog := ⟨[st (constDecl (longName 0)
                  (arrowOf (longName 1) (arrowOf (longName 2)
                    (arrowOf (longName 3) (call "handle" [v (longName 1)])))))]⟩ }
  , { name := "arrow-chain-block-body"
      prog := ⟨[st (constDecl (longName 0)
                  (.arrow false [par (longName 1)] (.expr (.arrow false [par (longName 2)]
                    (.block [.return_ (some (v (longName 1)))])))))]⟩ }
  , { name := "arrow-chain-argument"
      prog := ⟨[es (call "wrap" [arrowOf (longName 0) (arrowOf (longName 1)
                  (arrowOf (longName 2) (v "result")))])]⟩ }
  , { name := "arrow-returning-conditional"
      prog := ⟨[st (constDecl (longName 0)
                  (arrowOf (longName 1) (.ternary (v (longName 1)) (v (longName 2))
                    (v (longName 3)))))]⟩ }
  , { name := "arrow-returning-object"
      prog := ⟨[st (constDecl (longName 0)
                  (arrowOf (longName 1) (.object [.keyValue (.ident (nes (longName 2)))
                    (v (longName 3))])))]⟩ }
  , { name := "assign-conditional"
      prog := ⟨[st (constDecl (longName 0) (.ternary (v (longName 1)) (v (longName 2))
                  (v (longName 3))))]⟩ }
  , { name := "assign-await"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [constDecl (longName 0) (.await (call (longName 1) [v (longName 2)]))])]⟩ }
  , { name := "assign-class"
      prog := ⟨[st (constDecl (longName 0) (.classExpr [] none (some (v (longName 1))) []))]⟩ }
  , { name := "assign-template"
      prog := ⟨[st (constDecl (longName 0)
                  (.template none "the value is " [⟨v (longName 1), " indeed"⟩]))]⟩ }
  , { name := "assign-chained"
      prog := ⟨[es (.assign (v (longName 0)) .assign
                  (.assign (v (longName 1)) .assign (.assign (v (longName 2)) .assign
                    (v (longName 3)))))]⟩ }
  , { name := "class-field-arrow"
      prog := ⟨[st (.classDecl [] (nes "A") none
                  [.field [] false false (.ident (nes (longName 0)))
                    (some (arrowOf (longName 1) (call "handle" [v (longName 1)])))])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
