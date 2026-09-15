import Tests.Corpus31

/-!
# Samples of the asynchronous forms, and of `debugger`

The samples here cover the syntax that carries the `async` keyword and the
`debugger` statement: asynchronous arrow functions (alone, in chains, as
callbacks and in the positions that need parentheses), asynchronous
methods and asynchronous generator methods of classes and of object
literals, the `for await (... of ...)` loop, and `debugger` in every
statement position.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples. -/
def samples32 : List Sample :=
  [ -- `debugger` on its own, and as the body of a statement
    { name := "debugger-statement"
      prog := ⟨[st .debugger, st (.block [.debugger]),
                st (.if_ (v "a") .debugger none),
                st (.labelled (nes "l") .debugger)]⟩ }
  , { name := "debugger-positions"
      prog := ⟨[st (.while_ (v "a") .debugger),
                st (.doWhile .debugger (v "a")),
                st (.switch (v "a") [.case (num 1) [.debugger], .default [.debugger]]),
                st (.try_ [.debugger] (.finallyOnly [.debugger])),
                st (.forOf false (.decl .const (p "x")) (v "xs") .debugger)]⟩ }
  , -- `for await (... of ...)`
    { name := "for-await"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.forOf true (.decl .const (p "x")) (v "xs")
                    (.block [.expr (call "g" [v "x"])])])]⟩ }
  , { name := "for-await-long-head"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.forOf true (.decl .const (p (longName 0)))
                    (call "theIteratorFactoryFunction" [v (longName 1)])
                    (.block [.expr (call "g" [v (longName 0)])])])]⟩ }
  , { name := "for-await-shapes"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.forOf true (.pattern (.array [.elem (p "k"), .elem (p "v")])) (v "xs") .empty,
                   .forOf true (.decl .let_ (p "x")) (.await (call "stream" [])) (.block []),
                   .forOf true (.decl .const (p "x")) (v "xs") (.expr (call "g" [v "x"]))])]⟩ }
  , -- asynchronous arrow functions
    { name := "async-arrow"
      prog := ⟨[st (constDecl "f" (.arrow true [par "x"] (.expr (call "g" [v "x"])))),
                st (constDecl "g" (.arrow true [] (.block [.return_ (some (num 1))]))),
                es (call "run" [.arrow true [] (.block [.expr (call "step" [])])])]⟩ }
  , { name := "async-arrow-breaking-parameters"
      prog := ⟨[st (constDecl (longName 0)
                  (.arrow true [par (longName 1), par (longName 2)]
                    (.expr (call "theFunctionBeingCalled" [v (longName 1)]))))]⟩ }
  , { name := "async-arrow-chain"
      prog := ⟨[st (constDecl "f" (.arrow true [par "a"] (.expr (.arrow false [par "b"]
                  (.expr (call "g" [v "a", v "b"]))))))]⟩ }
  , { name := "async-arrow-chain-breaking"
      prog := ⟨[st (constDecl (longName 0)
                  (.arrow true [par (longName 1)] (.expr (.arrow true [par (longName 2)]
                    (.expr (call "theFunctionBeingCalled" [v (longName 1), v (longName 2)]))))))]⟩ }
  , { name := "async-arrow-chain-positions"
      prog := ⟨[es (call "theFunctionBeingCalled" [.arrow true [par (longName 0)]
                  (.expr (.arrow true [par (longName 1)] (.expr (call "g" [v (longName 0)]))))]),
                es (.object [.keyValue (.ident (nes "theKeyOfTheProperty"))
                  (.arrow true [par (longName 0)]
                    (.expr (.arrow true [par (longName 1)] (.expr (call "g" [v (longName 1)])))))])]⟩ }
  , { name := "async-arrow-needs-parentheses"
      prog := ⟨[es (.await (.call (.arrow true [] (.expr (num 1))) [])),
                es (.call (.arrow true [] (.block [])) []),
                es (.dot (.arrow true [] (.expr (num 1))) (nes "call"))]⟩ }
  , { name := "async-arrow-operand"
      prog := ⟨[es (.new (.arrow true [] (.expr (num 1))) []),
                es (.binary (.arrow true [] (.expr (num 1))) .plus (num 1)),
                es (.unary .typeof (.arrow true [] (.expr (num 1)))),
                st (.return_ (some (.arrow true [] (.expr (num 1)))))]⟩ }
  , { name := "async-arrow-callback"
      prog := ⟨[es (.call (.dot (v "items") (nes "map")) [.arrow true [par "item"]
                  (.expr (.await (call "load" [v "item"])))]),
                es (call "useEffect" [.arrow true [] (.block [.expr (call "run" [])]),
                  .array []]),
                es (call "setTimeout" [.arrow true [] (.block []), num 0])]⟩ }
  , { name := "async-arrow-callback-breaking"
      prog := ⟨[es (.call (.dot (v "theCollectionOfItems") (nes "map"))
                  [.arrow true [par "theItemOfTheCollection"]
                    (.expr (.await (call "theLoadingFunction" [v "theItemOfTheCollection"])))])]⟩ }
  , { name := "async-arrow-test-call"
      prog := ⟨[es (call "describe" [.string "the name of the test", .arrow true []
                  (.block [.expr (call "expect" [v "a"])])]),
                es (call "it" [.string "does the thing", .arrow true [] (.block [])])]⟩ }
  , { name := "async-arrow-object-body"
      prog := ⟨[st (constDecl "f" (.arrow true [] (.expr (.object [.shorthand (nes "a")])))),
                st (constDecl "g" (.arrow true [par "x"]
                  (.expr (.ternary (v "x") (num 1) (num 2)))))]⟩ }
  , { name := "async-arrow-assignment"
      prog := ⟨[es (.assign (.dot (v "theObjectBeingConfigured") (nes "theHandlerProperty"))
                  .assign (.arrow true [par (longName 0)]
                    (.expr (call "theFunctionBeingCalled" [v (longName 0)]))))]⟩ }
  , { name := "async-arrow-parameters"
      prog := ⟨[st (constDecl "f"
                  (.arrow true [.plain (.object [⟨.ident (nes "a"), .ident (nes "a")⟩] none)]
                    (.expr (v "a")))),
                st (constDecl "g"
                  (.arrow true [.plain (.withDefault (p "x") (num 1)), .rest (p "ys")]
                    (.expr (v "x"))))]⟩ }
  , -- asynchronous methods
    { name := "async-method"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.method [] false .async (.ident (nes "m")) [] [],
                   .method [] true .async (.ident (nes "n")) [par "x"] [],
                   .method [] false .asyncGenerator (.ident (nes "g")) [] [],
                   .method [] true .asyncGenerator (.ident (nes "h")) [] []]),
                es (.object [.method .async (.ident (nes "m")) [] [],
                             .method .asyncGenerator (.ident (nes "g")) [] [],
                             .method .async (.computed (v "k")) [par "x"] []])]⟩ }
  , { name := "async-method-breaking-parameters"
      prog := ⟨[st (.classDecl [] (nes "TheClassName") none
                  [.method [] false .async (.ident (nes "theMethodWithAVeryLongName"))
                    [par (longName 0), par (longName 1)]
                    [.return_ (some (.await (call "f" [])))]])]⟩ }
  , -- the `accessor` fields of a class
    { name := "accessor-field"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [] false true (.ident (nes "x")) (some (num 1)),
                   .field [] true true (.ident (nes "y")) none,
                   .field [] false true (.private_ (nes "z")) (some (num 2)),
                   .field [] false true (.computed (v "k")) (some (num 3)),
                   .field [] false true (.string "the key") none])]⟩ }
  , { name := "accessor-field-decorated"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [v "dec"] false true (.ident (nes "x")) (some (num 1)),
                   .field [call "dec" [v "a"]] true true (.ident (nes "y"))
                     (some (.object []))])]⟩ }
  , { name := "accessor-field-breaking"
      prog := ⟨[st (.classDecl [] (nes "TheClassName") none
                  [.field [] false true (.ident (nes "theFieldWithAVeryLongName"))
                    (some (call "theFunctionBeingCalled"
                      [v "aLongIdentifierNameNumberZero", v "aLongIdentifierNameNumberOne"]))])]⟩ }
  , -- prettier indents the operands of a chain of operators of an
    -- `accessor` field one step further than those of an ordinary field
    { name := "accessor-field-operator-chain"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [] false false (.ident (nes "value"))
                     (some (.binary (.binary (.string "a-key") .plus
                       (.string "a string of a length which is in the middle"))
                       .plus (v "theHandlerFunction"))),
                   .field [] false true (.ident (nes "value2"))
                     (some (.binary (.binary (.string "a-key") .plus
                       (.string "a string of a length which is in the middle"))
                       .plus (v "theHandlerFunction"))),
                   .field [] false true (.ident (nes "value3"))
                     (some (.binary (.binary (v (longName 0)) .and (v (longName 1)))
                       .and (v (longName 2))))])]⟩ }
  , { name := "accessor-field-other-values"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [] false true (.ident (nes "tern"))
                     (some (.ternary (v "someConditionToTest")
                       (.string "a string of a length which is in the middle") (v "other"))),
                   .field [] false true (.ident (nes "called"))
                     (some (call "theFunctionBeingCalled" [v (longName 0), v (longName 1)])),
                   .field [] false true (.ident (nes "arrow"))
                     (some (.arrow false [par (longName 0)]
                       (.expr (call "theFunctionBeingCalled" [v (longName 0)]))))])]⟩ }
  , -- `using` in the head of a `for ... of`
    { name := "for-of-using"
      prog := ⟨[st (.forOf false (.usingDecl false (p "x")) (v "xs") (.block [])),
                st (.funcDecl true false (nes "f") []
                  [.forOf true (.usingDecl false (p "x")) (v "xs") (.block []),
                   .forOf true (.usingDecl true (p "y")) (v "ys") (.block [])])]⟩ }
  , { name := "for-of-using-long-head"
      prog := ⟨[st (.forOf false (.usingDecl false (p "theResourceBeingUsed"))
                  (call "theIteratorFactoryFunction" [v "aLongIdentifierNameNumberOne"])
                  (.block [.expr (call "g" [v "theResourceBeingUsed"])]))]⟩ }
  , -- the interpreter directive a file may start with
    { name := "interpreter-directive"
      prog := ⟨[st (constDecl "x" (num 1))]⟩
      interpreter := some "/usr/bin/env node" }
  , { name := "interpreter-directive-only"
      prog := ⟨[]⟩
      interpreter := some "/bin/sh" }
  , { name := "interpreter-directive-and-prologue"
      prog := ⟨[es (.string "use strict"), st (constDecl "x" (num 1))]⟩
      interpreter := some "/usr/bin/env node" }
  , { name := "async-method-keys"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.method [] false .async (.string "the key") [] [],
                   .method [] false .async (.private_ (nes "secret")) [] [],
                   .method [] false .asyncGenerator (.computed (call "key" [])) [] [],
                   .field [] true false (.ident (nes "f")) (some (.arrow true [] (.expr (num 1))))]),
                es (.object [.method .async (.string "the key") [] [],
                             .method .async (.number (JSNumber.ofNat 1)) [] []])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
