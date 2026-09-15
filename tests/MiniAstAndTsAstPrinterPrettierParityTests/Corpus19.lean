import Tests.Corpus18

/-!
# Samples of the shapes whose layout prettier decides by a heuristic

The samples here exercise the parts of prettier which do not simply break
a line when it is too long: member chains, chains of arrows, the layout of
an assignment, the hug of a first or of a last argument, and the
parenthesisation the precedence of the operators calls for.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A chain of `n` calls of the method `name` on `base`. -/
def chainOf (base : MiniExpr) (name : String) : Nat → MiniExpr
  | 0 => base
  | n + 1 => methodCall (chainOf base name n) name [v "item"]

/-- A curried arrow of the given parameters. -/
def curried : List String → MiniExpr → MiniExpr
  | [], body => body
  | x :: xs, body => .arrow false [par x] (.expr (curried xs body))

/-- The samples. -/
def samples19 : List Sample :=
  [ -- member chains
    { name := "chain-four-calls"
      prog := ⟨[es (chainOf (v "theCollection") "filterTheValues" 4)]⟩ }
  , { name := "chain-two-calls-short"
      prog := ⟨[es (chainOf (v "a") "map" 2)]⟩ }
  , { name := "chain-with-index"
      prog := ⟨[es (methodCall (.index (methodCall (v "theCollection") "values")
                  (num 0)) "toString")]⟩ }
  , { name := "chain-on-this"
      prog := ⟨[es (chainOf .this "handleTheValue" 3)]⟩ }
  , { name := "chain-factory"
      prog := ⟨[es (methodCall (call "expect" [v "value"]) "toBe" [num 1])]⟩ }
  , { name := "chain-short-head"
      prog := ⟨[es (chainOf (v "z") "aMethodWithARatherLongName" 3)]⟩ }
  , { name := "chain-computed-member"
      prog := ⟨[es (.index (chainOf (v "theCollection") "filter" 2) (.string "key"))]⟩ }
  , { name := "chain-with-function-argument"
      prog := ⟨[es (methodCall (methodCall (v "theCollection") "map"
                  [.arrow false [par "item"] (.expr (.dot (v "item") (nes "value")))]) "filter"
                  [.arrow false [par "item"] (.expr (v "item"))])]⟩ }
  , { name := "chain-of-awaits"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.expr (methodCall (.await (methodCall (v "theClient") "request"
                    [v (longName 0)])) "json")])]⟩ }
  , { name := "chain-after-new"
      prog := ⟨[es (methodCall (methodCall (.new (v "TheBuilderClass") [])
                  "withTheFirstOption" [v (longName 0)]) "build")]⟩ }
  , { name := "chain-capitalised-factory"
      prog := ⟨[es (methodCall (methodCall (call "Factory" [v "a"]) "theFirstStep" [])
                  "theSecondStep" [v (longName 0)])]⟩ }
  , { name := "chain-this-property-head"
      prog := ⟨[es (methodCall (methodCall (.dot .this (nes "theProperty")) "first" [])
                  "second" [v (longName 0)])]⟩ }
  , { name := "chain-optional-calls"
      prog := ⟨[es (.chain (v (longName 0))
                  ⟨.dot true (nes "theFirstMethod"), [.call false [],
                    .dot true (nes "theSecondMethod"), .call false [v (longName 1)]]⟩)]⟩ }
  , { name := "optional-chain-long"
      prog := ⟨[es (.chain (v (longName 0))
                  ⟨.dot true (nes (longName 1)), [.call false [v "item"],
                    .dot true (nes (longName 2)), .index false (num 0)]⟩)]⟩ }
    -- chains of arrows
  , { name := "arrow-chain-long"
      prog := ⟨[st (constDecl (longName 0)
                  (curried ["first", "second", "third"]
                    (.binary (v (longName 1)) .plus (v (longName 2)))))]⟩ }
  , { name := "arrow-chain-object-body"
      prog := ⟨[es (call "f" [curried ["a", "bb"] (.object [kv "value" (v "a")])])]⟩ }
  , { name := "arrow-returning-arrow-call"
      prog := ⟨[es (.call (curried ["a"] (v "a")) [num 1])]⟩ }
  , { name := "arrow-body-object-long"
      prog := ⟨[es (.arrow false [par "item"] (.expr (.object
                  [kv (longName 0) (v "item"), kv (longName 1) (v "item")])))]⟩ }
  , { name := "arrow-body-sequence"
      prog := ⟨[es (.arrow false [par "a"] (.expr (.seq (call "first" []) (call "second" []))))]⟩ }
    -- the argument prettier hugs
  , { name := "hug-first-arg-arrow"
      prog := ⟨[es (call "useEffect" [.arrow false [] (.block [.expr (call "doTheThing" [])]),
                  .array [.elem (v (longName 0))]])]⟩ }
  , { name := "hug-first-arg-function"
      prog := ⟨[es (call "setTimeout" [.func false false none []
                  [.expr (call "tick" [])], num 500])]⟩ }
  , { name := "two-function-arguments"
      prog := ⟨[es (call "theFunction" [.arrow false [par "a"] (.block [.expr (v "a")]),
                  .arrow false [par "bb"] (.block [.expr (v "bb")])])]⟩ }
  , { name := "hug-last-arg-object"
      prog := ⟨[es (call "configureTheThing" [v (longName 0),
                  .object [kv "first" (v (longName 1)), kv "second" (v (longName 2))]])]⟩ }
  , { name := "hug-last-arg-template"
      prog := ⟨[es (call "theTaggedFunction" [v (longName 0),
                  .template none "a rather long piece of template text here" []])]⟩ }
  , { name := "last-arg-function"
      prog := ⟨[es (call "describe" [.string "the suite",
                  .func false false none [] [.expr (call "check" [])]])]⟩ }
  , { name := "param-destructuring-hug"
      prog := ⟨[es (call "theFunction" [.arrow false [.plain (.object
                  [⟨.ident (nes (longName 0)), p (longName 0)⟩] none)]
                  (.expr (v (longName 0)))])]⟩ }
    -- the layout of an assignment
  , { name := "assign-long-binary"
      prog := ⟨[st (constDecl (longName 0)
                  (.binary (.binary (v (longName 1)) .plus (v (longName 2))) .plus
                    (v (longName 3))))]⟩ }
  , { name := "assign-long-chain"
      prog := ⟨[st (constDecl (longName 0) (chainOf (v "theCollection") "mapTheValue" 3))]⟩ }
  , { name := "assign-ternary"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (v (longName 1)) (v (longName 2)) (v (longName 3))))]⟩ }
  , { name := "assign-member-target"
      prog := ⟨[es (.assign (.dot (.dot (v (longName 0)) (nes (longName 1)))
                  (nes "theProperty")) .assign (call (longName 2) [v "item"]))]⟩ }
  , { name := "assign-destructuring-long"
      prog := ⟨[st (.decl .const ⟨⟨.object
                  [⟨.ident (nes (longName 0)), p (longName 0)⟩,
                   ⟨.ident (nes (longName 1)), p (longName 1)⟩] none,
                  some (call "theConfiguration" [])⟩, []⟩)]⟩ }
  , { name := "assign-chain"
      prog := ⟨[es (.assign (v (longName 0)) .assign
                  (.assign (v (longName 1)) .assign (v (longName 2))))]⟩ }
  , { name := "assign-arrow-chain"
      prog := ⟨[st (constDecl (longName 0)
                  (curried [longName 1, longName 2] (call "theResult" [])))]⟩ }
  , { name := "assign-await-long"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [constDecl (longName 0) (.await (call "theRatherLongFunctionName"
                    [v (longName 1)]))])]⟩ }
  , { name := "assign-string-concat"
      prog := ⟨[st (constDecl (longName 0)
                  (.binary (.binary (.string "a rather long string literal here") .plus
                    (v (longName 1))) .plus (.string "another rather long string")))]⟩ }
  , { name := "assign-class-field-arrow"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.field [] false false (.ident (nes (longName 0)))
                    (some (.arrow false [par "item"] (.expr (call "handle" [v "item"]))))])]⟩ }
  , { name := "decl-multiple-long"
      prog := ⟨[st (.decl .let_ ⟨⟨p (longName 0), some (num 1)⟩,
                  [⟨p (longName 1), some (num 2)⟩, ⟨p (longName 2), some (num 3)⟩]⟩)]⟩ }
    -- conditionals
  , { name := "ternary-binary-test"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (.binary (.unary .typeof (v (longName 1))) .strictEq
                    (.string "string")) (v (longName 2)) (v (longName 3))))]⟩ }
  , { name := "ternary-nested-consequent"
      prog := ⟨[es (.ternary (v (longName 0))
                  (.ternary (v (longName 1)) (num 1) (num 2)) (num 3))]⟩ }
  , { name := "ternary-in-arguments"
      prog := ⟨[es (call "theFunction" [v (longName 0),
                  .ternary (v (longName 1)) (v (longName 2)) (v (longName 3))])]⟩ }
  , { name := "ternary-member-chain"
      prog := ⟨[es (.dot (.ternary (v "a") (v "bb") (v "value")) (nes "length"))]⟩ }
  , { name := "nested-ternary-chain"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (v (longName 1)) (num 1)
                    (.ternary (v (longName 2)) (num 2)
                      (.ternary (v (longName 3)) (num 3) (num 4)))))]⟩ }
    -- operators and their parentheses
  , { name := "binary-mixed-precedence"
      prog := ⟨[es (.binary (.binary (v "a") .plus (.binary (v "bb") .times (v "value")))
                  .minus (v "item"))]⟩ }
  , { name := "binary-xor-and-shifts"
      prog := ⟨[es (.binary (.binary (v "a") .bitXor (v "bb")) .ursh (num 2)),
                es (.binary (v "a") .strictNeq (v "bb")),
                es (.binary (v "a") .rsh (num 1))]⟩ }
  , { name := "logical-parens"
      prog := ⟨[es (.binary (v "a") .and (.binary (v "bb") .or (v "value")))]⟩ }
  , { name := "logical-long-in-if"
      prog := ⟨[st (.if_ (.binary (.binary (v (longName 0)) .and (v (longName 1))) .and
                  (v (longName 2))) (.block [.expr (v "a")]) none)]⟩ }
  , { name := "postfix-and-prefix"
      prog := ⟨[es (.postfix (v "a") .incr), es (.postfix (v "a") .decr),
                es (.unary .minus (.unary .minus (v "a"))),
                es (.unary .not (.unary .not (v "a")))]⟩ }
  , { name := "delete-and-void"
      prog := ⟨[es (.unary .delete (.dot (v "a") (nes "bb"))),
                es (.unary .void (num 0))]⟩ }
  , { name := "unary-not-of-logical"
      prog := ⟨[es (.unary .not (.binary (v (longName 0)) .and (v (longName 1))))]⟩ }
  , { name := "await-unary"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.expr (.unary .typeof (.await (call "g" []))),
                   .expr (.unary .not (.await (call "g" [])))])]⟩ }
  , { name := "sequence-statement"
      prog := ⟨[es (.seq (call "first" []) (.seq (call "second" []) (call "third" [])))]⟩ }
    -- literals and keys
  , { name := "strings-quotes"
      prog := ⟨[es (.string "it's"), es (.string "say \"hi\""),
                es (.string "both ' and \""), es (.string "back\\slash"),
                es (.string "line\nbreak\ttab")]⟩ }
  , { name := "numbers-normalisation"
      prog := ⟨[es (.number (.decimal 1 3)), es (.number (.decimal 150 (-2))),
                es (.number (.decimal 5 (-1))), es (.number (.radix .hexadecimal 171)),
                es (.number (.decimal 1000000 0)), es (.number (.bigint .hexadecimal 255))]⟩ }
  , { name := "number-edge-cases"
      prog := ⟨[es (.number (.decimal 0 0)), es (.number (.decimal 5 (-1))),
                es (.number (.decimal 1 21)), es (.number (.decimal 1 (-7))),
                es (.number (.decimal 100 (-2))), es (.number (.radix .octal 8)),
                es (.number (.radix .binary 5)), es (.number (.bigint .decimal 0))]⟩ }
  , { name := "template-long-expr"
      prog := ⟨[es (.template none "value: " [⟨.binary (v (longName 0)) .plus
                  (v (longName 1)), " end"⟩])]⟩ }
  , { name := "template-tagged-member"
      prog := ⟨[es (.template (some (.dot (v "String") (nes "raw"))) "a" [⟨v "bb", "c"⟩])]⟩ }
  , { name := "template-nested"
      prog := ⟨[es (.template none "outer " [⟨.template none "inner" [], " end"⟩])]⟩ }
  , { name := "object-quoted-keys-mixed"
      prog := ⟨[es (.object [.keyValue (.string "a-key") (num 1),
                  .keyValue (.ident (nes "plain")) (num 2)])]⟩ }
  , { name := "object-number-and-quoted-keys"
      prog := ⟨[es (.object [.keyValue (.string "a-key") (num 1),
                  .keyValue (.number (JSNumber.ofNat 2)) (num 2)])]⟩ }
  , { name := "property-key-numbers"
      prog := ⟨[es (.object [.keyValue (.number (.decimal 15 (-1))) (num 1),
                  .keyValue (.number (.radix .hexadecimal 255)) (num 2)])]⟩ }
  , { name := "computed-keys"
      prog := ⟨[es (.object [.keyValue (.computed (.string "a")) (num 1),
                  .keyValue (.computed (.binary (v "a") .plus (v "bb"))) (num 2)])]⟩ }
  , { name := "object-methods"
      prog := ⟨[es (.object [.method .get (.ident (nes "value")) [] [.return_ (some (num 1))],
                  .method .set (.ident (nes "value")) [par "x"] [],
                  .method .generator (.ident (nes "items")) [] []])]⟩ }
  , { name := "nested-data-literal"
      prog := ⟨[st (constDecl (longName 0) (.object
                  [kv "first" (.array [.elem (num 1), .elem (num 2)]),
                   kv "second" (.object [kv "inner" (.array [.elem (.string "a"),
                     .elem (.string "bb")])])]))]⟩ }
  , { name := "spread-everywhere"
      prog := ⟨[es (call "f" [.spread (v "xs"), num 1]),
                es (.array [.elem (.spread (v "xs")), .elem (num 1)]),
                es (.object [.spread (v "xs"), .shorthand (nes "a")])]⟩ }
    -- classes, modules and statements
  , { name := "class-extends-call"
      prog := ⟨[st (.classDecl [] (nes "TheClass")
                  (some (call "mixinTheBehaviour" [v (longName 0), v (longName 1)])) [])]⟩ }
  , { name := "class-empty-and-fields"
      prog := ⟨[st (.classDecl [] (nes "A") none []),
                st (.classDecl [] (nes "B") none
                  [.field [] true false (.ident (nes "x")) (some (num 1)),
                   .field [] false false (.private_ (nes "y")) none])]⟩ }
  , { name := "class-decorated-long"
      prog := ⟨[st (.classDecl [call "Component" [.object [kv "selector" (.string "app-root")]]]
                  (nes "TheComponent") none [])]⟩ }
  , { name := "getter-setter-static"
      prog := ⟨[st (.classDecl [] (nes "A") none
                  [.method [] true .get (.ident (nes "value")) [] [.return_ (some (num 1))],
                   .method [] false .set (.computed (.string "x")) [par "value"] [],
                   .staticBlock [.expr (call "init" [])]])]⟩ }
  , { name := "export-default-arrow"
      prog := ⟨[.exportDecl (.defaultExpr (.arrow false [par "item"]
                  (.expr (call "handleTheValue" [v "item", v (longName 0)]))))]⟩ }
  , { name := "export-default-class"
      prog := ⟨[.exportDecl (.defaultExpr (.classExpr [] (some (nes "TheClass")) none []))]⟩ }
  , { name := "export-named-long"
      prog := ⟨[.exportDecl (.locals ((List.range 5).map fun k =>
                  ⟨nes (longName k), some (nes ("alias" ++ toString k))⟩))]⟩ }
  , { name := "import-default-and-named"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes "theDefault")) none
                  (some [⟨nes "first", none⟩, ⟨nes "second", some (nes "renamed")⟩])
                  (nes "the-module")))]⟩ }
  , { name := "if-else-if-chain"
      prog := ⟨[st (.if_ (v "a") (.block [.expr (v "first")])
                  (some (.if_ (v "bb") (.block [.expr (v "second")])
                    (some (.block [.expr (v "third")])))))]⟩ }
  , { name := "if-single-statement"
      prog := ⟨[st (.if_ (v "a") (.expr (call "theFunction" [v (longName 0)])) none)]⟩ }
  , { name := "try-catch-and-finally"
      prog := ⟨[st (.try_ [.expr (v "a")] (.catches ⟨⟨p "e", none, [.expr (v "bb")]⟩, []⟩
                  (.some [.expr (v "value")])))]⟩ }
  , { name := "switch-fallthrough"
      prog := ⟨[st (.switch (v "value")
                  [.case (num 1) [], .case (num 2) [.expr (v "a"), .break_ none],
                   .default []])]⟩ }
  , { name := "switch-long-discriminant"
      prog := ⟨[st (.switch (.binary (v (longName 0)) .plus (v (longName 1)))
                  [.case (.string "a rather long case label here") [.break_ none]])]⟩ }
  , { name := "do-while-long-condition"
      prog := ⟨[st (.doWhile (.block [.expr (v "a")])
                  (.binary (v (longName 0)) .and (v (longName 1))))]⟩ }
  , { name := "for-long-header"
      prog := ⟨[st (.for_ (.decl .let_ ⟨⟨p (longName 0), some (num 0)⟩, []⟩)
                  (some (.binary (v (longName 0)) .lt (.dot (v (longName 1)) (nes "length"))))
                  (some (.postfix (v (longName 0)) .incr)) (.block []))]⟩ }
  , { name := "for-comma-init"
      prog := ⟨[st (.for_ (.decl .let_ ⟨⟨p "a", some (num 0)⟩, [⟨p "bb", some (num 1)⟩]⟩)
                  (some (.binary (v "a") .lt (v "bb"))) (some (.seq (.postfix (v "a") .incr)
                    (.postfix (v "bb") .decr))) (.block []))]⟩ }
  , { name := "for-of-destructuring"
      prog := ⟨[st (.forOf false (.decl .const (.array [.elem (p "key"), .elem (p "value")]))
                  (methodCall (v (longName 0)) "entries") (.block [.expr (v "key")]))]⟩ }
  , { name := "in-operator-in-for-init"
      prog := ⟨[st (.for_ (.expr (.binary (.string "a") .inOp (v "bb"))) none none (.block []))]⟩ }
  , { name := "new-forms"
      prog := ⟨[es (.new (v "Foo") []),
                es (.new (.call (v "getTheClass") []) [v "a"]),
                es (.new (.dot (v "name") (nes "Space")) [])]⟩ }
  , { name := "yield-forms"
      prog := ⟨[st (.funcDecl false true (nes "g") []
                  [.expr (.yield none), .expr (.yield (some (v "a"))),
                   .expr (.yieldFrom (call "other" [])),
                   .expr (.binary (.yield (some (v "a"))) .plus (num 1))])]⟩ }
  , { name := "return-long-logical"
      prog := ⟨[st (.funcDecl false false (nes "f") []
                  [.return_ (some (.binary (.binary (v (longName 0)) .or (v (longName 1)))
                    .or (v (longName 2))))])]⟩ }
  , { name := "throw-new-error"
      prog := ⟨[st (.throw (.new (v "Error") [.string "a rather long message here"]))]⟩ }
  , { name := "empty-bodies"
      prog := ⟨[es (.object []), es (.array []), es (.func false false none [] []),
                st (.block []), st (.funcDecl false false (nes "f") [] [])]⟩ }
  , { name := "labelled-block"
      prog := ⟨[st (.labelled (nes "outer") (.block [.break_ (some (nes "outer"))]))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
