import Tests.Corpus

/-!
# More sample programs

Samples of the kind of code whose layout prettier decides with its member
chain, call argument and assignment heuristics.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A string literal expression. -/
def str (s : String) : MiniExpr := .string s

/-- A method call, `obj.name(args)`. -/
def dotCall (obj : MiniExpr) (name : String) (args : List MiniExpr) : MiniExpr :=
  .call (.dot obj (nes name)) args

/-- An arrow function with a block body. -/
def arrowBlock (params : List String) (body : List MiniStatement) : MiniExpr :=
  .arrow false (params.map par) (.block body)

/-- An arrow function with an expression body. -/
def arrowExpr (params : List String) (body : MiniExpr) : MiniExpr :=
  .arrow false (params.map par) (.expr body)

/-- The samples. -/
def samples2 : List Sample :=
  [ { name := "chain-promise"
      prog := ⟨[es (dotCall (dotCall (v "promise") "then"
                  [arrowBlock ["result"] [.expr (dotCall (v "console") "log" [v "result"])]])
                  "catch" [arrowBlock ["error"] [.throw (v "error")]])]⟩ }
  , { name := "chain-long"
      prog := ⟨[es (dotCall (dotCall (dotCall (dotCall (v "someObject")
                  "someMethodName" []) "anotherMethodName" []) "yetAnotherMethod" [])
                  "finalMethod" [])]⟩ }
  , { name := "chain-fits"
      prog := ⟨[es (dotCall (dotCall (dotCall (v "wrapper")
                  "find" [str "SomethingLikeAComponent"]) "prop" [str "open", .true_])
                  "simulate" [str "click", num 1])]⟩ }
  , { name := "chain-factory"
      prog := ⟨[es (dotCall (dotCall (dotCall (v "Object") "keys" [v "itemsCollection"])
                  "filter" [arrowExpr ["x"] (.dot (v "x") (nes "enabled"))])
                  "map" [arrowExpr ["x"] (.dot (v "x") (nes "identifier"))])]⟩ }
  , { name := "chain-short-base"
      prog := ⟨[es (dotCall (dotCall (dotCall (v "d3") "scaleLinear" [])
                  "domain" [.array [.elem (num 0), .elem (num 100)]])
                  "range" [.array [.elem (num 0), .elem (v "aWidthValueThatIsLong")]])]⟩ }
  , { name := "chain-this"
      prog := ⟨[es (dotCall (.dot (.this) (nes "someProperty")) "someMethod" [v "argument"])]⟩ }
  , { name := "chain-members-only"
      prog := ⟨[st (constDecl "result"
                  (.dot (.dot (.dot (.dot (v "someObject") (nes "propertyOne"))
                    (nes "propertyTwo")) (nes "propertyThree")) (nes "propertyFourth")))]⟩ }
  , { name := "hug-last-arrow"
      prog := ⟨[es (call "foo" [v "a", v "b", arrowBlock [] [.return_ (some (num 1))]])]⟩ }
  , { name := "hug-last-function"
      prog := ⟨[es (call "describe" [str "a description of the behaviour",
                  .func false false none [] [.expr (call "runTheTest" [])]])]⟩ }
  , { name := "hug-last-object"
      prog := ⟨[es (call "configure" [v "target",
                  .object [.keyValue (.ident (nes "optionNumberOne")) (.true_),
                           .keyValue (.ident (nes "optionNumberTwo")) (str "value"),
                           .keyValue (.ident (nes "optionNumberThree")) (num 42)]])]⟩ }
  , { name := "hug-timeout"
      prog := ⟨[es (call "setTimeout" [arrowBlock [] [.expr (call "tick" [])], num 1000])]⟩ }
  , { name := "hug-map"
      prog := ⟨[st (constDecl "doubled"
                  (dotCall (v "values") "map" [arrowExpr ["x"] (.binary (v "x") .times (num 2))]))]⟩ }
  , { name := "assign-string"
      prog := ⟨[st (constDecl "longVariableNameHereXX"
                  (str "a string literal that is quite long and will not fit"))]⟩ }
  , { name := "assign-call"
      prog := ⟨[st (constDecl "x" (call "someFunctionCallWithLongName"
                  [v "argumentNumberOne", v "argumentNumberTwo", v "three"]))]⟩ }
  , { name := "assign-await"
      prog := ⟨[st (.funcDecl true false (nes "main") []
                  [constDecl "responseValue" (.await (call "fetchTheThing"
                    [v "argumentOne", v "argumentTwo"]))])]⟩ }
  , { name := "assign-new"
      prog := ⟨[st (constDecl "instanceOfSomething"
                  (.new (v "SomeVeryLongConstructorName") [v "argumentOne", v "argTwo"]))]⟩ }
  , { name := "assign-arrow"
      prog := ⟨[st (constDecl "handlerFunction"
                  (arrowBlock ["eventArgument"]
                    [.expr (dotCall (v "eventArgument") "preventDefault" [])]))]⟩ }
  , { name := "assign-member-chain"
      prog := ⟨[st (constDecl "value"
                  (.dot (.dot (.dot (v "configurationObject") (nes "nestedSection"))
                    (nes "anotherLevel")) (nes "finalPropertyName")))]⟩ }
  , { name := "assign-ternary-binary-test"
      prog := ⟨[st (constDecl "chosenValue"
                  (.ternary (.binary (v "someCondition") .and (v "otherCondition"))
                    (v "theFirstValue") (v "theSecondValue")))]⟩ }
  , { name := "assign-property"
      prog := ⟨[es (.assign (.dot (.dot (v "someObject") (nes "someProperty")) (nes "nested"))
                  .assign (call "computeTheValue" [v "argument", v "another"]))]⟩ }
  , { name := "return-long-binary"
      prog := ⟨[st (.funcDecl false false (nes "f") []
                  [.return_ (some (.binary (.binary (v (longName 0)) .and (v (longName 1)))
                    .and (v (longName 2))))])]⟩ }
  , { name := "return-object"
      prog := ⟨[st (.funcDecl false false (nes "f") []
                  [.return_ (some (.object [.keyValue (.ident (nes "a")) (num 1),
                    .keyValue (.ident (nes "b")) (num 2)]))])]⟩ }
  , { name := "if-call-condition"
      prog := ⟨[st (.if_ (call "someVeryLongFunctionCallName"
                    [v "argumentOne", v "argumentTwo", v "argumentThree", v "four"])
                  (.block []) none)]⟩ }
  , { name := "if-not-logical"
      prog := ⟨[st (.if_ (.unary .not (.binary (v (longName 0)) .or (v (longName 1))))
                  (.block [.return_ none]) none)]⟩ }
  , { name := "class-long"
      prog := ⟨[st (.classDecl [] (nes "AVeryLongClassNameHere")
                  (some (v "SomeOtherVeryLongBaseClassNameThatIsLong123")) []),
                st (.classDecl [.call (v "decorator") []] (nes "B") none
                  [.method [.call (v "logged") []] false .normal (.ident (nes "run")) []
                    [.return_ (some (.this))]])]⟩ }
  , { name := "object-keys"
      prog := ⟨[st (constDecl "o" (.object
                  [.keyValue (.string "abc") (num 1),
                   .keyValue (.string "a-b") (num 2),
                   .keyValue (.string "1") (num 3),
                   .keyValue (.string "1.5") (num 4),
                   .keyValue (.string "01") (num 5),
                   .keyValue (.number (JSNumber.ofNat 7)) (num 6)]))]⟩ }
  , { name := "object-nested"
      prog := ⟨[st (constDecl "settings" (.object
                  [.keyValue (.ident (nes "server")) (.object
                    [.keyValue (.ident (nes "host")) (str "localhost"),
                     .keyValue (.ident (nes "port")) (num 8080)]),
                   .keyValue (.ident (nes "debug")) (.false_)]))]⟩ }
  , { name := "template-long"
      prog := ⟨[st (constDecl "message" (.template none "a template with "
                  [⟨v "aLongIdentifierNameNumberZero", " and "⟩, ⟨v "anotherOne", " text"⟩]))]⟩ }
  , { name := "optional-chain-call"
      prog := ⟨[es (.chain (v "someObject")
                  ⟨.dot true (nes "maybeMethod"), [.call false [v "argument"]]⟩)]⟩ }
  , { name := "for-long-header"
      prog := ⟨[st (.for_ (.decl .let_ ⟨⟨p "indexVariable", some (num 0)⟩, []⟩)
                  (some (.binary (v "indexVariable") .lt (.dot (v "collection") (nes "length"))))
                  (some (.postfix (v "indexVariable") .incr))
                  (.block [.expr (call "process" [.index (v "collection") (v "indexVariable")])]))]⟩ }
  , { name := "try-content"
      prog := ⟨[st (.try_ [.expr (call "mightThrow" [])]
                  (.catches ⟨⟨p "err", none,
                    [.expr (dotCall (v "console") "error" [v "err"])]⟩, []⟩ .none))]⟩ }
  , { name := "switch-blocks"
      prog := ⟨[st (.switch (v "value")
                  [.case (str "one") [.block [constDecl "x" (num 1), .break_ none]],
                   .default []])]⟩ }
  , { name := "destructuring-nested"
      prog := ⟨[st (.decl .const ⟨⟨.object
                    [⟨.ident (nes "data"), .object [⟨.ident (nes "items"), p "items"⟩] none⟩,
                     ⟨.ident (nes "status"), p "status"⟩] none,
                    some (v "response")⟩, []⟩)]⟩ }
  , { name := "params-long"
      prog := ⟨[st (.funcDecl false false (nes "aFunctionWithManyParameters")
                  [par "parameterNumberOne", par "parameterNumberTwo",
                   par "parameterNumberThree"]
                  [.return_ (some (v "parameterNumberOne"))])]⟩ }
  , { name := "params-defaults"
      prog := ⟨[st (.funcDecl false false (nes "f")
                  [.plain (.withDefault (p "a") (num 1)),
                   .plain (.object [⟨.ident (nes "b"), p "b"⟩] none),
                   .rest (p "rest")] [])]⟩ }
  , { name := "nested-calls-long"
      prog := ⟨[es (call "outerFunction"
                  [call "innerFunctionWithLongName" [v "argumentOne", v "argumentTwo"],
                   v "anotherArgument"])]⟩ }
  , { name := "await-in-binary"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.expr (.binary (.await (v "a")) .and (v "b")),
                   .expr (.binary (.await (call "g" [])) .plus (num 1))])]⟩ }
  , { name := "arrow-chain"
      prog := ⟨[st (constDecl "curried"
                  (arrowExpr ["a"] (arrowExpr ["b"] (arrowExpr ["c"] (v "someValue")))))]⟩ }
  , { name := "arrow-long-body"
      prog := ⟨[st (constDecl "computedValue"
                  (arrowExpr [] (.binary (.binary (v (longName 0)) .plus (v (longName 1)))
                    .plus (v "aaa"))))]⟩ }
  , { name := "imports-long"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
                  (some [⟨nes "aLongSpecifierName", none⟩,
                         ⟨nes "anotherLongSpecifierName", none⟩,
                         ⟨nes "thirdName", none⟩]) (nes "./module"))),
                .importDecl (.bare (nes "./polyfills.js") [⟨"type", "json"⟩])]⟩ }
  , { name := "exports-long"
      prog := ⟨[.exportDecl (.defaultExpr (.binary (.binary (v (longName 0)) .plus (v (longName 1)))
                  .plus (v "aaaa")))]⟩ }
  , { name := "logical-assignment-object"
      prog := ⟨[st (constDecl "options" (.binary (v "providedOptions") .or
                  (.object [.keyValue (.ident (nes "a")) (num 1)])))]⟩ }
  , { name := "mixed-operators"
      prog := ⟨[es (.binary (.binary (v "a") .and (v "b")) .or (v "c")),
                es (.binary (v "a") .plus (.binary (v "b") .mod (v "c"))),
                es (.binary (.binary (v "a") .bitAnd (v "b")) .bitOr (v "c")),
                es (.binary (.binary (v "a") .times (v "b")) .mod (v "c")),
                es (.binary (.binary (v "a") .eq (v "b")) .eq (v "c")),
                es (.binary (v "a") .plus (.binary (v "b") .plus (v "c")))]⟩ }
  , { name := "unary-await-parens"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.expr (.dot (.await (v "p")) (nes "value")),
                   .expr (.unary .not (.binary (v "a") .and (v "b"))),
                   .expr (.array [.elem (.spread (.binary (v "a") .or (v "b")))])])]⟩ }
  , { name := "getter-setter-class"
      prog := ⟨[st (.classDecl [] (nes "Point") none
                  [.field [] false false (.private_ (nes "x")) (some (num 0)),
                   .method [] false .get (.ident (nes "x")) []
                     [.return_ (some (.privateDot (.this) (nes "x")))],
                   .method [] false .set (.ident (nes "x")) [par "value"]
                     [.expr (.assign (.privateDot (.this) (nes "x")) .assign (v "value"))],
                   .staticBlock [.expr (call "register" [])]])]⟩ }
  , { name := "long-condition-mixed"
      prog := ⟨[st (.if_ (.binary (.binary (v "firstConditionValue") .and (v "secondCondition"))
                    .or (.binary (v "thirdCondition") .and (v "fourthConditionValue")))
                  (.block [.expr (call "doSomething" [])]) none)]⟩ }
  , { name := "statement-sequence"
      prog := ⟨[es (.seq (.assign (v "a") .assign (num 1))
                  (.seq (.assign (v "b") .assign (num 2)) (.assign (v "c") .assign (num 3))))]⟩ }
  , { name := "labelled-loop"
      prog := ⟨[st (.labelled (nes "outer")
                  (.forOf false (.decl .const (p "item")) (v "items")
                    (.block [.if_ (.dot (v "item") (nes "skip"))
                      (.continue_ (some (nes "outer"))) none])))]⟩ }
  , { name := "do-while-body"
      prog := ⟨[st (.doWhile (.block [.expr (call "step" [])])
                  (.binary (v "counter") .lt (num 10)))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
