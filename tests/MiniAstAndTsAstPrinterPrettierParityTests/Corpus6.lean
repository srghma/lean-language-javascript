import Tests.Corpus5

/-!
# Sample programs near the edges of the layout

Samples where the layout decisions interact: a chain of arrow functions
inside a member chain, a call whose arguments are expanded in place, a
conditional inside an argument, and lines that end close to the eightieth
column.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An identifier of `n` letters, `aaa…`. -/
def wide (n : Nat) : String := "a" ++ String.ofList (List.replicate (n - 1) 'x')

/-- The samples. -/
def samples6 : List Sample :=
  [ { name := "width-boundary-call-79"
      prog := ⟨[es (call (wide 40) [v (wide 36)])]⟩ }
  , { name := "width-boundary-call-80"
      prog := ⟨[es (call (wide 41) [v (wide 36)])]⟩ }
  , { name := "width-boundary-call-81"
      prog := ⟨[es (call (wide 42) [v (wide 36)])]⟩ }
  , { name := "width-boundary-decl"
      prog := ⟨[st (constDecl (wide 30) (call (wide 30) [v (wide 12)]))]⟩ }
  , { name := "width-boundary-binary"
      prog := ⟨[st (constDecl (wide 20) (.binary (v (wide 25)) .plus (v (wide 28))))]⟩ }
  , { name := "width-boundary-member"
      prog := ⟨[es (.dot (.dot (v (wide 30)) (nes (wide 24))) (nes (wide 20)))]⟩ }
  , { name := "arrow-chain-in-member-chain"
      prog := ⟨[es (dotCall (dotCall (v "theCollectionOfThings") "map"
                  [arrowExpr ["item"] (arrowExpr ["index"]
                    (call "combine" [v "item", v "index"]))]) "flat" [])]⟩ }
  , { name := "arrow-with-object-param"
      prog := ⟨[es (dotCall (v "theCollection") "map"
                  [.arrow false [.plain (.object [opp "identifier" (p "identifier"),
                    opp "name" (p "name")] none)]
                    (.expr (.object [kv "identifier" (v "identifier"), kv "name" (v "name")]))])]⟩ }
  , { name := "arrow-block-in-property"
      prog := ⟨[st (constDecl "theHandlers" (.object
                  [kv "onTheClickEvent" (arrowBlock ["event"]
                    [.expr (call "preventTheDefault" [v "event"]),
                     .expr (call "dispatchTheAction" [v "event"])])]))]⟩ }
  , { name := "class-field-arrow"
      prog := ⟨[st (.classDecl [] (nes "Widget") none
                  [.field [] false false (.ident (nes "handleTheClickEvent"))
                    (some (arrowBlock ["event"]
                      [.expr (call "process" [v "event"])])),
                   .field [] false false (.ident (nes "compute"))
                    (some (arrowExpr ["first"] (arrowExpr ["second"]
                      (.binary (v "first") .plus (v "second")))))])]⟩ }
  , { name := "assignment-chain"
      prog := ⟨[es (.assign (v "first") .assign (.assign (v "second") .assign (num 0))),
                es (.assign (.dot (v "theObject") (nes "property")) .assign
                  (.assign (v "theLocalVariable") .assign (call "computeTheValue" [])))]⟩ }
  , { name := "assignment-chain-arrow"
      prog := ⟨[es (.assign (v "theFirstBinding") .assign (.assign (v "theSecondBinding") .assign
                  (arrowExpr ["value"] (arrowExpr ["other"]
                    (call "combineTheValues" [v "value", v "other"])))))]⟩ }
  , { name := "ternary-in-argument-long"
      prog := ⟨[es (call "renderTheComponent" [.ternary (v "isLoadingRightNow")
                  (call "makeTheSpinner" []) (call "makeTheContent" [v "theData"]),
                  v "theContainerElement"])]⟩ }
  , { name := "ternary-as-callee"
      prog := ⟨[es (.call (.ternary (v "useTheFirst") (v "firstFunction") (v "secondFunction"))
                  [v "argument"])]⟩ }
  , { name := "ternary-object-value"
      prog := ⟨[st (constDecl "theResultingObject" (.object
                  [kv "status" (.ternary (v "hasFailedSomewhere") (str "failed")
                    (str "succeeded")),
                   kv "detail" (.ternary (v "isVerboseModeEnabled")
                    (call "describeTheFailure" [v "theError"]) .null)]))]⟩ }
  , { name := "nested-ternary-alternates"
      prog := ⟨[st (constDecl "theSelectedLabel" (.ternary (v "first") (str "the first label")
                  (.ternary (v "second") (str "the second label")
                    (.ternary (v "third") (str "the third label") (str "the last label")))))]⟩ }
  , { name := "ternary-in-template"
      prog := ⟨[st (constDecl "theMessage" (.template none "you have "
                  [⟨.ternary (v "count") (v "count") (str "no"), " new messages"⟩]))]⟩ }
  , { name := "call-object-then-function"
      prog := ⟨[es (call "describeTheTest" [str "does the right thing",
                  arrowBlock [] [.expr (call "expectSomething" [])]])]⟩ }
  , { name := "call-function-then-object"
      prog := ⟨[es (call "register" [arrowBlock [] [.expr (call "run" [])],
                  .object [kv "once" .true_]])]⟩ }
  , { name := "call-with-three-functions"
      prog := ⟨[es (call "onEveryOutcome" [arrowBlock [] [.expr (call "first" [])],
                  arrowBlock [] [.expr (call "second" [])],
                  arrowBlock [] [.expr (call "third" [])]])]⟩ }
  , { name := "call-long-single-object"
      prog := ⟨[es (dotCall (v "theApplicationInstance") "configureEverything"
                  [.object [kv "theFirstOption" (num 1), kv "theSecondOption" (num 2),
                    kv "theThirdOption" (num 3)]])]⟩ }
  , { name := "member-chain-two-calls"
      prog := ⟨[es (dotCall (dotCall (v "wrapper") "first" []) "second" [])]⟩ }
  , { name := "member-chain-computed-calls"
      prog := ⟨[es (.call (.index (call "getTheHandlers" []) (str "onEvent"))
                  [v "theEventObject"])]⟩ }
  , { name := "member-chain-this-base"
      prog := ⟨[st (.classDecl [] (nes "Service") none
                  [.method [] false .normal (.ident (nes "run")) []
                    [.return_ (some (dotCall (dotCall (dotCall .this "prepareTheRequest" [])
                      "sendTheRequest" []) "then" [arrowExpr ["response"]
                      (.dot (v "response") (nes "body"))]))]])]⟩ }
  , { name := "await-in-chain"
      prog := ⟨[st (.funcDecl true false (nes "load") []
                  [constDecl "theParsedBody"
                    (.await (dotCall (.await (call "fetch" [v "theUrl"])) "json" []))])]⟩ }
  , { name := "new-chain"
      prog := ⟨[es (dotCall (.new (v "TheBuilderClass") [v "options"]) "buildIt" [])]⟩ }
  , { name := "long-binary-in-argument"
      prog := ⟨[es (call "assertThat" [.binary (.binary (v "theFirstValue") .plus
                  (v "theSecondValue")) .plus (v "theThirdValue"), str "sum"])]⟩ }
  , { name := "long-binary-in-array"
      prog := ⟨[st (constDecl "theValues" (.array [.elem (.binary (v "aLongNameOne") .times
                  (v "aLongNameTwo")), .elem (.binary (v "aLongNameThree") .times
                  (v "aLongNameFour"))]))]⟩ }
  , { name := "long-binary-in-property"
      prog := ⟨[st (constDecl "theTotals" (.object [kv "sum" (.binary (.binary
                  (v "theFirstValue") .plus (v "theSecondValue")) .plus (v "theThirdValue"))]))]⟩ }
  , { name := "long-logical-in-return"
      prog := ⟨[st (.funcDecl false false (nes "isReady") []
                  [.return_ (some (.binary (.binary (v "hasLoadedTheData") .and
                    (v "hasRenderedTheView")) .and (.unary .not (v "hasErrors"))))])]⟩ }
  , { name := "for-long-comma-header"
      prog := ⟨[st (.for_ (.decl .let_ ⟨⟨p "index", some (num 0)⟩,
                    [⟨p "length", some (.dot (v "theCollection") (nes "length"))⟩]⟩)
                  (some (.binary (v "index") .lt (v "length")))
                  (some (.postfix (v "index") .incr))
                  (.block [.expr (call "visit" [.index (v "theCollection") (v "index")])]))]⟩ }
  , { name := "yield-ternary"
      prog := ⟨[st (.funcDecl false true (nes "choose") [par "flag"]
                  [.expr (.yield (some (.ternary (v "flag") (v "theFirstValue")
                    (v "theSecondValue"))))])]⟩ }
  , { name := "decorated-methods"
      prog := ⟨[st (.classDecl [] (nes "Controller") none
                  [.method [call "route" [str "/the/long/path/for/the/resource"]] false .normal
                    (.ident (nes "handle")) [par "request"]
                    [.return_ (some (call "respond" [v "request"]))]])]⟩ }
  , { name := "object-method-long-params"
      prog := ⟨[st (constDecl "theApi" (.object
                  [.method .normal (.ident (nes "requestSomething"))
                    [par "theFirstParameter", par "theSecondParameter", par "theThirdParameter"]
                    [.return_ (some (v "theFirstParameter"))]]))]⟩ }
  , { name := "computed-key-long"
      prog := ⟨[st (constDecl "theLookupTable" (.object
                  [.keyValue (.computed (.dot (v "TheConstants") (nes "THE_FIRST_KEY"))) (num 1),
                   .keyValue (.computed (.template none "prefix-" [⟨v "suffix", ""⟩])) (num 2)]))]⟩ }
  , { name := "array-of-arrays"
      prog := ⟨[st (constDecl "theMatrix" (.array
                  [.elem (.array [.elem (num 1), .elem (num 2), .elem (num 3)]),
                   .elem (.array [.elem (num 4), .elem (num 5), .elem (num 6)]),
                   .elem (.array [.elem (num 7), .elem (num 8), .elem (num 9)])]))]⟩ }
  , { name := "array-long-strings"
      prog := ⟨[st (constDecl "theListOfMessages" (.array
                  [.elem (str "the first message of the list"),
                   .elem (str "the second message of the list")]))]⟩ }
  , { name := "template-long-substitution"
      prog := ⟨[st (constDecl "theRenderedTemplate" (.template none "<div class=\""
                  [⟨call "classNamesFor" [v "theComponentState"], "\">"⟩,
                   ⟨.dot (v "theComponentState") (nes "label"), "</div>"⟩]))]⟩ }
  , { name := "optional-call-chain-long"
      prog := ⟨[st (constDecl "theResultValue" (.chain (v "theRegistryObject")
                  ⟨.dot true (nes "lookupTheHandler"),
                   [.call false [v "theEventName"], .dot true (nes "result")]⟩))]⟩ }
  , { name := "private-in-methods"
      prog := ⟨[st (.classDecl [] (nes "Box") none
                  [.field [] false false (.private_ (nes "value")) none,
                   .method [] true .normal (.ident (nes "isBox")) [par "candidate"]
                    [.return_ (some (.binary (.privateName (nes "value")) .inOp (v "candidate")))]])]⟩ }
  , { name := "empty-function-bodies"
      prog := ⟨[st (.funcDecl false false (nes "nothing") [] []),
                st (constDecl "alsoNothing" (arrowBlock [] [])),
                st (constDecl "theEmptyClass" (.classExpr [] none none []))]⟩ }
  , { name := "nested-calls-deep"
      prog := ⟨[es (call "first" [call "second" [call "third" [call "fourth" [v "theValue"]]]])]⟩ }
  , { name := "long-condition-in-while"
      prog := ⟨[st (.while_ (.binary (.binary (v "theCurrentIndex") .lt
                  (.dot (v "theCollection") (nes "length"))) .and
                  (.unary .not (v "hasFoundTheMatch")))
                  (.block [.expr (.postfix (v "theCurrentIndex") .incr)]))]⟩ }
  , { name := "if-else-if-long"
      prog := ⟨[st (.if_ (call "isTheFirstCase" [v "theValue"])
                  (.block [.return_ (some (num 1))])
                  (some (.if_ (call "isTheSecondCase" [v "theValue"])
                    (.block [.return_ (some (num 2))])
                    (some (.block [.return_ (some (num 3))])))))]⟩ }
  , { name := "return-parenthesised-binary"
      prog := ⟨[st (.funcDecl false false (nes "total") []
                  [.return_ (some (.binary (.binary (v "theFirstLongValue") .plus
                    (v "theSecondLongValue")) .plus (v "theThirdLongValue")))])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
