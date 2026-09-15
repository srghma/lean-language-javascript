import Tests.Corpus25

/-!
# Samples of the layout decisions of the harder places

The samples here walk over the decisions which depend on the shape of a
whole subtree rather than on a single node: the arrays prettier fills, the
calls whose argument it expands in place, the chains it would gain little
by breaking, and the layouts of an assignment whose right hand side is one
of those.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A member chain of two calls, long enough to break. -/
def chainOfTwoCalls : MiniExpr :=
  .call (.dot (.call (.dot (v "theCollection") (nes "filterTheItems"))
    [v "handler"]) (nes "mapTheItems")) [v "theIteratorOfTheList"]

/-- `abcd?.aVeryVeryLongIdentifierNameHere`, an optional chain. -/
def optionalChainBase : MiniExpr :=
  .chain (v "abcd") ⟨.dot true (nes "aVeryVeryLongIdentifierNameHere"), []⟩

/-- The samples. -/
def samples26 : List Sample :=
  [ -- an array of object literals, which prettier always breaks
    { name := "layout-array-of-objects"
      prog := ⟨[st (constDecl "value" (.array [.elem (.object [kv "a" (num 1)]),
                  .elem (.object [kv "bb" (num 2)])])),
                st (constDecl "single" (.array [.elem (.object [kv "a" (num 1)])])),
                st (constDecl "empties" (.array [.elem (.object []), .elem (.object [])]))]⟩ }
  , { name := "layout-array-of-arrays"
      prog := ⟨[st (constDecl "value" (.array [.elem (.array [.elem (num 1), .elem (num 2)]),
                  .elem (.array [.elem (num 3), .elem (num 4)])]))]⟩ }
  , -- the arrays prettier fills, and the ones it does not
    { name := "layout-fill-numbers"
      prog := ⟨[st (constDecl "value" (.array
                  ((List.range 30).map fun i => .elem (num (i * 111)))))]⟩ }
  , { name := "layout-fill-strings"
      prog := ⟨[st (constDecl "value" (MiniExpr.array
                  ((List.range 20).map fun i => MiniArrayElement.elem (.string s!"s{i}"))))]⟩ }
  , { name := "layout-fill-mixed"
      prog := ⟨[st (constDecl "value" (MiniExpr.array
                  ((List.range 20).map (fun i => MiniArrayElement.elem (num (i * 111))) ++
                    [MiniArrayElement.elem (.string "end")])))]⟩ }
  , { name := "layout-fill-signed"
      prog := ⟨[st (constDecl "value" (.array
                  ((List.range 25).map fun i => .elem (.unary .minus (num (i * 37))))))]⟩ }
  , -- the heads a member chain may have
    { name := "layout-chain-heads"
      prog := ⟨[es (.call (.dot (.call (.dot .this (nes "theHandlerName"))
                    [v "aLongIdentifierNameNumberZero"]) (nes "theIteratorOfTheList")) []),
                es (.call (.dot (.call (.dot (v "z") (nes "theHandlerName"))
                    [v "aLongIdentifierNameNumberZero"]) (nes "theIteratorOfTheList")) []),
                es (.call (.dot (.call (.dot (v "TheFactory") (nes "theHandlerName"))
                    [v "aLongIdentifierNameNumberZero"]) (nes "theIteratorOfTheList")) [])]⟩ }
  , { name := "layout-chain-two"
      prog := ⟨[es (.call (.dot (.call (.dot (v "theCollection") (nes "filter"))
                    [v "handler"]) (nes "map")) [v "item"])]⟩ }
  , { name := "layout-chain-three"
      prog := ⟨[es (.call (.dot (.call (.dot (.call (.dot (v "theCollection")
                    (nes "filterTheItems")) [v "handler"]) (nes "mapTheItems"))
                    [v "theIteratorOfTheList"]) (nes "reduceTheItems"))
                  [v "aLongIdentifierNameNumberZero"])]⟩ }
  , { name := "layout-chain-call-base"
      prog := ⟨[es (.call (.dot (.call (v "theVeryLongNameForAVariableHere")
                    [v "aLongIdentifierNameNumberZero"]) (nes "theRatherLongPropertyName")) [])]⟩ }
  , { name := "layout-computed-chain"
      prog := ⟨[es (.index (.index (.index (v "theConfigurationObject")
                    (.string "aLongKeyNameHere")) (.string "anotherLongKeyName"))
                  (.string "theThirdKeyName"))]⟩ }
  , -- the arguments a call expands in place, and the ones it does not
    { name := "layout-hug-fallback"
      prog := ⟨[es (.call (v "computeTheValue")
                  [v "aVeryVeryLongIdentifierNameHere", v "theIteratorOfTheList",
                   .arrow false [par "item"] (.block [.expr (call "f" [v "item"])])])]⟩ }
  , { name := "layout-hug-object"
      prog := ⟨[es (.call (v "computeTheValue")
                  [.object [kv "aLongIdentifierNameNumberZero" (num 1),
                            kv "aLongIdentifierNameNumberOne" (num 2),
                            kv "aLongIdentifierNameNumberTwo" (num 3)]])]⟩ }
  , { name := "layout-hug-first"
      prog := ⟨[es (.call (v "setTheTimeout")
                  [.arrow false [] (.block [.expr (call "computeTheValue" [v "item"])]), num 1000])]⟩ }
  , { name := "layout-arrow-chain-arg"
      prog := ⟨[es (.call (.dot (v "thePromise") (nes "then"))
                  [.arrow false [par "aLongIdentifierNameNumberZero"]
                    (.expr (.arrow false [par "aLongIdentifierNameNumberOne"]
                      (.expr (call "computeTheValue" [v "item"]))))])]⟩ }
  , { name := "layout-arrow-chain-body"
      prog := ⟨[es (.call (.dot (v "theCollection") (nes "forEach"))
                  [.arrow false [par "item"] (.expr chainOfTwoCalls)])]⟩ }
  , { name := "layout-long-string-arg"
      prog := ⟨[es (call "computeTheValue"
                  [.string "a string which is quite long and does not fit on one line at all"])]⟩ }
  , -- the heads of the statements which hold an expression
    { name := "layout-destructure-long"
      prog := ⟨[st (.decl .const ⟨⟨.object
                  [⟨.ident (nes "aLongIdentifierNameNumberZero"),
                    .ident (nes "aLongIdentifierNameNumberZero")⟩,
                   ⟨.ident (nes "aLongIdentifierNameNumberOne"),
                    .ident (nes "aLongIdentifierNameNumberOne")⟩] none,
                  some (v "theConfigurationObject")⟩, []⟩)]⟩ }
  , { name := "layout-for-long"
      prog := ⟨[st (.for_ (.decl .let_ ⟨⟨p "theIteratorOfTheList", some (num 0)⟩, []⟩)
                  (some (.binary (v "theIteratorOfTheList") .lt
                    (.dot (v "theConfigurationObject") (nes "theRatherLongPropertyName"))))
                  (some (.postfix (v "theIteratorOfTheList") .incr)) (.block []))]⟩ }
  , { name := "layout-while-long"
      prog := ⟨[st (.while_ (.binary (.call (v "computeTheValue")
                    [v "aVeryVeryLongIdentifierNameHere"]) .and
                    (v "theIteratorOfTheList")) (.block []))]⟩ }
  , { name := "layout-for-of-long"
      prog := ⟨[st (.forOf false (.decl .const (.ident (nes "theIteratorOfTheList")))
                  chainOfTwoCalls (.block []))]⟩ }
  , { name := "layout-if-mixed"
      prog := ⟨[st (.if_ (.binary (.binary (v "aVeryVeryLongIdentifierNameHere") .plus
                      (v "theIteratorOfTheList")) .lt
                    (.binary (v "theHandlerName") .times (v "currentValue")))
                  (.block []) none)]⟩ }
  , { name := "layout-switch-fallthrough"
      prog := ⟨[st (.switch (v "value")
                  [.case (num 1) [], .case (num 2) [.expr (call "f" []), .break_ none],
                   .default [.block [.expr (call "g" [])]]])]⟩ }
  , -- the values of a property, of a field and of a declarator
    { name := "layout-prop-chain"
      prog := ⟨[st (constDecl "value" (.object
                  [kv "aLongIdentifierNameNumberZero" chainOfTwoCalls]))]⟩ }
  , { name := "layout-long-property"
      prog := ⟨[st (constDecl "value" (.object
                  [kv "aLongIdentifierNameNumberZero" (v "theVeryLongNameForAVariableHere")]))]⟩ }
  , { name := "layout-ternary-property"
      prog := ⟨[st (constDecl "value" (.object
                  [kv "theKeyName" (.ternary (v "aVeryVeryLongIdentifierNameHere")
                      (v "theIteratorOfTheList") (v "theHandlerName"))]))]⟩ }
  , { name := "layout-field-values"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.field [] false false (.ident (nes "theFieldName")) (some chainOfTwoCalls),
                   .field [] true false (.ident (nes "theOtherFieldName"))
                     (some (.arrow false [par "item"] (.expr (call "computeTheValue" [v "item"]))))])]⟩ }
  , { name := "layout-assign-computed"
      prog := ⟨[es (.assign (.index (v "theConfigurationObject")
                    (.binary (.string "prefix-") .plus (v "theIteratorOfTheList")))
                  .assign (v "aVeryVeryLongIdentifierNameHere"))]⟩ }
  , { name := "layout-assign-ternary"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZero"
                  (.ternary (v "theVeryLongNameForAVariableHere")
                    (v "aVeryVeryLongIdentifierNameHere") (v "theIteratorOfTheList")))]⟩ }
  , { name := "layout-logical-object"
      prog := ⟨[st (constDecl "value" (.binary (v "aVeryVeryLongIdentifierNameHere") .or
                  (.object [kv "theKeyName" (num 1)]))),
                st (constDecl "other" (.binary (v "aVeryVeryLongIdentifierNameHere") .coalesce
                  (.array [.elem (num 1), .elem (num 2)])))]⟩ }
  , -- the chains prettier would gain little by breaking, which it writes
    -- on the line after the operator instead
    { name := "poorly-breakable-chain-call"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZero"
                  (.call optionalChainBase [.string "a string"]))]⟩ }
  , { name := "poorly-breakable-chain-property"
      prog := ⟨[es (.object [kv "handlerName"
                  (.call (.chain (v "theVeryLongNameForAVariableHere")
                    ⟨.dot true (nes "theIteratorOfTheList"), []⟩) [.string "a string"])])]⟩ }
  , { name := "poorly-breakable-chain-base"
      prog := ⟨[st (.decl .let_ ⟨⟨p "value15931",
                  some (.chain (.call optionalChainBase [])
                    ⟨.dot true (nes "g"), [.dot false (nes "theRatherLongPropertyName")]⟩)⟩,
                  []⟩)]⟩ }
  , { name := "poorly-breakable-call-of-call"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZeroHere"
                  (.call (.call (v "theVeryLongNameForAVariableHere") []) [])),
                st (constDecl "aLongIdentifierNameNumberOneHere"
                  (.call (.call (v "theVeryLongNameForAVariable") [v "item"]) [v "index"]))]⟩ }
  , { name := "poorly-breakable-call-of-call-dot"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZeroHe"
                  (.dot (.call (.call (v "theVeryLongNameForAVariable") []) [])
                    (nes "value")))]⟩ }
  , { name := "poorly-breakable-optional-calls"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZeroHer"
                  (.chain (v "theVeryLongNameForAVariable")
                    ⟨.call true [], [.call false []]⟩)),
                st (constDecl "aLongIdentifierNameNumberZeroHere"
                  (.chain (v "theVeryLongNameFor")
                    ⟨.dot true (nes "handler"), [.call false [], .call false []]⟩)),
                st (constDecl "aLongIdentifierNameNumberZeroH"
                  (.chain (v "theVeryLongNameFor")
                    ⟨.dot true (nes "handler"), [.call false [], .dot false (nes "value")]⟩))]⟩ }
  , { name := "poorly-breakable-new"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZeroHere"
                  (.new (.dot (v "theConfiguration") (nes "TheBuilder")) []))]⟩ }
  , -- the remaining corners of the earlier probes
    { name := "layout-template-chain-subst"
      prog := ⟨[st (constDecl "value" (.template none "before " [⟨chainOfTwoCalls, " after"⟩]))]⟩ }
  , { name := "layout-unary-chain"
      prog := ⟨[es (.unary .typeof chainOfTwoCalls),
                es (.unary .not chainOfTwoCalls)]⟩ }
  , { name := "layout-regex-long"
      prog := ⟨[st (constDecl "value"
                  (.regex ⟨nes "^[a-z]+([0-9]{2,4})?(the rest of a long pattern)*$",
                    { global := true, ignoreCase := true, multiline := true }⟩))]⟩ }
  , { name := "layout-import-attrs"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk!
                  (some (nes "theDefaultExportName")) none none
                  (nes "a/rather/long/module/path/with/segments.json")
                  [⟨"type", "json"⟩])),
                .exportDecl (.all (some (nes "theNamespaceName"))
                  (nes "another/long/module/path.js") [⟨"type", "json"⟩])]⟩ }
  , { name := "layout-new-chain"
      prog := ⟨[es (.new (.dot (.dot (v "theConfigurationObject")
                    (nes "theRatherLongPropertyName")) (nes "TheBuilderName"))
                  [v "theIteratorOfTheList"])]⟩ }
  , { name := "layout-class-params"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.method [] false .normal (.ident (nes "theMethodName"))
                    [par "aLongIdentifierNameNumberZero", par "aLongIdentifierNameNumberOne",
                     par "theIteratorOfTheList"] []])]⟩ }
  , { name := "layout-object-method"
      prog := ⟨[st (constDecl "value" (.object
                  [.method .normal (.ident (nes "theMethodNameHere"))
                    [par "aLongIdentifierNameNumberZero", par "aLongIdentifierNameNumberOne"]
                    [.return_ (some (num 1))]]))]⟩ }
  , { name := "layout-decorated-members"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.method [.call (v "logged") [.string "name"]] false .normal
                    (.ident (nes "theMethodName")) [par "item"] [],
                   .method [v "cached"] true .get (.ident (nes "theGetterName")) [] []])]⟩ }
  , { name := "layout-arrow-destructure"
      prog := ⟨[es (.arrow false [.plain (.object [⟨.ident (nes "aLongIdentifierNameNumberZero"),
                      .ident (nes "aLongIdentifierNameNumberZero")⟩,
                    ⟨.ident (nes "aLongIdentifierNameNumberOne"),
                      .ident (nes "aLongIdentifierNameNumberOne")⟩] none)]
                  (.expr (num 1)))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
