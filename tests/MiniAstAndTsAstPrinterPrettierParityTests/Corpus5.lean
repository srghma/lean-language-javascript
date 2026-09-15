import Tests.Corpus4

/-!
# Further sample programs

Samples that cover the parts of the syntax tree the earlier corpora touch
only lightly: classes, patterns, template literals, the module syntax and
the long expressions whose layout prettier decides with its heuristics.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A property whose key is a string literal. -/
def kvs (k : String) (e : MiniExpr) : MiniProperty := .keyValue (.string k) e

/-- An object pattern property. -/
def opp (k : String) (pat : MiniPattern) : MiniObjectPatternProp := ⟨.ident (nes k), pat⟩

/-- The samples. -/
def samples5 : List Sample :=
  [ { name := "call-with-object-arg"
      prog := ⟨[es (call "configureTheApplication"
                  [.object [kv "retries" (num 3), kv "timeoutInMilliseconds" (num 1000),
                    kv "verbose" .true_]])]⟩ }
  , { name := "call-with-two-objects"
      prog := ⟨[es (call "merge" [.object [kv "a" (num 1)], .object [kv "b" (num 2)]])]⟩ }
  , { name := "call-with-array-arg"
      prog := ⟨[es (call "processEverySingleOne"
                  [.array [.elem (str "the first element"), .elem (str "the second element"),
                    .elem (str "the third element")]])]⟩ }
  , { name := "call-function-and-number"
      prog := ⟨[es (call "setTimeout" [arrowBlock [] [.expr (call "tick" [])], num 1000])]⟩ }
  , { name := "call-two-functions"
      prog := ⟨[es (call "subscribeToTheStream"
                  [arrowBlock ["value"] [.expr (call "handleTheValue" [v "value"])],
                   arrowBlock ["error"] [.expr (call "handleTheError" [v "error"])]])]⟩ }
  , { name := "nested-object-long"
      prog := ⟨[st (constDecl "configuration" (.object
                  [kv "server" (.object [kv "host" (str "localhost"), kv "port" (num 8080)]),
                   kv "client" (.object [kv "retries" (num 3)]),
                   .spread (v "defaults")]))]⟩ }
  , { name := "object-quoted-keys"
      prog := ⟨[st (constDecl "headers" (.object
                  [kvs "content-type" (str "application/json"), kvs "accept" (str "*/*"),
                   kvs "valid" (num 1), .keyValue (.number (JSNumber.ofNat 42)) (str "answer")]))]⟩ }
  , { name := "object-getters"
      prog := ⟨[st (constDecl "point" (.object
                  [.method .get (.ident (nes "x")) [] [.return_ (some (v "theStoredValue"))],
                   .method .set (.ident (nes "x")) [par "value"]
                     [.expr (.assign (.dot .this (nes "stored")) .assign (v "value"))],
                   .method .normal (.computed (call "keyFor" [str "y"])) []
                     [.return_ (some (num 0))]]))]⟩ }
  , { name := "class-static-and-private"
      prog := ⟨[st (.classDecl [] (nes "Counter") none
                  [.field [] true false (.ident (nes "instances")) (some (num 0)),
                   .field [] false false (.private_ (nes "count")) (some (num 0)),
                   .method [] false .normal (.ident (nes "increment")) []
                     [.expr (.assign (.privateDot .this (nes "count")) .plus (num 1)),
                      .return_ (some (.privateDot .this (nes "count")))],
                   .method [] true .get (.ident (nes "total")) []
                     [.return_ (some (.dot (v "Counter") (nes "instances")))]])]⟩ }
  , { name := "class-decorated"
      prog := ⟨[st (.classDecl [call "component" [str "app-root"]] (nes "AppRoot")
                  (some (.dot (v "framework") (nes "Component")))
                  [.field [v "observable"] false false (.ident (nes "state")) (some (.object [])),
                   .method [v "logged"] false .normal (.ident (nes "render")) []
                     [.return_ (some (.template none "hello" []))]])]⟩ }
  , { name := "class-long-heritage"
      prog := ⟨[st (.classDecl [] (nes "TheDerivedComponentClass")
                  (some (call "withTheMixin" [v "TheBaseComponentClass"]))
                  [.method [] false .normal (.ident (nes "constructor")) [par "props"]
                    [.expr (.superCall [v "props"])]])]⟩ }
  , { name := "generator-and-yield"
      prog := ⟨[st (.funcDecl false true (nes "numbers") []
                  [.expr (.yield (some (num 1))),
                   .expr (.yieldFrom (call "otherNumbers" [])),
                   constDecl "received" (.yield none)])]⟩ }
  , { name := "async-generator-await"
      prog := ⟨[st (.funcDecl true true (nes "streamThem") [par "source"]
                  [.forOf false (.decl .const (p "chunk")) (v "source")
                    (.block [.expr (.yield (some (.await (call "transform" [v "chunk"]))))])])]⟩ }
  , { name := "template-substitutions"
      prog := ⟨[st (constDecl "message" (.template none "Hello, "
                  [⟨v "name", "! You have "⟩, ⟨.dot (v "messages") (nes "length"), " messages."⟩])),
                st (constDecl "query" (.template (some (v "sql")) "select * from "
                  [⟨v "table", " where id = "⟩, ⟨v "id", ""⟩]))]⟩ }
  , { name := "long-member-chain-calls"
      prog := ⟨[es (dotCall (dotCall (dotCall (dotCall (v "theCollection") "filter"
                  [arrowExpr ["item"] (.dot (v "item") (nes "isActive"))]) "map"
                  [arrowExpr ["item"] (.dot (v "item") (nes "identifier"))]) "sort" [])
                  "join" [str ", "])]⟩ }
  , { name := "chain-with-index"
      prog := ⟨[st (constDecl "firstMatchingEntry" (.index (call "findAllOfTheEntries"
                  [v "theCollection", v "thePredicate"]) (num 0)))]⟩ }
  , { name := "optional-chain-deep"
      prog := ⟨[st (constDecl "cityName" (.chain (v "response")
                  ⟨.dot true (nes "data"), [.dot true (nes "address"),
                    .dot true (nes "city"), .call true []]⟩))]⟩ }
  , { name := "new-with-object"
      prog := ⟨[st (constDecl "theRequest" (.new (v "Request")
                  [str "https://example.com/api", .object [kv "method" (str "POST"),
                    kv "body" (v "payload")]]))]⟩ }
  , { name := "iife"
      prog := ⟨[es (.call (.func false false none [] [.expr (call "start" [])]) []),
                es (.call (arrowExpr [] (call "start" [])) [])]⟩ }
  , { name := "assignment-layouts"
      prog := ⟨[es (.assign (.dot (.dot (v "theObject") (nes "nested")) (nes "property")) .assign
                  (.await (call "fetchTheValue" [v "identifier"]))),
                es (.assign (v "cache") .logicalOr (.object [])),
                es (.assign (v "total") .plus (.binary (v "price") .times (v "quantity"))),
                st (constDecl "label" (.template none "value: " [⟨v "amount", ""⟩]))]⟩ }
  , { name := "long-string-assignment"
      prog := ⟨[st (constDecl "theDescriptionOfTheThing"
                  (str "a fairly long string literal that does not fit on one line here"))]⟩ }
  , { name := "destructuring-params"
      prog := ⟨[st (.funcDecl false false (nes "draw")
                  [.plain (.object [opp "x" (.withDefault (p "x") (num 0)),
                    opp "y" (.withDefault (p "y") (num 0))] none),
                   .plain (.array [.elem (p "first"), .rest (p "others")])]
                  [.return_ (some (v "x"))])]⟩ }
  , { name := "destructuring-long-object"
      prog := ⟨[st (.decl .const ⟨⟨.object
                  [opp "aLongPropertyNameHere" (p "aLongPropertyNameHere"),
                   opp "anotherLongPropertyName" (p "anotherLongPropertyName"),
                   opp "aThirdPropertyName" (p "renamedProperty")] none,
                  some (v "theSourceObject")⟩, []⟩)]⟩ }
  , { name := "for-of-destructuring"
      prog := ⟨[st (.forOf false (.decl .const (.array [.elem (p "key"), .elem (p "value")]))
                  (call "entriesOf" [v "theObject"])
                  (.block [.expr (call "record" [v "key", v "value"])]))]⟩ }
  , { name := "for-in-long-body"
      prog := ⟨[st (.forIn (.decl .const (p "propertyName")) (v "theSourceObject")
                  (.block [.if_ (call "hasOwnProperty" [v "theSourceObject", v "propertyName"])
                    (.block [.expr (call "copyTheProperty"
                      [v "theTarget", v "theSourceObject", v "propertyName"])]) none]))]⟩ }
  , { name := "while-with-break"
      prog := ⟨[st (.while_ .true_ (.block
                  [.if_ (.unary .not (call "hasMore" [])) (.block [.break_ none]) none,
                   .expr (call "step" [])]))]⟩ }
  , { name := "try-catch-no-param"
      prog := ⟨[st (.try_ [.expr (call "risky" [])]
                  (.catches ⟨⟨.target (v "error"), none, [.expr (call "report" [v "error"])]⟩, []⟩
                    .none))]⟩ }
  , { name := "throw-long"
      prog := ⟨[st (.throw (.new (v "TypeError")
                  [.template none "the value " [⟨v "value", " is not of the expected kind"⟩]]))]⟩ }
  , { name := "switch-long-discriminant"
      prog := ⟨[st (.switch (.dot (.dot (v "theEvent") (nes "payload")) (nes "kind"))
                  [.case (str "created") [.expr (call "onCreated" [v "theEvent"]), .break_ none],
                   .case (str "deleted") [.expr (call "onDeleted" [v "theEvent"]), .break_ none],
                   .default [.throw (.new (v "Error") [str "unknown"])]])]⟩ }
  , { name := "labelled-continue"
      prog := ⟨[st (.labelled (nes "outer") (.for_
                  (.decl .let_ ⟨⟨p "i", some (num 0)⟩, []⟩)
                  (some (.binary (v "i") .lt (num 10))) (some (.postfix (v "i") .incr))
                  (.block [.forOf false (.decl .const (p "x")) (v "xs")
                    (.block [.continue_ (some (nes "outer"))])])))]⟩ }
  , { name := "do-while-long-condition"
      prog := ⟨[st (.doWhile (.block [.expr (call "attemptTheOperation" [])])
                  (.binary (.binary (v "attemptsSoFar") .lt (v "maximumAttempts")) .and
                    (.unary .not (v "hasSucceeded"))))]⟩ }
  , { name := "logical-coalesce-mix"
      prog := ⟨[st (constDecl "value" (.binary (.binary (v "first") .coalesce (v "second"))
                  .coalesce (v "third"))),
                st (constDecl "other" (.binary (.binary (v "a") .and (v "b")) .or
                  (.binary (v "c") .and (v "d"))))]⟩ }
  , { name := "in-and-instanceof-condition"
      prog := ⟨[st (.if_ (.binary (.binary (str "key") .inOp (v "theObject")) .and
                  (.binary (v "theObject") .instanceOf (v "TheExpectedClass")))
                  (.block [.return_ (some .true_)]) none)]⟩ }
  , { name := "unary-combinations"
      prog := ⟨[es (.unary .not (.unary .not (v "value"))),
                es (.unary .typeof (.unary .typeof (v "value"))),
                es (.unary .void (num 0)),
                es (.unary .delete (.index (v "theObject") (str "key"))),
                es (.unary .tilde (.unary .minus (num 1))),
                es (.binary (.unary .minus (v "a")) .minus (.unary .minus (v "b")))]⟩ }
  , { name := "numbers-and-bigints"
      prog := ⟨[es (.array [.elem (.number (.decimal 5 (-1))),
                  .elem (.number (.decimal 1000000 0)),
                  .elem (.number (.decimal 1 (-21))),
                  .elem (.number (.decimal 25 20)),
                  .elem (.number (.radix .hexadecimal 3735928559)),
                  .elem (.number (.bigint .hexadecimal 255)),
                  .elem (.number (.radix .binary 5))])]⟩ }
  , { name := "strings-escapes"
      prog := ⟨[es (.array [.elem (str "back\\slash"), .elem (str "quote\" and 'single'"),
                  .elem (str "carriage\rreturn"), .elem (str "null\u0000byte"),
                  .elem (str "unicode \u00e9\u4e2d")])]⟩ }
  , { name := "regex-flags"
      prog := ⟨[es (.regex ⟨nes "^[a-z]+$", { global := true, multiline := true }⟩),
                es (dotCall (v "text") "replace"
                  [.regex ⟨nes "\\s+", { global := true }⟩, str " "])]⟩ }
  , { name := "spread-everywhere"
      prog := ⟨[st (constDecl "combined" (.array [.elem (.spread (v "first")),
                  .elem (.spread (v "second")), .elem (num 0)])),
                st (constDecl "merged" (.object [.spread (v "defaults"), kv "extra" .true_])),
                es (call "apply" [.spread (v "theArguments")])]⟩ }
  , { name := "imports-with-attributes"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes "config")) none none
                  (nes "./config.json"))),
                .importDecl (.clause (MiniImportClause.mk! none (some (nes "everything")) none
                  (nes "./module.js"))),
                .exportDecl (.fromClause [⟨nes "first", some (nes "renamedFirst")⟩]
                  (nes "./other.js") [])]⟩ }
  , { name := "export-default-arrow"
      prog := ⟨[.exportDecl (.defaultExpr (arrowExpr ["theInput"]
                  (call "transformTheInput" [v "theInput"]))),
                .exportDecl (.decl (.funcDecl true false (nes "load") []
                  [.return_ (some (.await (call "fetchIt" [])))]))]⟩ }
  , { name := "import-call-and-meta"
      prog := ⟨[st (.funcDecl true false (nes "loadModule") []
                  [constDecl "mod" (.await (.importCall (str "./plugin.js") none)),
                   constDecl "base" (.dot .importMeta (nes "url")),
                   .return_ (some (v "mod"))])]⟩ }
  , { name := "using-declarations"
      prog := ⟨[st (.funcDecl true false (nes "withResource") []
                  [.using_ false ⟨⟨p "handle", some (call "openTheFile" [str "./data"])⟩, []⟩,
                   .using_ true ⟨⟨p "connection", some (call "connect" [])⟩, []⟩,
                   .expr (call "useThem" [v "handle", v "connection"])])]⟩ }
  , { name := "deep-nesting-blocks"
      prog := ⟨[st (.funcDecl false false (nes "outer") []
                  [.if_ (v "condition")
                    (.block [.forOf false (.decl .const (p "item")) (v "items")
                      (.block [.try_ [.expr (call "handle" [v "item"])]
                        (.catches ⟨⟨p "error", none,
                          [.expr (call "log" [v "error"])]⟩, []⟩ .none)])]) none])]⟩ }
  , { name := "long-ternary-chain-in-return"
      prog := ⟨[st (.funcDecl false false (nes "classify") [par "value"]
                  [.return_ (some (.ternary (.binary (v "value") .lt (num 0)) (str "negative")
                    (.ternary (.binary (v "value") .strictEq (num 0)) (str "zero")
                      (str "positive"))))])]⟩ }
  , { name := "sequence-in-arrow-and-for"
      prog := ⟨[st (constDecl "step" (arrowExpr ["state"]
                  (.seq (call "record" [v "state"]) (call "advance" [v "state"])))),
                st (.for_ (.expr (.seq (.assign (v "i") .assign (num 0))
                    (.assign (v "j") .assign (.dot (v "xs") (nes "length")))))
                  (some (.binary (v "i") .lt (v "j"))) (some (.postfix (v "i") .incr))
                  (.block []))]⟩ }
  , { name := "with-and-empty"
      prog := ⟨[st (.with_ (v "theScope") (.block [.expr (call "evaluate" [])])),
                st .empty,
                st (.block [])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
