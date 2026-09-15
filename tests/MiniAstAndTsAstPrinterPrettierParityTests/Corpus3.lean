import Tests.Corpus2

/-!
# Harder sample programs

Samples that exercise the layout decisions prettier makes for nested
conditionals, arrow chains, long operator chains, optional chaining,
objects with methods, generators and the module syntax.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A regular expression literal. -/
def re (s : String) : MiniExpr := .regex ⟨nes s, {}⟩

/-- A `.name` access. -/
def dot (e : MiniExpr) (n : String) : MiniExpr := .dot e (nes n)

/-- A property of an object literal. -/
def kv (k : String) (e : MiniExpr) : MiniProperty := .keyValue (.ident (nes k)) e

/-- The samples. -/
def samples3 : List Sample :=
  [ { name := "ternary-nested"
      prog := ⟨[st (constDecl "animalName"
                  (.ternary (v "isBird") (str "bird")
                    (.ternary (v "isCat") (str "cat")
                      (.ternary (v "isDog") (str "dog") (str "unknown animal")))))]⟩ }
  , { name := "ternary-long"
      prog := ⟨[st (constDecl "resultOfTheComputation"
                  (.ternary (v "conditionIsSatisfiedHere")
                    (call "computeTheFirstValue" [v "argument"])
                    (call "computeTheSecondValue" [v "argument"])))]⟩ }
  , { name := "ternary-in-call"
      prog := ⟨[es (call "render" [.ternary (v "loading") (v "spinnerComponent")
                  (v "contentComponent"), v "container"])]⟩ }
  , { name := "arrow-chain-long"
      prog := ⟨[st (constDecl "composedFunction"
                  (arrowExpr ["firstArgument"] (arrowExpr ["secondArgument"]
                    (arrowExpr ["thirdArgument"]
                      (call "combineAllOfThem"
                        [v "firstArgument", v "secondArgument", v "thirdArgument"])))))]⟩ }
  , { name := "arrow-returning-object"
      prog := ⟨[st (constDecl "makeState"
                  (arrowExpr ["initialValue"]
                    (.object [kv "value" (v "initialValue"), kv "version" (num 0)])))]⟩ }
  , { name := "arrow-block-body"
      prog := ⟨[st (constDecl "loadEverything" (.arrow false [] (.block
                  [constDecl "data" (call "loadTheData" []),
                   .return_ (some (v "data"))])))]⟩ }
  , { name := "concat-strings"
      prog := ⟨[st (constDecl "sentence" (.binary (.binary (.binary
                  (str "the first part of the text ") .plus (v "middleValue"))
                  .plus (str " and then the last part")) .plus (str " with more")))]⟩ }
  , { name := "numeric-array"
      prog := ⟨[st (constDecl "numbers" (.array
                  ((List.range 30).map (fun k => MiniArrayElement.elem (num k)))))]⟩ }
  , { name := "string-array"
      prog := ⟨[st (constDecl "words" (.array
                  [.elem (str "alpha"), .elem (str "bravo"), .elem (str "charlie"),
                   .elem (str "delta"), .elem (str "echo"), .elem (str "foxtrot"),
                   .elem (str "golf"), .elem (str "hotel"), .elem (str "india")]))]⟩ }
  , { name := "array-of-objects"
      prog := ⟨[st (constDecl "records" (.array
                  [.elem (.object [kv "id" (num 1), kv "name" (str "first")]),
                   .elem (.object [kv "id" (num 2), kv "name" (str "second")])]))]⟩ }
  , { name := "array-holes"
      prog := ⟨[st (constDecl "sparse" (.array [.elem (num 1), .hole, .elem (num 3), .hole]))]⟩ }
  , { name := "object-methods"
      prog := ⟨[st (constDecl "api" (.object
                  [.method .normal (.ident (nes "get")) [par "url"]
                     [.return_ (some (call "request" [str "GET", v "url"]))],
                   .method .get (.ident (nes "size")) [] [.return_ (some (num 0))],
                   .method .generator (.ident (nes "items")) []
                     [.expr (.yield (some (num 1)))],
                   .shorthand (nes "cache"),
                   .spread (v "defaults")]))]⟩ }
  , { name := "object-computed-key"
      prog := ⟨[st (constDecl "table" (.object
                  [.keyValue (.computed (v "keyName")) (num 1),
                   .keyValue (.computed (.binary (str "a") .plus (v "b"))) (num 2)]))]⟩ }
  , { name := "generator-function"
      prog := ⟨[st (.funcDecl false true (nes "counter") [par "limit"]
                  [.for_ (.decl .let_ ⟨⟨p "i", some (num 0)⟩, []⟩)
                    (some (.binary (v "i") .lt (v "limit"))) (some (.postfix (v "i") .incr))
                    (.block [.expr (.yield (some (v "i")))]),
                   .expr (.yieldFrom (call "otherGenerator" []))])]⟩ }
  , { name := "optional-chain-long"
      prog := ⟨[st (constDecl "cityName" (.chain (v "response")
                  ⟨.dot true (nes "userProfile"),
                   [.dot true (nes "addressDetails"), .dot false (nes "city")]⟩))]⟩ }
  , { name := "optional-chain-index"
      prog := ⟨[es (.chain (v "items") ⟨.index true (num 0), [.dot true (nes "run"),
                  .call true [v "argument"]]⟩)]⟩ }
  , { name := "regex-and-typeof"
      prog := ⟨[es (dotCall (re "^a+b$") "test" [v "input"]),
                es (.binary (.unary .typeof (v "value")) .strictEq (str "string")),
                es (.unary .void (num 0)),
                es (.unary .delete (.dot (v "obj") (nes "prop")))]⟩ }
  , { name := "in-instanceof"
      prog := ⟨[st (.if_ (.binary (str "key") .inOp (v "object")) (.block []) none),
                st (.if_ (.binary (v "value") .instanceOf (v "SomeClass")) (.block []) none)]⟩ }
  , { name := "tagged-template"
      prog := ⟨[st (constDecl "query" (.template (some (v "sql")) "select * from "
                  [⟨v "tableName", " where id = "⟩, ⟨v "identifier", ""⟩]))]⟩ }
  , { name := "new-no-args"
      prog := ⟨[st (constDecl "map" (.new (v "Map") [])),
                st (constDecl "nested" (.new (.dot (v "namespace") (nes "Thing")) [num 1]))]⟩ }
  , { name := "chain-computed"
      prog := ⟨[es (dotCall (.index (dotCall (v "registry") "lookup" [str "name"]) (num 0))
                  "activate" [])]⟩ }
  , { name := "chain-with-long-args"
      prog := ⟨[es (dotCall (dotCall (v "queryBuilder")
                  "where" [str "status", str "active"])
                  "orderBy" [str "creationTimestamp", str "descending"])]⟩ }
  , { name := "chain-three-short"
      prog := ⟨[es (dotCall (dotCall (v "a") "b" []) "c" [])]⟩ }
  , { name := "nested-arrow-call"
      prog := ⟨[es (call "useEffect" [arrowBlock []
                  [.expr (call "subscribe" [v "handler"])], .array []])]⟩ }
  , { name := "long-call-chain-args"
      prog := ⟨[es (call "registerTheHandler" [str "an event name that is long",
                  arrowBlock ["event"] [.expr (call "handleTheEvent" [v "event"])]])]⟩ }
  , { name := "switch-many"
      prog := ⟨[st (.switch (dot (v "action") "type")
                  [.case (str "increment") [.return_ (some (.binary (v "state") .plus (num 1)))],
                   .case (str "decrement") [.return_ (some (.binary (v "state") .minus (num 1)))],
                   .case (str "reset") [], .case (str "clear") [.return_ (some (num 0))],
                   .default [.return_ (some (v "state"))]])]⟩ }
  , { name := "while-long-cond"
      prog := ⟨[st (.while_ (.binary (.binary (v (longName 0)) .and (v (longName 1)))
                    .and (v (longName 2)))
                  (.block [.expr (call "step" [])]))]⟩ }
  , { name := "if-else-chain"
      prog := ⟨[st (.if_ (.binary (v "a") .lt (num 1)) (.block [.expr (call "one" [])])
                  (some (.if_ (.binary (v "a") .lt (num 2)) (.block [.expr (call "two" [])])
                    (some (.block [.expr (call "three" [])])))))]⟩ }
  , { name := "try-finally"
      prog := ⟨[st (.try_ [.expr (call "start" [])]
                  (.catches ⟨⟨p "e", none, []⟩, []⟩ (.some [.expr (call "cleanup" [])])))]⟩ }
  , { name := "export-named"
      prog := ⟨[.exportDecl (.locals [⟨nes "first", none⟩, ⟨nes "second", some (nes "alias")⟩]),
                .exportDecl (.all (some (nes "everything")) (nes "./other") []),
                .exportDecl (.fromClause [⟨nes "a", none⟩] (nes "./a") []),
                .exportDecl (.decl (constDecl "exported" (num 1)))]⟩ }
  , { name := "import-forms"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes "defaultExport")) none
                  none (nes "./default"))),
                .importDecl (.clause (MiniImportClause.mk! none (some (nes "namespaceImport"))
                  none (nes "./namespace"))),
                .importDecl (.clause (MiniImportClause.mk! (some (nes "def"))
                  none (some [⟨nes "named", none⟩]) (nes "./both"))),
                .importDecl (.clause (MiniImportClause.mk! none none (some []) (nes "./empty")))]⟩ }
  , { name := "assign-operators"
      prog := ⟨[es (.assign (v "total") .plus (v "delta")),
                es (.assign (v "flags") .bitOr (v "mask")),
                es (.assign (v "value") .coalesce (v "fallback")),
                es (.assign (.index (v "arr") (num 0)) .times (num 2))]⟩ }
  , { name := "assign-chain"
      prog := ⟨[es (.assign (v "first") .assign (.assign (v "second") .assign (v "third")))]⟩ }
  , { name := "assign-long-member-lhs"
      prog := ⟨[es (.assign (dot (dot (dot (v "someObject") "firstLevel") "secondLevel")
                    "thirdLevel")
                  .assign (call "computeSomething" [v "withAnArgument"]))]⟩ }
  , { name := "await-chain"
      prog := ⟨[st (.funcDecl true false (nes "run") []
                  [constDecl "json" (.await (dotCall (.await (call "fetch" [v "url"]))
                    "json" []))])]⟩ }
  , { name := "unary-sequence"
      prog := ⟨[es (.unary .not (.unary .not (v "value"))),
                es (.unary .minus (.unary .minus (v "value"))),
                es (.unary .minus (num 1)),
                es (.binary (.unary .minus (v "a")) .minus (.unary .minus (v "b")))]⟩ }
  , { name := "exponent-like-chain"
      prog := ⟨[es (.binary (.binary (v "a") .divide (v "b")) .times (v "c")),
                es (.binary (v "a") .times (.binary (v "b") .divide (v "c"))),
                es (.binary (.binary (v "a") .lsh (v "b")) .rsh (v "c")),
                es (.binary (.binary (v "a") .coalesce (v "b")) .coalesce (v "c"))]⟩ }
  , { name := "long-logical-in-arg"
      prog := ⟨[es (call "assertThat" [.binary (.binary (v (longName 0)) .and (v (longName 1)))
                  .and (v (longName 2))])]⟩ }
  , { name := "object-in-arrow-body"
      prog := ⟨[es (dotCall (v "items") "map" [arrowExpr ["item"]
                  (.object [kv "key" (dot (v "item") "id"), kv "label" (dot (v "item") "name")])])]⟩ }
  , { name := "class-members"
      prog := ⟨[st (.classDecl [] (nes "Service") (some (v "Base"))
                  [.field [] true false (.ident (nes "instances")) (some (.array [])),
                   .method [] false .normal (.ident (nes "constructor")) [par "options"]
                     [.expr (.superCall [v "options"]),
                      .expr (.assign (dot (.this) "options") .assign (v "options"))],
                   .method [] true .normal (.ident (nes "create")) []
                     [.return_ (some (.new (v "Service") [.object []]))],
                   .method [] false .normal (.computed (v "symbolName")) [] []])]⟩ }
  , { name := "labelled-block"
      prog := ⟨[st (.labelled (nes "block") (.block [.break_ (some (nes "block"))]))]⟩ }
  , { name := "with-statement"
      prog := ⟨[st (.with_ (v "scope") (.block [.expr (call "use" [])]))]⟩ }
  , { name := "using-declaration"
      prog := ⟨[st (.using_ false ⟨⟨p "handle", some (call "open" [str "file"])⟩, []⟩),
                st (.using_ true ⟨⟨p "resource", some (call "acquire" [])⟩, []⟩)]⟩ }
  , { name := "numbers-formatting"
      prog := ⟨[es (.array [.elem (.number (JSNumber.decimal 15 (-1))),
                   .elem (.number (JSNumber.decimal 1000 3)),
                   .elem (.number (JSNumber.radix .hexadecimal 255)),
                   .elem (.number (JSNumber.bigint .decimal 12))])]⟩ }
  , { name := "strings-quotes"
      prog := ⟨[es (.array [.elem (str "plain"), .elem (str "with \"double\" quotes"),
                   .elem (str "with 'single' quotes"), .elem (str "with \\ backslash"),
                   .elem (str "tab\tand\nnewline")])]⟩ }
  , { name := "deep-nesting"
      prog := ⟨[st (.funcDecl false false (nes "outer") []
                  [.if_ (v "condition")
                    (.block [.forOf false (.decl .const (p "item")) (v "collection")
                      (.block [.try_ [.expr (dotCall (v "item") "run" [])]
                        (.catches ⟨⟨p "error", none,
                          [.expr (dotCall (v "console") "warn" [v "error"])]⟩, []⟩ .none)])])
                    none])]⟩ }
  , { name := "spread-arguments"
      prog := ⟨[es (call "combine" [.spread (v "firstCollection"), v "middle",
                  .spread (v "secondCollection")]),
                st (constDecl "merged" (.object [.spread (v "defaults"), kv "extra" (num 1)]))]⟩ }
  , { name := "empty-things"
      prog := ⟨[st (.funcDecl false false (nes "noop") [] []),
                st (constDecl "emptyObject" (.object [])),
                st (constDecl "emptyArray" (.array [])),
                st (.classDecl [] (nes "Empty") none []),
                st (.while_ (.true_) (.block []))]⟩ }
  , { name := "long-new-expression"
      prog := ⟨[st (constDecl "theInstance" (.new (v "SomeConstructorWithAVeryLongName")
                  [v "firstArgument", v "secondArgument", v "thirdArgument"]))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
