import Tests.Ts.Prelude

/-!
# TypeScript samples for the places the layout turned out to differ

The samples here pin down the rules found by comparing the printer with
prettier on random programs: where an instantiation expression keeps
parentheses and where it does not, what a chain of `!` and calls is read
as, how the `?` of an optional element of a tuple is written, and where a
string literal statement is a directive.  They also cover the corners of
the TypeScript grammar the first two corpus files leave out.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- `f<T>`, an instantiation expression. -/
def instFT : MiniExpr := .instantiation (v "f") [ty "T"]

/-- A string literal statement. -/
def strStmt : MiniStatement := .expr (.string "a string")

/-- A `let a = 1;` statement. -/
def letA1 : MiniStatement := .decl .let_ ⟨⟨p "a", false, none, some (num 1)⟩, []⟩

/-- A class expression with one method, long enough not to fit. -/
def classExprSample : MiniExpr :=
  .classExpr [] (some (nes "AVeryVeryLongTypeNameWrittenHereIsHere")) [] none []
    [.method [] {} .normal (.ident (nes "m")) false [] [] (some (ty "number"))
      (some [.return_ (some (num 1))])]

/-- `const value77000000000000000: T = class … {…};`, with the annotation
given. -/
def annotatedClassDecl (type : MiniTsType) : MiniStatement :=
  .decl .const ⟨declT "value77000000000000000" (some type) (some classExprSample), []⟩

/-- `<TValue = unknown, TKey extends bigint = Result, TOther extends
ReadonlyArray>(value: any): -1000 => []`, an arrow whose type parameters
do not fit on one line. -/
def typedArrowSample : MiniExpr :=
  .arrow false
    [⟨false, none, nes "TValue", none, some (ty "unknown")⟩,
     ⟨false, none, nes "TKey", some (ty "bigint"), some (ty "Result")⟩,
     ⟨false, none, nes "TOther", some (ty "ReadonlyArray"), none⟩]
    [parT "value" (ty "any")] (some (.negNumLit (JSNumber.ofNat 1000)))
    (.expr (.array []))

/-- The samples. -/
def samples3 : List Sample :=
  [ -- ## An instantiation expression, `f<T>`, in each position
    -- Prettier keeps the parentheses around one read through a `.`, a
    -- `[]` or a `?.`, and writes none anywhere else.
    { name := "instantiation-member-object"
      prog := ⟨[es (.dot instFT (nes "x"))]⟩ }
  , { name := "instantiation-index-object"
      prog := ⟨[es (.index instFT (num 0))]⟩ }
  , { name := "instantiation-optional-chain-base"
      prog := ⟨[es (.chain instFT ⟨.dot true (nes "x"), []⟩)]⟩ }
  , { name := "instantiation-member-chain"
      prog := ⟨[es (.dot (.dot instFT (nes "x")) (nes "y"))]⟩ }
  , { name := "instantiation-method-call"
      prog := ⟨[es (.call (.dot instFT (nes "x")) [] [])]⟩ }
  , { name := "instantiation-callee"
      prog := ⟨[es (.call instFT [] [v "a"])]⟩ }
  , { name := "instantiation-new-callee"
      prog := ⟨[es (.new instFT [] [v "a"])]⟩ }
  , { name := "instantiation-template-tag"
      prog := ⟨[es (.template (some instFT) [] "x" [])]⟩ }
  , { name := "instantiation-as-operand"
      prog := ⟨[es (.asExpr instFT (ty "U"))]⟩ }
  , { name := "instantiation-argument"
      prog := ⟨[es (.call (v "g") [] [instFT])]⟩ }
  , { name := "instantiation-initialiser"
      prog := ⟨[st (constDecl "y" none instFT)]⟩ }
  , { name := "instantiation-type-args-break"
      prog := ⟨[es (.dot (.instantiation (v (longName 0))
        [ty (longType 0), ty (longType 1), ty (longType 2)]) (nes "x"))]⟩ }

    -- ## `!` and calls read as one member chain
    -- A chain of links none of which is written `?.` is an ordinary
    -- member expression, and keeps no parentheses of its own.
  , { name := "nonnull-call-member-object"
      prog := ⟨[es (.dot (.chain (.dot (v "a") (nes "b"))
        ⟨.nonNull, [.call false [] []]⟩) (nes "g"))]⟩ }
  , { name := "nonnull-call-index-object"
      prog := ⟨[es (.index (.chain (.dot (v "a") (nes "b"))
        ⟨.nonNull, [.call false [] []]⟩) (num 0))]⟩ }
  , { name := "nonnull-call-callee"
      prog := ⟨[es (.call (.chain (.dot (v "a") (nes "b"))
        ⟨.nonNull, [.call false [] []]⟩) [] [v "x"])]⟩ }
  , { name := "nonnull-call-optional-link"
      prog := ⟨[es (.dot (.chain (.dot (v "a") (nes "b"))
        ⟨.nonNull, [.call true [] []]⟩) (nes "g"))]⟩ }
  , { name := "nonnull-callee-call"
      prog := ⟨[es (.dot (.call (.nonNull (.dot (v "a") (nes "b"))) [] []) (nes "g"))]⟩ }
  , { name := "nonnull-of-call"
      prog := ⟨[es (.dot (.nonNull (.call (.dot (v "a") (nes "b")) [] [])) (nes "g"))]⟩ }

    -- ## The `?` of an optional element of a tuple
    -- Prettier writes it after the type as it stands, with no
    -- parentheses of its own.
  , { name := "tuple-optional-typeof"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.tuple [.named (nes "a") true false (ty "One"),
          .optional (.typeQuery (.ident (nes "b")) []),
          .optional (ty "boolean")]))]⟩ }
  , { name := "tuple-optional-operators"
      prog := ⟨[st (.typeAlias (nes "B") []
        (.tuple [.optional (.keyof (ty "A")), .optional (.fn [] [] (ty "void")),
          .optional (.conditional (ty "A") (ty "B") (ty "C") (ty "D")),
          .optional (.union [ty "A", ty "B"]), .optional (.array (ty "C")),
          .optional (.readonlyOp (.array (ty "D")))]))]⟩ }
  , { name := "tuple-optional-union-breaks"
      prog := ⟨[st (.typeAlias (nes "C") []
        (.tuple [.optional (.union [ty (longType 0), ty (longType 1), ty (longType 2),
            ty (longType 3), ty (longType 4)]),
          .elem (ty "b")]))]⟩ }
  , { name := "tuple-optional-union-breaks-alone"
      prog := ⟨[st (.typeAlias (nes "D") []
        (.tuple [.optional (.union [ty (longType 0), ty (longType 1), ty (longType 2),
          ty (longType 3), ty (longType 4)])]))]⟩ }
  , { name := "tuple-optional-conditional-breaks"
      prog := ⟨[st (.typeAlias (nes "E") []
        (.tuple [.optional (.conditional (ty (longType 0)) (ty (longType 1))
            (ty (longType 2)) (ty (longType 3))),
          .elem (ty "b")]))]⟩ }
  , { name := "tuple-rest-and-named"
      prog := ⟨[st (.typeAlias (nes "F") []
        (.tuple [.named (nes "a") false false (ty "A"), .named (nes "b") true false (ty "B"),
          .named (nes "c") false true (.array (ty "C"))]))]⟩ }

    -- ## A string literal statement
    -- It is a directive where a program or a function body starts, and
    -- is parenthesised where it stands in a block and is not one; in the
    -- body of a namespace, of a module, of a static block and of a
    -- `case` it is never read as a directive, and prettier writes it
    -- plain wherever it stands.
  , { name := "string-statement-block"
      prog := ⟨[st (.block [letA1, strStmt])]⟩ }
  , { name := "string-statement-function-body"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [] none (some [letA1, strStmt]))]⟩ }
  , { name := "string-statement-directive"
      prog := ⟨[st (.funcDecl false false (nes "g") [] [] none (some [strStmt, letA1]))]⟩ }
  , { name := "string-statement-namespace"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "N", []⟩) (some [st letA1, st strStmt]))]⟩ }
  , { name := "string-statement-namespace-first"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "M", []⟩) (some [st strStmt, st letA1]))]⟩ }
  , { name := "string-statement-module"
      prog := ⟨[st (.declare_ (.namespaceDecl true (.str "mod")
        (some [st (letDecl "b" (some (ty "number"))), st strStmt])))]⟩ }
  , { name := "string-statement-static-block"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none [] [.staticBlock [letA1, strStmt]])]⟩ }
  , { name := "string-statement-case"
      prog := ⟨[st (.switch (v "q") [.case (num 1) [letA1, strStmt]])]⟩ }

    -- ## Corners of the grammar the other samples leave out
  , { name := "class-abstract-accessor-override"
      prog := ⟨[st (.classDecl [] true (nes "C") [] (some ⟨v "Base", []⟩) []
        [.field [] { isAbstract := true } false (.ident (nes "a")) false false
           (some (ty "number")) none,
         .field [] { isStatic := true, isReadonly := true } true (.ident (nes "b")) false false
           (some (ty "string")) (some (.string "x")),
         .method [] { isAbstract := true } .get (.ident (nes "c")) false [] []
           (some (ty "number")) none,
         .method [] { isOverride := true, accessibility := some .protected_ } .set
           (.ident (nes "c")) false [] [parT "v" (ty "number")] none (some []),
         .indexSig { isReadonly := true } (nes "k") (ty "string") (ty "unknown")])]⟩ }
  , { name := "class-optional-and-definite-members"
      prog := ⟨[st (.classDecl [] false (nes "D") [] none []
        [.field [] {} false (.ident (nes "a")) true false (some (ty "number")) none,
         .field [] {} false (.ident (nes "b")) false true (some (ty "number")) none,
         .method [] {} .normal (.ident (nes "m")) true [] [] (some (ty "void")) (some [])])]⟩ }
  , { name := "interface-optional-methods-and-signatures"
      prog := ⟨[st (.interface_ (nes "I") [tp "T"] []
        [.method .normal (.ident (nes "m")) true [tp "U"] [parT "a" (ty "U")] (some (ty "void")),
         .method .get (.ident (nes "p")) false [] [] (some (ty "number")),
         .method .set (.ident (nes "p")) false [] [parT "v" (ty "number")] none,
         .callSig [tp "U"] [parT "a" (ty "U")] (some (ty "void")),
         .ctorSig [] [parT "a" (ty "T")] (some (ty "I")),
         .indexSig true (nes "k") (ty "string") (ty "T"),
         .property true (.string "a-b") true (some (ty "number"))])]⟩ }
  , { name := "type-parameter-defaults-and-variance"
      prog := ⟨[st (.interface_ (nes "J")
        [⟨false, some .in_, nes "A", none, none⟩,
         ⟨false, some .out_, nes "B", some (ty "string"), some (ty "string")⟩,
         ⟨true, some .inOut, nes "C", none, some (ty "number")⟩] [] [])]⟩ }
  , { name := "type-mapped-modifiers"
      prog := ⟨[st (.typeAlias (nes "G") [tp "T"]
        (.mapped (some .remove) (nes "K") (.keyof (ty "T"))
          (some (.templateLit "get" [⟨ty "K", ""⟩])) (some .add) (some (.indexed (ty "T") (ty "K")))))]⟩ }
  , { name := "type-nested-operators"
      prog := ⟨[st (.typeAlias (nes "H") []
        (.array (.union [ty "A", ty "B"])))
        , st (.typeAlias (nes "H2") [] (.keyof (.union [ty "A", ty "B"])))
        , st (.typeAlias (nes "H3") [] (.array (.fn [] [] (ty "void"))))
        , st (.typeAlias (nes "H4") [] (.indexed (.typeQuery (.ident (nes "x")) []) (.strLit "a")))
        , st (.typeAlias (nes "H5") [] (.readonlyOp (.array (.intersection [ty "A", ty "B"]))))]⟩ }
  , { name := "type-predicate-forms"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [parT "a" (ty "unknown")]
          (some (.predicate false (nes "a") (some (ty "string")))) (some [])),
        st (.funcDecl false false (nes "g") [] [parT "a" (ty "unknown")]
          (some (.predicate true (nes "a") none)) (some [])),
        st (.funcDecl false false (nes "h") [] [parT "a" (ty "unknown")]
          (some (.predicate true (nes "a") (some (ty "string")))) (some []))]⟩ }
  , { name := "type-import-and-query-with-args"
      prog := ⟨[st (.typeAlias (nes "K") []
          (.importType false "mod" [] (some (.qualified (.ident (nes "A")) (nes "B"))) [ty "T"])),
        st (.typeAlias (nes "L") [] (.typeQuery (.ident (nes "f")) [ty "T"])),
        st (.typeAlias (nes "M2") [] (.importType false "mod" [] none []))]⟩ }
  , { name := "enum-const-and-initialisers"
      prog := ⟨[st (.enum_ true (nes "E")
        [⟨.ident (nes "A"), some (num 1)⟩, ⟨.ident (nes "B"), none⟩,
         ⟨.string "c d", some (.string "x")⟩])]⟩ }
  , { name := "declare-namespace-nested-and-abstract-class"
      prog := ⟨[st (.declare_ (.namespaceDecl false (.qualified ⟨nes "A", [nes "B"]⟩)
        (some [st (.classDecl [] true (nes "C") [] none []
          [.method [] { isAbstract := true } .normal (.ident (nes "m")) false [] []
            (some (ty "void")) none])])))]⟩ }
  , { name := "import-equals-and-export-forms"
      prog := ⟨[.importDecl (.equals false (nes "A") (.entity (.qualified (.ident (nes "N")) (nes "M")))),
        .importDecl (.equals true (nes "B") (.require "mod")),
        .exportDecl (.decl (.typeAlias (nes "T2") [] (ty "string"))),
        .exportDecl (.locals true [⟨false, nes "T2", some (nes "T3")⟩])]⟩ }
  , { name := "satisfies-and-as-const-chain"
      prog := ⟨[st (constDecl "x" none
        (.satisfies (.asExpr (.object [.keyValue (.ident (nes "a")) (num 1)])
            (.ref (.ident (nes "const")) []))
          (.ref (.ident (nes "Record")) [ty "string", ty "number"])))]⟩ }
  , { name := "this-type-and-parameter"
      prog := ⟨[st (.interface_ (nes "Chainable") [] []
        [.method .normal (.ident (nes "m")) false [] [] (some .this)]),
        st (.typeAlias (nes "Self") [] (.fn [] [] .this))]⟩ }
    -- ## What a template literal type holds
    -- Prettier writes what stands between the braces of a `${…}` on one
    -- line, however long it is.
  , { name := "template-type-long-intersection"
      prog := ⟨[st (.typeAlias (nes "T1") []
        (.templateLit "x" [⟨.intersection [ty "AVeryLongTypeNameNumberOne",
          ty "AVeryLongTypeNameNumberTwo", ty "AVeryLongTypeNameNumberThree",
          ty "AVeryLongTypeNameNumberFour"], "y"⟩]))]⟩ }
  , { name := "template-type-object"
      prog := ⟨[st (.typeAlias (nes "T2") []
        (.templateLit "x" [⟨.objectType [prop "aVeryLongPropertyNameHere" (ty "number"),
          prop "anotherVeryLongPropertyName" (ty "string")], "y"⟩]))]⟩ }
  , { name := "template-type-long-union"
      prog := ⟨[st (.typeAlias (nes "T3") []
        (.templateLit "x" [⟨.union [ty "AVeryLongTypeNameNumberOne",
          ty "AVeryLongTypeNameNumberTwo", ty "AVeryLongTypeNameNumberThree",
          ty "AVeryLongTypeName4"], "y"⟩]))]⟩ }

    -- ## A class expression as the initialiser of an annotated declarator
    -- Prettier keeps it on the line of the `=` unless the annotation
    -- itself is one that may break.
  , { name := "class-expression-annotation-simple"
      prog := ⟨[st (annotatedClassDecl (ty "T"))]⟩ }
  , { name := "class-expression-annotation-template"
      prog := ⟨[st (annotatedClassDecl (.templateLit "./a/rather/long/module/path/here"
        [⟨.intersection [.numLit (JSNumber.ofNat 1000), ty "Bar"], "say hi"⟩]))]⟩ }
  , { name := "class-expression-annotation-array"
      prog := ⟨[st (annotatedClassDecl (.array (ty "AlphaTypeName")))]⟩ }
  , { name := "class-expression-annotation-type-args"
      prog := ⟨[st (annotatedClassDecl (tyA "Foo" [ty "AlphaTypeName", ty "BetaTypeName"]))]⟩ }
  , { name := "class-expression-annotation-union"
      prog := ⟨[st (annotatedClassDecl (.union [ty "AlphaTypeName", ty "BetaTypeName"]))]⟩ }

    -- ## The arguments of a call which hold a typed function
  , { name := "hug-last-arrow-type-params-break"
      prog := ⟨[es (.call (.instantiation (v "result") [.keyof (ty "Bar"), .objectType []]) []
        [.nonNull (.asExpr (v "collection") (ty "T")), typedArrowSample])]⟩ }
  , { name := "hug-last-arrow-type-params-break-short-callee"
      prog := ⟨[es (.call (v "result") [] [v "a", typedArrowSample])]⟩ }
  , { name := "hug-last-arrow-one-type-param"
      prog := ⟨[es (.call (v "result") [] [v "a",
        .arrow false [tp "T"] [parT "value" (ty "any")] none (.expr (.array []))])]⟩ }
  , { name := "hug-first-arrow-satisfies-second"
      prog := ⟨[es (.call (v "theCollection") [.typeQuery (.ident (nes "bb")) []]
        [.arrow false [] [parT "value" (ty "void")] (some (ty "U"))
           (.block [.return_ (some (.array []))]),
         .satisfies (.string "") (.numLit (JSNumber.ofNat 1000))])]⟩ }
  , { name := "hug-first-arrow-as-second"
      prog := ⟨[es (.call (v "theCollection") []
        [.arrow false [] [par "value"] none (.block [.return_ (some (.array []))]),
         .asExpr (.string "") (ty "X")])]⟩ }
  , { name := "hug-first-arrow-as-complex-type-second"
      prog := ⟨[es (.call (v "theCollection") []
        [.arrow false [] [par "value"] none (.block [.return_ (some (.array []))]),
         .asExpr (.string "") (.union [ty "X", ty "Y"])])]⟩ }
  , { name := "unique-symbol-and-literal-types"
      prog := ⟨[st (.declare_ (.decl .const ⟨declT "s" (some .uniqueSymbol) none, []⟩)),
        st (.typeAlias (nes "N2") [] (.union [.numLit (JSNumber.ofNat 1),
          .negNumLit (JSNumber.ofNat 2), .strLit "three", ty "null"]))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
