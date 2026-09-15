import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs

The programs in this file exercise the printer over the TypeScript part
of the `MiniTsAST` syntax tree.  They are used by the prettier
conformance tests.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- The samples: type annotations, type expressions, and the TypeScript
declarations. -/
def samples : List Sample :=
  [ -- ## Annotations on declarations
    { name := "let-annotated"
      prog := ⟨[st (letDecl "a" (some (ty "number")))]⟩ },
    { name := "const-annotated"
      prog := ⟨[st (constDecl "x" (some (ty "string")) (.string "a"))]⟩ },
    { name := "let-definite"
      prog := ⟨[st (.decl .let_ ⟨⟨p "x", true, some (ty "number"), none⟩, []⟩)]⟩ },
    { name := "let-generic-annotation"
      prog := ⟨[st (letDecl "xs" (some (tyA "Array" [ty "number"])))]⟩ },
    { name := "const-array-type"
      prog := ⟨[st (letDecl "xs" (some (.array (ty "string"))))]⟩ },
    { name := "let-annotation-breaks"
      prog := ⟨[st (letDecl (longName 0)
        (some (tyA "Record" [ty (longType 0), ty (longType 1)])))]⟩ },
    { name := "two-declarators-annotated"
      prog := ⟨[st (.decl .let_
        ⟨declT "a" (some (ty "number")) (some (num 1)),
          [declT "b" (some (ty "string")) (some (.string "b"))]⟩)]⟩ },

    -- ## Functions
    { name := "function-annotated"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [parT "a" (ty "string"), parOpt "b" (ty "number")] (some (ty "void")) (some []))]⟩ },
    { name := "function-type-params"
      prog := ⟨[st (.funcDecl false false (nes "f") [tpC "T" (ty "object")]
        [parT "a" (ty "T")] (some (ty "T")) (some [.return_ (some (v "a"))]))]⟩ },
    { name := "function-overloads"
      prog := ⟨[st (.funcDecl false false (nes "g") [] [parT "a" (ty "string")]
          (some (ty "void")) none),
        st (.funcDecl false false (nes "g") [] [parT "a" (ty "number")]
          (some (ty "void")) none),
        st (.funcDecl false false (nes "g") [] [parT "a" (ty "any")]
          (some (ty "void")) (some []))]⟩ },
    { name := "function-rest-param"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [parT "a" (ty "string"), parRest "rest" (some (.array (ty "number")))]
        (some (ty "void")) (some []))]⟩ },
    { name := "function-type-params-break"
      prog := ⟨[st (.funcDecl false false (nes "fff")
        [tpC (longType 0) (ty "object"),
          ⟨false, none, nes (longType 1), none, some (ty "string")⟩,
          ⟨false, none, nes (longType 2), none, some (ty "number")⟩]
        [parT "a" (ty (longType 0))] none (some []))]⟩ },
    { name := "function-params-break-with-return-type"
      prog := ⟨[st (.funcDecl false false (nes "retty") []
        [parT (longName 0) (ty "string"), parT (longName 1) (ty "number")]
        (some (.union [ty (longType 0), ty (longType 1)])) (some []))]⟩ },
    { name := "async-function-annotated"
      prog := ⟨[st (.funcDecl true false (nes "f") [] [parT "a" (ty "string")]
        (some (tyA "Promise" [ty "void"])) (some []))]⟩ },
    { name := "function-predicate"
      prog := ⟨[st (.funcDecl false false (nes "isString") [] [parT "v" (ty "unknown")]
        (some (.predicate false (nes "v") (some (ty "string")))) (some []))]⟩ },
    { name := "function-asserts"
      prog := ⟨[st (.funcDecl false false (nes "assertIsString") []
        [parT "v" (ty "unknown")]
        (some (.predicate true (nes "v") (some (ty "string")))) (some []))]⟩ },

    -- ## Arrows
    { name := "arrow-annotated"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [] [parT "a" (ty "number")] (some (ty "number")) (.expr (v "a"))))]⟩ },
    { name := "arrow-one-type-param"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [tp "T"] [parT "a" (ty "T")] none (.expr (v "a"))))]⟩ },
    { name := "arrow-constrained-type-param"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [tpC "T" (ty "object")] [parT "a" (ty "T")] none (.expr (v "a"))))]⟩ },
    { name := "arrow-two-type-params"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [tp "T", tp "U"] [parT "a" (ty "T"), parT "b" (ty "U")] none
          (.expr (v "a"))))]⟩ },

    -- ## Calls and expressions
    { name := "call-type-args"
      prog := ⟨[es (.call (v "f") [ty "string"] [v "a"])]⟩ },
    { name := "new-type-args"
      prog := ⟨[es (.new (v "Map") [ty "string", ty "number"] [])]⟩ },
    { name := "instantiation-expression"
      prog := ⟨[st (constDecl "t" none (.instantiation (v "f") [ty "string"]))]⟩ },
    { name := "as-expression"
      prog := ⟨[st (constDecl "x" none (.asExpr (v "value") (ty "string")))]⟩ },
    { name := "as-const"
      prog := ⟨[st (constDecl "x" none (.asExpr (.array [.elem (num 1)]) (ty "const")))]⟩ },
    { name := "as-chain"
      prog := ⟨[st (constDecl "x" none
        (.asExpr (.asExpr (v "value") (ty "unknown")) (ty "string")))]⟩ },
    { name := "satisfies-expression"
      prog := ⟨[st (constDecl "x" none (.satisfies (v "value") (ty "string")))]⟩ },
    { name := "non-null"
      prog := ⟨[st (constDecl "x" none (.dot (.nonNull (v "obj")) (nes "a")))]⟩ },
    { name := "non-null-call"
      prog := ⟨[es (.call (.nonNull (.dot (v "obj") (nes "f"))) [] [])]⟩ },
    { name := "as-of-binary"
      prog := ⟨[st (constDecl "x" none
        (.asExpr (.binary (v "a") .plus (v "b")) (ty "number")))]⟩ },
    { name := "as-in-call"
      prog := ⟨[es (call "f" [.asExpr (v "a") (ty "string")])]⟩ },
    { name := "non-null-chain"
      prog := ⟨[st (constDecl "x" none
        (.chain (v "obj") ⟨.dot true (nes "a"), [.nonNull, .dot false (nes "b")]⟩))]⟩ },

    -- ## Type aliases and the type grammar
    { name := "type-alias"
      prog := ⟨[st (.typeAlias (nes "A") [] (ty "string"))]⟩ },
    { name := "type-alias-generic"
      prog := ⟨[st (.typeAlias (nes "A") [tp "T"] (.array (ty "T")))]⟩ },
    { name := "type-union"
      prog := ⟨[st (.typeAlias (nes "U") [] (.union [ty "string", ty "number"]))]⟩ },
    { name := "type-union-breaks"
      prog := ⟨[st (.typeAlias (nes "U") []
        (.union [ty (longType 0), ty (longType 1), ty (longType 2), ty (longType 3)]))]⟩ },
    { name := "type-intersection"
      prog := ⟨[st (.typeAlias (nes "I") [] (.intersection [ty "A", ty "B"]))]⟩ },
    { name := "type-object"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType [prop "a" (ty "string"), prop "b" (ty "number")]))]⟩ },
    { name := "type-object-breaks"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType [prop (longName 0) (ty "string"), prop (longName 1) (ty "number"),
          prop (longName 2) (ty "boolean")]))]⟩ },
    { name := "type-object-optional-readonly"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType [.property true (.ident (nes "a")) false (some (ty "string")),
          .property false (.ident (nes "b")) true (some (ty "number"))]))]⟩ },
    { name := "type-object-methods"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType
          [.method .normal (.ident (nes "m")) false [] [parT "x" (ty "number")]
             (some (ty "void")),
           .callSig [] [] (some (ty "void")),
           .ctorSig [] [] (some (ty "O")),
           .indexSig false (nes "k") (ty "string") (ty "any")]))]⟩ },
    { name := "type-function"
      prog := ⟨[st (.typeAlias (nes "F") []
        (.fn [] [parT "a" (ty "string")] (ty "void")))]⟩ },
    { name := "type-function-breaks"
      prog := ⟨[st (.typeAlias (nes "F") []
        (.fn [] [parT (longName 0) (ty (longType 0)), parT (longName 1) (ty (longType 1))]
          (ty (longType 2))))]⟩ },
    { name := "type-constructor"
      prog := ⟨[st (.typeAlias (nes "C") [] (.ctor false [] [parT "a" (ty "string")] (ty "C")))]⟩ },
    { name := "type-abstract-constructor"
      prog := ⟨[st (.typeAlias (nes "C") [] (.ctor true [] [] (ty "C")))]⟩ },
    { name := "type-function-in-union"
      prog := ⟨[st (.typeAlias (nes "U") []
        (.union [.fn [] [] (ty "void"), ty "null"]))]⟩ },
    { name := "type-conditional"
      prog := ⟨[st (.typeAlias (nes "C") [tp "T"]
        (.conditional (ty "T") (ty "object") (ty "A") (ty "B")))]⟩ },
    { name := "type-conditional-breaks"
      prog := ⟨[st (.typeAlias (nes "C") [tp "T"]
        (.conditional (ty "T") (ty (longType 0)) (ty (longType 1)) (ty (longType 2))))]⟩ },
    { name := "type-infer"
      prog := ⟨[st (.typeAlias (nes "C") [tp "T"]
        (.conditional (ty "T") (.infer_ (nes "U") none) (ty "U") (ty "never")))]⟩ },
    { name := "type-infer-constrained"
      prog := ⟨[st (.typeAlias (nes "C") [tp "T"]
        (.conditional (ty "T") (.infer_ (nes "U") (some (ty "object"))) (ty "U") (ty "never")))]⟩ },
    { name := "type-keyof-typeof"
      prog := ⟨[st (.typeAlias (nes "K") [] (.keyof (.typeQuery (.ident (nes "x")) [])))]⟩ },
    { name := "type-indexed"
      prog := ⟨[st (.typeAlias (nes "K") [] (.indexed (ty "A") (.strLit "b")))]⟩ },
    { name := "type-tuple"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.tuple [.elem (ty "string"), .optional (ty "number"),
          .rest (.array (ty "boolean"))]))]⟩ },
    { name := "type-tuple-named"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.tuple [.named (nes "a") false false (ty "string"),
          .named (nes "b") true false (ty "number"),
          .named (nes "rest") false true (.array (ty "boolean"))]))]⟩ },
    { name := "type-readonly-array"
      prog := ⟨[st (.typeAlias (nes "T") [] (.readonlyOp (.array (ty "string"))))]⟩ },
    { name := "type-literals"
      prog := ⟨[st (.typeAlias (nes "L") []
        (.union [.strLit "a", .numLit (JSNumber.ofNat 1), .negNumLit (JSNumber.ofNat 1),
          ty "true", ty "null", ty "undefined"]))]⟩ },
    { name := "type-template-literal"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.templateLit "get" [⟨ty "string", "Suffix"⟩]))]⟩ },
    { name := "type-import"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.importType false "mod" [] (some (.ident (nes "A"))) [ty "string"]))]⟩ },
    { name := "type-unique-symbol"
      prog := ⟨[st (.decl .const ⟨⟨p "s", false, some .uniqueSymbol, none⟩, []⟩)]⟩ },
    { name := "type-this"
      prog := ⟨[st (.typeAlias (nes "T") [] (.fn [] [] .this))]⟩ },
    { name := "type-mapped"
      prog := ⟨[st (.typeAlias (nes "M") [tp "T"]
        (.mapped (some .keep) (nes "K") (.keyof (ty "T")) none (some .keep)
          (some (.indexed (ty "T") (ty "K")))))]⟩ },
    { name := "type-mapped-remove"
      prog := ⟨[st (.typeAlias (nes "M") [tp "T"]
        (.mapped (some .remove) (nes "K") (.keyof (ty "T")) none (some .remove)
          (some (.indexed (ty "T") (ty "K")))))]⟩ },
    { name := "type-mapped-as"
      prog := ⟨[st (.typeAlias (nes "M") [tp "T"]
        (.mapped none (nes "K") (.keyof (ty "T"))
          (some (.templateLit "get" [⟨ty "K", ""⟩])) none
          (some (.indexed (ty "T") (ty "K")))))]⟩ },
    { name := "type-nested-parens"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.array (.union [ty "string", ty "number"])))]⟩ },
    { name := "type-intersection-of-union"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.intersection [.union [ty "A", ty "B"], ty "C"]))]⟩ },

    -- ## Interfaces
    { name := "interface-empty"
      prog := ⟨[st (.interface_ (nes "I") [] [] [])]⟩ },
    { name := "interface-members"
      prog := ⟨[st (.interface_ (nes "I") [tp "T"] []
        [.property true (.ident (nes "a")) false (some (ty "string")),
         .method .normal (.ident (nes "b")) true [] [parT "x" (ty "number")]
           (some (ty "void")),
         .ctorSig [] [] (some (tyA "I" [ty "T"])),
         .callSig [] [] (some (ty "void")),
         .indexSig false (nes "k") (ty "string") (ty "any"),
         .method .get (.ident (nes "p")) false [] [] (some (ty "number")),
         .method .set (.ident (nes "p")) false [] [parT "v" (ty "number")] none])]⟩ },
    { name := "interface-extends"
      prog := ⟨[st (.interface_ (nes "I") [] [her "A", her "B" [ty "T"]]
        [prop "a" (ty "string")])]⟩ },
    { name := "interface-extends-breaks"
      prog := ⟨[st (.interface_ (nes "Iface") []
        [her (longType 0), her (longType 1), her (longType 2)] [])]⟩ },

    -- ## Classes
    { name := "class-abstract"
      prog := ⟨[st (.classDecl [] true (nes "C") [] none []
        [.method [] { isAbstract := true } .normal (.ident (nes "m")) false [] []
          (some (ty "void")) none])]⟩ },
    { name := "class-type-params-implements"
      prog := ⟨[st (.classDecl [] false (nes "C") [tp "T"]
        (some ⟨v "Base", [ty "T"]⟩) [her "I" [ty "T"]] [])]⟩ },
    { name := "class-implements-breaks"
      prog := ⟨[st (.classDecl [] false (nes "Klass") []
        none [her (longType 0), her (longType 1), her (longType 2)] [])]⟩ },
    { name := "class-member-modifiers"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { accessibility := some .private_, isReadonly := true } false
           (.ident (nes "x")) false false (some (ty "number")) (some (num 1)),
         .field [] { isStatic := true } false (.private_ (nes "p")) true false
           (some (ty "string")) none,
         .field [] { isDeclare := true } false (.ident (nes "y")) false false
           (some (ty "number")) none,
         .field [] {} false (.ident (nes "z")) false true (some (ty "number")) none,
         .method [] { accessibility := some .protected_, isOverride := true } .async
           (.ident (nes "n")) false [tp "U"] [parT "a" (ty "U")]
           (some (tyA "Promise" [ty "void"])) (some [])])]⟩ },
    { name := "class-parameter-properties"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [] { accessibility := some .public_, isReadonly := true } (p "a") false
             (some (ty "string")),
           .plain [] { accessibility := some .private_ } (.withDefault (p "b") (num 2)) false none]
          none (some [.expr (.superCall [])])])]⟩ },
    { name := "class-index-signature"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.indexSig {} (nes "k") (ty "string") (ty "number")])]⟩ },
    { name := "class-accessor-field"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] {} true (.ident (nes "c")) false false (some (ty "number"))
          (some (num 3))])]⟩ },
    { name := "class-method-overloads"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) false [] [parT "a" (ty "string")]
           (some (ty "void")) none,
         .method [] {} .normal (.ident (nes "m")) false [] [parT "a" (ty "any")]
           (some (ty "void")) (some [])])]⟩ },
    { name := "class-expression-typed"
      prog := ⟨[st (constDecl "C" none
        (.classExpr [] none [tp "T"] (some ⟨v "Base", []⟩) [her "I"] []))]⟩ },

    -- ## Enums, namespaces and ambient declarations
    { name := "enum"
      prog := ⟨[st (.enum_ false (nes "E")
        [⟨.ident (nes "A"), some (num 1)⟩, ⟨.ident (nes "B"), none⟩])]⟩ },
    { name := "enum-const-empty"
      prog := ⟨[st (.enum_ true (nes "CE") []),
        st (.enum_ true (nes "D") [⟨.ident (nes "X"), none⟩])]⟩ },
    { name := "enum-string-keys"
      prog := ⟨[st (.enum_ false (nes "E")
        [⟨.string "a-b", some (.string "x")⟩])]⟩ },
    { name := "namespace"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "N", [nes "M"]⟩)
        (some [st (.decl .const ⟨declT "w" none (some (num 1)), []⟩)]))]⟩ },
    { name := "namespace-export"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "N", []⟩)
        (some [.exportDecl (.decl (.decl .const ⟨declT "w" none (some (num 1)), []⟩))]))]⟩ },
    { name := "declare-module"
      prog := ⟨[st (.declare_ (.namespaceDecl true (.str "foo")
        (some [.exportDecl (.decl (letDecl "q" (some (ty "number"))))])))]⟩ },
    { name := "declare-global"
      prog := ⟨[st (.declare_ (.namespaceDecl false .global
        (some [st (.interface_ (nes "Window") [] [] [prop "x" (ty "number")])])))]⟩ },
    { name := "declare-const"
      prog := ⟨[st (.declare_ (.decl .const ⟨declT "dd" (some (ty "number")) none, []⟩))]⟩ },
    { name := "declare-function"
      prog := ⟨[st (.declare_ (.funcDecl false false (nes "f") [] [parT "a" (ty "string")]
        (some (ty "void")) none))]⟩ },
    { name := "empty-namespace"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "N", []⟩) (some []))]⟩ },

    -- ## Imports and exports
    { name := "import-type"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
        (some [⟨false, nes "A", none⟩]) (nes "m") [] true))]⟩ },
    { name := "import-inline-type"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
        (some [⟨true, nes "B", none⟩, ⟨false, nes "C", some (nes "D")⟩]) (nes "m")))]⟩ },
    { name := "export-type-locals"
      prog := ⟨[.exportDecl (.locals true [⟨false, nes "A", none⟩])]⟩ },
    { name := "export-type-from"
      prog := ⟨[.exportDecl (.fromClause true [⟨false, nes "A", none⟩] (nes "m") [])]⟩ },
    { name := "export-assignment"
      prog := ⟨[.exportDecl (.assign (v "C"))]⟩ },
    { name := "export-as-namespace"
      prog := ⟨[.exportDecl (.asNamespace (nes "N"))]⟩ },
    { name := "import-equals-require"
      prog := ⟨[.importDecl (.equals false (nes "fs") (.require "fs"))]⟩ },
    { name := "import-equals-entity"
      prog := ⟨[.importDecl (.equals false (nes "A") (.entity (.qualified (.ident (nes "B"))
        (nes "C"))))]⟩ },
    { name := "export-import-equals"
      prog := ⟨[.importDecl (.equals true (nes "A") (.entity (.ident (nes "B"))))]⟩ },
    { name := "export-interface"
      prog := ⟨[.exportDecl (.decl (.interface_ (nes "I") [] [] [prop "a" (ty "string")]))]⟩ },
    { name := "export-type-alias"
      prog := ⟨[.exportDecl (.decl (.typeAlias (nes "A") [] (ty "string")))]⟩ },
    { name := "export-declare-const"
      prog := ⟨[.exportDecl (.decl (.declare_
        (.decl .const ⟨declT "x" (some (ty "number")) none, []⟩)))]⟩ },

    -- ## Types in other positions
    { name := "catch-annotated"
      prog := ⟨[st (.try_ [] (.catches ⟨⟨p "e", some (ty "unknown"), none, []⟩, []⟩ .none))]⟩ },
    { name := "object-method-annotated"
      prog := ⟨[st (constDecl "o" none
        (.object [.method .normal (.ident (nes "m")) [tp "T"] [parT "a" (ty "T")]
          (some (ty "void")) []]))]⟩ },
    { name := "destructured-param-annotated"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [.plain [] {} (.object [⟨.ident (nes "a"), p "a"⟩] none) false
          (some (.objectType [prop "a" (ty "string")]))] none (some []))]⟩ },
    { name := "param-default-annotated"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [.plain [] {} (.withDefault (p "a") (num 1)) false (some (ty "number"))] none (some []))]⟩ },
    { name := "jsx-with-types"
      prog := ⟨[st (constDecl "el" (some (ty "JSX.Element"))
        (.jsx (.element (.ident (nes "div")) [] [] none)))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
