import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part five

The samples of this file cover the TypeScript syntax added last: the
type-only `export *`, the ambient module declaration with no body,
`export default` of an `abstract class` and of an `interface`,
`typeof import("mod")`, the import attributes of an `import(...)` type,
and the type arguments a JSX component may be read at.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A JSX element expression. -/
private def el (name : String) (typeArgs : List MiniTsType)
    (attrs : List MiniJSXAttribute) (children : Option (List MiniJSXChild)) : MiniExpr :=
  .jsx (.element (.ident (nes name)) typeArgs attrs children)

/-- A JSX attribute whose value is a string. -/
private def attrStr (name value : String) : MiniJSXAttribute :=
  .attr (.ident (nes name)) (some (.string value))

/-- A JSX attribute whose value is an expression. -/
private def attrExpr (name : String) (e : MiniExpr) : MiniJSXAttribute :=
  .attr (.ident (nes name)) (some (.expr e))

/-- An `import(...)` type with import attributes, long enough to break. -/
private def importAttrs : MiniTsType :=
  .importType false "a-module-name-here" [⟨"resolution-mode", "import"⟩]
    (some (.ident (nes "Foo"))) []

/-- The samples. -/
def samples5 : List Sample :=
  [ -- ## `export type *`
    { name := "export-type-star"
      prog := ⟨[.exportDecl (.all true none (nes "mod") [])]⟩ }
  , { name := "export-type-star-as"
      prog := ⟨[.exportDecl (.all true (some (nes "ns")) (nes "mod") [])]⟩ }
  , { name := "export-type-star-attrs"
      prog := ⟨[.exportDecl (.all true (some (nes "ns")) (nes "mod") [⟨"type", "json"⟩])]⟩ }
  , { name := "export-star-and-type-star"
      prog := ⟨[.exportDecl (.all false none (nes "a-module") []),
        .exportDecl (.all true none (nes "a-module") []),
        .exportDecl (.all true (some (nes (longName 0))) (nes "a-long-module-name-here") [])]⟩ }
  , { name := "export-type-star-in-namespace"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "N", []⟩)
        (some [.exportDecl (.all true none (nes "mod") [])]))]⟩ }

    -- ## An ambient module with no body
  , { name := "declare-module-no-body"
      prog := ⟨[st (.declare_ (.namespaceDecl true (.str "foo") none))]⟩ }
  , { name := "declare-module-no-body-and-body"
      prog := ⟨[st (.declare_ (.namespaceDecl true (.str "foo") none)),
        st (.declare_ (.namespaceDecl true (.str "bar") (some []))),
        st (.declare_ (.namespaceDecl true (.str "baz")
          (some [.exportDecl (.decl (letDecl "q" (some (ty "number"))))])))]⟩ }

    -- ## `export default` of a declaration that is no expression
  , { name := "export-default-abstract-class"
      prog := ⟨[.exportDecl (.defaultDecl (.classDecl [] true (nes "A") [] none [] []))]⟩ }
  , { name := "export-default-abstract-class-members"
      prog := ⟨[.exportDecl (.defaultDecl
        (.classDecl [] true (nes "AbstractThing") [tp "T"] none [her "I" [ty "T"]]
          [.method [] { isAbstract := true } .normal (.ident (nes "m")) false [] []
            (some (ty "void")) none,
           .field [] { isReadonly := true } false (.ident (nes "x")) false false
            (some (ty "number")) none]))]⟩ }
  , { name := "export-default-abstract-class-heritage-breaks"
      prog := ⟨[.exportDecl (.defaultDecl
        (.classDecl [] true (nes (longType 0)) []
          (some ⟨v (longName 0), [ty (longType 1)]⟩) [her (longType 2) [], her (longType 3) []]
          []))]⟩ }
  , { name := "export-default-class-decorated"
      prog := ⟨[.exportDecl (.defaultDecl
        (.classDecl [v "dec"] false (nes "A") [] none [] []))]⟩ }
  , { name := "export-default-interface"
      prog := ⟨[.exportDecl (.defaultDecl
        (.interface_ (nes "Thing") [] [] [prop "a" (ty "number")]))]⟩ }
  , { name := "export-default-interface-generic"
      prog := ⟨[.exportDecl (.defaultDecl
        (.interface_ (nes "Thing") [tpC "T" (ty "object")] [her "Base" [ty "T"]]
          [prop "a" (ty "T"),
           .method .normal (.ident (nes "m")) false [] [parT "x" (ty "T")] (some (ty "void"))]))]⟩ }
  , { name := "export-default-interface-empty"
      prog := ⟨[.exportDecl (.defaultDecl (.interface_ (nes "Empty") [] [] []))]⟩ }

    -- ## `typeof import("mod")`
  , { name := "typeof-import"
      prog := ⟨[st (.typeAlias (nes "A") [] (.importType true "mod" [] none []))]⟩ }
  , { name := "typeof-import-qualified"
      prog := ⟨[st (.typeAlias (nes "B") []
        (.importType true "mod" [] (some (.qualified (.ident (nes "A")) (nes "B"))) [ty "C"]))]⟩ }
  , { name := "typeof-import-array"
      prog := ⟨[st (.typeAlias (nes "C") []
          (.array (.importType true "mod" [] (some (.ident (nes "A"))) []))),
        st (.typeAlias (nes "D") [] (.array (.importType false "mod" [] none [])))]⟩ }
  , { name := "typeof-import-operators"
      prog := ⟨[st (.typeAlias (nes "E") [] (.keyof (.importType true "mod" [] none []))),
        st (.typeAlias (nes "F") []
          (.indexed (.importType true "mod" [] none []) (.strLit "x"))),
        st (.typeAlias (nes "G") []
          (.union [.importType true "a" [] none [], .importType false "b" [] none []])),
        st (.typeAlias (nes "H") []
          (.readonlyOp (.array (.importType true "mod" [] none []))))]⟩ }
  , { name := "typeof-import-conditional"
      prog := ⟨[st (.typeAlias (nes "I") []
        (.conditional (.importType true "mod" [] (some (.ident (nes "A"))) []) (ty "B")
          (ty "C") (ty "D")))]⟩ }
  , { name := "typeof-import-mapped"
      prog := ⟨[st (.typeAlias (nes "J") []
        (.mapped none (nes "K") (.keyof (.importType true "mod" [] none [])) none none
          (some (ty "K"))))]⟩ }
  , { name := "typeof-import-annotations"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [parT "x" (.importType true "mod" [] (some (.ident (nes "A"))) [])]
        (some (.importType true "m" [] none [])) (some [.return_ (some (v "x"))]))]⟩ }
  , { name := "typeof-import-breaks"
      prog := ⟨[st (.typeAlias (nes (longType 0)) []
        (.union [.importType true "a-long-module-name-number-one" [] none [],
          .importType true "a-long-module-name-number-two" [] none []]))]⟩ }

    -- ## The import attributes of an `import(...)` type
  , { name := "import-type-attrs"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.importType false "mod" [⟨"type", "json"⟩] (some (.ident (nes "Foo"))) []))]⟩ }
  , { name := "import-type-attrs-typeof"
      prog := ⟨[st (.typeAlias (nes "B") []
        (.importType true "mod" [⟨"resolution-mode", "import"⟩] none []))]⟩ }
  , { name := "import-type-attrs-break"
      prog := ⟨[st (.typeAlias (nes "C") []
        (.importType false "a-really-long-module-name-that-goes-on"
          [⟨"resolution-mode", "import"⟩] (some (.ident (nes "Foo"))) []))]⟩ }
  , { name := "import-type-attrs-break-inner"
      prog := ⟨[st (.typeAlias (nes "D") []
        (.importType false "mod"
          [⟨"resolution-mode-is-long-here", "import"⟩, ⟨"another", "value-here-too-long"⟩]
          (some (.ident (nes "Foo"))) []))]⟩ }
  , { name := "import-type-attrs-annotation"
      prog := ⟨[st (letDecl "x"
          (some (.importType false "mod" [⟨"type", "json"⟩] (some (.ident (nes "A"))) []))),
        st (letDecl "y"
          (some (.indexed (.importType false "mod" [⟨"type", "json"⟩] none []) (.strLit "x"))))]⟩ }
  , { name := "import-type-attrs-args"
      prog := ⟨[st (.typeAlias (nes "E") []
        (.importType false "mod" [⟨"type", "json"⟩] (some (.ident (nes "A"))) [ty "B", ty "C"]))]⟩ }

    -- ## The type arguments of a JSX component
  , { name := "jsx-type-args"
      prog := ⟨[st (constDecl "a" none (el "Comp" [ty "string"] [] none))]⟩ }
  , { name := "jsx-type-args-children"
      prog := ⟨[st (constDecl "b" none
        (el "Comp" [ty "string"] [] (some [.text "hello"])))]⟩ }
  , { name := "jsx-type-args-attrs-break"
      prog := ⟨[st (constDecl "c" none
        (el "Comp" [ty "AVeryLongTypeNameHere", ty "AnotherVeryLongTypeName",
            ty "AThirdLongTypeName"]
          [attrExpr "prop" (num 1), attrStr "other" "x"] none))]⟩ }
  , { name := "jsx-type-args-long-alone"
      prog := ⟨[st (constDecl "d" none
        (el "Comp" [ty "AVeryLongTypeNameHereOkay", ty "AnotherVeryLongTypeNameHere",
            ty "AThirdOne"] [] none))]⟩ }
  , { name := "jsx-type-args-member-name"
      prog := ⟨[st (constDecl "e" none
        (.jsx (.element (.member (.ident (nes "A")) (nes "B")) [ty "string"]
          [attrExpr "x" (num 1)] none)))]⟩ }
  , { name := "jsx-type-args-spread-attr"
      prog := ⟨[st (constDecl "f" none
        (el "Comp" [ty "string"] [.spread (v "p")] none))]⟩ }
  , { name := "jsx-type-args-nested"
      prog := ⟨[st (constDecl "g" none
        (el "Outer" [] []
          (some [.node (.element (.ident (nes "Comp")) [ty "string"]
            [attrStr "a" "x"] (some [.text "text"]))])))]⟩ }
  , { name := "jsx-type-args-one-string-attr"
      prog := ⟨[st (constDecl "h" none
        (el "Comp" [ty (longType 0), ty (longType 1)]
          [attrStr "className" "a-fairly-long-class-name-here"] none))]⟩ }
  , { name := "jsx-type-args-in-return"
      prog := ⟨[st (.funcDecl false false (nes "render") [] [] (some (ty "JSX.Element"))
        (some [.return_ (some (el "Comp" [ty "Props"]
          [attrExpr "value" (v "value")] (some [.expr (v "child")])))]))]⟩ }
  , { name := "jsx-type-args-import-type"
      prog := ⟨[st (constDecl "i" none
        (el "Comp" [.importType true "./props" [] (some (.ident (nes "Props"))) []]
          [attrExpr "value" (v "value")] none))]⟩ }

    -- ## The `this` parameter, and the `this` of a type predicate
  , { name := "this-parameter"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [parT "this" (ty "Foo"), parT "x" (ty "number")] (some (ty "void")) (some []))]⟩ }
  , { name := "this-parameter-type"
      prog := ⟨[st (.typeAlias (nes "G") []
        (.fn [] [parT "this" (ty "Foo"), parT "x" (ty "number")] (ty "void")))]⟩ }
  , { name := "this-parameter-method"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) false [] [parT "this" (ty "C")]
          (some (.predicate false (nes "this") (some (ty "D")))) (some [])])]⟩ }
  , { name := "asserts-this"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) false [] []
          (some (.predicate true (nes "this") (some (ty "D")))) (some [])])]⟩ }
  , { name := "this-parameter-breaks"
      prog := ⟨[st (.funcDecl false false (nes (longName 0)) []
        [parT "this" (ty (longType 0)), parT (longName 1) (ty (longType 1))]
        (some (ty "void")) (some []))]⟩ }

    -- ## The new forms in a decorated member, where the layout of the
    -- arguments of the import type decides where the decorators stand
  , { name := "import-type-attrs-decorated-getter"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [.call (v "Result") [] [.object [], .string "mod"]] {} .get
          (.ident (nes "aVeryVeryLongIdentifierNameHere")) false [] []
          (some (.importType true "say-hi" [⟨"a-key", "require"⟩] none []))
          (some [.return_ (some (v "x"))])])]⟩ }
  , { name := "import-type-attrs-getter"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .get (.ident (nes "aVeryVeryLongIdentifierNameHere")) false [] []
          (some (.importType true "say-hi" [⟨"a-key", "require"⟩] none []))
          (some [.return_ (some (v "x"))])])]⟩ }

    -- ## The new forms in the positions that decide their layout
  , { name := "typeof-import-in-call-type-args"
      prog := ⟨[es (.call (v "f") [.importType true "mod" [] none []] [v "x"]),
        es (.new (v "C") [.importType true "mod" [⟨"type", "json"⟩] none []] [])]⟩ }
  , { name := "import-attrs-in-union-breaks"
      prog := ⟨[st (.typeAlias (nes (longType 0)) []
        (.union [importAttrs, ty (longType 1), ty (longType 2)]))]⟩ }
  , { name := "import-attrs-in-conditional"
      prog := ⟨[st (.typeAlias (nes (longType 0)) []
        (.conditional importAttrs (ty (longType 1)) (ty (longType 2)) (ty (longType 3))))]⟩ }
  , { name := "import-attrs-in-type-args"
      prog := ⟨[st (letDecl (longName 0) (some (tyA "Record" [importAttrs, ty (longType 1)])))]⟩ }
  , { name := "import-attrs-in-object-type"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType [prop (longName 0) importAttrs, prop "b" (ty "number")]))]⟩ }
  , { name := "export-default-interface-long-extends"
      prog := ⟨[.exportDecl (.defaultDecl
        (.interface_ (nes (longType 0)) [tp "T"]
          [her (longType 1) [ty "T"], her (longType 2) [], her (longType 3) []]
          [prop "a" (ty "T")]))]⟩ }
  , { name := "export-default-abstract-class-decorated"
      prog := ⟨[.exportDecl (.defaultDecl
        (.classDecl [.call (v "Injectable") [] [.object []]] true (nes "Base") [] none [] []))]⟩ }
  , { name := "jsx-type-args-as-call-argument"
      prog := ⟨[es (call "render"
          [el "Comp" [ty "Props"] [attrExpr "value" (v "value")] none, v "root"]),
        es (.dot (el "Comp" [ty "Props"] [] none) (nes "props"))]⟩ }
  , { name := "jsx-type-args-in-arrow-body"
      prog := ⟨[st (constDecl (longName 0) none
        (.arrow false [] [par "props"] none
          (.expr (el "AComponentName" [ty (longType 0), ty (longType 1)]
            [attrExpr "value" (v "props")] (some [.text "the text here"])))))]⟩ }
  , { name := "jsx-type-args-conditional-child"
      prog := ⟨[st (constDecl "x" none
        (el "Outer" [] []
          (some [.expr (.ternary (v "cond")
            (el "Comp" [ty "A"] [] none) (el "Other" [ty "B"] [] none))])))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
