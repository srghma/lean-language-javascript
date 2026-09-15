import Tests.Ts.Prelude

/-!
# The shapes prettier's options decide

The samples here are the ones whose text changes with one of prettier's
options, gathered so that `scripts/check-options-ts.sh` compares them
under every configuration it runs:

* `semi: false` — the statements a parser reads on into, which keep a
  semicolon of their own (`(`, `[`, a template literal, `+`, `-`, `/` and
  `<`), the arrow function written `async` first, and the class members a
  field is read on into (a computed name, `in`, an index signature, a
  generator), together with those a modifier stops it being read into
  (`static`, `readonly`, an accessibility modifier) and the field named
  `static`, `get` or `set` with neither value nor annotation.
* `quoteProps` — a name that has to keep its quotes among the properties
  of an object, the members of a class, of an interface, of an object
  type and of an enum, which quotes all of them under `"consistent"`;
  a name written as a number, which prettier leaves alone where it reads
  TypeScript.
* `trailingComma` — the lists that take a comma from `"es5"` up (an
  array, an object, a tuple type, an enum, a type parameter list) and
  those that take one only at `"all"` (the arguments of a call, the
  parameters of a function), beside the lists that never take one (a rest
  parameter at the end, a type argument list).
* `bracketSpacing` — an object literal, an object pattern, an import
  clause of one specifier, an object type and a mapped type.
* `arrowParens` — the sole parameter of an arrow, which keeps its
  parentheses under `"avoid"` as soon as it carries an annotation, a `?`,
  a default value or a decorator, or the arrow has type parameters or a
  return type.
* `tabWidth` and `useTabs` — the places that are aligned rather than
  indented: the branches of a conditional expression and of a conditional
  type, and the members of a union.
* `bracketSameLine` and `singleAttributePerLine` — a JSX element with
  several attributes.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

private def longCall : MiniExpr :=
  .call (v (longName 0)) [] [v (longName 1), v (longName 2), v (longName 3)]

/-- The samples. -/
def samples15 : List Sample :=
  [ -- `semi: false`: the statements read on into
    { name := "opt-asi-hazards"
      prog := ⟨[es (.call (.arrow false [] [par "x"] none (.expr (v "x"))) [] [num 1]),
        es (.array [.elem (num 1)]),
        es (.template none [] "text" []),
        es (.unary .plus (v "x")),
        es (.unary .minus (v "x")),
        es (.unary .preIncr (v "x")),
        es (.binary (.regex ⟨nes "a", {}⟩) .divide (v "x")),
        es (.arrow true [] [par "x"] none (.expr (v "x"))),
        es (.asExpr (v "x") (ty "T")),
        es (.nonNull (v "x"))]⟩ }
  , { name := "opt-asi-jsx"
      prog := ⟨[es (.jsx (.element (.ident (nes "div")) [] [] none)),
        es (call "f" [num 1])]⟩ }
    -- `semi: false`: the class members a field is read on into
  , { name := "opt-field-semicolons"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] {} false (.ident (nes "a")) false false (some (ty "number")) none,
         .method [] {} .normal (.computed (v "k")) false [] [] none (some []),
         .field [] {} false (.ident (nes "b")) false false none (some (num 1)),
         .field [] {} false (.ident (nes "in")) false false none (some (num 2)),
         .field [] {} false (.ident (nes "c")) false false (some (ty "number")) none,
         .indexSig {} (nes "key") (ty "string") (ty "unknown"),
         .field [] {} false (.ident (nes "d")) false false none (some (num 3)),
         .method [] {} .generator (.ident (nes "m")) false [] [] none (some [])])]⟩ }
  , { name := "opt-field-semicolons-stopped"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] {} false (.ident (nes "a")) false false (some (ty "number")) none,
         .field [] { isStatic := true } false (.computed (v "k")) false false none (some (num 1)),
         .field [] {} false (.ident (nes "b")) false false none none,
         .field [] { isReadonly := true } false (.computed (v "k")) false false
           (some (ty "number")) none,
         .field [] {} false (.ident (nes "c")) false false none none,
         .method [] { accessibility := some .public_ } .normal (.computed (v "k")) false [] []
           none (some []),
         .field [] {} false (.ident (nes "d")) false false none none,
         .method [] {} .get (.computed (v "k")) false [] [] none (some [.return_ (some (num 1))])])]⟩ }
  , { name := "opt-field-named-static-get-set"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] {} false (.ident (nes "static")) false false none none,
         .field [] {} false (.ident (nes "get")) false false none none,
         .field [] {} false (.ident (nes "set")) false false (some (ty "number")) none,
         .field [] {} true (.ident (nes "accessorField")) false false none (some (num 1))])]⟩ }
    -- `quoteProps`
  , { name := "opt-quote-props-object"
      prog := ⟨[st (constDecl "theObject" none
          (.object [.keyValue (.ident (nes "plain")) (num 1),
            .keyValue (.string "a key") (num 2),
            .keyValue (.number (JSNumber.ofNat 3)) (num 3)])),
        st (constDecl "theOtherObject" none
          (.object [.keyValue (.ident (nes "plain")) (num 1),
            .keyValue (.string "alsoPlain") (num 2)]))]⟩ }
  , { name := "opt-quote-props-class"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] {} false (.ident (nes "plain")) false false none (some (num 1)),
         .field [] {} false (.string "a key") false false none (some (num 2)),
         .method [] {} .normal (.string "a method") false [] [] none (some [])])]⟩ }
  , { name := "opt-quote-props-interface"
      prog := ⟨[st (.interface_ (nes "I") [] []
          [prop "plain" (ty "number"), .property false (.string "a key") false (some (ty "string"))]),
        st (.typeAlias (nes "T") []
          (.objectType [prop "plain" (ty "number"),
            .property false (.string "a key") false (some (ty "string"))]))]⟩ }
  , { name := "opt-quote-props-enum"
      prog := ⟨[st (.enum_ false (nes "E")
        [⟨.ident (nes "Plain"), some (num 1)⟩,
         ⟨.string "a key", some (num 2)⟩])]⟩ }
    -- `trailingComma`
  , { name := "opt-trailing-comma-es5"
      prog := ⟨[st (constDecl "theArray" none
          (.array [.elem (v (longName 0)), .elem (v (longName 1)), .elem (v (longName 2))])),
        st (constDecl "theObject" none
          (.object [.keyValue (.ident (nes (longName 0))) (v (longName 1)),
            .keyValue (.ident (nes (longName 2))) (v (longName 3))])),
        st (.typeAlias (nes "T") []
          (.tuple [.elem (ty (longType 0)), .elem (ty (longType 1)), .elem (ty (longType 2))])),
        st (.enum_ false (nes "E") [⟨.ident (nes (longName 0)), none⟩,
          ⟨.ident (nes (longName 1)), none⟩])]⟩ }
  , { name := "opt-trailing-comma-all"
      prog := ⟨[es longCall,
        st (.funcDecl false false (nes "theFunction")
          [tp (longType 0), tp (longType 1), tp (longType 2)]
          [parT (longName 0) (ty (longType 0)), parT (longName 1) (ty (longType 1))]
          none (some []))]⟩ }
  , { name := "opt-trailing-comma-never"
      prog := ⟨[st (.funcDecl false false (nes "theFunction") []
          [parT (longName 0) (ty (longType 0)), parRest (longName 1) (some (.array (ty "string")))]
          none (some [])),
        st (constDecl "theValue" none
          (.instantiation (v (longName 0)) [ty (longType 0), ty (longType 1), ty (longType 2)]))]⟩ }
    -- `bracketSpacing`
  , { name := "opt-bracket-spacing"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
          (some [⟨false, nes "aName", none⟩]) (nes "a-module"))),
        st (constDecl "theObject" none (.object [.keyValue (.ident (nes "a")) (num 1)])),
        st (.decl .const ⟨⟨.object [⟨.ident (nes "a"), p "a"⟩] none, false, none,
          some (v "theObject")⟩, []⟩),
        st (.typeAlias (nes "T") [] (.objectType [prop "a" (ty "number")])),
        st (.typeAlias (nes "M") []
          (.mapped none (nes "K") (.keyof (ty "T")) none none (some (ty "number"))))]⟩ }
    -- `arrowParens`
  , { name := "opt-arrow-parens"
      prog := ⟨[st (constDecl "plain" none (.arrow false [] [par "x"] none (.expr (v "x")))),
        st (constDecl "typed" none
          (.arrow false [] [parT "x" (ty "number")] none (.expr (v "x")))),
        st (constDecl "optional" none
          (.arrow false [] [parOpt "x" (ty "number")] none (.expr (v "x")))),
        st (constDecl "returns" none
          (.arrow false [] [par "x"] (some (ty "number")) (.expr (v "x")))),
        st (constDecl "generic" none
          (.arrow false [tp "T"] [par "x"] none (.expr (v "x")))),
        st (constDecl "asyncPlain" none (.arrow true [] [par "x"] none (.expr (v "x")))),
        st (constDecl "restParam" none
          (.arrow false [] [parRest "x"] none (.expr (v "x")))),
        st (constDecl "defaulted" none
          (.arrow false [] [.plain [] {} (.withDefault (p "x") (num 1)) false none] none
            (.expr (v "x"))))]⟩ }
    -- `tabWidth` and `useTabs`: the aligned places
  , { name := "opt-aligned-conditionals"
      prog := ⟨[st (constDecl "theValue" none
          (.ternary (v (longName 0)) (v (longName 1))
            (.ternary (v (longName 2)) (v (longName 3)) (v (longName 4))))),
        st (.typeAlias (nes "C") [tp "T"]
          (.conditional (ty "T") (ty (longType 0)) (ty (longType 1))
            (.conditional (ty "T") (ty (longType 2)) (ty (longType 3)) (ty "never")))),
        st (.typeAlias (nes "U") []
          (.union [ty (longType 0), ty (longType 1), ty (longType 2), ty (longType 3)]))]⟩ }
    -- `bracketSameLine` and `singleAttributePerLine`
  , { name := "opt-jsx-attributes"
      prog := ⟨[st (constDecl "theElement" none
          (.jsx (.element (.ident (nes "TheComponentName")) []
            [.attr (.ident (nes (longName 0))) (some (.string "a value")),
             .attr (.ident (nes (longName 1))) (some (.expr (v (longName 2))))]
            (some [.text "the text of the element"])))),
        st (constDecl "theSelfClosing" none
          (.jsx (.element (.ident (nes "TheComponentName")) []
            [.attr (.ident (nes (longName 0))) (some (.string "a value")),
             .attr (.ident (nes (longName 1))) (some (.expr (v (longName 2))))]
            none)))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
