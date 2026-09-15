import Tests.Corpus41

/-!
# The shapes prettier's options decide

The samples here are the JavaScript shapes whose text changes with one of
prettier's options, gathered so that `scripts/check-options.sh` compares
them under every configuration it runs.  `Tests/Ts/Corpus15.lean` is the
same file for TypeScript, and `Tests/Corpus41.lean` covers the
conditional expression, whose layout `experimentalTernaries` replaces.

* `semi: false` — the statements a parser reads on into, which keep a
  semicolon of their own (one beginning with `(`, `[`, a template
  literal, `+`, `-`, a prefix `++`, a regular expression, and an
  arrow written `async` first), a JSX element as a statement, and the
  class members a field is read on into (a computed name, a name that is
  a keyword, a generator, a getter), together with the field named
  `static`, `get` or `set`.
* `singleQuote` and `jsxSingleQuote` — string literals and JSX attribute
  values holding each quote, which choose the other quote where that
  escapes less.
* `quoteProps` — a name that has to keep its quotes among the properties
  of an object and the members of a class, which quotes the rest of them
  under `"consistent"`, and a name written as a number.
* `trailingComma` — the lists that take a comma from `"es5"` up (an
  array, an object, a destructuring pattern, a named import and a named
  export) and those that take one only at `"all"` (the arguments of a
  call and the parameters of a function), beside a parameter list that
  ends in a rest element, which never takes one.
* `bracketSpacing` — an object literal, an object pattern, and an import
  and an export clause.
* `arrowParens` — the sole parameter of an arrow function, which keeps
  its parentheses under `"avoid"` as soon as it is a pattern, carries a
  default value, or is a rest element.
* `tabWidth` and `useTabs` — the places prettier aligns rather than
  indents: the branches of a conditional expression and the operands of
  a broken operator chain written inside parentheses.
* `bracketSameLine` and `singleAttributePerLine` — JSX elements with
  several attributes, one of them self-closing.
* `experimentalOperatorPosition` — broken chains of the operators whose
  links prettier does and does not break in front of.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A call whose arguments do not fit on one line. -/
private def longCall : MiniExpr :=
  call (longName 0) [v (longName 1), v (longName 2), v (longName 3)]

/-- The samples. -/
def samples42 : List Sample :=
  [ -- `semi: false`: the statements a parser reads on into
    { name := "opt-js-asi-hazards"
      prog := ⟨[es (.call (.arrow false [par "x"] (.expr (v "x"))) [num 1]),
        es (.array [.elem (num 1)]),
        es (.template none "text" []),
        es (.unary .plus (v "x")),
        es (.unary .minus (v "x")),
        es (.unary .preIncr (v "x")),
        es (.binary (.regex ⟨nes "a", {}⟩) .divide (v "x")),
        es (.arrow true [par "x"] (.expr (v "x"))),
        es (call "f" [num 1])]⟩ }
  , { name := "opt-js-asi-jsx"
      prog := ⟨[es (.jsx (.element (.ident (nes "div")) [] none)),
        es (call "f" [num 1])]⟩ }
    -- `semi: false`: the class members a field is read on into
  , { name := "opt-js-field-semicolons"
      prog := ⟨[st (.classDecl [] (nes "C") none
        [.field [] false false (.ident (nes "a")) none,
         .method [] false .normal (.computed (v "k")) [] [],
         .field [] false false (.ident (nes "b")) (some (num 1)),
         .field [] false false (.ident (nes "in")) (some (num 2)),
         .field [] false false (.ident (nes "c")) none,
         .method [] false .generator (.ident (nes "m")) [] [],
         .field [] false false (.ident (nes "d")) none,
         .method [] false .get (.ident (nes "value")) [] [.return_ (some (num 1))]])]⟩ }
  , { name := "opt-js-field-named-static-get-set"
      prog := ⟨[st (.classDecl [] (nes "C") none
        [.field [] false false (.ident (nes "static")) none,
         .field [] false false (.ident (nes "get")) none,
         .field [] false false (.ident (nes "set")) none,
         .field [] false true (.ident (nes "accessorField")) (some (num 1)),
         .staticBlock [.expr (call "f" [])]])]⟩ }
    -- `singleQuote` and `jsxSingleQuote`
  , { name := "opt-js-quotes"
      prog := ⟨[es (.string "plain"),
        es (.string "it's"),
        es (.string "say \"hi\""),
        es (.string "both ' and \""),
        es (.string "two '' and one \"")]⟩ }
  , { name := "opt-js-jsx-quotes"
      prog := ⟨[es (.jsx (.element (.ident (nes "div"))
          [.attr (.ident (nes "a")) (some (.string "plain")),
           .attr (.ident (nes "b")) (some (.string "it's")),
           .attr (.ident (nes "c")) (some (.string "say \"hi\"")),
           .attr (.ident (nes "d")) (some (.expr (.string "in braces")))]
          none))]⟩ }
    -- `quoteProps`
  , { name := "opt-js-quote-props-object"
      prog := ⟨[st (constDecl "theObject"
          (.object [.keyValue (.ident (nes "plain")) (num 1),
            .keyValue (.string "a key") (num 2),
            .keyValue (.number (JSNumber.ofNat 3)) (num 3)])),
        st (constDecl "theOtherObject"
          (.object [.keyValue (.ident (nes "plain")) (num 1),
            .keyValue (.string "alsoPlain") (num 2)])),
        st (constDecl "theNumericObject"
          (.object [.keyValue (.number (JSNumber.ofNat 1)) (num 1),
            .keyValue (.string "2") (num 2)]))]⟩ }
  , { name := "opt-js-quote-props-class"
      prog := ⟨[st (.classDecl [] (nes "C") none
        [.field [] false false (.ident (nes "plain")) (some (num 1)),
         .field [] false false (.string "a key") (some (num 2)),
         .method [] false .normal (.string "a method") [] []])]⟩ }
    -- `trailingComma`
  , { name := "opt-js-trailing-comma-es5"
      prog := ⟨[st (constDecl "theArray"
          (.array [.elem (v (longName 0)), .elem (v (longName 1)), .elem (v (longName 2))])),
        st (constDecl "theObject"
          (.object [.keyValue (.ident (nes (longName 0))) (v (longName 1)),
            .keyValue (.ident (nes (longName 2))) (v (longName 3))])),
        st (.decl .const ⟨⟨.object [⟨.ident (nes (longName 0)), p (longName 0)⟩,
            ⟨.ident (nes (longName 1)), p (longName 1)⟩,
            ⟨.ident (nes (longName 2)), p (longName 2)⟩] none,
          some (v "theObject")⟩, []⟩)]⟩ }
  , { name := "opt-js-trailing-comma-imports"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
          (some [⟨nes (longName 0), none⟩, ⟨nes (longName 1), none⟩,
            ⟨nes (longName 2), none⟩]) (nes "a-module"))),
        .exportDecl (.locals [⟨nes (longName 0), none⟩, ⟨nes (longName 1), none⟩,
          ⟨nes (longName 2), none⟩])]⟩ }
  , { name := "opt-js-trailing-comma-all"
      prog := ⟨[es longCall,
        st (.funcDecl false false (nes "theFunctionName")
          [par (longName 0), par (longName 1), par (longName 2)] [])]⟩ }
  , { name := "opt-js-trailing-comma-never"
      prog := ⟨[st (.funcDecl false false (nes "theFunctionName")
          [par (longName 0), par (longName 1), .rest (p (longName 2))] [])]⟩ }
    -- `bracketSpacing`
  , { name := "opt-js-bracket-spacing"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
          (some [⟨nes "aName", none⟩]) (nes "a-module"))),
        .exportDecl (.locals [⟨nes "aName", none⟩]),
        st (constDecl "theObject" (.object [.keyValue (.ident (nes "a")) (num 1)])),
        st (constDecl "theEmptyObject" (.object [])),
        st (.decl .const ⟨⟨.object [⟨.ident (nes "a"), p "a"⟩] none,
          some (v "theObject")⟩, []⟩)]⟩ }
    -- `arrowParens`
  , { name := "opt-js-arrow-parens"
      prog := ⟨[st (constDecl "plain" (.arrow false [par "x"] (.expr (v "x")))),
        st (constDecl "asyncPlain" (.arrow true [par "x"] (.expr (v "x")))),
        st (constDecl "defaulted"
          (.arrow false [.plain (.withDefault (p "x") (num 1))] (.expr (v "x")))),
        st (constDecl "destructured"
          (.arrow false [.plain (.object [⟨.ident (nes "a"), p "a"⟩] none)] (.expr (v "a")))),
        st (constDecl "restOnly" (.arrow false [.rest (p "xs")] (.expr (v "xs")))),
        st (constDecl "none" (.arrow false [] (.expr (num 1)))),
        st (constDecl "two" (.arrow false [par "x", par "y"] (.expr (v "x")))),
        st (constDecl "chained"
          (.arrow false [par "x"] (.expr (.arrow false [par "y"] (.expr (v "y"))))))]⟩ }
    -- `tabWidth` and `useTabs`: the places that are aligned
  , { name := "opt-js-aligned"
      prog := ⟨[st (constDecl "theValue"
          (.ternary (v (longName 0)) (v (longName 1))
            (.ternary (v (longName 2)) (v (longName 3)) (v (longName 4))))),
        es (call "theFunctionName"
          [.binary (.binary (v (longName 0)) .plus (v (longName 1))) .plus (v (longName 2))])]⟩ }
    -- `experimentalOperatorPosition`
  , { name := "opt-js-operator-position"
      prog := ⟨[st (constDecl "theSum"
          (.binary (.binary (v (longName 0)) .plus (v (longName 1))) .plus (v (longName 2)))),
        st (constDecl "theTest"
          (.binary (.binary (v (longName 0)) .and (v (longName 1))) .and (v (longName 2)))),
        st (constDecl "theDefault"
          (.binary (v (longName 0)) .coalesce (call (longName 1) [v (longName 2)]))),
        st (.if_ (.binary (.binary (v (longName 0)) .or (v (longName 1))) .or (v (longName 2)))
          (.block [.expr (call "f" [])]) none)]⟩ }
    -- `bracketSameLine` and `singleAttributePerLine`
  , { name := "opt-js-jsx-attributes"
      prog := ⟨[st (constDecl "theElement"
          (.jsx (.element (.ident (nes "TheComponentName"))
            [.attr (.ident (nes (longName 0))) (some (.string "a value")),
             .attr (.ident (nes (longName 1))) (some (.expr (v (longName 2))))]
            (some [.text "the text of the element"])))),
        st (constDecl "theSelfClosing"
          (.jsx (.element (.ident (nes "TheComponentName"))
            [.attr (.ident (nes (longName 0))) (some (.string "a value")),
             .attr (.ident (nes (longName 1))) (some (.expr (v (longName 2))))]
            none))),
        st (constDecl "theOneAttribute"
          (.jsx (.element (.ident (nes "TheComponentName"))
            [.attr (.ident (nes "a")) (some (.string "a value"))]
            (some [.text "text"]))))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
