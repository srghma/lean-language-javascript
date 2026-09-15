import Tests.Corpus38

/-!
# JSX in the shapes a React program is written in

The samples here are the patterns a component file holds: a hook call with
a list of dependencies, a chain of `filter` and `map` building a list of
elements, an element hugged as the only argument of a call, arrays and
objects of elements, the fields and the static block of a class, an
element written in the value of an attribute behind `&&`, a fragment as
the body of an arrow function, a chain of conditionals as a child, an
`await` and a `yield` as children, and an element exported by default.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An element wide enough that it has to break. -/
private def wideEl : MiniExpr :=
  el "div" [sattr "className" "a-very-long-class-name-here", eattr "onClick" (v "handler")]
    (some [.text "some text that is long enough to force the element to break apart"])

/-- An item of a list, as a component writes one. -/
private def item : MiniExpr :=
  el "li" [eattr "key" (.dot (v "item") (nes "id"))] (some [.expr (.dot (v "item") (nes "label"))])

/-- The samples. -/
def samples39 : List Sample :=
  [ { name := "jsx-hook-with-deps"
      prog := ⟨[st (.expr (call "useEffect"
                  [.arrow false [] (.block [.expr (call "render" [wideEl])]),
                   .array [.elem (v "dependency")]]))]⟩ }
  , { name := "jsx-map-filter-chain"
      prog := ⟨[st (constDecl "rows" (.call (.dot (.call (.dot (v "items") (nes "filter"))
                  [.arrow false [par "item"] (.expr (.dot (v "item") (nes "visible")))])
                  (nes "map")) [.arrow false [par "item"] (.expr item)]))]⟩ }
  , { name := "jsx-hugged-only-argument"
      prog := ⟨[st (.expr (call "render" [wideEl])),
                st (.expr (call "expect" [wideEl])),
                st (.expr (call "aFunctionWithARatherLongName" [v "first", wideEl]))]⟩ }
  , { name := "jsx-array-of-elements"
      prog := ⟨[st (constDecl "rows" (.array [.elem wideEl, .elem (el "br" [] none)]))]⟩ }
  , { name := "jsx-object-of-elements"
      prog := ⟨[st (constDecl "icons" (.object
                  [.keyValue (.ident (nes "open")) wideEl,
                   .keyValue (.ident (nes "closed")) (el "br" [] none)]))]⟩ }
  , { name := "jsx-class-fields"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [] true false (.ident (nes "fallback")) (some wideEl),
                   .field [] false false (.private_ (nes "view")) (some wideEl),
                   .field [] false true (.ident (nes "accessorView")) (some wideEl),
                   .staticBlock [.expr (call "register" [wideEl])]])]⟩ }
  , { name := "jsx-attribute-jsx-binary"
      prog := ⟨[st (constDecl "a" (el "Modal"
                  [eattr "body" (.binary (v "isReadyToShowTheContent") .and
                     (el "Body" [sattr "kind" "primary"] (some [.text "the body text"])))] none))]⟩ }
  , { name := "jsx-arrow-body-fragment"
      prog := ⟨[st (.expr (call "wrapTheComponentInAnotherOne"
                  [.arrow false [par "props"]
                    (.expr (.jsx (.fragment
                      [.node (.element (jn "Header") [] none), .text " between ",
                       .node (.element (jn "Footer") [] none)])))]))]⟩ }
  , { name := "jsx-conditional-chain-in-child"
      prog := ⟨[st (constDecl "a" (el "div" []
                  (some [.expr (.ternary (v "isLoading")
                    (el "Spinner" [] none)
                    (.ternary (v "hasError") (el "Error" [sattr "kind" "fatal"] none)
                      (el "Content" [eattr "value" (v "value")] none)))])))]⟩ }
  , { name := "jsx-await-and-yield-children"
      prog := ⟨[st (.funcDecl true true (nes "f") []
                  [.return_ (some (el "div" []
                    (some [.expr (.await (call "loadTheContentOfThePage" [v "id"])),
                           .expr (.yield (some (el "span" [] none)))])))])]⟩ }
  , { name := "jsx-long-attribute-chain-value"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "value" (.call (.dot (.call (.dot (v "theServiceObject")
                     (nes "fetchTheValue")) [v "argument"]) (nes "then"))
                     [.arrow false [par "value"] (.expr (v "value"))])] none))]⟩ }
  , { name := "jsx-element-in-export-default"
      prog := ⟨[.exportDecl (.defaultExpr wideEl),
                .exportDecl (.decl (.funcDecl false false (nes "App") []
                  [.return_ (some wideEl)]))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
