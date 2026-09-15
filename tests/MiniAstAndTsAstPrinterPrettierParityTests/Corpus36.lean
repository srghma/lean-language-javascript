import Tests.Corpus35

/-!
# Further samples of JSX

The samples here cover the corners the earlier files leave open: the
shapes an attribute value may have, the names of an element, the runs of
whitespace inside a text and around the children, the positions an
element stands in which are not the usual ones, and the body of an arrow
function written as the argument of a call inside a `{ }`.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A fragment, as a child. -/
private def fragc (kids : List MiniJSXChild) : MiniJSXChild := .node (.fragment kids)

/-- The samples. -/
def samples36 : List Sample :=
  [ { name := "jsx-attr-empty-string"
      prog := ⟨[st (constDecl "a" (el "div" [sattr "title" "", sattr "id" "x"] none))]⟩ }
  , { name := "jsx-attr-fragment-value"
      prog := ⟨[st (constDecl "a" (el "Layout"
                  [.attr (jn "header") (some (.node (.fragment [.text "hi"])))] none))]⟩ }
  , { name := "jsx-deep-member-name"
      prog := ⟨[st (constDecl "a" (.jsx (.element
                  (.member (.member (.ident (nes "Foo")) (nes "Bar")) (nes "Baz")) []
                  (some [.text "text"]))))]⟩ }
  , { name := "jsx-text-runs-of-space"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.text "  a  b  "]))),
                st (constDecl "b" (el "p" [] (some [.text "\n  a\n  b\n"]))),
                st (constDecl "c" (el "p" [] (some [.text "a\tb"])))]⟩ }
  , { name := "jsx-empty-expr-beside-text"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.text "before ", .emptyExpr, .text " after"]))),
                st (constDecl "b" (el "p" [] (some [.emptyExpr, .emptyExpr])))]⟩ }
  , { name := "jsx-export-default-jsx"
      prog := ⟨[.exportDecl (.defaultExpr (el "div" [sattr "className" "a"] (some [.text "text"])))]⟩ }
  , { name := "jsx-jsx-nullish"
      prog := ⟨[st (constDecl "a" (.binary (v (longName 0)) .coalesce
                  (el "TheFallbackComponent" [eattr "value" (v (longName 1))] none))),
                st (constDecl "b" (.binary (v (longName 0)) .or
                  (el "TheFallbackComponent" [eattr "value" (v (longName 1))] none)))]⟩ }
  , { name := "jsx-jsx-unary"
      prog := ⟨[es (.unary .not (el "div" [] none)),
                es (.unary .typeof (el "div" [] none))]⟩ }
  , { name := "jsx-jsx-fragment-in-conditional"
      prog := ⟨[st (constDecl "a" (.ternary (v (longName 0))
                  (.jsx (.fragment [.text "the first branch of the conditional here"]))
                  (.jsx (.fragment [.text "the second branch of the conditional"]))))]⟩ }
  , { name := "jsx-jsx-whitespace-ends"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.expr (.string " "), .text "word",
                  .expr (.string " ")]))),
                st (constDecl "b" (el "p" [] (some [.expr (.string " "), .expr (.string " ")]))),
                st (constDecl "c" (el "p" [] (some [.text "a", .expr (.string " "),
                  .expr (.string " "), .text "b"])))]⟩ }
  , { name := "jsx-jsx-nested-fragment-whitespace"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [fragc [.text "one"], .expr (.string " "), fragc [.text "two"]])))]⟩ }
  , { name := "jsx-jsx-attr-conditional"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "className" (.ternary (v (longName 0)) (.string "the-first-class")
                    (.string "the-second-class"))] none))]⟩ }
  , { name := "jsx-jsx-attr-binary"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "width" (.binary (v (longName 0)) .plus (v (longName 1)))] none))]⟩ }
  , { name := "jsx-jsx-new-and-optional"
      prog := ⟨[st (constDecl "a" (.dot (el "div" [] none) (nes "props"))),
                st (constDecl "b" (.chain (el "div" [] none) ⟨MiniChainLink.dot true (nes "props"), []⟩))]⟩ }
  , { name := "jsx-jsx-yield-and-await"
      prog := ⟨[st (.funcDecl false true (nes "g") []
                  [.expr (.yield (some (el "div" [] (some [.text "text"]))))]),
                st (.funcDecl true false (nes "h") []
                  [.return_ (some (.await (el "div" [] (some [.text "text"]))))])]⟩ }
  , { name := "jsx-jsx-comma-and-sequence"
      prog := ⟨[es (.seq (el "div" [] none) (el "span" [] none))]⟩ }
  , { name := "jsx-jsx-long-fill-with-whitespace"
      prog := ⟨[st (constDecl "a" (el "p" [] (some
                  [.text "the quick brown fox jumps over the lazy dog and keeps going",
                   .expr (.string " "), elc "b" [] (some [.text "bold"]),
                   .text " and more text after the element that wraps the line"])))]⟩ }
  , { name := "jsx-jsx-self-closing-runs"
      prog := ⟨[st (constDecl "a" (el "p" [] (some
                  [elc "br" [] none, .expr (.string " "), elc "br" [] none,
                   .text "x", elc "br" [] none])))]⟩ }
  , { name := "jsx-jsx-arrow-seq-body"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [.expr (call "f" [.arrow false [] (.expr
                    (.seq (el "X" [] none) (v "b")))])]))),
                st (constDecl "b" (el "div" [] (some
                  [.expr (call "f" [.arrow false [] (.expr
                    (.seq (v "b") (el "X" [] none)))])]))),
                st (constDecl "c" (el "div" [] (some
                  [.expr (call "f" [.arrow false [] (.expr
                    (.seq (.object [.keyValue (.ident (nes "a")) (num 1)]) (v "b")))])]))),
                st (constDecl "d" (el "div" [] (some
                  [.expr (call "f" [.arrow false [] (.expr
                    (.assign (.ident (nes "x")) .assign (el "X" [] none)))])])))]⟩ }
  , { name := "jsx-ws-then-text"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.string " "), .text "x"]))),
                st (constDecl "b" (el "div" [] (some [.text "x", .expr (.string " ")]))),
                st (constDecl "c" (el "div" [eattr "a" (el "b" [] none)] (some
                  [.expr (.string " ")])))]⟩ }
  , { name := "jsx-two-space-string-child"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.string "  "), .text "x"]))),
                st (constDecl "b" (el "div" [] (some [.expr (.string "\n"), .text "x"])))]⟩ }
  , { name := "jsx-string-children"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.string "text")]))),
                st (constDecl "b" (el "div" [] (some [.expr (.string "a"), .expr (.string "b")])))]⟩ }
  , { name := "jsx-attr-entities"
      prog := ⟨[st (constDecl "a" (el "div" [sattr "a" "\"", sattr "b" "&",
                  sattr "c" "a'b", sattr "d" "both \" and '"] none))]⟩ }
  , { name := "jsx-empty-children-vs-self-closing"
      prog := ⟨[st (constDecl "a" (el "div" [] (some []))),
                st (constDecl "b" (el "div" [] none)),
                st (constDecl "c" (el "div" [] (some [.text ""])))]⟩ }
  , { name := "jsx-jsx-callee"
      prog := ⟨[es (.call (el "div" [] none) [v "a"]),
                es (.new (el "div" [] none) [v "a"]),
                es (.template (some (el "div" [] none)) "text" []),
                es (.index (el "div" [] none) (.string "props")),
                es (.new (.dot (el "div" [] none) (nes "props")) [v "a"]),
                es (.new (.index (el "div" [] none) (.string "x")) [v "a"])]⟩ }
  , { name := "jsx-jsx-in-tests"
      prog := ⟨[st (.if_ (el "div" [] none) (.block []) none),
                st (.while_ (el "div" [] none) (.block [])),
                st (.switch (el "div" [] none) [])]⟩ }
  , { name := "jsx-jsx-spread-and-rest"
      prog := ⟨[st (constDecl "a" (.array [.elem (.spread (el "div" [] none))])),
                es (call "f" [.spread (el "div" [] none)]),
                st (constDecl "b" (.object [.spread (el "div" [] none)]))]⟩ }
  , { name := "jsx-jsx-long-attribute-chain"
      prog := ⟨[st (constDecl "a" (el "Component"
                  [eattr "onClick" (.call (.dot (.call (.dot (v "theStore") (nes "getState")) [])
                    (nes "theHandlerOfTheComponent")) [v (longName 0)])] (some [.text "text"])))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
