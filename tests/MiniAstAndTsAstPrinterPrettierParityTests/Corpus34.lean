import Tests.Corpus33

/-!
# More samples of JSX

The samples here cover the JSX shapes the first file of JSX samples does
not: the runs of text a parser reads as one, the substitutions prettier
keeps the braces of and those it does not, the `{" "}` it writes for a
run of whitespace, and the positions an element stands in beside the
usual ones.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples. -/
def samples34 : List Sample :=
  [ -- two texts written next to one another are one text to a parser, so
    -- the words they hold decide the layout together
    { name := "jsx-adjacent-text"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.text "hello", .text " world"]))),
                st (constDecl "b" (el "p" [] (some
                  [.text ("the quick brown fox jumps over " ++ "the lazy dog"),
                   .text "x", elc "br" [] none]))),
                st (constDecl "c" (el "p" [] (some [.text "a", .text "b", elc "br" [] none]))),
                st (constDecl "d" (el "p" [] (some [.text " ", .text "word",
                  elc "span" [] (some [.text "y"])])))]⟩ }
  , { name := "jsx-text-around-elements"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [elc "br" [] none, .text "x"]))),
                st (constDecl "b" (el "p" [] (some [elc "br" [] none, .text "xy"]))),
                st (constDecl "c" (el "p" [] (some [elc "b" [] (some [.text "bold"]), .text "x"]))),
                st (constDecl "d" (el "p" [] (some [.text "x", elc "br" [] none, .text "y"])))]⟩ }
    -- a call written in a substitution keeps the braces on its line; a
    -- dynamic import and a `new` stand between braces of their own
  , { name := "jsx-substitution-containers"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "attrname" (call "theFunctionBeingCalled"
                    [.string "some/rather/long/module/name/here",
                     .object [.keyValue (.ident (nes "aaaa")) (num 1),
                              .keyValue (.ident (nes "bbbb")) (num 2),
                              .keyValue (.ident (nes "cccc")) (num 3)]]),
                   sattr "id" "aaaa"] none)),
                st (constDecl "b" (el "div"
                  [eattr "attrname" (.importCall (.string "some/rather/long/module/name/here")
                    (some (.object [.keyValue (.ident (nes "with"))
                      (.object [.keyValue (.ident (nes "type")) (.string "json")])]))),
                   sattr "id" "aaaa"] none)),
                st (constDecl "c" (el "div"
                  [eattr "attrname" (.new (v "TheConstructorName")
                    [.string "some/rather/long/module/name/here",
                     .object [.keyValue (.ident (nes "aaaa")) (num 1),
                              .keyValue (.ident (nes "bbbb")) (num 2)]]),
                   sattr "id" "aaaa"] none))]⟩ }
  , { name := "jsx-substitution-containers-child"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [.expr (.importCall (.string "some/rather/long/module/name/here/and/more")
                    (some (.object [.keyValue (.ident (nes "with"))
                      (.object [.keyValue (.ident (nes "type")) (.string "json")])])))]))),
                st (constDecl "b" (el "div" [] (some
                  [.expr (.new (v "TheConstructorNameHere")
                    [v (longName 0), v (longName 1), v (longName 2)])])))]⟩ }
    -- the runs of whitespace prettier writes as `{" "}`
  , { name := "jsx-whitespace-written"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [elc "TheFirstComponentName" [] (some [.text "one"]), .text " ",
                   elc "TheSecondComponentName" [] (some [.text "two"])]))),
                st (constDecl "b" (el "div" [] (some
                  [.text " ", elc "span" [] (some [.text "x"])]))),
                st (constDecl "c" (el "div" [] (some
                  [elc "span" [] (some [.text "x"]), .expr (.string " ")]))),
                st (constDecl "d" (el "div" [] (some
                  [.expr (.string " "), .expr (v "x"), .expr (.string " ")])))]⟩ }
    -- an element written where a line break would leave it beside other text
  , { name := "jsx-positions"
      prog := ⟨[st (constDecl "a" (.dot (el "div" [] none) (nes "props"))),
                st (constDecl "b" (.template none "before" [⟨el "div" [] none, "after"⟩])),
                st (.expr (.assign (v "theTargetOfTheAssignment") .assign
                  (el "div" [sattr "className" "a-long-class-name-here"]
                    (some [.text "some text in here"])))),
                st (.throw (el "div" [] none)),
                st (constDecl "c" (.seq (el "a" [] none) (el "b" [] none)))]⟩ }
  , { name := "jsx-in-hook"
      prog := ⟨[st (constDecl "a" (call "useMemo"
                  [.arrow false [] (.expr (el "div" [sattr "className" "the-class-name-here"]
                    (some [.text "the contents of the element"]))), .array []]))]⟩ }
  , { name := "jsx-arrow-chain"
      prog := ⟨[st (constDecl "render" (.arrow false [par "props"]
                  (.expr (.arrow false [par "state"]
                    (.expr (el "div" [eattr "id" (v "props")]
                      (some [.expr (v "state")])))))))]⟩ }
  , { name := "jsx-conditional-chain"
      prog := ⟨[st (constDecl "a" (.ternary (v "first") (el "First" [] none)
                  (.ternary (v "second") (el "Second" [] none)
                    (.ternary (v "third") (el "Third" [] none) .null))))]⟩ }
  , { name := "jsx-logical-chain"
      prog := ⟨[st (constDecl "a" (.binary (.binary (v (longName 0)) .and (v (longName 1))) .and
                  (el "div" [sattr "className" "a-class"] (some [.text "shown when true"]))))]⟩ }
  , { name := "jsx-await-child"
      prog := ⟨[st (.funcDecl true false (nes "App") []
                  [.return_ (some (el "div" [] (some
                    [.expr (.await (call "theFunctionBeingAwaited" [v (longName 0)]))])))])]⟩ }
  , { name := "jsx-namespaced-attributes"
      prog := ⟨[st (constDecl "a" (.jsx (.element (.namespaced (nes "svg") (nes "path"))
                  [.attr (.namespaced (nes "xlink") (nes "href")) (some (.string "#icon")),
                   .attr (.ident (nes "d")) (some (.string "M0 0 L10 10"))] none)))]⟩ }
  , { name := "jsx-attribute-string-lines"
      prog := ⟨[st (constDecl "a" (el "div" [sattr "title" "two\nlines"] none)),
                st (constDecl "b" (el "div" [sattr "title" "two\nlines", sattr "id" "x"] none))]⟩ }
  , { name := "jsx-one-long-string-attribute"
      prog := ⟨[st (constDecl "a" (el "TheComponentNameHere"
                  [sattr "className" ("a rather long class name which does not fit on the " ++
                    "line at all")] none))]⟩ }
  , { name := "jsx-spread-attributes"
      prog := ⟨[st (constDecl "a" (el "div" [.spread (v (longName 0)),
                  .spread (.object [.keyValue (.ident (nes "id")) (v (longName 1))])] none)),
                st (constDecl "b" (el "div" [.spread (.call (.dot (v "Object") (nes "assign"))
                  [.object [], v (longName 0), v (longName 1)])] none))]⟩ }
  , { name := "jsx-element-as-attribute"
      prog := ⟨[st (constDecl "a" (el "Layout"
                  [eattr "header" (el "Header" [sattr "title" "a title"] none),
                   eattr "footer" (el "Footer" [] (some [.text "the footer text"]))] none))]⟩ }
  , { name := "jsx-fragment-children"
      prog := ⟨[st (constDecl "a" (.jsx (.fragment
                  [elc "TheFirstComponentName" [] none, .text " and ", .expr (v "value"),
                   elc "TheSecondComponentName" [] none])))]⟩ }
  , { name := "jsx-non-ascii-text"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.text "café and naïve"]))),
                st (constDecl "b" (el "p" [] (some [.text "全角の文字が入っている行のテキスト"])))]⟩ }
  , { name := "jsx-long-word-text"
      prog := ⟨[st (constDecl "a" (el "p" [] (some
                  [.text ("supercalifragilisticexpialidociousandthensomemoretomakeitreallylong" ++
                    "indeed")])))]⟩ }
  , { name := "jsx-children-many-expressions"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [.expr (v "first"), .text " ", .expr (v "second"), .text " ",
                   .expr (v "third")])))]⟩ }
    -- a line break written where no whitespace stands between two children
    -- is one a parser reads as whitespace, so the child that follows it is
    -- laid out as it would be after a line break of its own
  , { name := "jsx-break-between-adjacent-children"
      prog := ⟨[st (constDecl "a" (el "li" [sattr "className" "k"] (some
                  [.text "two words",
                   elc "b" [sattr "onClick" "a value whose length just reaches the end of line"]
                     (some [.expr .true_]),
                   .text " padded "]))),
                st (constDecl "b" (el "li" [sattr "className" "k"] (some
                  [.text "two words",
                   elc "b" [sattr "onClick" "a value whose length just fits on the line here"]
                     (some [.expr .true_]),
                   .text " padded "])))]⟩ }
    -- `{...children}`, which keeps its braces on the line of the
    -- expression however long it is
  , { name := "jsx-spread-child"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.spread (v "children"))]))),
                st (constDecl "b" (el "div" [] (some [.text "x", .expr (.spread (v "kids"))]))),
                st (constDecl "c" (el "div" [sattr "className" "a-wrapper"] (some
                  [.expr (.spread (call "theChildrenOfTheComponent"
                    [v (longName 0), v (longName 1)]))])))]⟩ }
    -- the operand of the `...` of a spread child takes the parentheses an
    -- assignment, a comma operator and an element take, and no others
  , { name := "jsx-spread-child-parens"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [.expr (.spread (.binary (v "x") .and (v "y")))]))),
                st (constDecl "b" (el "div" [] (some
                  [.expr (.spread (.ternary (v "a") (v "b") (v "c")))]))),
                st (constDecl "c" (el "div" [] (some
                  [.expr (.spread (.arrow false [] (.expr (v "x"))))]))),
                st (constDecl "d" (el "div" [] (some
                  [.expr (.spread (.assign (v "x") .assign (v "y")))]))),
                st (constDecl "e" (el "div" [] (some
                  [.expr (.spread (.seq (v "a") (v "b")))]))),
                st (constDecl "f" (el "div" [] (some
                  [.expr (.spread (el "span" [] none))])))]⟩ }
    -- the decorators of a class keep the line of the `class` where the
    -- line they stand on is laid out flat, as a spread child is
  , { name := "jsx-spread-child-decorated-class"
      prog := ⟨[st (constDecl "a" (el "p" [eattr "id" (num 1)] (some
                  [.node (.fragment []), .text " ",
                   .expr (.spread (.classExpr [v "logged"] none none
                     [.method [] false .normal (.ident (nes "m")) [] []]))]))),
                st (constDecl "b" (el "p" [eattr "id" (num 1)] (some
                  [.expr (.spread (.classExpr [v "logged"] none none
                     [.method [] false .normal (.ident (nes "m")) [] []]))])))]⟩ }
    -- `{}`, a substitution with nothing in it
  , { name := "jsx-empty-substitution"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.emptyExpr]))),
                st (constDecl "b" (el "div" [] (some [.text "a", .emptyExpr, .text "b"]))),
                st (constDecl "c" (el "div" [] (some [.emptyExpr, .emptyExpr])))]⟩ }
    -- an element written as the value of an attribute with no braces
  , { name := "jsx-element-attribute-value"
      prog := ⟨[st (constDecl "a" (el "Layout"
                  [.attr (jn "header") (some (.node (.element (jn "Header")
                    [sattr "title" "a title", sattr "subtitle" "another title here"] none))),
                   sattr "id" "x"] none)),
                st (constDecl "b" (el "Layout"
                  [.attr (jn "header") (some (.node (.fragment [.text "fragment value"])))] none)),
                st (constDecl "c" (el "Layout"
                  [.attr (jn "header") (some (.node (.element (jn "Header") [] (some
                    [.text "the header contents which are rather long indeed here"]))))] none))]⟩ }
    -- an element which is the body of an arrow function written as an
    -- argument of a call standing directly in a `{ }` keeps lines of its
    -- own; one written deeper inside an argument does not
  , { name := "jsx-arrow-argument-of-call-in-braces"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "onRender" (call "f" [.arrow false [par "props"]
                    (.expr (.jsx (.fragment [.text "x"])))])] none)),
                st (constDecl "b" (el "div" [] (some
                  [.expr (call "f" [.arrow false [par "props"]
                    (.expr (.jsx (.fragment [.text "x"])))])]))),
                st (constDecl "c" (el "div"
                  [eattr "onRender" (.chain (v "handlers")
                    ⟨.dot true (nes "render"),
                     [.call false [.arrow false [par "props"]
                       (.expr (.jsx (.fragment [.text "x"])))]]⟩)] none)),
                st (constDecl "d" (el "div"
                  [eattr "onRender" (call "f"
                    [.ternary (.arrow false [par "props"]
                       (.expr (.jsx (.fragment [.text "x"])))) (v "a") (v "b")])] none))]⟩ }
  , { name := "jsx-whitespace-only-children"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.string " ")]))),
                st (constDecl "b" (el "div" [] (some [.text " "]))),
                st (constDecl "c" (el "div" [] (some
                  [.expr (.string " "), .expr (.string " ")])))]⟩ }
  , { name := "jsx-adjacent-self-closing"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.text "x", elc "br" [] none, .text "y"]))),
                st (constDecl "b" (el "p" [] (some [elc "br" [] none, elc "br" [] none]))),
                st (constDecl "c" (el "p" [] (some [.text "xy", elc "br" [] none])))]⟩ }
  , { name := "jsx-template-children-and-attributes"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.template none
                  "a rather long piece of template text that goes past the line" [])]))),
                st (constDecl "b" (el "div" [eattr "title" (.template none "text "
                  [⟨v (longName 0), " more"⟩]), sattr "id" "x"] none))]⟩ }
  , { name := "jsx-wide-characters"
      prog := ⟨[st (constDecl "a" (el "p" [] (some
                  [.text "全角の文字が並んでいる行 全角の文字が並んでいる行 全角の文字が並んでいる行",
                   elc "br" [] none])))]⟩ }
  , { name := "jsx-nested-fragments"
      prog := ⟨[st (constDecl "a" (.jsx (.fragment
                  [.node (.fragment [.text "inner"]), .text " and ",
                   .node (.fragment [elc "span" [] (some [.text "deep"])])])))]⟩ }
  , { name := "jsx-array-attribute"
      prog := ⟨[st (constDecl "a" (el "List"
                  [eattr "items" (.array [.elem (el "li" [] none), .elem (el "li" [] none)])]
                  none))]⟩ }
  , { name := "jsx-conditional-in-call"
      prog := ⟨[st (.expr (call "render"
                  [.ternary (v (longName 0)) (el "TheFirstComponent" [] none)
                    (el "TheSecondComponent" [] none), v "root"]))]⟩ }
  , { name := "jsx-keyed-list"
      prog := ⟨[st (constDecl "a" (el "ul" [sattr "className" "the-list"] (some
                  [.expr (.call (.dot (v "theItemsOfTheList") (nes "map"))
                    [.arrow false [par "item"] (.expr (el "li"
                      [eattr "key" (.dot (v "item") (nes "id"))]
                      (some [.expr (.dot (v "item") (nes "theNameOfTheItem"))])))])])))]⟩ }
  , { name := "jsx-render-call"
      prog := ⟨[es (call "render" [el "App" [] none,
                  .call (.dot (v "document") (nes "getElementById")) [.string "root"]]),
                es (call "render" [el "TheApplicationComponent"
                  [eattr "store" (v "theApplicationStore")] none,
                  .call (.dot (v "document") (nes "getElementById")) [.string "root"]])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
