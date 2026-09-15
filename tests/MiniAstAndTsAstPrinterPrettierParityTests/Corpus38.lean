import Tests.Corpus37

/-!
# JSX in the remaining positions of the tree

The samples of `Tests.Corpus33` to `Tests.Corpus37` cover the shapes a JSX
element takes and the places a React program writes one.  The samples here
cover the rest of the positions an element may stand in — the head of a
statement, a class member, a default value, an operand of the comma
operator, the object of a member access, the tag of a template literal, a
decorator, a computed key — together with the values an attribute may take
and the runs of whitespace between children which decide where a `{" "}`
has to be written.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An element wide enough that it has to break. -/
private def wideEl : MiniExpr :=
  el "div" [sattr "className" "a-very-long-class-name-here", eattr "onClick" (v "handler")]
    (some [.text "some text that is long enough to force the element to break apart"])

/-- The samples. -/
def samples38 : List Sample :=
  [ -- an element in the head of a statement, which takes the parentheses
    -- a leftmost `<` asks for
    { name := "jsx-throw"
      prog := ⟨[st (.throw wideEl)]⟩ }
  , { name := "jsx-switch-and-case"
      prog := ⟨[st (.switch (el "div" [] none) [.case (el "span" [] none) [.break_ none]])]⟩ }
  , { name := "jsx-if-and-while"
      prog := ⟨[st (.if_ (el "div" [] none) (.block [.debugger]) none),
                st (.while_ wideEl (.block []))]⟩ }
  , { name := "jsx-do-while"
      prog := ⟨[st (.doWhile (.block [.expr (el "div" [] none)]) (el "span" [] none))]⟩ }
  , { name := "jsx-for-head"
      prog := ⟨[st (.for_ (.expr (el "div" [] none)) (some (el "span" [] none))
                  (some (el "p" [] none)) (.block [])),
                st (.forOf false (.decl .const (p "x")) (el "div" [] none) (.block [])),
                st (constDecl "c" (.binary (.string "k") .inOp (el "div" [] none)))]⟩ }
    -- an element read through, called on, or written as the tag of a
    -- template literal, all of which need the parentheses
  , { name := "jsx-member-and-tag"
      prog := ⟨[st (constDecl "a" (.dot (el "div" [] none) (nes "props"))),
                st (constDecl "b" (.call (.dot wideEl (nes "toString")) [])),
                st (constDecl "c" (.chain (el "div" [] none) ⟨.dot true (nes "props"), []⟩)),
                st (constDecl "d" (.template (some (el "div" [] none)) "x" []))]⟩ }
  , { name := "jsx-class-member"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [] false false (.ident (nes "view")) (some wideEl),
                   .method [] true .get (.ident (nes "icon")) [] [.return_ (some wideEl)]])]⟩ }
  , { name := "jsx-decorator-and-heritage"
      prog := ⟨[st (.classDecl [call "withView" [el "div" [] (some [.text "hi"])]] (nes "C")
                  (some (el "div" [] none)) [])]⟩ }
  , { name := "jsx-default-parameter"
      prog := ⟨[st (.funcDecl false false (nes "f")
                  [.plain (.withDefault (p "node") wideEl)] [.return_ (some (v "node"))])]⟩ }
  , { name := "jsx-comma-and-unary"
      prog := ⟨[es (.seq (el "div" [] none) (el "span" [] none)),
                st (constDecl "a" (.unary .typeof (el "div" [] none))),
                st (constDecl "b" (.unary .void (el "div" [] none)))]⟩ }
  , { name := "jsx-assignment-and-new"
      prog := ⟨[es (.assign (v "aVeryLongTargetIdentifierName") .assign wideEl),
                st (constDecl "a" (.new (v "Wrapper") [el "div" [] (some [.text "hi"])]))]⟩ }
  , { name := "jsx-computed-key-and-index"
      prog := ⟨[st (constDecl "a" (.object [.keyValue (.computed (el "div" [] none)) (num 1)])),
                st (constDecl "b" (.index (v "o") (el "div" [] none)))]⟩ }
    -- the values an attribute may take, each of which is laid out as it is
    -- anywhere else
  , { name := "jsx-attribute-arrow-value"
      prog := ⟨[st (constDecl "a" (el "button"
                  [eattr "onClick" (.arrow false [] (.expr (call "doTheThing" [v "event"]))),
                   eattr "onHover" (.arrow false [par "e"] (.block [.expr (call "log" [v "e"])]))]
                  none))]⟩ }
  , { name := "jsx-attribute-object-value"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "style" (.object [.keyValue (.ident (nes "color")) (.string "red"),
                    .keyValue (.ident (nes "backgroundColor")) (.string "blue"),
                    .keyValue (.ident (nes "fontWeight")) (.string "bold")])] none))]⟩ }
  , { name := "jsx-attribute-template-value"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "className" (.template none "row " [⟨v "extra", " end"⟩])] none))]⟩ }
  , { name := "jsx-attribute-call-value"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "data" (call "computeTheValueOfTheAttribute"
                     [v "first", v "second", v "third", v "fourth"])] none))]⟩ }
  , { name := "jsx-attribute-conditional-value"
      prog := ⟨[st (constDecl "a" (el "div"
                  [eattr "className" (.ternary (v "isActiveAndSelected")
                     (.string "the-active-class-name") (.string "the-inactive-class-name"))] none)),
                st (constDecl "b" (el "Modal"
                  [eattr "footer" (.ternary (v "showFooter")
                     (el "Footer" [sattr "kind" "primary"] none) .null)] none))]⟩ }
  , { name := "jsx-attribute-await-value"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.return_ (some (el "div" [eattr "value" (.await (call "load" []))] none))])]⟩ }
  , { name := "jsx-attribute-element-value-long"
      prog := ⟨[st (constDecl "a" (el "Layout"
                  [.attr (jn "header") (some (.node (.element (jn "TheVeryLongHeaderComponent")
                     [sattr "title" "the title of the page"] none)))] none))]⟩ }
  , { name := "jsx-attribute-string-long"
      prog := ⟨[st (constDecl "a" (el "div"
                  [sattr "title"
                    "a string value that is much much longer than the line width allows"]
                  none))]⟩ }
  , { name := "jsx-many-attributes-and-children"
      prog := ⟨[st (constDecl "a" (el "section"
                  [sattr "id" "main", sattr "className" "a-long-class-name-goes-here",
                   eattr "onClick" (v "handleTheClickEvent"), battr "hidden"]
                  (some [elc "p" [] (some [.text "the body of the section"])])))]⟩ }
    -- the runs of whitespace between children, which are written `{" "}`
    -- where the line breaks
  , { name := "jsx-whitespace-between-elements"
      prog := ⟨[st (constDecl "a" (el "div" []
                  (some [elc "span" [] (some [.text "first"]), .text " ",
                         elc "span" [] (some [.text "second"]), .text "   ",
                         elc "span" [] (some [.text "third"])]))),
                st (constDecl "aLongName" (el "div" []
                  (some [elc "span" [] (some [.text "the first item of the row"]), .text " ",
                         elc "span" [] (some [.text "the second item of the row"]), .text " ",
                         elc "span" [] (some [.text "the third item of the row"])])))]⟩ }
  , { name := "jsx-text-around-substitution"
      prog := ⟨[st (constDecl "a" (el "p" []
                  (some [.text "a long run of words that fills the line up to here ",
                         .expr (v "value"), .text " and some words after it as well"]))),
                st (constDecl "b" (el "div" []
                  (some [.text "line one\n", .expr (v "value"), .text "\nline two"])))]⟩ }
  , { name := "jsx-entities-in-a-fill"
      prog := ⟨[st (constDecl "a" (el "p" []
                  (some [.text "the value of a > b is {maybe} true & the rest is false here"]))),
                st (constDecl "b" (el "div" [] (some [.text "a\u00a0b"]))),
                st (constDecl "c" (el "div" [sattr "title" "a\u00a0b"] none))]⟩ }
  , { name := "jsx-whitespace-only-text"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.text "\n\n"]))),
                st (constDecl "b" (el "div" [] (some [.text "   "]))),
                st (constDecl "c" (el "div" [] (some [.text "\n", .text " ", .text "\n"]))),
                st (constDecl "d" (el "div" []
                  (some [.expr (.string "  "), elc "b" [] none, .expr (.string " ")]))),
                st (constDecl "e" (el "div" []
                  (some [.text "x", .expr (.string " "), .text "y"])))]⟩ }
  , { name := "jsx-fill-of-wide-and-long-words"
      prog := ⟨[st (constDecl "a" (el "p" []
                  (some [.text "全角の文字がここにあります ",
                         .text "aVeryLongWordWithoutAnySpacesInItAtAllWhatsoeverIndeed ",
                         .text "終わり"])))]⟩ }
  , { name := "jsx-long-member-name"
      prog := ⟨[st (constDecl "a" (.jsx (.element
                  (.member (.member (jn "TheOuterNamespace") (nes "TheInnerNamespace"))
                    (nes "TheComponentName")) [] (some [.text "text inside"]))))]⟩ }
  , { name := "jsx-nested-elements-breaking"
      prog := ⟨[st (constDecl "a" (el "div" [sattr "className" "outer"]
                  (some [elc "div" [sattr "className" "middle"]
                    (some [elc "div" [sattr "className" "inner"]
                      (some [elc "span" [eattr "onClick" (v "onClick")]
                        (some [.text "the deepest text of them all"])])])])))]⟩ }
  , { name := "jsx-nested-conditional"
      prog := ⟨[st (constDecl "a" (.ternary (v "cond")
                  (el "div" [] (some [.text "the first branch of the conditional"]))
                  (.ternary (v "other")
                    (el "span" [] (some [.text "the second branch"]))
                    (el "p" [] (some [.text "the third branch here"])))))]⟩ }
  , { name := "jsx-in-template-substitution"
      prog := ⟨[st (constDecl "a" (.template none "x" [⟨el "div" [] (some [.text "hi"]), "y"⟩]))]⟩ }
    -- an element written as the callee of a call, or of a `new`, keeps the
    -- parentheses a `<` asks for around it as it stands: they are not the
    -- parentheses an element takes lines of its own between, which is what
    -- the same element written as the tag of a template literal, or read
    -- through a member access, does take
  , { name := "jsx-callee"
      prog := ⟨[es (.call wideEl [v "argument"]),
                es (.call (el "div" [] none) [v "a"]),
                st (constDecl "b" (.call wideEl [v "argument"])),
                es (.assign (v "x") .assign (.call wideEl [v "argument"]))]⟩ }
  , { name := "jsx-new-callee"
      prog := ⟨[es (.new wideEl []), es (.new (el "div" [] none) [v "a"])]⟩ }
  , { name := "jsx-callee-against-tag-and-member"
      prog := ⟨[st (constDecl "a" (.template (some wideEl) "tagged" [])),
                st (constDecl "b" (.dot wideEl (nes "props"))),
                st (constDecl "c" (.index wideEl (v "key"))),
                st (constDecl "d" (.chain wideEl ⟨.dot true (nes "props"), []⟩))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
