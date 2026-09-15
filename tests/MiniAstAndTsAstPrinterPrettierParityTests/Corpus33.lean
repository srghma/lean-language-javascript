import Tests.Corpus32

/-!
# Samples of JSX

The samples here cover the JSX the syntax tree can express: elements,
fragments, attributes of every kind, substitutions, text, and the places
a JSX element may stand in an expression.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A JSX element name. -/
def jn (x : String) : JSXName := .ident (nes x)

/-- A JSX element, as an expression. -/
def el (name : String) (attrs : List MiniJSXAttribute)
    (kids : Option (List MiniJSXChild)) : MiniExpr :=
  .jsx (.element (jn name) attrs kids)

/-- A JSX element, as a child. -/
def elc (name : String) (attrs : List MiniJSXAttribute)
    (kids : Option (List MiniJSXChild)) : MiniJSXChild :=
  .node (.element (jn name) attrs kids)

/-- An attribute whose value is a string. -/
def sattr (name value : String) : MiniJSXAttribute :=
  .attr (jn name) (some (.string value))

/-- An attribute whose value is a substitution. -/
def eattr (name : String) (e : MiniExpr) : MiniJSXAttribute :=
  .attr (jn name) (some (.expr e))

/-- An attribute with no value. -/
def battr (name : String) : MiniJSXAttribute := .attr (jn name) none

/-- The samples. -/
def samples33 : List Sample :=
  [ -- the shapes of an element
    { name := "jsx-self-closing"
      prog := ⟨[st (constDecl "a" (el "div" [] none)),
                st (constDecl "b" (el "Foo" [battr "flag"] none)),
                st (constDecl "c" (el "div" [sattr "className" "row"] none)),
                st (constDecl "d" (.jsx (.element (.member (jn "Foo") (nes "Bar")) [] none))),
                st (constDecl "e" (.jsx (.element (.namespaced (nes "svg") (nes "path")) [] none)))]⟩ }
  , { name := "jsx-empty"
      prog := ⟨[st (constDecl "a" (el "div" [] (some []))),
                st (constDecl "b" (.jsx (.fragment []))),
                st (constDecl "c" (el "div" [sattr "id" "x"] (some [])))]⟩ }
  , { name := "jsx-text"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.text "hello"]))),
                st (constDecl "b" (el "p" [] (some [.text "hello world"]))),
                st (constDecl "c" (el "p" [] (some [.text " padded "])))]⟩ }
  , { name := "jsx-statement"
      prog := ⟨[es (el "div" [] (some [.text "hi"])), es (el "br" [] none)]⟩ }
  , { name := "jsx-children-elements"
      prog := ⟨[st (constDecl "a" (el "ul" [] (some [elc "li" [] none, elc "li" [] none]))),
                st (constDecl "b" (el "div" [] (some [elc "span" [] (some [.text "x"])])))]⟩ }
  , { name := "jsx-fragment"
      prog := ⟨[st (constDecl "a" (.jsx (.fragment [elc "a" [] none, elc "b" [] none]))),
                st (constDecl "b" (.jsx (.fragment [.text "text"])))]⟩ }
  , { name := "jsx-expression-child"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (v "x")]))),
                st (constDecl "b" (el "div" [] (some [.expr (v "x"), .expr (v "y")]))),
                st (constDecl "c" (el "div" [] (some [.text "a", .expr (v "x")])))]⟩ }
  , { name := "jsx-whitespace"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [elc "b" [] (some [.text "x"]), .text " ",
                  elc "i" [] (some [.text "y"])]))),
                st (constDecl "b" (el "div" [] (some [.text "hello ", elc "b" [] (some [.text "w"]),
                  .text " and more"]))),
                st (constDecl "c" (el "div" [] (some [.expr (v "x"), .text " ", .expr (v "y")])))]⟩ }
  , { name := "jsx-attributes"
      prog := ⟨[st (constDecl "a" (el "input" [sattr "type" "text", eattr "value" (v "x"),
                  battr "disabled"] none)),
                st (constDecl "b" (el "div" [.spread (v "props")] none)),
                st (constDecl "c" (el "div" [sattr "title" "say \"hi\"", sattr "alt" "it's"] none))]⟩ }
  , { name := "jsx-attribute-values"
      prog := ⟨[st (constDecl "a" (el "div" [eattr "onClick" (.arrow false [] (.expr (call "f" [])))]
                  none)),
                st (constDecl "b" (el "div" [eattr "style" (.object [.keyValue (.ident (nes "a"))
                  (num 1)])] none)),
                st (constDecl "c" (el "div" [eattr "x" (.binary (v "a") .plus (v "b"))] none)),
                st (constDecl "d" (el "div" [eattr "x" (.ternary (v "a") (v "b") (v "c"))] none))]⟩ }
  , { name := "jsx-long-attributes"
      prog := ⟨[st (constDecl (longName 0)
                  (el "SomeComponent" [sattr "className" "a-long-class-name-here",
                    eattr "onSelect" (v (longName 1)), eattr "value" (v (longName 2))] none))]⟩ }
  , { name := "jsx-long-text"
      prog := ⟨[st (constDecl "a" (el "p" [] (some
                  [.text ("the quick brown fox jumps over the lazy dog and then keeps " ++
                    "running for a while longer")])))]⟩ }
  , { name := "jsx-nested"
      prog := ⟨[st (constDecl "a" (el "div" [sattr "className" "wrapper"] (some
                  [elc "header" [] (some [.text "Title"]),
                   elc "main" [] (some [elc "p" [] (some [.text "Body text here"]),
                                        elc "img" [sattr "src" "a.png"] none]),
                   elc "footer" [] (some [.expr (v "year")])])))]⟩ }
  , { name := "jsx-in-return"
      prog := ⟨[st (.funcDecl false false (nes "App") []
                  [.return_ (some (el "div" [sattr "className" "app"]
                    (some [elc "span" [] (some [.text "hello"])])))]),
                st (.funcDecl false false (nes "Short") [] [.return_ (some (el "br" [] none))])]⟩ }
  , { name := "jsx-in-arrow"
      prog := ⟨[st (constDecl "A" (.arrow false [] (.expr (el "div" [] (some [.text "x"]))))),
                st (constDecl "B" (.arrow false [par "props"]
                  (.expr (el "div" [eattr "id" (v "props")] (some [.text "some text here"])))))]⟩ }
  , { name := "jsx-map"
      prog := ⟨[st (constDecl "a" (el "ul" [] (some
                  [.expr (.call (.dot (v "items") (nes "map"))
                    [.arrow false [par "item"] (.expr (el "li" [eattr "key" (v "item")]
                      (some [.expr (v "item")])))])])))]⟩ }
  , { name := "jsx-map-short"
      prog := ⟨[st (constDecl "a" (el "ul" [] (some
                  [.expr (.call (.dot (v "xs") (nes "map"))
                    [.arrow false [par "x"] (.expr (el "li" [] none))])])))]⟩ }
  , { name := "jsx-conditional"
      prog := ⟨[st (constDecl "a" (.ternary (v "ok") (el "Yes" [] none) (el "No" [] none))),
                st (constDecl "b" (.ternary (v "ok") (el "Yes" [] none) .null)),
                st (constDecl "c" (.binary (v "ok") .and (el "Yes" [] none)))]⟩ }
  , { name := "jsx-conditional-long"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (v (longName 1))
                    (el "SomeComponent" [eattr "value" (v (longName 2))] none)
                    (el "OtherComponent" [eattr "value" (v (longName 3))] none)))]⟩ }
  , { name := "jsx-logical-long"
      prog := ⟨[st (constDecl (longName 0)
                  (.binary (v (longName 1)) .and
                    (el "SomeComponent" [eattr "value" (v (longName 2)),
                      eattr "other" (v (longName 3))] none)))]⟩ }
  , { name := "jsx-as-argument"
      prog := ⟨[es (call "render" [el "div" [] (some [.text "x"]), v "root"]),
                es (call "render" [el "div" [sattr "className" "a-long-class-name"]
                  (some [elc "span" [] (some [.text "a fair amount of text here"])]), v "root"])]⟩ }
  , { name := "jsx-in-array"
      prog := ⟨[st (constDecl "a" (.array [.elem (el "div" [] none), .elem (el "span" [] none)]))]⟩ }
  , { name := "jsx-in-object"
      prog := ⟨[st (constDecl "a" (.object [.keyValue (.ident (nes "icon")) (el "Icon" [] none)]))]⟩ }
  , { name := "jsx-nested-expression"
      prog := ⟨[st (constDecl "a" (el "div" [] (some
                  [.expr (.ternary (v "ok") (el "Yes" [] none) (el "No" [] none))]))),
                st (constDecl "b" (el "div" [] (some
                  [.expr (.binary (v "ok") .and (el "Yes" [] none))])))]⟩ }
  , { name := "jsx-template-child"
      prog := ⟨[st (constDecl "a" (el "div" [] (some [.expr (.template none "text" [])])))]⟩ }
  , { name := "jsx-entities"
      prog := ⟨[st (constDecl "a" (el "p" [] (some [.text "a < b & c > d"]))),
                st (constDecl "b" (el "p" [] (some [.text "{braces}"])))]⟩ }
  , { name := "jsx-deep"
      prog := ⟨[st (.funcDecl false false (nes "App") []
                  [.return_ (some (el "div" [sattr "className" "container"] (some
                    [elc "Header" [eattr "title" (.string "Hello"), battr "compact"] none,
                     elc "ul" [sattr "className" "list"] (some
                       [.expr (.call (.dot (v "items") (nes "map"))
                         [.arrow false [par "item"]
                           (.expr (el "li" [eattr "key" (.dot (v "item") (nes "id"))]
                             (some [.expr (.dot (v "item") (nes "name"))])))])]),
                     elc "footer" [] (some [.text "Copyright ", .expr (v "year")])])))])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
