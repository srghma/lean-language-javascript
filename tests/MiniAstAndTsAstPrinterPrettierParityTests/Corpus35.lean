import Tests.Corpus34

/-!
# Samples of the layout inside a JSX child laid out flat

The children of a JSX element are laid out as a `fill`, which prints the
ones that fit on the line as if the line held: a line written inside such
a child prints as a space, while a forced line break inside it still ends
the line.  The samples here pin down what prettier does with a decorated
class in that position, which is where the two rules meet: the decorators
of a class *expression* keep the line of the `class`, and the decorators
of a class *declaration*, which prettier groups with the declaration they
stand above, break away from it.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A decorated class declaration with one method. -/
private def decoratedClass (n : String) : MiniStatement :=
  .classDecl [v "logged"] (nes n) none [.method [] false .normal (.ident (nes "m")) [] []]

/-- A class expression whose getter body holds a decorated class
declaration. -/
private def classHoldingDecorated : MiniExpr :=
  .classExpr [] none none
    [.method [] false .get (.ident (nes "index")) [] [decoratedClass "TheClass"]]

/-- The samples. -/
def samples35 : List Sample :=
  [ -- a decorated class declaration written where the line around it is
    -- laid out flat: the decorators still stand on their own line
    { name := "jsx-decorated-class-decl-in-fill"
      prog := ⟨[st (constDecl "element" (el "span" [] (some
                  [.node (.fragment [.expr (.string " "),
                    .expr (.spread classHoldingDecorated)])])))]⟩ }
  , { name := "jsx-decorated-class-decl-in-attribute"
      prog := ⟨[st (constDecl "element" (el "Layout"
                  [eattr "header" (el "span" [.spread (v "item"), sattr "id" "a string"]
                    (some [.node (.fragment [.expr (.string " "),
                      .expr (.spread classHoldingDecorated)])]))]
                  none))]⟩ }
    -- the same class with no run of whitespace beside it: the children
    -- are not a `fill`, and the decorators break as they always do
  , { name := "jsx-decorated-class-decl-alone"
      prog := ⟨[st (constDecl "element" (el "span" [] (some
                  [.expr (.spread classHoldingDecorated)]))),
                st (constDecl "other" (el "span" [] (some
                  [.node (.fragment [.expr (.spread classHoldingDecorated)])])))]⟩ }
    -- a decorated class *expression*, which prettier does not group with
    -- its decorators: in a child laid out flat they keep its line
  , { name := "jsx-decorated-class-expr-in-fill"
      prog := ⟨[st (constDecl "element" (el "div" [] (some
                  [.expr (.string " "),
                   .expr (.spread (.classExpr [v "logged"] none none
                     [.method [] false .normal (.ident (nes "m")) [] []]))])))]⟩ }
    -- the same class expression in the positions where the line breaks
  , { name := "decorated-class-expr-positions"
      prog := ⟨[st (constDecl "a" (.array
                  [.elem (.classExpr [v "logged"] none none [])])),
                es (call "f" [.classExpr [v "logged"] none none []]),
                st (constDecl "b" (.object [.keyValue (.ident (nes "x"))
                  (.classExpr [v "logged"] none none [])])),
                st (constDecl "c" (.classExpr [v "logged", v "sealed"] none none
                  [.method [] false .normal (.ident (nes "m")) [] []]))]⟩ }
    -- a decorated class declaration in the statement positions
  , { name := "decorated-class-decl-positions"
      prog := ⟨[st (decoratedClass "A"),
                st (.funcDecl false false (nes "f") [] [decoratedClass "B"]),
                st (constDecl "o" (.object
                  [.method .get (.ident (nes "g")) [] [decoratedClass "C"]])),
                st (.classDecl [] (nes "D") none
                  [.method [] false .get (.ident (nes "g")) [] [decoratedClass "E"]])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
