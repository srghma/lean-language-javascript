import Tests.Corpus22

/-!
# Samples of the layout of an assignment whose right hand side is a call

Prettier breaks the line after the `=` when the right hand side is a chain
of member accesses and calls which it would gain little by breaking: one
whose calls take no argument, or one short argument.  An update, `--x`, is
not one of those short arguments, while a short template literal of no
substitution is.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A declaration of `name`, whose value is a call of `f` on `args`. -/
def declOfCall (name f : String) (args : List MiniExpr) : MiniStatement :=
  constDecl name (call f args)

/-- The samples. -/
def samples23 : List Sample :=
  [ { name := "assign-call-of-template"
      prog := ⟨[st (declOfCall "aLongIdentifierNameNumberZeroHere"
                  "theHandlerNameThatIsLongEnough" [.template none "abc" []]),
                st (declOfCall "aLongIdentifierNameNumberZeroHereX"
                  "theHandlerNameThatIsLongEnough" [.template none "abc" []])]⟩ }
  , { name := "assign-call-of-template-substitution"
      prog := ⟨[st (declOfCall "aLongIdentifierNameNumberZeroHereX"
                  "theHandlerNameThatIsLongEnou" [.template none "a" [⟨v "b", "c"⟩]])]⟩ }
  , { name := "assign-call-of-long-template"
      prog := ⟨[st (declOfCall "aLongIdentifierNameNumberZeroHereX"
                  "theHandlerNameThatIsLongEn"
                  [.template none "abcdefghijklmnopqrstuvwxyz" []])]⟩ }
  , { name := "assign-call-of-update"
      prog := ⟨[st (declOfCall "aLongIdentifierNameNumberZeroHereX"
                  "theHandlerNameThatIsLongEnough" [.unary .preDecr (v "it")]),
                st (declOfCall "aLongIdentifierNameNumberZeroHereXY"
                  "theHandlerNameThatIsLongEnough" [.unary .preDecr (v "it")])]⟩ }
  , { name := "assign-call-of-negation"
      prog := ⟨[st (declOfCall "aLongIdentifierNameNumberZeroHereXY"
                  "theHandlerNameThatIsLongEnough" [.unary .not (v "it")]),
                st (declOfCall "aLongIdentifierNameNumberZeroHereXYZ"
                  "theHandlerNameThatIsLongEnough" [.unary .not (v "it")])]⟩ }
  , { name := "assign-call-of-postfix-update"
      prog := ⟨[st (declOfCall "aLongIdentifierNameNumberZeroHereXY"
                  "theHandlerNameThatIsLongEnough" [.postfix (v "it") .incr])]⟩ }
  , { name := "pattern-assign-call-of-update"
      prog := ⟨[st (nestBlocks 4 (.expr (.assignPattern
                  (.object [⟨.ident (nes (longName 0)), p (longName 0)⟩] (some (p "target9")))
                  (call "theHandlerName" [.unary .preDecr (v "iterator")]))))]⟩ }
  , { name := "pattern-assign-call-of-name"
      prog := ⟨[es (.assignPattern
                  (.object [⟨.ident (nes (longName 0)), p (longName 0)⟩] (some (p "target9")))
                  (call "theHandlerNameLongerHere" [v "item"]))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
