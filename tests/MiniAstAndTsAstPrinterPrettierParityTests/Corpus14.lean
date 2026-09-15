import Tests.Corpus13

/-!
# Samples of template literals, of regular expressions, of clauses and of patterns

Programs which exercise the parts of the tree the other samples reach
less often: the text of a template literal, a regular expression literal
where the parser would otherwise read a division, an `import` or an
`export` clause long enough to break, a destructuring pattern which
assigns to something that already exists, and a handful of statements of
shapes the corpus did not hold.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A regular expression literal. -/
def regexLit (src : String) (flags : RegExpFlags := {}) : MiniExpr :=
  .regex ⟨nes src, flags⟩

/-- The samples. -/
def samples14 : List Sample :=
  -- template literals
  [ { name := "template-newline"
      prog := ⟨[es (.template none "a\nb" [⟨v "x", "\nc"⟩])]⟩ }
  , { name := "template-backslash"
      prog := ⟨[es (.template none "a\\n" [⟨v "x", ""⟩])]⟩ }
  , { name := "template-long"
      prog := ⟨[st (constDecl (longName 0)
                  (.template none "the value is " [⟨.binary (v (longName 1)) .plus
                    (v (longName 2)), " indeed"⟩]))]⟩ }
  , { name := "template-member"
      prog := ⟨[es (.dot (.template none "a" []) (nes "length"))]⟩ }
  , { name := "template-tagged-chain"
      prog := ⟨[es (.template (some (.dot (v "String") (nes "raw"))) "a" [⟨v "b", "c"⟩])]⟩ }
  -- regular expressions
  , { name := "regex-flags"
      prog := ⟨[es (regexLit "^[a-z]+$" { global := true, ignoreCase := true, sticky := true })]⟩ }
  , { name := "regex-statement", prog := ⟨[es (regexLit "ab+c")]⟩ }
  , { name := "regex-divide", prog := ⟨[es (.binary (regexLit "a") .divide (v "b"))]⟩ }
  , { name := "regex-member", prog := ⟨[es (.dot (regexLit "a") (nes "source"))]⟩ }
  , { name := "regex-slash", prog := ⟨[es (regexLit "a\\/b")]⟩ }
  -- imports and exports that break
  , { name := "import-long"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes (longName 0)))
                  none (some [⟨nes (longName 1), none⟩, ⟨nes (longName 2), some (nes "x")⟩,
                    ⟨nes (longName 3), none⟩]) (nes "the-module-with-a-long-name")))]⟩ }
  , { name := "import-attrs-long"
      prog := ⟨[.importDecl (.bare (nes "the-module-with-a-rather-long-name-here")
                  [⟨"type", "json"⟩, ⟨"lazy", "true"⟩])]⟩ }
  , { name := "export-long"
      prog := ⟨[.exportDecl (.fromClause [⟨nes (longName 0), some (nes (longName 1))⟩,
                  ⟨nes (longName 2), none⟩] (nes "the-module-with-a-long-name") [])]⟩ }
  , { name := "export-empty", prog := ⟨[.exportDecl (.locals [])]⟩ }
  , { name := "import-empty-named"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none (some []) (nes "m")))]⟩ }
  -- patterns
  , { name := "pattern-target"
      prog := ⟨[es (.assignPattern (.array [.elem (.target (.dot (v "o") (nes "p")))])
                  (v "xs"))]⟩ }
  , { name := "pattern-target-forof"
      prog := ⟨[st (.forOf false (.pattern (.target (.dot (v "o") (nes "p")))) (v "xs")
                  (.block []))]⟩ }
  , { name := "pattern-long-object"
      prog := ⟨[st (.decl .const ⟨⟨.object [⟨.ident (nes (longName 0)), .ident (nes (longName 1))⟩,
                    ⟨.ident (nes (longName 2)), .ident (nes (longName 3))⟩] none,
                  some (v "source")⟩, []⟩)]⟩ }
  , { name := "pattern-catch"
      prog := ⟨[st (.try_ [] (.catches ⟨⟨.object [⟨.ident (nes "message"), .ident (nes "message")⟩]
                  none, none, []⟩, []⟩ .none))]⟩ }
  , { name := "pattern-default-long"
      prog := ⟨[st (.funcDecl false false (nes "f")
                  [.plain (.withDefault (p (longName 0)) (v (longName 1))),
                   .plain (.withDefault (p (longName 2)) (v (longName 3)))] [])]⟩ }
  -- miscellaneous statements
  , { name := "empty-program", prog := ⟨[]⟩ }
  , { name := "empty-class", prog := ⟨[st (.classDecl [] (nes "A") none [])]⟩ }
  , { name := "labelled-nested"
      prog := ⟨[st (.labelled (nes "outer") (.labelled (nes "inner")
                  (.while_ (v "a") (.block [.break_ (some (nes "outer"))]))))]⟩ }
  , { name := "do-while-non-block"
      prog := ⟨[st (.doWhile (.expr (call "f" [v "a"])) (v "cond"))]⟩ }
  , { name := "switch-long-discriminant"
      prog := ⟨[st (.switch (.binary (v (longName 0)) .plus (v (longName 1)))
                  [.case (num 1) [.break_ none]])]⟩ }
  , { name := "class-heritage-long"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName") (some (call (longName 0)
                  [v (longName 1), v (longName 2)])) [])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
