import Tests.Corpus20

/-!
# Samples of widths, of text that spans lines, and of the class header

The samples here exercise the number of columns a character takes, the
layout around a template literal whose text spans lines, the line the
`extends` of a class stands on, and the import attributes prettier keeps
on the line of the import.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An array of `n` copies of the string `s`. -/
def stringArray (n : Nat) (s : String) : MiniExpr :=
  .array ((List.range n).map fun _ => .elem (.string s))

/-- The samples. -/
def samples21 : List Sample :=
  [ -- the width of a character
    { name := "width-cjk"
      prog := ⟨[es (stringArray 12 "日本語のテキスト")]⟩ }
  , { name := "width-emoji"
      prog := ⟨[es (stringArray 14 "😀😀😀")]⟩ }
  , { name := "width-combining"
      prog := ⟨[es (stringArray 14 "éeée\u0301e\u0301")]⟩ }
  , { name := "width-flag"
      prog := ⟨[es (stringArray 10 "🇯🇵 flag")]⟩ }
  , { name := "width-halfwidth-kana"
      prog := ⟨[es (stringArray 12 "ｱｲｳｴｵ")]⟩ }
  , { name := "width-in-identifier"
      prog := ⟨[st (constDecl "日本語の変数名前" (call "f" [v (longName 0), v (longName 1)]))]⟩ }
  , { name := "width-in-template"
      prog := ⟨[es (call "f" [.template none "日本語のテキストがここにある、とても長い" [],
                  v (longName 0)])]⟩ }
    -- a template literal whose text spans lines
  , { name := "multiline-template-in-pattern-assign"
      prog := ⟨[st (nestBlocks 3 (.decl .const ⟨⟨.object
                  [⟨.ident (nes (longName 0)), p "handler"⟩] (some (p "rest")),
                  some (.template none "two\nlines" [])⟩, []⟩))]⟩ }
  , { name := "multiline-template-in-call"
      prog := ⟨[es (call "theFunctionWithALongName"
                  [v (longName 0), .template none "first\nsecond" []])]⟩ }
  , { name := "multiline-template-in-ternary"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (.template none "first\nsecond" []) (v (longName 1))
                    (v (longName 2))))]⟩ }
  , { name := "multiline-template-in-object"
      prog := ⟨[es (.object [kv "text" (.template none "first\nsecond" []),
                  kv "other" (v (longName 0))])]⟩ }
  , { name := "multiline-template-in-member-chain"
      prog := ⟨[es (methodCall (methodCall (.template none "first\nsecond" []) "trim" [])
                  "split" [.string "\n"])]⟩ }
  , { name := "multiline-template-in-arrow-body"
      prog := ⟨[es (.arrow false [par "item"] (.expr (.template none "a\nb" [⟨v "item", ""⟩])))]⟩ }
  , { name := "multiline-template-in-return"
      prog := ⟨[st (.funcDecl false false (nes "f") []
                  [.return_ (some (.template none "a\nb" []))])]⟩ }
  , { name := "multiline-template-in-binary"
      prog := ⟨[st (constDecl (longName 0)
                  (.binary (.template none "a\nb" []) .plus (v (longName 1))))]⟩ }
  , { name := "multiline-template-tagged"
      prog := ⟨[st (constDecl (longName 0)
                  (.template (some (v "styled")) "color: red;\nmargin: 0;" []))]⟩ }
    -- the line the `extends` of a class stands on
  , { name := "class-heritage-member-long"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName")
                  (some (.dot (v (longName 0)) (nes (longName 1))))
                  [.field [] false false (.ident (nes "a")) (some (num 1))])]⟩ }
  , { name := "class-heritage-member-long-empty-body"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName")
                  (some (.dot (v (longName 0)) (nes (longName 1)))) [])]⟩ }
  , { name := "class-heritage-index-long"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName")
                  (some (.index (.dot (v (longName 0)) (nes (longName 1))) (v "key")))
                  [.field [] false false (.ident (nes "a")) (some (num 1))])]⟩ }
  , { name := "class-heritage-optional-long"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName")
                  (some (.chain (v (longName 0)) ⟨.dot true (nes (longName 1)), []⟩))
                  [.field [] false false (.ident (nes "a")) (some (num 1))])]⟩ }
  , { name := "class-heritage-call-long"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName")
                  (some (.call (.dot (v (longName 0)) (nes (longName 1))) []))
                  [.field [] false false (.ident (nes "a")) (some (num 1))])]⟩ }
  , { name := "class-heritage-name-long"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongNameHereOk")
                  (some (v (longName 0 ++ "AndMoreTextHereToGoOverTheLimit")))
                  [.field [] false false (.ident (nes "a")) (some (num 1))])]⟩ }
  , { name := "class-heritage-member-short"
      prog := ⟨[st (.classDecl [] (nes "A") (some (.dot (v "b") (nes "c")))
                  [.field [] false false (.ident (nes "a")) (some (num 1))])]⟩ }
  , { name := "class-heritage-member-of-declarator"
      prog := ⟨[st (constDecl "x" (.classExpr [] (some (nes "TheClassWithALongName"))
                  (some (.dot (v (longName 0)) (nes "aLongIdentifierNumberOn")))
                  [.field [] false false (.ident (nes "a")) (some (num 1))]))]⟩ }
  , { name := "class-heritage-member-of-assignment"
      prog := ⟨[es (.assign (v "x") .assign
                  (.classExpr [] (some (nes "TheClassWithALongName"))
                    (some (.dot (v (longName 0)) (nes (longName 1))))
                    [.field [] false false (.ident (nes "a")) (some (num 1))]))]⟩ }
  , { name := "class-heritage-anonymous-long"
      prog := ⟨[es (call "f" [.classExpr [] none
                  (some (.dot (v (longName 0)) (nes (longName 1))))
                  [.field [] false false (.ident (nes "a")) (some (num 1))]])]⟩ }
  , { name := "class-heritage-exported-long"
      prog := ⟨[.exportDecl (.defaultExpr (.classExpr [] (some (nes "TheClassWithALongName"))
                  (some (.dot (v (longName 0)) (nes "aLongIdentifierName")))
                  [.field [] false false (.ident (nes "a")) (some (num 1))]))]⟩ }
    -- import attributes
  , { name := "import-attributes-type-long"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes (longName 0))) none none
                  (nes "a-module-with-a-rather-long-name") [⟨"type", "json"⟩]))]⟩ }
  , { name := "import-attributes-several"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes (longName 0))) none none
                  (nes "a-module-with-a-long-name")
                  [⟨"type", "json"⟩, ⟨"other", "value"⟩, ⟨"third", "something"⟩]))]⟩ }
  , { name := "import-attributes-not-type"
      prog := ⟨[.importDecl (.bare (nes "a-module-with-a-rather-long-name-here-and-more")
                  [⟨"other", "a rather long attribute value"⟩])]⟩ }
  , { name := "export-attributes-type-long"
      prog := ⟨[.exportDecl (.all (some (nes "ns"))
                  (nes "a-module-with-a-rather-long-name-here-and-more")
                  [⟨"type", "json"⟩])]⟩ }
    -- long lists at the boundary
  , { name := "arguments-at-boundary"
      prog := ⟨[es (call "theFunctionName" [v "aaaaaaaaaaaaaaaa", v "bbbbbbbbbbbbbbbb",
                  v "cccccccccccccccc", v "dddddddd"])]⟩ }
  , { name := "export-from-long"
      prog := ⟨[.exportDecl (.fromClause ((List.range 4).map fun k =>
                  ⟨nes (longName k), none⟩) (nes "the-module") [])]⟩ }
  , { name := "class-many-members"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithALongName")
                  (some (.dot (v (longName 0)) (nes (longName 1))))
                  [.field [] false false (.ident (nes "a")) (some (num 1)),
                   .method [] false .normal (.ident (nes (longName 2)))
                     [par (longName 3), par (longName 4)] [.return_ (some (num 1))]])]⟩ }
  , { name := "switch-case-long-tests"
      prog := ⟨[st (.switch (v (longName 0))
                  [.case (.binary (v (longName 1)) .plus (v (longName 2)))
                     [.expr (call "f" []), .break_ none],
                   .case (.template none "a\nb" []) [],
                   .default [.throw (v "error")]])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
