import Tests.Corpus27

/-!
# Samples of the module clauses, of wide characters and of the metas

The samples here cover the clauses of an `import` and of an `export`,
including the empty list of names, which is written out only when it is
the whole clause; the strings whose characters are wider than one column,
which the layout has to measure; and `super`, `new.target`, `import.meta`
and the private names of a class.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples. -/
def samples28 : List Sample :=
  [ { name := "export-default-arrow"
      prog := ⟨[.exportDecl (.defaultExpr (.arrow false [par "item"] (.expr (num 1))))]⟩ }
  , { name := "export-default-object"
      prog := ⟨[.exportDecl (.defaultExpr (.object [.keyValue (.ident (nes "theKeyName"))
                  (v "aVeryVeryLongIdentifierNameHere")]))]⟩ }
  , { name := "export-default-decorated-class"
      prog := ⟨[.exportDecl (.defaultExpr (.classExpr [v "logged"] none none []))]⟩ }
  , { name := "export-default-logical"
      prog := ⟨[.exportDecl (.defaultExpr (.binary (v "aVeryVeryLongIdentifierNameHere") .or
                  (v "theVeryLongNameForAVariableHere")))]⟩ }
  , { name := "export-as-default"
      prog := ⟨[st (constDecl "theLocalName" (num 1)),
                .exportDecl (.locals [⟨nes "theLocalName", some (nes "default")⟩])]⟩ }
  , -- an empty list of names, which stands on its own but not beside a
    -- default import
    { name := "import-empty-names"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none (some [])
                  (nes "a/module/path"))),
                .importDecl (.clause (MiniImportClause.mk! (some (nes "theDefaultName")) none
                  (some []) (nes "another/module/path"))),
                .exportDecl (.fromClause [] (nes "a/third/module/path") []),
                .exportDecl (.locals [])]⟩ }
  , { name := "import-default-and-namespace"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes "theDefaultName"))
                  (some (nes "theNamespaceName")) none (nes "a/module/path")))]⟩ }
  , -- strings whose characters take more than one column
    { name := "wide-strings"
      prog := ⟨[st (constDecl "theValueName" (.array
                  [.elem (.string "日本語のテキストがここにあります"),
                   .elem (.string "もっと日本語のテキスト")]))]⟩ }
  , { name := "emoji-strings"
      prog := ⟨[st (constDecl "theValueName" (.array
                  [.elem (.string "🙂🙂🙂🙂🙂🙂🙂🙂🙂🙂"),
                   .elem (.string "a string of some length here"),
                   .elem (.string "another string of some length")]))]⟩ }
  , { name := "super-in-arrow"
      prog := ⟨[st (.classDecl [] (nes "TheClass") (some (v "TheBase"))
                  [.method [] false .normal (.ident (nes "theMethodName")) []
                    [.expr (.arrow false [] (.expr (.call (.superDot (nes "theBaseMethod")) [])))]])]⟩ }
  , { name := "new-target-and-import-meta"
      prog := ⟨[st (.funcDecl false false (nes "theFunctionName") []
                  [.if_ (.binary .newTarget .strictEq (v "undefined")) (.block []) none]),
                es (.call (.dot (.dot .importMeta (nes "url")) (nes "toString")) [])]⟩ }
  , { name := "optional-private-access"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.field [] false false (.private_ (nes "x")) (some (num 1)),
                   .method [] false .normal (.ident (nes "theMethodName")) [par "other"]
                     [.return_ (some (.chain (v "other") ⟨.privateDot true (nes "x"), []⟩)),
                      .expr (.binary (.privateName (nes "x")) .inOp (v "other"))]])]⟩ }
  , { name := "static-block-long"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.staticBlock [.expr (call "computeTheValue"
                    [v "aVeryVeryLongIdentifierNameHere", v "theIteratorOfTheList"])]])]⟩ }
  , { name := "bigint-literals"
      prog := ⟨[st (constDecl "theValueName" (.number (.bigint .decimal 9007199254740993))),
                es (.object [.keyValue (.ident (nes "theKeyName"))
                  (.number (.bigint .hexadecimal 255))]),
                es (.binary (.number (.bigint .decimal 2)) .times
                  (.number (.bigint .decimal 3)))]⟩ }
  , { name := "accessor-bodies"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.method [] false .get (.ident (nes "theGetterName")) []
                    [.return_ (some (.binary (v "aVeryVeryLongIdentifierNameHere") .plus
                      (v "theIteratorOfTheList")))],
                   .method [] false .set (.ident (nes "theSetterName"))
                     [.plain (.withDefault (p "theValueName") (num 1))] []])]⟩ }
  , -- the wrapper an Angular test is written with, inside the test call
    -- it belongs to, keeps its argument on the line of the call
    { name := "angular-test-wrapper"
      prog := ⟨[st (.decl .const ⟨⟨.array [.elem (.withDefault (p "theBoundName") .true_)],
                  some (call "beforeEach" [call "inject" [.arrow false []
                    (.block [.return_ (some (num 1)),
                             .expr (call "computeTheValue" [v "item"])])]])⟩, []⟩),
                es (.template (some (v "theCollection")) "text "
                  [⟨call "beforeEach" [call "inject" [.arrow false []
                      (.block [.expr (call "computeTheValue" [v "item"])])]], "more"⟩])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
