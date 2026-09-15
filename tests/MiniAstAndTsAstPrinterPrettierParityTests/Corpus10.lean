import Tests.Corpus9

/-!
# Samples of the names, the quotes and the declarations

Programs which exercise the rules on the quotes of a property name, the
parentheses of the callee of a `new`, and the shapes an `export default`
may take.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A key/value property with a string key. -/
def keyedString (k : String) (e : MiniExpr) : MiniProperty := .keyValue (.string k) e

/-- The samples. -/
def samples10 : List Sample :=
  [ { name := "string-keys"
      prog := ⟨[es (.object [keyedString "1" (v "a"), keyedString "1.5" (v "b"), keyedString "01" (v "c"),
                  keyedString "1e3" (v "d")]),
                es (.object [keyedString "1.50" (v "a"), keyedString "1.0" (v "b"), keyedString "0" (v "c"),
                  keyedString "00" (v "d"), keyedString "-1" (v "e"), keyedString "0x10" (v "f")]),
                es (.object [keyedString "a-b" (v "a"), keyedString "$a" (v "b"), keyedString "_a" (v "c"),
                  keyedString "await" (v "d"), keyedString "" (v "e"), keyedString "a b" (v "f")]),
                st (.classDecl [] (nes "C") none
                  [.field [] false false (.string "a") (some (num 1)),
                   .field [] false false (.string "b-c") (some (num 2)),
                   .field [] false false (.string "01") (some (num 3))])]⟩ }
  , { name := "string-quotes"
      prog := ⟨[es (.array [.elem (.string "it's"), .elem (.string "say \"hi\""),
                  .elem (.string "both ' and \""), .elem (.string "two '' one \""),
                  .elem (.string "\u0000"), .elem (.string "\u001f"),
                  .elem (.string "back\\slash")])]⟩ }
  , { name := "directives"
      prog := ⟨[es (.string "use strict"), es (.string "another"), es (v "a"),
                es (.string "not a directive"),
                st (.funcDecl false false (nes "f") []
                  [.expr (.string "use strict"), .expr (v "a"), .expr (.string "late")])]⟩ }
  , { name := "assign-chain"
      prog := ⟨[es (.assign (v "a") .assign (.assign (v "b") .assign (v "c"))),
                es (.assign (.index (v "a") (num 0)) .assign (v "b")),
                es (.assignPattern (.array [.elem (p "a"), .elem (p "b")]) (v "xs")),
                es (.assignPattern (.object [⟨.ident (nes "a"), p "a"⟩] none) (v "o"))]⟩ }
  , { name := "new-shapes"
      prog := ⟨[es (.new (.dot (v "a") (nes "b")) []),
                es (.new (call "f" []) []),
                es (.new (.new (v "a") []) []),
                es (.dot (.new (v "a") [num 1]) (nes "b")),
                es (.new (.chain (v "a") ⟨.dot true (nes "b"), []⟩) [])]⟩ }
  , { name := "if-else-chain"
      prog := ⟨[st (.if_ (v "a") (.expr (v "b"))
                  (some (.if_ (v "c") (.block [.expr (v "d")])
                    (some (.if_ (v "e") (.expr (v "f")) (some (.block []))))))),
                st (.if_ (v "a") .empty none),
                st (.if_ (v "a") (.block []) (some .empty)),
                st (.doWhile (.expr (v "a")) (v "b")),
                st (.while_ (v "a") .empty)]⟩ }
  , { name := "export-shapes"
      prog := ⟨[.exportDecl (.defaultExpr (.func false false none [] [])),
                .exportDecl (.locals []),
                .exportDecl (.decl (.funcDecl true false (nes "f") [] [])),
                .importDecl (.clause (MiniImportClause.mk! none none (some []) (nes "m")))]⟩ }
  , { name := "export-default-class"
      prog := ⟨[.exportDecl (.defaultExpr (.classExpr [] none none []))]⟩ }
  , { name := "export-default-arrow"
      prog := ⟨[.exportDecl (.defaultExpr (.arrow false [par "a"] (.expr (v "a"))))]⟩ }
  , { name := "export-default-function-member"
      prog := ⟨[.exportDecl (.defaultExpr (.dot (.func false false none [] []) (nes "x")))]⟩ }
  , { name := "export-default-class-member"
      prog := ⟨[.exportDecl (.defaultExpr (.dot (.dot (.classExpr [] none none []) (nes "x"))
                  (nes "y")))]⟩ }
  , { name := "export-default-function-call"
      prog := ⟨[.exportDecl (.defaultExpr (.call (.func false false none [] []) []))]⟩ }
  , { name := "export-default-class-call"
      prog := ⟨[.exportDecl (.defaultExpr (.call (.classExpr [] none none []) []))]⟩ }
  , { name := "export-default-function-tagged"
      prog := ⟨[.exportDecl (.defaultExpr
                  (.template (some (.func false false none [] [])) "t" []))]⟩ }
  , { name := "export-default-sequence"
      prog := ⟨[.exportDecl (.defaultExpr (.seq (.func false false none [] []) (num 0)))]⟩ }
  , { name := "export-default-object-member"
      prog := ⟨[.exportDecl (.defaultExpr (.dot (.object [.shorthand (nes "a")]) (nes "x")))]⟩ }
  , { name := "export-default-function-binary"
      prog := ⟨[.exportDecl (.defaultExpr
                  (.binary (.func false false none [] []) .plus (num 1)))]⟩ }
  , { name := "class-shapes"
      prog := ⟨[st (.classDecl [] (nes "C") (some (call "mixin" [v "Base"]))
                  [.staticBlock [.expr (v "a")],
                   .method [] true .get (.private_ (nes "x")) [] [.return_ (some (num 1))],
                   .method [] true .generator (.computed (v "k")) [] [],
                   .field [] false false (.computed (.string "k")) none,
                   .field [] true false (.ident (nes "y")) none]),
                es (.classExpr [] (some (nes "D")) (some (.dot (v "a") (nes "b"))) [])]⟩ }
  , { name := "call-hug"
      prog := ⟨[es (call (longName 0)
                  [.object [.keyValue (.ident (nes (longName 1))) (num 1),
                    .keyValue (.ident (nes (longName 2))) (num 2)]]),
                es (call (longName 0)
                  [v "a", .arrow false [par "x"] (.block [.return_ (some (v "x"))])]),
                es (call (longName 0) [.array [.elem (v (longName 1)), .elem (v (longName 2)),
                  .elem (v (longName 3))]])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
