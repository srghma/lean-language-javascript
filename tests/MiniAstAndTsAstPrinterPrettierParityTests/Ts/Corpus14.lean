import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part fourteen

The last of the shapes that had no sample of their own: a decorator read
at type arguments, private members with type annotations (a field, a
method and a `#name in x` check inside a type predicate), an `override`
getter, a module augmentation, `as const satisfies …`, and members of an
`enum` written with string keys.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- The samples. -/
def samples14 : List Sample :=
  [ { name := "decorator-type-args"
      prog := ⟨[st (.classDecl [.call (v "Dec") [ty "string"] []] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) false [] [] (some (ty "void")) (some [])])]⟩ }
  , { name := "private-members-typed"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { isReadonly := true } false (.private_ (nes "value")) false false
          (some (ty "number")) (some (num 1)),
         .method [] {} .normal (.private_ (nes "compute")) false [] []
          (some (ty "number")) (some [.return_ (some (.privateDot .this (nes "value")))]),
         .method [] { isStatic := true } .normal (.ident (nes "has")) false []
          [parT "candidate" (ty "unknown")]
          (some (.predicate false (nes "candidate") (some (ty "C"))))
          (some [.return_ (some (.binary (.privateName (nes "value")) .inOp (v "candidate")))])])]⟩ }
  , { name := "override-getter"
      prog := ⟨[st (.classDecl [] false (nes "C") [] (some ⟨v "Base", []⟩) []
        [.method [] { isOverride := true } .get (.ident (nes "value")) false [] []
          (some (ty "number")) (some [.return_ (some (num 1))])])]⟩ }
  , { name := "module-augmentation"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes "d")) none none (nes "dep"))),
        st (.declare_ (.namespaceDecl true (.str "dep")
          (some [.stmt (.interface_ (nes "AnInterfaceName") [] []
            [prop "aPropertyName" (ty "number")])])))]⟩ }
  , { name := "as-const-satisfies"
      prog := ⟨[st (constDecl "theConfiguration" none
        (.satisfies (.asExpr (.object [.keyValue (.ident (nes "aKeyName")) (.string "a value")])
          (.ref (.ident (nes "const")) [])) (tyA "Record" [ty "string", ty "string"])))]⟩ }
  , { name := "enum-member-string-keys"
      prog := ⟨[st (.enum_ false (nes "E")
        [⟨.string "a member", some (.string "a value")⟩,
         ⟨.ident (nes "another"), some (.number (JSNumber.ofNat 2))⟩])]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
