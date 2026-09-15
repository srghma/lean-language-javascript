import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part seven

The samples of this file cover the type arguments a tagged template literal
is read at (`` tag<T>`…` ``, which the tree now holds), the order prettier
writes the modifiers of a class member in — `abstract` before `override`,
whatever order the member was written in — and a batch of declarations that
had no sample of their own: the ambient `declare class`, `declare enum` and
`declare abstract class`, a namespace written with a qualified name, a
`for` head and a `using` binder that carry a type annotation, overload
signatures of a constructor and of an exported function, and the `this`
parameter of a method.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- `` tag<T>`x` ``, a tagged template read at type arguments. -/
private def taggedT (tag : MiniExpr) (args : List MiniTsType) : MiniExpr :=
  .template (some tag) args "x" []

/-- `const aLongName: ALongTypeNameNumberThree = e;` -/
private def constAnn (name : String) (e : MiniExpr) : MiniStatement :=
  constDecl name (some (ty (longType 3))) e

/-- The samples. -/
def samples7 : List Sample :=
  [ -- ## The type arguments of a tagged template literal
    { name := "tagged-template-type-args"
      prog := ⟨[st (constDecl "a" none
        (.template (some (v "tag")) [ty "string"] "hello " [⟨v "x", " world"⟩]))]⟩ }
  , { name := "tagged-template-type-args-long"
      prog := ⟨[st (constDecl "b" none
        (.template (some (.dot (v "objectName") (nes "method")))
          [ty "AVeryLongTypeNameHereOk", ty "AnotherVeryLongTypeName"] "text "
          [⟨v "value", ""⟩]))]⟩ }
  , { name := "tagged-template-type-args-as"
      prog := ⟨[st (constDecl "c" none
        (.template (some (.asExpr (v "f") (ty "Tag"))) [ty "T"] "x" []))]⟩ }
  , { name := "tagged-template-chain"
      prog := ⟨[es (.call (.dot (.template (some (.dot (.dot (v "a") (nes "b")) (nes "c")))
        [ty "T"] "x" []) (nes "d")) [] [])]⟩ }
  , { name := "tagged-template-callee"
      prog := ⟨[es (.call (taggedT (v "tag") [ty "T"]) [] [v "y"])]⟩ }
  , { name := "tagged-template-new-callee"
      prog := ⟨[es (.new (taggedT (v "tag") [ty "T"]) [] [])]⟩ }
  , { name := "tagged-template-instantiation-tag"
      prog := ⟨[es (taggedT (.instantiation (v "f") [ty "T"]) [ty "U"])]⟩ }
  , { name := "tagged-template-type-args-union"
      prog := ⟨[st (constAnn "aLongIdentifierNameNumberOne"
        (taggedT (v "tag") [.union [ty (longType 0), ty (longType 1), ty (longType 2)]]))]⟩ }
  , { name := "tagged-template-type-args-fn"
      prog := ⟨[st (constAnn "aLongIdentifierNameNumberOne"
        (taggedT (v "tag") [.fn [] [parT "value" (ty (longType 0))] (ty (longType 1))]))]⟩ }
  , { name := "tagged-template-in-object"
      prog := ⟨[st (constDecl "obj" none (.object
        [.keyValue (.ident (nes "aLongPropertyNameHereOk"))
          (taggedT (.dot (v "objectName") (nes "method")) [ty (longType 0), ty (longType 1)])]))]⟩ }
    -- ## The order of the modifiers of a class member
  , { name := "abstract-override"
      prog := ⟨[st (.classDecl [] true (nes "C") [] (some ⟨v "Base", []⟩) []
        [.method [] { isAbstract := true, isOverride := true } .normal (.ident (nes "m")) false
          [] [] (some (ty "void")) none])]⟩ }
  , { name := "abstract-override-field"
      prog := ⟨[st (.classDecl [] true (nes "C") [] (some ⟨v "Base", []⟩) []
        [.field []
          { accessibility := some .protected_, isAbstract := true, isOverride := true,
            isReadonly := true }
          false (.ident (nes "x")) false false (some (ty "number")) none])]⟩ }
  , { name := "abstract-accessor"
      prog := ⟨[st (.classDecl [] true (nes "C") [] none []
        [.field [] { isAbstract := true, accessibility := some .protected_ } true
          (.ident (nes "y")) false false (some (ty "number")) none])]⟩ }
  , { name := "abstract-getter-setter"
      prog := ⟨[st (.classDecl [] true (nes "C") [] none []
        [.method [] { isAbstract := true } .get (.ident (nes "z")) false [] []
          (some (ty "number")) none,
         .method [] { isAbstract := true } .set (.ident (nes "z")) false []
          [parT "value" (ty "number")] none none])]⟩ }
  , { name := "static-accessor"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { isStatic := true } true (.ident (nes "x")) false false none
          (some (num 1))])]⟩ }
  , { name := "optional-method"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) true [] [] (some (ty "void")) (some [])])]⟩ }
  , { name := "static-index-signature"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.indexSig { isStatic := true, isReadonly := true } (nes "key") (ty "string")
          (ty "number")])]⟩ }
    -- ## Declarations
  , { name := "declare-class"
      prog := ⟨[st (.declare_ (.classDecl [] false (nes "D") [] none []
        [.field [] {} false (.ident (nes "x")) false false (some (ty "number")) none]))]⟩ }
  , { name := "declare-enum"
      prog := ⟨[st (.declare_ (.enum_ false (nes "F") [⟨.ident (nes "A"), none⟩]))]⟩ }
  , { name := "declare-abstract-class"
      prog := ⟨[st (.declare_ (.classDecl [] true (nes "G") [] none [] []))]⟩ }
  , { name := "namespace-qualified"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "A", [nes "B", nes "C"]⟩)
        (some [.exportDecl (.decl (constDecl "x" none (num 1)))]))]⟩ }
  , { name := "namespace-import-equals"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "N", []⟩)
        (some [.importDecl (.equals false (nes "fs") (.require "fs")),
          .importDecl (.equals true (nes "A") (.entity (.qualified (.ident (nes "B"))
            (nes "C"))))]))]⟩ }
  , { name := "ambient-module-with-import"
      prog := ⟨[st (.declare_ (.namespaceDecl true (.str "a-module")
        (some [.importDecl (.clause (MiniImportClause.mk! (some (nes "d")) none none (nes "dep"))),
          .exportDecl (.decl (.decl .const ⟨declT "x" (some (ty "number")) none, []⟩))])))]⟩ }
  , { name := "for-typed-init"
      prog := ⟨[st (.for_ (.decl .let_ ⟨declT "i" (some (ty "number")) (some (num 0)),
        [declT "j" (some (ty "string")) (some (.string ""))]⟩) none none (.block []))]⟩ }
  , { name := "using-typed"
      prog := ⟨[st (.using_ false ⟨declT "u" (some (ty "Disposable"))
        (some (call "get" [])), []⟩)]⟩ }
  , { name := "export-default-generic-function"
      prog := ⟨[.exportDecl (.defaultDecl (.funcDecl false false (nes "fn") [tp "T"]
        [parT "x" (ty "T")] (some (ty "T")) (some [.return_ (some (v "x"))])))]⟩ }
  , { name := "constructor-overloads"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false [] [parT "x" (ty "number")]
          none none,
         .method [] {} .normal (.ident (nes "constructor")) false [] [parT "x" (ty "string")]
          none none,
         .method [] {} .normal (.ident (nes "constructor")) false []
          [parT "x" (.union [ty "number", ty "string"])] none (some [])])]⟩ }
  , { name := "function-overloads-exported"
      prog := ⟨[.exportDecl (.decl (.funcDecl false false (nes "fn") [] [parT "x" (ty "number")]
          (some (ty "number")) none)),
        .exportDecl (.decl (.funcDecl false false (nes "fn") [] [parT "x" (ty "string")]
          (some (ty "string")) none)),
        .exportDecl (.decl (.funcDecl false false (nes "fn") []
          [parT "x" (.union [ty "number", ty "string"])] (some (ty "unknown"))
          (some [.return_ (some (v "x"))])))]⟩ }
  , { name := "method-this-param"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "m")) false [tp "T"]
          [parT "this" (ty "Foo"), parT "x" (ty "T")] (some (ty "void")) (some [])])]⟩ }
    -- ## Types and expressions with no sample of their own
  , { name := "import-type-default"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! (some (nes "D")) none none
        (nes "mod") [] true))]⟩ }
  , { name := "import-type-namespace"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none (some (nes "ns")) none
        (nes "mod") [] true))]⟩ }
  , { name := "export-type-specifier"
      prog := ⟨[.exportDecl (.locals false [⟨true, nes "A", some (nes "B")⟩])]⟩ }
  , { name := "predicate-this"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [.method .normal (.ident (nes "isFoo")) false [] []
          (some (.predicate false (nes "this") (some (ty "Foo")))),
         .method .normal (.ident (nes "assertFoo")) false [] []
          (some (.predicate true (nes "this") (some (ty "Foo"))))])]⟩ }
  , { name := "tuple-labelled-rest"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.tuple [.named (nes "first") false false (ty "string"),
          .named (nes "rest") false true (.array (ty "number"))]))]⟩ }
  , { name := "const-type-param-arrow"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [⟨true, none, nes "T", none, none⟩] [parT "x" (ty "T")] none
          (.expr (v "x"))))]⟩ }
  , { name := "construct-signature-generic"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [.ctorSig [tpC "T" (ty "object")] [parT "value" (ty "T")]
          (some (tyA "Wrapper" [ty "T"]))])]⟩ }
  , { name := "mapped-as-plus-readonly"
      prog := ⟨[st (.typeAlias (nes "T") [tp "K"]
        (.mapped (some .add) (nes "P") (.keyof (ty "K"))
          (some (.templateLit "prefix" [⟨ty "P", ""⟩])) (some .remove)
          (some (.indexed (ty "K") (ty "P")))))]⟩ }
  , { name := "arrow-return-predicate"
      prog := ⟨[st (constDecl "isFoo" none
        (.arrow false [] [parT "value" (ty "unknown")]
          (some (.predicate false (nes "value") (some (ty "Foo")))) (.expr .true_)))]⟩ }
  , { name := "intersection-of-object-types"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.intersection [.objectType [prop "aLongPropertyNameHere" (ty "string")],
          .objectType [prop "anotherLongPropertyName" (ty "number")]]))]⟩ }
  , { name := "new-long-type-args"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZero" none
        (.new (v "AClassNameHere") [ty (longType 0), ty (longType 1)] [v "argument"]))]⟩ }
  , { name := "satisfies-object-breaks"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberOne" none
        (.satisfies (.object [.keyValue (.ident (nes "aPropertyName")) (num 1),
          .keyValue (.ident (nes "anotherPropertyName")) (num 2)])
          (tyA "Record" [ty "string", ty "number"])))]⟩ }
  , { name := "class-extends-long-type-args"
      prog := ⟨[st (.classDecl [] false (nes "AClassWithALongName") []
        (some ⟨v "ABaseClassName", [ty (longType 0), ty (longType 1)]⟩)
        [her (longType 2)] [])]⟩ }
  , { name := "implements-long-list"
      prog := ⟨[st (.classDecl [] false (nes "AClassWithAVeryLongNameHere") [] none
        [her (longType 0), her (longType 1), her (longType 2)] [])]⟩ }
  , { name := "as-in-template-subst"
      prog := ⟨[st (constDecl "s" none
        (.template none [] "a " [⟨.asExpr (v "x") (ty "string"), " b"⟩]))]⟩ }
  , { name := "as-in-spread-and-array"
      prog := ⟨[st (constDecl "arr" none
        (.array [.elem (.spread (.asExpr (v "x") (ty "number[]"))),
          .elem (.nonNull (v "y"))]))]⟩ }
  , { name := "nonnull-as-as"
      prog := ⟨[st (constDecl "q" none
        (.asExpr (.asExpr (.nonNull (v "a")) (ty "unknown")) (ty "string")))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
