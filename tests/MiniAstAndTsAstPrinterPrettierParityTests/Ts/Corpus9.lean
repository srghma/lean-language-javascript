import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part nine

The samples of this file cover the TypeScript written where JSX, a chain
or a `new` meets it: a type written inside an attribute and inside a child
of an element, a generic component whose attributes break, the type
arguments of an optional call, and the parentheses the callee of a `new`
takes — which an `as` and a `satisfies` need and a `!` does not, and which
go around the `as` itself rather than the whole callee when the callee
reads a property off it.  The rest are shapes that had no sample of their
own: `delete` of an `as`, `typeof f<T>`, a `yield` and an `await` of a
type operator, a class expression with an `implements` clause, an
`abstract new` constructor type in a union, an object type whose call
signature breaks, a template literal type, a field of a `unique symbol`
type, an async generic method, an arrow annotated with an object type,
`as const` on a nested object literal, a long qualified type name, the
overload signatures of an ambient class, and a decorated class whose
heritage clauses break.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A JSX element expression. -/
private def el9 (name : String) (typeArgs : List MiniTsType) (attrs : List MiniJSXAttribute)
    (children : Option (List MiniJSXChild)) : MiniExpr :=
  .jsx (.element (.ident (nes name)) typeArgs attrs children)

/-- The samples. -/
def samples9 : List Sample :=
  [ { name := "jsx-attr-as"
      prog := ⟨[es (el9 "Component" []
        [.attr (.ident (nes "value")) (some (.expr (.asExpr (v "theValue") (ty "string")))),
          .attr (.ident (nes "other")) (some (.expr (.nonNull (v "another"))))] none)]⟩ }
  , { name := "jsx-child-as"
      prog := ⟨[es (el9 "div" [] []
        (some [.expr (.asExpr (v "theValue") (ty "ReactNode"))]))]⟩ }
  , { name := "jsx-generic-long-attrs"
      prog := ⟨[es (el9 "AComponentWithALongName" [ty (longType 0)]
        [.attr (.ident (nes "aPropertyName")) (some (.string "a rather long value")),
          .attr (.ident (nes "anotherProperty")) (some (.expr (num 1)))] none)]⟩ }
  , { name := "optional-call-type-args"
      prog := ⟨[es (.chain (v "theObject")
        ⟨.dot true (nes "aMethodName"), [.call true [ty "T"] [v "argument"]]⟩)]⟩ }
  , { name := "new-as-callee"
      prog := ⟨[es (.new (.asExpr (v "TheClass") (ty "any")) [] [v "argument"])]⟩ }
  , { name := "new-satisfies-callee"
      prog := ⟨[es (.new (.satisfies (v "TheClass") (ty "Ctor")) [] [])]⟩ }
  , { name := "new-nonnull-callee"
      prog := ⟨[es (.new (.nonNull (v "TheClass")) [] [])]⟩ }
  , { name := "new-as-member-callee"
      prog := ⟨[es (.new (.dot (.asExpr (v "theValue") (ty "any")) (nes "Inner")) [] [])]⟩ }
  , { name := "new-nonnull-member-callee"
      prog := ⟨[es (.new (.dot (.nonNull (v "theValue")) (nes "Inner")) [] [])]⟩ }
  , { name := "new-as-tag-callee"
      prog := ⟨[es (.new (.template (some (.asExpr (v "theTag") (ty "any"))) [] "x" []) [] [])]⟩ }
  , { name := "delete-as"
      prog := ⟨[es (.unary .delete (.dot (.asExpr (v "theValue") (ty "any")) (nes "key")))]⟩ }
  , { name := "typeof-instantiation"
      prog := ⟨[st (constDecl "g" none (.instantiation (v "f") [ty "T"])),
        st (.typeAlias (nes "G") [] (.typeQuery (.ident (nes "f")) [ty "T"]))]⟩ }
  , { name := "yield-as"
      prog := ⟨[st (.funcDecl false true (nes "gen") [] [] none
        (some [.expr (.yield (some (.asExpr (v "theValue") (ty "number"))))]))]⟩ }
  , { name := "await-nonnull"
      prog := ⟨[st (.funcDecl true false (nes "f") [] [] none
        (some [.expr (.await (.nonNull (call "get" [])))]))]⟩ }
  , { name := "class-expression-implements"
      prog := ⟨[st (constDecl "C" none
        (.classExpr [] none [tp "T"] none [her "AnInterfaceName"]
          [.field [] {} false (.ident (nes "x")) false false (some (ty "T")) none]))]⟩ }
  , { name := "abstract-new-in-union"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.union [.ctor true [] [parT "value" (ty "string")] (ty "object"), ty "null"]))]⟩ }
  , { name := "object-type-call-signature-breaks"
      prog := ⟨[st (.typeAlias (nes "AHandlerTypeName") []
        (.objectType [.callSig [] [parT "aParameterName" (ty (longType 0)),
            parT "anotherParameter" (ty (longType 1))] (some (ty "void")),
          prop "aPropertyName" (ty "number")]))]⟩ }
  , { name := "template-literal-type-breaks"
      prog := ⟨[st (.typeAlias (nes "ATemplateTypeName") []
        (.templateLit "a-rather-long-prefix-"
          [⟨ty (longType 0), "-in-the-middle-"⟩, ⟨ty (longType 1), "-suffix"⟩]))]⟩ }
  , { name := "unique-symbol-field"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { isStatic := true, isReadonly := true } false (.ident (nes "key")) false false
          (some .uniqueSymbol) none])]⟩ }
  , { name := "async-generic-method-long"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .async (.ident (nes "aMethodWithALongName")) false
          [tpC "T" (ty (longType 0))] [parT "value" (ty "T")]
          (some (tyA "Promise" [ty (longType 1)])) (some [])])]⟩ }
  , { name := "arrow-annotated-object-type"
      prog := ⟨[st (constDecl "aFactoryWithALongName" none
        (.arrow false [] [] (some (.objectType [prop "aPropertyName" (ty (longType 0))]))
          (.expr (.object []))))]⟩ }
  , { name := "as-const-nested-object"
      prog := ⟨[st (constDecl "theConfiguration" none
        (.asExpr (.object [.keyValue (.ident (nes "aKeyName"))
            (.object [.keyValue (.ident (nes "anInnerKey")) (.string "a value")])])
          (.ref (.ident (nes "const")) [])))]⟩ }
  , { name := "qualified-long-type-name"
      prog := ⟨[st (letDecl "aLongIdentifierNameNumberZero"
        (some (.ref (.qualified (.qualified (.ident (nes "ANamespaceName"))
          (nes "AnInnerNamespace")) (nes "ATypeNameHere")) [ty (longType 0)])))]⟩ }
  , { name := "declare-class-overloads"
      prog := ⟨[st (.declare_ (.classDecl [] false (nes "D") [] none []
        [.method [] {} .normal (.ident (nes "m")) false [] [parT "x" (ty "number")]
          (some (ty "void")) none,
         .method [] {} .normal (.ident (nes "m")) false [] [parT "x" (ty "string")]
          (some (ty "void")) none]))]⟩ }
  , { name := "decorated-class-long-heritage"
      prog := ⟨[st (.classDecl [.call (v "Component") [] [.object
          [.keyValue (.ident (nes "selector")) (.string "a-selector-name")]]]
        false (nes "AClassWithALongName") [] (some ⟨v "ABaseClassName", [ty (longType 0)]⟩)
        [her (longType 1)] [])]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
