import Tests.Ts.Prelude

/-!
# More sample TypeScript programs

Where `Tests/Ts/Corpus.lean` shows each piece of the TypeScript grammar
once, the samples here are long enough not to fit on one line: they are
the ones whose layout prettier decides by breaking a union, a list of
type arguments, a parameter list or an assignment.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A union of the `k` long type names. -/
def longUnion (k : Nat) : MiniTsType :=
  .union ((List.range k).map fun i => ty (longType i))

/-- An intersection of the `k` long type names. -/
def longIntersection (k : Nat) : MiniTsType :=
  .intersection ((List.range k).map fun i => ty (longType i))

/-- An object type of the `k` long property names. -/
def longObjectType (k : Nat) : MiniTsType :=
  .objectType ((List.range k).map fun i => prop (longName i) (ty (longType i)))

/-- The samples. -/
def samples2 : List Sample :=
  [ -- ## Unions that have to break
    { name := "union-in-annotation"
      prog := ⟨[st (letDecl (longName 0) (some (longUnion 4)))]⟩ }
  , { name := "union-in-annotation-fits"
      prog := ⟨[st (letDecl "a" (some (.union [ty "string", ty "number"])))]⟩ }
  , { name := "union-in-return-type"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [] (some (longUnion 4)) (some []))]⟩ }
  , { name := "union-in-param-type"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [parT (longName 0) (longUnion 3)]
        none (some []))]⟩ }
  , { name := "union-in-type-args"
      prog := ⟨[st (.typeAlias (nes "A") [] (tyA "Promise" [longUnion 4]))]⟩ }
  , { name := "union-in-array"
      prog := ⟨[st (.typeAlias (nes "A") [] (.array (longUnion 4)))]⟩ }
  , { name := "union-in-tuple"
      prog := ⟨[st (.typeAlias (nes "A") [] (.tuple [.elem (longUnion 3), .elem (ty "number")]))]⟩ }
  , { name := "union-of-objects"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.union [longObjectType 2, longObjectType 2]))]⟩ }
  , { name := "union-of-two-objects-short"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.union [.objectType [prop "a" (ty "string")], .objectType [prop "b" (ty "number")]]))]⟩ }
  , { name := "union-with-null"
      prog := ⟨[st (.typeAlias (nes "A") [] (.union [longUnion 3, ty "null"]))]⟩ }
  , { name := "union-nested-in-union"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.union [ty (longType 0), .union [ty (longType 1), ty (longType 2)],
          ty (longType 3)]))]⟩ }
  , { name := "union-in-property-type"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [prop (longName 0) (longUnion 3)])]⟩ }
  , { name := "union-in-mapped-value"
      prog := ⟨[st (.typeAlias (nes "M") [tp "T"]
        (.mapped none (nes "K") (.keyof (ty "T")) none none (some (longUnion 3))))]⟩ }
  , { name := "union-in-as-expression"
      prog := ⟨[st (constDecl (longName 0) none (.asExpr (v (longName 1)) (longUnion 3)))]⟩ }
  , { name := "union-of-function-types"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.union [.fn [] [parT "a" (ty (longType 0))] (ty (longType 1)),
          .fn [] [parT "b" (ty (longType 2))] (ty (longType 3))]))]⟩ }

    -- ## Intersections
  , { name := "intersection-breaks"
      prog := ⟨[st (.typeAlias (nes "A") [] (longIntersection 4))]⟩ }
  , { name := "intersection-of-objects"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.intersection [longObjectType 2, longObjectType 2]))]⟩ }
  , { name := "intersection-object-and-ref"
      prog := ⟨[st (.typeAlias (nes "A") []
        (.intersection [ty (longType 0), longObjectType 2]))]⟩ }
  , { name := "intersection-in-annotation"
      prog := ⟨[st (letDecl (longName 0) (some (longIntersection 3)))]⟩ }

    -- ## Type arguments
  , { name := "type-args-break"
      prog := ⟨[st (.typeAlias (nes "A") []
        (tyA "ARecordOfThings" [ty (longType 0), ty (longType 1), ty (longType 2)]))]⟩ }
  , { name := "type-args-nested"
      prog := ⟨[st (.typeAlias (nes "A") []
        (tyA "Promise" [tyA "Array" [tyA "Record" [ty (longType 0), ty (longType 1)]]]))]⟩ }
  , { name := "call-type-args-break"
      prog := ⟨[es (.call (v (longName 0)) [ty (longType 0), ty (longType 1)]
        [v (longName 1)])]⟩ }
  , { name := "new-type-args-break"
      prog := ⟨[st (constDecl (longName 0) none
        (.new (v "MapOfSomething") [ty (longType 0), ty (longType 1)] [v (longName 1)]))]⟩ }
  , { name := "call-type-args-and-args-break"
      prog := ⟨[es (.call (v (longName 0)) [ty (longType 0)]
        [v (longName 1), v (longName 2), v (longName 3)])]⟩ }

    -- ## Parameter lists
  , { name := "params-break-annotated"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [parT (longName 0) (ty (longType 0)), parT (longName 1) (ty (longType 1))]
        none (some []))]⟩ }
  , { name := "params-break-with-return-type"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [parT (longName 0) (ty (longType 0)), parT (longName 1) (ty (longType 1))]
        (some (ty (longType 2))) (some []))]⟩ }
  , { name := "params-break-object-type"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [.plain [] {} (.object [⟨.ident (nes "a"), p "a"⟩] none) false (some (longObjectType 2))]
        none (some []))]⟩ }
  , { name := "arrow-params-break-annotated"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [] [parT (longName 0) (ty (longType 0)), parT (longName 1)
          (ty (longType 1))] (some (ty "void")) (.block [])))]⟩ }
  , { name := "arrow-in-call-annotated"
      prog := ⟨[es (call "map" [.arrow false [] [parT (longName 0) (ty (longType 0))]
        (some (ty (longType 1))) (.expr (v (longName 0)))])]⟩ }
  , { name := "method-params-break"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "method")) false []
          [parT (longName 0) (ty (longType 0)), parT (longName 1) (ty (longType 1))]
          (some (ty "void")) (some [])])]⟩ }
  , { name := "constructor-parameter-properties-break"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [] { accessibility := some .private_, isReadonly := true } (p (longName 0))
             false (some (ty (longType 0))),
           .plain [] { accessibility := some .public_ } (p (longName 1)) false
             (some (ty (longType 1)))]
          none (some [])])]⟩ }
  , { name := "one-parameter-property-breaks"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [] { accessibility := some .private_ } (p "a") false (some (ty "string"))]
          none (some [])])]⟩ }

    -- ## Type parameters
  , { name := "type-params-break-class"
      prog := ⟨[st (.classDecl [] false (nes "C")
        [tpC (longType 0) (ty (longType 1)), tpC (longType 2) (ty (longType 3))]
        none [] [])]⟩ }
  , { name := "type-params-break-alias"
      prog := ⟨[st (.typeAlias (nes "A")
        [tpC (longType 0) (ty (longType 1)), tpC (longType 2) (ty (longType 3))]
        (ty (longType 0)))]⟩ }
  , { name := "type-params-break-interface"
      prog := ⟨[st (.interface_ (nes "I")
        [tpC (longType 0) (ty (longType 1)), tpC (longType 2) (ty (longType 3))] [] [])]⟩ }
  , { name := "type-param-variance"
      prog := ⟨[st (.interface_ (nes "I")
        [⟨false, some .in_, nes "T", none, none⟩, ⟨false, some .out_, nes "U", none, none⟩,
         ⟨false, some .inOut, nes "V", none, none⟩] [] [])]⟩ }
  , { name := "type-param-const"
      prog := ⟨[st (.funcDecl false false (nes "f") [⟨true, none, nes "T", none, none⟩]
        [parT "a" (ty "T")] none (some []))]⟩ }
  , { name := "type-param-default-long"
      prog := ⟨[st (.typeAlias (nes "A")
        [⟨false, none, nes "T", some (ty (longType 0)), some (ty (longType 1))⟩]
        (ty "T"))]⟩ }

    -- ## Conditional types
  , { name := "conditional-chain"
      prog := ⟨[st (.typeAlias (nes "C") [tp "T"]
        (.conditional (ty "T") (ty (longType 0)) (ty (longType 1))
          (.conditional (ty "T") (ty (longType 2)) (ty (longType 3)) (ty "never"))))]⟩ }
  , { name := "conditional-nested-in-true"
      prog := ⟨[st (.typeAlias (nes "C") [tp "T"]
        (.conditional (ty "T") (ty "object")
          (.conditional (ty "T") (ty "string") (ty "A") (ty "B")) (ty "C")))]⟩ }
  , { name := "conditional-with-infer-breaks"
      prog := ⟨[st (.typeAlias (nes "ElementTypeOfArray") [tp "T"]
        (.conditional (ty "T") (.array (.infer_ (nes "TheElement") none))
          (ty "TheElement") (ty "never")))]⟩ }
  , { name := "conditional-in-annotation"
      prog := ⟨[st (letDecl (longName 0)
        (some (.conditional (ty (longType 0)) (ty (longType 1)) (ty (longType 2))
          (ty (longType 3)))))]⟩ }

    -- ## Object types, interfaces and classes
  , { name := "interface-many-members"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [prop (longName 0) (ty (longType 0)),
         .method .normal (.ident (nes (longName 1))) false []
           [parT (longName 2) (ty (longType 1))] (some (ty (longType 2))),
         .property true (.ident (nes (longName 3))) true (some (longUnion 3))])]⟩ }
  , { name := "interface-extends-with-type-args-break"
      prog := ⟨[st (.interface_ (nes "I") []
        [her (longType 0) [ty (longType 1)], her (longType 2) [ty (longType 3)]] [])]⟩ }
  , { name := "class-extends-implements-break"
      prog := ⟨[st (.classDecl [] false (nes (longType 0)) []
        (some ⟨v (longName 0), [ty (longType 1)]⟩) [her (longType 2), her (longType 3)] [])]⟩ }
  , { name := "class-extends-call-typed"
      prog := ⟨[st (.classDecl [] false (nes "C") []
        (some ⟨.call (v "mixin") [ty "Base"] [v "Base"], []⟩) [] [])]⟩ }
  , { name := "class-abstract-members"
      prog := ⟨[st (.classDecl [] true (nes "C") [] none []
        [.field [] { isAbstract := true, accessibility := some .protected_ } false
           (.ident (nes (longName 0))) false false (some (ty (longType 0))) none,
         .method [] { isAbstract := true } .normal (.ident (nes (longName 1))) false []
           [parT (longName 2) (ty (longType 1))] (some (ty "void")) none])]⟩ }
  , { name := "class-field-long-initialiser"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { isStatic := true, isReadonly := true } false (.ident (nes (longName 0)))
          false false (some (ty (longType 0)))
          (some (call (longName 1) [v (longName 2)]))])]⟩ }
  , { name := "class-getter-setter-typed"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] { accessibility := some .public_ } .get (.ident (nes "value")) false []
           [] (some (ty "number")) (some [.return_ (some (num 1))]),
         .method [] {} .set (.ident (nes "value")) false [] [parT "v" (ty "number")] none
           (some [])])]⟩ }
  , { name := "object-type-nested-breaks"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType [.property false (.ident (nes (longName 0))) false
          (some (longObjectType 2))]))]⟩ }
  , { name := "object-type-method-breaks"
      prog := ⟨[st (.typeAlias (nes "O") []
        (.objectType [.method .normal (.ident (nes (longName 0))) false []
          [parT (longName 1) (ty (longType 0)), parT (longName 2) (ty (longType 1))]
          (some (ty "void"))]))]⟩ }

    -- ## Assignments and expressions
  , { name := "annotated-assignment-breaks"
      prog := ⟨[st (constDecl (longName 0) (some (ty (longType 0)))
        (call (longName 1) [v (longName 2)]))]⟩ }
  , { name := "annotated-assignment-union-breaks"
      prog := ⟨[st (constDecl (longName 0) (some (longUnion 3)) (num 1))]⟩ }
  , { name := "satisfies-breaks"
      prog := ⟨[st (constDecl (longName 0) none
        (.satisfies (.object [.keyValue (.ident (nes (longName 1))) (num 1)])
          (longObjectType 2)))]⟩ }
  , { name := "as-of-object-breaks"
      prog := ⟨[st (constDecl (longName 0) none
        (.asExpr (.object [.keyValue (.ident (nes (longName 1))) (v (longName 2))])
          (ty (longType 0))))]⟩ }
  , { name := "non-null-in-chain-breaks"
      prog := ⟨[es (.chain (v (longName 0))
        ⟨.dot false (nes (longName 1)),
         [.nonNull, .call false [] [], .dot false (nes (longName 2)), .call false [] [],
          .dot false (nes (longName 3)), .call false [] []]⟩)]⟩ }
  , { name := "generic-method-chain"
      prog := ⟨[es (.call (.dot (.call (.dot (v (longName 0)) (nes "get")) [ty (longType 0)] [])
        (nes "then")) [ty (longType 1)] [v "cb"])]⟩ }
  , { name := "return-as-expression-breaks"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [] none
        (some [.return_ (some (.asExpr (call (longName 0) [v (longName 1)])
          (ty (longType 0))))]))]⟩ }
  , { name := "arrow-body-as-expression"
      prog := ⟨[st (constDecl "f" none
        (.arrow false [] [] none (.expr (.asExpr (v (longName 0)) (ty (longType 0))))))]⟩ }

    -- ## Enums, namespaces, declarations
  , { name := "enum-breaks"
      prog := ⟨[st (.enum_ false (nes "TheEnumeration")
        [⟨.ident (nes (longName 0)), some (.string "a")⟩,
         ⟨.ident (nes (longName 1)), some (.string "b")⟩])]⟩ }
  , { name := "enum-computed-member"
      prog := ⟨[st (.enum_ true (nes "E")
        [⟨.ident (nes "A"), some (.binary (num 1) .lsh (num 2))⟩])]⟩ }
  , { name := "namespace-nested"
      prog := ⟨[st (.namespaceDecl false (.qualified ⟨nes "Outer", [nes "Inner"]⟩)
        (some [st (.namespaceDecl false (.qualified ⟨nes "Deep", []⟩)
          (some [.exportDecl (.decl (.typeAlias (nes "A") [] (longUnion 3)))]))]))]⟩ }
  , { name := "declare-class"
      prog := ⟨[st (.declare_ (.classDecl [] true (nes "C") [tp "T"] none [her "I" [ty "T"]]
        [.method [] {} .normal (.ident (nes "m")) false [] [parT "a" (ty "T")]
          (some (ty "void")) none]))]⟩ }
  , { name := "declare-enum-namespace"
      prog := ⟨[st (.declare_ (.enum_ false (nes "E") [⟨.ident (nes "A"), none⟩])),
        st (.declare_ (.namespaceDecl false (.qualified ⟨nes "N", []⟩)
          (some [st (.declare_ (.funcDecl false false (nes "f") [] [] none none))])))]⟩ }
  , { name := "import-type-many-specifiers"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
        (some [⟨false, nes (longType 0), none⟩, ⟨false, nes (longType 1), none⟩,
          ⟨false, nes (longType 2), none⟩]) (nes "a-long-module-name") [] true))]⟩ }
  , { name := "export-type-many-specifiers"
      prog := ⟨[.exportDecl (.fromClause true
        [⟨false, nes (longType 0), none⟩, ⟨false, nes (longType 1), none⟩,
         ⟨false, nes (longType 2), none⟩] (nes "a-long-module-name") [])]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
