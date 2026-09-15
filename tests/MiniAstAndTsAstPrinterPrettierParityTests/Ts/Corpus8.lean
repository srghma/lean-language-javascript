import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part eight

The samples of this file pin down the layout of the wider TypeScript
shapes: a signature whose return type is a union that breaks, a type
predicate of one, a chain of conditional types written inside a type
argument, the import attributes of an `import(...)` type, the `extends`
list of an interface and the members of an `enum` that break, tuples of
labelled and of object element types, an index signature and a mapped type
whose value breaks, `declare global` with members, an export assignment of
a call read at type arguments, a call whose type arguments and arguments
both break, a generic arrow hugged as the argument of a call, a member
chain read off an `as`, a `keyof typeof` written inside an indexed access,
a decorated static member, and an arrow a `satisfies` takes parentheses
around.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A long union type, which has to break. -/
private def longUnion8 : MiniTsType :=
  .union [ty (longType 0), ty (longType 1), ty (longType 2), ty (longType 3)]

/-- The samples. -/
def samples8 : List Sample :=
  [ { name := "function-return-long-union"
      prog := ⟨[st (.funcDecl false false (nes "aFunctionWithALongName") []
        [parT "value" (ty "string")] (some longUnion8) (some []))]⟩ }
  , { name := "method-return-long-union"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "aMethodWithALongName")) false []
          [parT "value" (ty "string")] (some longUnion8) (some [])])]⟩ }
  , { name := "predicate-long-type"
      prog := ⟨[st (.funcDecl false false (nes "isOneOfThem") []
        [parT "value" (ty "unknown")]
        (some (.predicate false (nes "value") (some longUnion8))) (some []))]⟩ }
  , { name := "conditional-chain-in-type-arg"
      prog := ⟨[st (.typeAlias (nes "T") [tp "A"]
        (tyA "Wrapper" [.conditional (ty "A") (ty (longType 0)) (ty (longType 1))
          (.conditional (ty "A") (ty (longType 2)) (ty (longType 3)) (ty "never"))]))]⟩ }
  , { name := "import-type-attrs-break"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.importType false "a/rather/long/module/specifier/here"
          [⟨"resolution-mode", "import"⟩] (some (.ident (nes "Inner"))) [ty (longType 0)]))]⟩ }
  , { name := "interface-extends-long-list"
      prog := ⟨[st (.interface_ (nes "AnInterfaceWithALongName") []
        [her (longType 0), her (longType 1), her (longType 2)]
        [prop "value" (ty "number")])]⟩ }
  , { name := "enum-long-initialisers"
      prog := ⟨[st (.enum_ true (nes "AnEnumWithALongName")
        [⟨.ident (nes "aMemberWithARatherLongName"), some (.string "a rather long value here")⟩,
         ⟨.string "another member", some (.number (JSNumber.ofNat 2))⟩])]⟩ }
  , { name := "readonly-tuple-optional-labels"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.readonlyOp (.tuple [.named (nes "first") false false (ty "string"),
          .named (nes "second") true false (ty "number")])))]⟩ }
  , { name := "tuple-of-object-types"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.tuple [.elem (.objectType [prop "aLongPropertyNameHere" (ty "string")]),
          .elem (.objectType [prop "anotherLongPropertyName" (ty "number")])]))]⟩ }
  , { name := "index-signature-long-type"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [.indexSig false (nes "aKeyNameHere") (ty "string") longUnion8])]⟩ }
  , { name := "declare-global-members"
      prog := ⟨[st (.declare_ (.namespaceDecl false .global
        (some [.stmt (.interface_ (nes "Window") [] [] [prop "aPropertyName" (ty "number")]),
          .stmt (.declare_ (.decl .const ⟨declT "value" (some (ty "string")) none, []⟩))])))]⟩ }
  , { name := "export-assign-long-call"
      prog := ⟨[.exportDecl (.assign (.call (.dot (v "aModuleObjectName")
        (nes "aMethodWithALongName")) [ty (longType 0)] [v "anArgumentName"]))]⟩ }
  , { name := "call-type-args-and-args-break"
      prog := ⟨[es (.call (v "aFunctionWithALongName") [ty (longType 0), ty (longType 1)]
        [v "aFirstArgumentName", v "aSecondArgumentName"])]⟩ }
  , { name := "generic-arrow-hugged-last-arg"
      prog := ⟨[es (.call (v "useMemo") []
        [.arrow false [tpC "T" (ty (longType 0))] [parT "value" (ty "T")] (some (ty "T"))
          (.block [.return_ (some (v "value"))])])]⟩ }
  , { name := "as-object-of-broken-chain"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZero" none
        (.call (.dot (.call (.dot (.asExpr (v "theValue") (ty (longType 0)))
          (nes "aMethodWithALongName")) [] []) (nes "anotherMethodName")) [] []))]⟩ }
  , { name := "keyof-typeof-chain"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.indexed (.typeQuery (.qualified (.ident (nes "AModuleName")) (nes "aValueName")) [])
          (.keyof (.typeQuery (.ident (nes "anotherValueName")) []))))]⟩ }
  , { name := "mapped-long-value"
      prog := ⟨[st (.typeAlias (nes "AMappedTypeName") [tp "K"]
        (.mapped none (nes "P") (.keyof (ty "K")) none none (some longUnion8)))]⟩ }
  , { name := "decorated-static-member"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [.call (v "Decorator") [] [.string "an argument"]]
          { isStatic := true, isReadonly := true } false (.ident (nes "x")) false false
          (some (ty "number")) (some (num 1))])]⟩ }
  , { name := "satisfies-arrow"
      prog := ⟨[st (constDecl "aHandlerWithALongName" none
        (.satisfies (.arrow false [] [parT "event" (ty (longType 0))] none (.expr (.object [])))
          (tyA "Handler" [ty (longType 1)])))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
