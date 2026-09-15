import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part ten

The samples of this file cover the remaining positions a type operator may
be written in — the head of `if`, `while`, `for … of`, `for … in` and
`switch`, an assignment target read through a property, a default
parameter value, a computed key, the `extends` clause of a class, and the
initialiser of a member of an `enum` — together with a batch of layouts
that had no sample of their own: a getter whose return type breaks, the
overload signatures of an interface method, a type alias of a function
type, a type parameter whose constraint breaks and one with a function
type as its default, a nested conditional type, a constructor of decorated
parameter properties, a rest parameter of a tuple type, a generic method of
an object literal, a nested ambient namespace, a member chain read at type
arguments, an optional chain, a default export of a `satisfies`, and a
curried arrow whose return types are function types.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A long union type, which has to break. -/
private def longUnion10 : MiniTsType :=
  .union [ty (longType 0), ty (longType 1), ty (longType 2), ty (longType 3)]

/-- The samples. -/
def samples10 : List Sample :=
  [ { name := "as-in-statement-heads"
      prog := ⟨[st (.if_ (.asExpr (v "theValue") (ty "boolean")) (.block []) none),
        st (.while_ (.nonNull (v "theValue")) (.block [])),
        st (.forOf false (.decl .const (.ident (nes "item")))
          (.asExpr (v "theList") (tyA "Array" [ty "number"])) (.block [])),
        st (.forIn (.decl .const (.ident (nes "key")))
          (.asExpr (v "theObject") (ty "object")) (.block [])),
        st (.switch (.asExpr (v "theValue") (ty "number")) [])]⟩ }
  , { name := "as-assignment-target-member"
      prog := ⟨[es (.assign (.dot (.asExpr (v "theValue") (ty "any")) (nes "key")) .assign
        (num 1))]⟩ }
  , { name := "as-in-default-parameter"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [.plain [] {} (.withDefault (p "x") (.asExpr (v "theValue") (ty "T"))) false
          (some (ty "T"))] none (some []))]⟩ }
  , { name := "as-in-computed-key"
      prog := ⟨[st (constDecl "theObject" none (.object
        [.keyValue (.computed (.asExpr (v "theKey") (ty "string"))) (num 1)]))]⟩ }
  , { name := "class-heritage-as"
      prog := ⟨[st (.classDecl [] false (nes "C") []
        (some ⟨.asExpr (v "Base") (ty "any"), []⟩) [] [])]⟩ }
  , { name := "implements-qualified-generic"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none
        [⟨.qualified (.ident (nes "ANamespaceName")) (nes "AnInterfaceName"), [ty "number"]⟩] [])]⟩ }
  , { name := "getter-long-union"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .get (.ident (nes "aPropertyWithALongName")) false [] []
          (some longUnion10) (some [.return_ (some (v "x"))])])]⟩ }
  , { name := "interface-method-overloads"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [.method .normal (.ident (nes "m")) false [] [parT "x" (ty "number")] (some (ty "void")),
         .method .normal (.ident (nes "m")) false [] [parT "x" (ty "string")]
          (some (ty "void"))])]⟩ }
  , { name := "type-alias-long-function-type"
      prog := ⟨[st (.typeAlias (nes "AHandlerTypeName") []
        (.fn [] [parT "aParameterName" (ty (longType 0)),
          parT "anotherParameter" (ty (longType 1))] (ty (longType 2))))]⟩ }
  , { name := "type-param-long-constraint"
      prog := ⟨[st (.typeAlias (nes "ATypeAliasName")
        [tpC "TheTypeParameter" (.union [ty (longType 0), ty (longType 1), ty (longType 2)])]
        (ty "TheTypeParameter"))]⟩ }
  , { name := "type-param-function-default"
      prog := ⟨[st (.typeAlias (nes "T")
        [⟨false, none, nes "F", none, some (.fn [] [parT "value" (ty "string")] (ty "void"))⟩]
        (ty "F"))]⟩ }
  , { name := "return-nested-conditional"
      prog := ⟨[st (.typeAlias (nes "T") [tp "A", tp "B"]
        (.conditional (ty "A") (ty "string")
          (.conditional (ty "B") (ty "number") (ty (longType 0)) (ty (longType 1)))
          (ty (longType 2))))]⟩ }
  , { name := "constructor-decorated-parameter-properties"
      prog := ⟨[st (.classDecl [] false (nes "AServiceClassName") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [.call (v "Inject") [] [v "TOKEN"]]
            { accessibility := some .private_, isReadonly := true } (p "theDependency") false
            (some (ty (longType 0))),
           .plain [] { accessibility := some .public_ } (p "another") false
            (some (ty (longType 1)))]
          none (some [])])]⟩ }
  , { name := "rest-parameter-tuple-type"
      prog := ⟨[st (.funcDecl false false (nes "f") []
        [.rest [] (p "args") (some (.tuple [.named (nes "first") false false (ty "string"),
          .named (nes "rest") false true (.array (ty "number"))]))] none (some []))]⟩ }
  , { name := "object-literal-generic-method"
      prog := ⟨[st (constDecl "theObject" none (.object
        [.method .normal (.ident (nes "aMethodName")) [tp "T"] [parT "value" (ty "T")]
          (some (ty "T")) [.return_ (some (v "value"))]]))]⟩ }
  , { name := "declare-namespace-nested"
      prog := ⟨[st (.declare_ (.namespaceDecl false (.qualified ⟨nes "Outer", []⟩)
        (some [.stmt (.namespaceDecl false (.qualified ⟨nes "Inner", []⟩)
          (some [.stmt (.typeAlias (nes "T") [] (ty "number"))]))])))]⟩ }
  , { name := "chain-with-type-args-breaks"
      prog := ⟨[st (constDecl "aLongIdentifierNameNumberZero" none
        (.call (.dot (.call (.dot (v "theObjectName") (nes "aMethodWithALongName"))
          [ty (longType 0)] [v "argument"]) (nes "anotherMethodName")) [ty (longType 1)] []))]⟩ }
  , { name := "optional-chain-nonnull-type-args"
      prog := ⟨[es (.chain (v "theObject")
        ⟨.dot true (nes "aMethodWithALongName"),
          [.call false [ty (longType 0)] [v "anArgumentName"], .nonNull,
            .dot false (nes "anotherProperty")]⟩)]⟩ }
  , { name := "enum-as-initialiser"
      prog := ⟨[st (.enum_ false (nes "E")
        [⟨.ident (nes "A"), some (.asExpr (num 1) (ty "number"))⟩])]⟩ }
  , { name := "export-default-satisfies"
      prog := ⟨[.exportDecl (.defaultExpr (.satisfies (.object
        [.keyValue (.ident (nes "aKeyName")) (num 1)]) (tyA "Config" [ty "number"])))]⟩ }
  , { name := "curried-arrow-return-types"
      prog := ⟨[st (constDecl "aCurriedFunctionName" none
        (.arrow false [] [parT "first" (ty (longType 0))]
          (some (.fn [] [parT "second" (ty (longType 1))] (ty (longType 2))))
          (.expr (.arrow false [] [parT "second" (ty (longType 1))] (some (ty (longType 2)))
            (.expr (v "second"))))))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
