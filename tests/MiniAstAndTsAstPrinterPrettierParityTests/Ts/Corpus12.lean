import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part twelve

A last batch of shapes that had no sample of their own: a default export
inside an ambient module, a default export of an `as`, an abstract class
with an index signature and both heritage clauses, a `satisfies` written
as the argument of a call, `keyof` of a mapped type, generic type
arguments nested deeply enough to break, an array and a union of function
types, a `readonly` array of a union, a chain of indexed accesses, an
interface whose one method fills the line, `infer … extends` with long
branches, a tuple of optional and rest elements, an `import(...)` type as
the type of a field and a `typeof import(...)` read through a qualified
name, a generic call written as an argument, an array of `as` expressions,
and an import whose specifiers carry the `type` modifier and break.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- The samples. -/
def samples12 : List Sample :=
  [ { name := "ambient-module-default-class"
      prog := ⟨[st (.declare_ (.namespaceDecl true (.str "a-module")
        (some [.exportDecl (.defaultDecl (.classDecl [] false (nes "C") [] none []
          [.method [] {} .normal (.ident (nes "m")) false [] [] (some (ty "void")) none]))])))]⟩ }
  , { name := "export-default-as"
      prog := ⟨[.exportDecl (.defaultExpr (.asExpr (v "theValue") (ty "AConfigTypeName")))]⟩ }
  , { name := "abstract-class-index-signature"
      prog := ⟨[st (.classDecl [] true (nes "C") [] (some ⟨v "Base", []⟩) [her "AnInterfaceName"]
        [.indexSig {} (nes "key") (ty "string") (ty "unknown"),
         .method [] { isAbstract := true } .normal (.ident (nes "m")) false [] []
          (some (ty "void")) none])]⟩ }
  , { name := "satisfies-in-arguments"
      prog := ⟨[es (.call (v "aFunctionWithALongName") []
        [.satisfies (.object [.keyValue (.ident (nes "aKeyName")) (num 1)])
          (tyA "AConfigTypeName" [ty (longType 0)])])]⟩ }
  , { name := "keyof-mapped-type"
      prog := ⟨[st (.typeAlias (nes "T") [tp "K"]
        (.keyof (.mapped none (nes "P") (.keyof (ty "K")) none none (some (ty "boolean")))))]⟩ }
  , { name := "nested-generics-break"
      prog := ⟨[st (letDecl "aValueName" (some (tyA "AGenericTypeName"
        [tyA "AnotherGenericName" [ty (longType 0), ty (longType 1)], ty (longType 2)])))]⟩ }
  , { name := "array-of-function-types"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.array (.fn [] [parT "value" (ty "string")] (ty "void"))))]⟩ }
  , { name := "readonly-array-of-union"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.readonlyOp (.array (.union [ty (longType 0), ty (longType 1)]))))]⟩ }
  , { name := "indexed-access-chain"
      prog := ⟨[st (.typeAlias (nes "ALongTypeAliasNameHere") []
        (.indexed (.indexed (ty (longType 0)) (.strLit "aRatherLongPropertyName"))
          (.strLit "anotherLongPropertyName")))]⟩ }
  , { name := "interface-one-long-method"
      prog := ⟨[st (.interface_ (nes "I") [] []
        [.method .normal (.ident (nes "aMethodWithARatherLongName")) false [tp "T"]
          [parT "theFirstParameter" (ty (longType 0)), parT "second" (ty "T")]
          (some (tyA "Promise" [ty (longType 1)]))])]⟩ }
  , { name := "function-type-in-union-breaks"
      prog := ⟨[st (.typeAlias (nes "AHandlerTypeName") []
        (.union [.fn [] [parT "value" (ty (longType 0))] (ty "void"),
          .fn [] [parT "value" (ty (longType 1))] (ty "void"), ty "null"]))]⟩ }
  , { name := "infer-extends-long-branches"
      prog := ⟨[st (.typeAlias (nes "T") [tp "A"]
        (.conditional (ty "A") (tyA "Array" [.infer_ (nes "U") (some (ty (longType 0)))])
          (ty (longType 1)) (ty (longType 2))))]⟩ }
  , { name := "tuple-many-optionals"
      prog := ⟨[st (.typeAlias (nes "ATupleTypeName") []
        (.tuple [.elem (ty (longType 0)), .optional (ty (longType 1)),
          .optional (ty (longType 2)), .rest (.array (ty (longType 3)))]))]⟩ }
  , { name := "import-type-field"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { isReadonly := true } false (.ident (nes "aFieldName")) false false
          (some (.importType false "a-module" [] (some (.ident (nes "AnExportedType")))
            [ty "string"])) none])]⟩ }
  , { name := "typeof-import-qualified"
      prog := ⟨[st (.typeAlias (nes "T") []
        (.importType true "a-module" [] (some (.qualified (.ident (nes "Inner"))
          (nes "Deeper"))) []))]⟩ }
  , { name := "generic-call-in-arguments"
      prog := ⟨[es (.call (v "aFunctionWithALongName") []
        [.call (v "anInnerFunctionName") [ty (longType 0)] [v "theArgumentName"],
          v "anotherArgument"])]⟩ }
  , { name := "as-in-array-of-objects"
      prog := ⟨[st (constDecl "theList" none
        (.array [.elem (.asExpr (.object [.keyValue (.ident (nes "aKeyName")) (num 1)])
            (ty (longType 0))),
          .elem (.asExpr (.object [.keyValue (.ident (nes "aKeyName")) (num 2)])
            (ty (longType 1)))]))]⟩ }
  , { name := "type-only-specifiers-break"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
        (some [⟨true, nes "AFirstTypeName", none⟩, ⟨false, nes "aValueName", none⟩,
          ⟨true, nes "AnotherTypeName", some (nes "Renamed")⟩]) (nes "a-rather-long-module")))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
