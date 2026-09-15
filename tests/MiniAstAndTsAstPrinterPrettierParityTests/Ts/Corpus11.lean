import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part eleven

The samples of this file cover prettier's layout of an assignment whose
left hand side carries a type annotation: when the type arguments of the
annotation break and the value keeps the line of the `=`, when the value
moves to a line of its own instead, and when it hugs — for a declarator
and for a field of a class, with the value a call, an `await`, an object
literal, an arrow, a conditional, an operator chain, a `new`, a template
literal, an instantiation expression, a hugged call argument and a member
chain — together with an `as` written as the right hand side of an
assignment and as the argument of `return`.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A call that all but fills the line. -/
private def aCall11 : MiniExpr :=
  .call (v "aFunctionWithARatherLongName") [] [v "theFirstArgument", v "theSecondArg"]

/-- The samples. -/
def samples11 : List Sample :=
  [ { name := "declarator-generic-annotation-breaks"
      prog := ⟨[st (constDecl "aValueName" (some (tyA "AGenericTypeName"
        [ty (longType 0), ty (longType 1)])) aCall11)]⟩ }
  , { name := "declarator-simple-annotation"
      prog := ⟨[st (constDecl "aLongerValueNameHere" (some (ty "SomeTypeName")) aCall11)]⟩ }
  , { name := "declarator-union-annotation"
      prog := ⟨[st (constDecl "aValueName"
        (some (.union [ty (longType 0), ty (longType 1)])) aCall11)]⟩ }
  , { name := "declarator-annotation-and-await"
      prog := ⟨[st (.funcDecl true false (nes "f") [] [] none
        (some [constDecl "aValueName" (some (tyA "Promise" [ty (longType 0)]))
          (.await aCall11)]))]⟩ }
  , { name := "declarator-annotation-object-literal"
      prog := ⟨[st (constDecl "aValueName" (some (tyA "Record" [ty "string", ty (longType 0)]))
        (.object [.keyValue (.ident (nes "aKeyName")) (v "aValue"),
          .keyValue (.ident (nes "anotherKeyName")) (v "anotherValue")]))]⟩ }
  , { name := "declarator-annotation-arrow"
      prog := ⟨[st (constDecl "aHandlerName" (some (.fn [] [parT "event" (ty (longType 0))]
          (ty "void")))
        (.arrow false [] [par "event"] none (.expr (.object []))))]⟩ }
  , { name := "declarator-annotation-conditional"
      prog := ⟨[st (constDecl "aValueName" (some (ty (longType 0)))
        (.ternary (v "theCondition") (v "theFirstValueName") (v "theSecondValueName")))]⟩ }
  , { name := "declarator-annotation-binary"
      prog := ⟨[st (constDecl "aValueName" (some (ty (longType 0)))
        (.binary (v "theFirstOperandName") .plus
          (.binary (v "theSecondOperandName") .plus (v "theThirdOperand"))))]⟩ }
  , { name := "field-annotation-breaks"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] {} false (.ident (nes "aFieldName"))
          false false (some (tyA "AGenericTypeName" [ty (longType 0), ty (longType 1)]))
          (some aCall11)])]⟩ }
  , { name := "field-annotation-long-init"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.field [] { isStatic := true } false (.ident (nes "aFieldName")) false false
          (some (ty "SomeTypeName"))
          (some (.call (v "aFunctionWithAVeryLongNameHere") [] [v "anArgumentName"]))])]⟩ }
  , { name := "assignment-as-rhs-breaks"
      prog := ⟨[es (.assign (v "aVariableWithALongName") .assign
        (.asExpr aCall11 (tyA "AGenericTypeName" [ty (longType 0)])))]⟩ }
  , { name := "return-as-breaks"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [] none
        (some [.return_ (some (.asExpr aCall11 (.union [ty (longType 0), ty (longType 1)])))]))]⟩ }
  , { name := "declarator-instantiation"
      prog := ⟨[st (constDecl "aValueName" (some (ty (longType 0)))
        (.instantiation (v "aFunctionWithARatherLongName") [ty (longType 1)]))]⟩ }
  , { name := "declarator-annotation-hugged-arrow-arg"
      prog := ⟨[st (constDecl "aValueName" (some (tyA "Array" [ty (longType 0)]))
        (.call (.dot (v "theList") (nes "map")) []
          [.arrow false [] [parT "item" (ty (longType 1))] none (.expr (v "item"))]))]⟩ }
  , { name := "declarator-annotation-member-chain"
      prog := ⟨[st (constDecl "aValueName" (some (tyA "Array" [ty (longType 0)]))
        (.call (.dot (.call (.dot (v "theListName") (nes "filter")) [] [v "thePredicate"])
          (nes "map")) [] [v "theMapper"]))]⟩ }
  , { name := "param-annotation-default-breaks"
      prog := ⟨[st (.funcDecl false false (nes "aFunctionWithALongName") []
        [.plain [] {} (.withDefault (p "theParameter") (.object [])) false
          (some (tyA "Partial" [ty (longType 0)]))] none (some []))]⟩ }
  , { name := "declarator-annotation-new"
      prog := ⟨[st (constDecl "aValueName" (some (tyA "AGenericTypeName" [ty (longType 0)]))
        (.new (v "AClassWithALongName") [] [v "anArgumentName"]))]⟩ }
  , { name := "declarator-annotation-template"
      prog := ⟨[st (constDecl "aValueName" (some (ty (longType 0)))
        (.template none [] "a rather long piece of template text " [⟨v "theValue", " here"⟩]))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
