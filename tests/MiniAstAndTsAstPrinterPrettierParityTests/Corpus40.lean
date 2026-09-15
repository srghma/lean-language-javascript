import Tests.Corpus39

/-!
# Decorators written as a member access

Prettier keeps the `.` of a decorator on the line of what it reads from,
however long the name is: `@A.b` is never broken in two, while a longer
chain of accesses is laid out the way a member chain is.  The samples
here pin both down, on a class, on a field and on a method.

The last two cover the field whose decorators make its left hand side one
that breaks, so that its value no longer keeps the line of the `=`.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A decorator read through a namespace, too long for one line. -/
private def longMemberDecorator : MiniExpr :=
  .dot (v "AVeryVeryLongDecoratorNamespaceNameHere")
    (nes "theVeryLongNameOfTheDecoratorItself")

/-- A long chain of accesses, which is laid out as a member chain. -/
private def longChainDecorator : MiniExpr :=
  .dot (.dot (.dot (.dot (.dot (.dot (.dot (v "Foo") (nes "barTheFirstOne"))
    (nes "bazTheSecondOne")) (nes "quxTheThirdOne")) (nes "longerAndLongerAndLonger"))
    (nes "moreOfThem")) (nes "evenMoreOfThem")) (nes "yetMoreOfThemHere")

/-- The samples of this file. -/
def samples40 : List Sample :=
  [ { name := "member-decorator-on-class"
      prog := ⟨[st (.classDecl [longMemberDecorator] (nes "D") none [])]⟩ }
  , { name := "member-decorator-on-field"
      prog := ⟨[st (.classDecl [] (nes "B") none
        [.field [longMemberDecorator] false false (.ident (nes "fieldName")) (some (num 1))])]⟩ }
  , { name := "member-decorator-on-method"
      prog := ⟨[st (.classDecl [] (nes "C") none
        [.method [longMemberDecorator] false .normal (.ident (nes "methodName")) [] []])]⟩ }
  , { name := "chain-decorator-on-method"
      prog := ⟨[st (.classDecl [] (nes "E") none
        [.method [longChainDecorator] false .normal (.ident (nes "m")) [] []])]⟩ }
  , { name := "decorated-field-class-value"
      prog := ⟨[st (.classDecl [] (nes "Outer") none
        [.field [call "Record" [], call "ReadonlyArray" []] true true
          (.ident (nes "theFieldNameThatIsRatherLongIndeedYesQuiteLongEnough"))
          (some (.classExpr [] (some (nes "T")) none
            [.field [] true false (.ident (nes "abc")) (some (num 1))]))])]⟩ }
  , { name := "field-class-value-no-decorators"
      prog := ⟨[st (.classDecl [] (nes "Outer") none
        [.field [] true true
          (.ident (nes "theFieldNameThatIsRatherLongIndeedYesQuiteLongEnough"))
          (some (.classExpr [] (some (nes "T")) none
            [.field [] true false (.ident (nes "abc")) (some (num 1))]))])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
