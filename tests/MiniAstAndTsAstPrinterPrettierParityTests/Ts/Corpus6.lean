import Tests.Ts.Prelude

/-!
# A corpus of sample TypeScript programs, part six

The samples of this file pin down three layout rules that random programs
turned up: the parentheses prettier writes around a JSX element exported
by an export assignment, the parameter list a parameter property holds
open even when its one parameter would otherwise be hugged, and the `!` of
a non-null assertion, which keeps the line of what it is written on.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- A JSX element expression. -/
private def el (name : String) (attrs : List MiniJSXAttribute)
    (children : Option (List MiniJSXChild)) : MiniExpr :=
  .jsx (.element (.ident (nes name)) [] attrs children)

/-- A JSX attribute whose value is a string. -/
private def attrStr (name value : String) : MiniJSXAttribute :=
  .attr (.ident (nes name)) (some (.string value))

/-- An object type with two members, long enough to break. -/
private def objType : MiniTsType :=
  .objectType [prop "theIteratorOfTheList" (ty "boolean"),
    .method .normal (.ident (nes "aLongIdentifierNameNumberZero")) false [] [] (some (ty "object"))]

/-- `target9?.value!.result` -/
private def chainA : MiniExpr :=
  .chain (v "target9") ⟨.dot true (nes "value"), [.nonNull, .dot false (nes "result")]⟩

/-- `<a = -123.456, b>(): "mod" => ({})`, an arrow with no parameters whose
type parameters may have to break. -/
private def genericArrow (a b : String) : MiniExpr :=
  .arrow false
    [⟨false, none, nes a, none, some (.negNumLit (JSNumber.decimal 123456 (-3)))⟩,
      ⟨false, none, nes b, none, none⟩]
    [] (some (.strLit "mod")) (.expr (.object []))

/-- `(currentValue as const) ? (target9 ? {} : 123.456) : {}!` -/
private def ternary : MiniExpr :=
  .ternary (.asExpr (v "currentValue") (.ref (.ident (nes "const")) []))
    (.ternary (v "target9") (.object []) (.number (JSNumber.decimal 123456 (-3))))
    (.nonNull (.object []))

/-- The samples. -/
def samples6 : List Sample :=
  [ -- ## A JSX element in an export assignment
    { name := "export-assign-jsx"
      prog := ⟨[.exportDecl (.assign (el "div" [.attr (.ident (nes "value"))
        (some (.expr (num 1)))] none))]⟩ }
  , { name := "export-assign-jsx-breaks"
      prog := ⟨[.exportDecl (.assign
        (el "div" [.attr (.ident (nes "value")) (some (.expr (num 1))),
          attrStr "className" "a-very-long-class-name-here",
          attrStr "other" "another-value"] none))]⟩ }
  , { name := "export-assign-jsx-fragment"
      prog := ⟨[.exportDecl (.assign (.jsx (.fragment [.text "fragment"])))]⟩ }
  , { name := "export-assign-jsx-children"
      prog := ⟨[.exportDecl (.assign
        (el "Outer" [] (some [.node (.element (.ident (nes "Inner")) [] [] none)])))]⟩ }
  , { name := "export-assign-call"
      prog := ⟨[.exportDecl (.assign (call "f" [num 1]))]⟩ }

    -- ## A parameter property is never hugged
  , { name := "parameter-property-object-type"
      prog := ⟨[st (.classDecl [] false (nes "C") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [] { accessibility := some .protected_ } (p "result") false (some objType)]
          none (some [])])]⟩ }
  , { name := "parameter-object-type-hugged"
      prog := ⟨[st (.classDecl [] false (nes "D") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [parT "result" objType] none (some [])])]⟩ }
  , { name := "parameter-property-short"
      prog := ⟨[st (.classDecl [] false (nes "E") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [] { accessibility := some .protected_ } (p "result") false
            (some (.objectType [prop "a" (ty "boolean")]))] none (some [])])]⟩ }
  , { name := "parameter-property-destructured"
      prog := ⟨[st (.classDecl [] false (nes "F") [] none []
        [.method [] {} .normal (.ident (nes "constructor")) false []
          [.plain [] {} (.object [⟨.ident (nes "theIteratorOfTheList"), p "a"⟩,
            ⟨.ident (nes "aLongIdentifierNameNumberZero"), p "b"⟩] none) false
            (some (ty "ALongTypeNameNumberZero"))] none (some [])])]⟩ }

    -- ## The `!` of a non-null assertion keeps its line
  , { name := "nonnull-chain-as-const"
      prog := ⟨[st (.decl .const
        ⟨declT "aVeryLongVariableNameHereOkay" (some (ty "SomeLongTypeName"))
          (some (.asExpr chainA (.ref (.ident (nes "const")) []))), []⟩)]⟩ }
  , { name := "nonnull-chain-after-function-type"
      prog := ⟨[.exportDecl (.decl (.decl .const
        ⟨declT "value1209"
          (some (.fn [] [parT "g" (.strLit "ok"), parT "value" (ty "Bar")]
            (.mapped (some .remove) (nes "TValue") (ty (longType 0)) none (some .add)
              (some (.negNumLit (JSNumber.radix .hexadecimal 255))))))
          (some (.asExpr chainA (.ref (.ident (nes "const")) []))), []⟩))]⟩ }
  , { name := "nonnull-chain-plain-members"
      prog := ⟨[st (.decl .const
        ⟨declT "aVeryLongVariableNameHere" (some (ty "ALongTypeNameNumberZero"))
          (some (.dot (.dot (.nonNull (.dot (v "aLongObjectName") (nes "firstProperty")))
            (nes "secondProperty")) (nes "thirdPropertyName"))), []⟩)]⟩ }
  , { name := "hug-generic-arrow-short"
      prog := ⟨[st (constDecl "y" none
        (.call (v "g") [] [genericArrow "TKey" "TheVeryLongTypeParameterName"]))]⟩ }
  , { name := "hug-generic-arrow-breaks"
      prog := ⟨[st (constDecl "z" none
        (.call (v "g") [] [genericArrow "TKeyAndMore" "TheVeryLongTypeParameterNameHere"]))]⟩ }
  , { name := "hug-generic-arrow-in-for-of"
      prog := ⟨[st (.forOf false (.decl .const (p "item248"))
        (.call (v "f") [.ctor true [] [] (.ref (.qualified (.ident (nes "Bar")) (nes "void")) [])]
          [genericArrow "TKey" "TheVeryLongTypeParameterName"])
        (.block []))]⟩ }
  , { name := "hug-arrow-with-parameters"
      prog := ⟨[st (constDecl "w" none
        (.call (v "g") []
          [.arrow false [] [parT "aVeryLongParameterNameHere" (ty "number"),
            parT "anotherLongParameterName" (ty "string")]
            (some (.strLit "mod")) (.expr (.object []))]))]⟩ }

    -- ## A conditional inside the parentheses of an `as`
  , { name := "ternary-as-member-chain"
      prog := ⟨[st (constDecl "other498" none
        (.call (.dot (.asExpr ternary (.union [ty (longType 0), ty "null"])) (nes "map")) []
          [v "f"]))]⟩ }
  , { name := "ternary-as-declarator"
      prog := ⟨[st (constDecl "other499" none
        (.asExpr ternary (.union [ty (longType 0), ty (longType 1)])))]⟩ }
  , { name := "ternary-as-await"
      prog := ⟨[st (.funcDecl true false (nes "f") [] [] none (some
        [.expr (.await (.asExpr ternary (.union [ty (longType 0), ty (longType 1)])))]))]⟩ }
  , { name := "ternary-satisfies-member-chain"
      prog := ⟨[st (constDecl "other500" none
        (.call (.dot (.satisfies ternary (.union [ty (longType 0), ty "null"])) (nes "map")) []
          [v "f"]))]⟩ }
  , { name := "nonnull-chain-calls"
      prog := ⟨[st (.decl .const
        ⟨declT "aVeryLongVariableNameHereOk" (some (ty "ALongTypeNameNumberZero"))
          (some (.call (.dot (.nonNull (.call (.dot (v "objectName") (nes "first")) [] []))
            (nes "second")) [] [])), []⟩)]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
