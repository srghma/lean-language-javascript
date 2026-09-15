import Tests.Corpus40

/-!
# Conditional expressions in every position

Prettier lays a conditional expression out in two quite different ways:
its default one, with the `?` and the `:` in front of the branches, and
the one `experimentalTernaries` selects, which writes the `?` at the end
of the line of the test and reads a chain of conditionals as a list of
cases.  The two differ in more than spelling -- which conditional is
grouped, which branch keeps the line of the operator, where the chain is
indented, and whether a conditional written in the test of another takes
parentheses -- and the rules depend on the position the conditional
stands in.

The samples here write conditionals in the positions those rules
distinguish, so that both layouts are pinned down: the right hand side of
an assignment, of a declarator, of a property and of a field (an
`accessor` field among them), the argument of `return`, of `throw` and of
a call, the object of a member access, the callee of a call, an operand of
an operator, the body of an arrow function, a substitution of a template
literal, the head of a statement, and the `{ }` of a JSX attribute and of
a JSX child, each with a chain and with a single conditional, and with
branches of the shapes the layouts read: a short one, a literal, an
object, an array and a JSX element.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A conditional expression. -/
private def tern (c a b : MiniExpr) : MiniExpr := .ternary c a b

/-- A test which is long enough to fill a line on its own. -/
private def longTest : MiniExpr :=
  .binary (.dot (v "theConfigurationObject") (nes "theSelectedValue")) .strictEq
    (.string "the value which was selected")

/-- A chain of four conditionals. -/
private def chain4 : MiniExpr :=
  tern (v "firstConditionHolds") (.string "the first label")
    (tern (v "secondConditionHolds") (.string "the second label")
      (tern (v "thirdConditionHolds") (.string "the third label")
        (.string "the label of the last case")))

/-- A conditional whose consequent is short, which prettier's
experimental layout writes as a case. -/
private def shortCase : MiniExpr :=
  tern (v "theCondition") (.string "yes")
    (.dot (v "theConfigurationObject") (nes "theRatherLongFallbackValue"))

/-- A conditional too long for one line, with plain branches. -/
private def plainLong : MiniExpr :=
  tern (v "theConditionBeingTested") (v "theValueOfTheFirstBranchHere")
    (v "theValueOfTheSecondBranchHere")

/-- A conditional whose branches are an object and an array. -/
private def objArray : MiniExpr :=
  tern (v "theConditionBeingTested")
    (.object [.keyValue (.ident (nes "theFirstKey")) (num 1),
      .keyValue (.ident (nes "theSecondKey")) (num 2)])
    (.array [.elem (v "theFirstElement"), .elem (v "theSecondElement")])

/-- A JSX element, for the branches of a conditional written in JSX. -/
private def elem0 (name : String) : MiniExpr :=
  .jsx (.element (.ident (nes name)) [] none)

/-- The samples of this file. -/
def samples41 : List Sample :=
  [ { name := "cond-statement"
      prog := ⟨[es plainLong, es chain4, es shortCase]⟩ }
  , { name := "cond-declarator"
      prog := ⟨[st (constDecl "theSelectedValue" plainLong),
                st (constDecl "theSelectedLabel" chain4),
                st (constDecl "theShortCaseValue" shortCase),
                st (constDecl "theObjectOrTheArray" objArray)]⟩ }
  , { name := "cond-declarator-long-test"
      prog := ⟨[st (constDecl "theSelectedValue"
                  (tern longTest (v "theValueOfTheFirstBranch")
                    (v "theValueOfTheSecondBranch")))]⟩ }
  , { name := "cond-assignment"
      prog := ⟨[es (.assign (v "theSelectedValue") .assign plainLong),
                es (.assign (.dot (v "theConfigurationObject") (nes "selected")) .assign chain4),
                es (.assign (v "a") .assign (.assign (v "b") .assign plainLong))]⟩ }
  , { name := "cond-property"
      prog := ⟨[es (.object
                  [.keyValue (.ident (nes "k")) plainLong,
                   .keyValue (.ident (nes "theRatherLongPropertyName")) chain4,
                   .keyValue (.ident (nes "shortCaseHere")) shortCase])]⟩ }
  , { name := "cond-class-field"
      prog := ⟨[st (.classDecl [] (nes "C") none
                  [.field [] false false (.ident (nes "theFieldName")) (some plainLong),
                   .field [] false true (.ident (nes "theAccessorName")) (some shortCase),
                   .field [] false false (.ident (nes "theChainField")) (some chain4)])]⟩ }
  , { name := "cond-return"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [.return_ (some plainLong)]),
                st (.funcDecl false false (nes "g") [] [.return_ (some chain4)]),
                st (.funcDecl false false (nes "h") [] [.return_ (some shortCase)])]⟩ }
  , { name := "cond-throw"
      prog := ⟨[st (.throw plainLong), st (.throw chain4)]⟩ }
  , { name := "cond-call-argument"
      prog := ⟨[es (call "theFunctionBeingCalled" [plainLong]),
                es (call "theFunctionBeingCalled" [v "first", chain4]),
                es (.new (v "TheClassBeingBuilt") [shortCase])]⟩ }
  , { name := "cond-array-element"
      prog := ⟨[es (.array [.elem plainLong]), es (.array [.elem chain4])]⟩ }
  , { name := "cond-member-object"
      prog := ⟨[es (.dot plainLong (nes "theFieldRead")),
                es (.index chain4 (num 0)),
                st (constDecl "theSelectedValue" (.dot plainLong (nes "theFieldRead")))]⟩ }
  , { name := "cond-callee"
      prog := ⟨[es (.call plainLong [v "theArgument"]),
                es (.call chain4 [])]⟩ }
  , { name := "cond-operand"
      prog := ⟨[es (.binary plainLong .plus (v "theOtherOperandHere")),
                es (.unary .not plainLong),
                es (.await plainLong)]⟩ }
  , { name := "cond-arrow-body"
      prog := ⟨[st (constDecl "theSelectingFunction"
                  (.arrow false [par "theCondition"] (.expr plainLong))),
                st (constDecl "theChainFunction"
                  (.arrow false [par "theCondition"] (.expr chain4)))]⟩ }
  , { name := "cond-template-substitution"
      prog := ⟨[es (.template none "the value is " [⟨plainLong, " indeed"⟩]),
                es (.template none "the label is " [⟨chain4, ""⟩])]⟩ }
  , { name := "cond-statement-head"
      prog := ⟨[st (.if_ plainLong (.expr (call "f" [])) none),
                st (.while_ plainLong (.expr (call "f" []))),
                st (.switch plainLong [])]⟩ }
  , { name := "cond-in-test"
      prog := ⟨[st (constDecl "theSelectedValue"
                  (tern (tern (v "theInnerCondition") (v "theInnerConsequent")
                      (v "theInnerAlternate"))
                    (v "theOuterConsequentValue") (v "theOuterAlternateValue")))]⟩ }
  , { name := "cond-in-consequent"
      prog := ⟨[st (constDecl "theSelectedValue"
                  (tern (v "theOuterCondition")
                    (tern (v "theInnerCondition") (v "theInnerConsequent")
                      (v "theInnerAlternate"))
                    (v "theOuterAlternateValue")))]⟩ }
  , { name := "cond-spread-and-key"
      prog := ⟨[es (call "theFunctionBeingCalled" [.spread plainLong]),
                es (.object [.keyValue (.computed plainLong) (num 1)])]⟩ }
  , { name := "cond-jsx-attribute"
      prog := ⟨[es (.jsx (.element (.ident (nes "Foo"))
                  [.attr (.ident (nes "value")) (some (.expr chain4))] none)),
                es (.jsx (.element (.ident (nes "Foo"))
                  [.attr (.ident (nes "value")) (some (.expr plainLong))] none))]⟩ }
  , { name := "cond-jsx-child"
      prog := ⟨[es (.jsx (.element (.ident (nes "Foo")) []
                  (some [.expr chain4]))),
                es (.jsx (.element (.ident (nes "Foo")) []
                  (some [.expr (tern (v "theConditionBeingTested") (elem0 "First")
                    (tern (v "theOtherCondition") (elem0 "Second") .null))])))]⟩ }
  , { name := "cond-jsx-branches"
      prog := ⟨[st (constDecl "theRenderedElement"
                  (tern (v "theConditionBeingTested") (elem0 "TheFirstComponent")
                    (elem0 "TheSecondComponent"))),
                st (constDecl "theRenderedOrNothing"
                  (tern (v "theConditionBeingTested") (elem0 "TheFirstComponent") .null))]⟩ }
  , { name := "cond-short-cases"
      prog := ⟨[st (constDecl "theFirstSelection"
                  (tern (v "cond") (.string "yes") (.string "no"))),
                st (constDecl "theSecondSelection"
                  (tern (.dot (v "theConfiguration") (nes "flag")) (num 1)
                    (call "theFallbackFunction" [v "theArgumentValue"]))),
                st (constDecl "theThirdSelection"
                  (tern (call "isTheConditionTrue" []) (.unary .minus (num 1))
                    (v "theRatherLongAlternateValueHere")))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
