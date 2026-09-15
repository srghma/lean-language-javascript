import Tests.Ts.Prelude

/-!
# The member accesses of an optional chain

Prettier keeps the accesses of a member chain on the line of their object
— rather than letting the line break in front of each of them — when the
chain is assigned to something other than a plain identifier, or is the
callee of a `new`.  It reads that off the node the chain is written in,
looking past the accesses themselves.

An optional chain hides it: where prettier reads TypeScript, a chain that
holds a `?.` is read into a chain expression of its own, and that
expression stands between the accesses and the assignment, so none of
them keeps its line for the sake of the assignment.  A chain of plain
accesses, one that is only parenthesised around the `?.`, and one whose
`!` is the only unusual link are unaffected.

The samples here pin that down, on both sides of the rule and at the
several widths the comparison scripts run: an assignment whose left hand
side is a member access, one whose left hand side is a plain identifier,
a declarator, and the callee of a `new`.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- `theObjectName.theFirstProperty.theSecondProperty`, long enough that
the line it stands on is over eighty columns once two more accesses are
written after it. -/
private def longBase : MiniExpr :=
  .dot (.dot (v "theObjectName") (nes "theFirstPropertyName")) (nes "theSecondPropertyName")

/-- The base with two more accesses, the first of them optional. -/
private def longOptionalChain : MiniExpr :=
  .chain longBase ⟨.dot true (nes "theThirdOne"), [.dot false (nes "theFourthOne")]⟩

/-- The same accesses, none of them optional. -/
private def longPlainChain : MiniExpr :=
  .dot (.dot longBase (nes "theThirdOne")) (nes "theFourthOne")

/-- The same accesses with a `!` where the `?.` stood. -/
private def longNonNullChain : MiniExpr :=
  .chain longBase ⟨.nonNull, [.dot false (nes "theThirdOne"), .dot false (nes "theFourthOne")]⟩

/-- `collection.property`, an assignment target that is not a plain
identifier. -/
private def memberTarget : MiniExpr := .dot (v "collection") (nes "property")

/-- The samples. -/
def samples16 : List Sample :=
  [ -- the rule itself: an optional chain assigned to a member access
    { name := "opt-chain-assigned-to-member"
      prog := ⟨[es (.assign memberTarget .assign longOptionalChain)]⟩ }
    -- the same chain with no `?.`, which keeps its accesses on one line
  , { name := "plain-chain-assigned-to-member"
      prog := ⟨[es (.assign memberTarget .assign longPlainChain)]⟩ }
    -- a `!` is not read into a chain expression, so it keeps them too
  , { name := "nonnull-chain-assigned-to-member"
      prog := ⟨[es (.assign memberTarget .assign longNonNullChain)]⟩ }
    -- assigned to a plain identifier, where the rule never applied
  , { name := "opt-chain-assigned-to-identifier"
      prog := ⟨[es (.assign (v "theAssignedName") .assign longOptionalChain)]⟩ }
  , { name := "plain-chain-assigned-to-identifier"
      prog := ⟨[es (.assign (v "theAssignedName") .assign longPlainChain)]⟩ }
    -- the same in a declarator
  , { name := "opt-chain-declarator"
      prog := ⟨[st (constDecl "theDeclaredName" none longOptionalChain)]⟩ }
    -- an optional chain that ends in a call, whose accesses trail the
    -- call: the chain expression hides the assignment from them as well
  , { name := "opt-chain-call-assigned-to-member"
      prog := ⟨[es (.assign memberTarget .assign
        (.chain (v "theObjectName")
          ⟨.dot true (nes "theFirstMethodName"),
           [.call false [] [], .dot false (nes "theSecondPropertyName"),
            .dot false (nes "theThirdPropertyName")]⟩))]⟩ }
    -- only the accesses inside the parentheses belong to the chain: the
    -- ones written on the parenthesised chain are read by the assignment
  , { name := "opt-chain-parenthesised-assigned-to-member"
      prog := ⟨[es (.assign memberTarget .assign
        (.dot (.dot (.chain (v "theObjectName") ⟨.dot true (nes "theFirstPropertyName"), []⟩)
          (nes "theSecondPropertyName")) (nes "theThirdPropertyName")))]⟩ }
    -- the callee of a `new`, which reads its accesses the same way
  , { name := "opt-chain-new-callee"
      prog := ⟨[es (.new (.chain (v "theObjectName")
        ⟨.dot true (nes "theFirstPropertyName"),
         [.dot false (nes "theSecondPropertyName"),
          .dot false (nes "TheConstructorName")]⟩) [] [v "theArgument"])]⟩ }
  , { name := "plain-chain-new-callee"
      prog := ⟨[es (.new (.dot (.dot (.dot (v "theObjectName") (nes "theFirstPropertyName"))
        (nes "theSecondPropertyName")) (nes "TheConstructorName")) [] [v "theArgument"])]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus
