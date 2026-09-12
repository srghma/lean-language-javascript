/-
Tests for the *extensions* of the scope safe tree.

`BrujinAST.Expr` and `BrujinAST.Target` take two parameters, `exprExt` and
`targetExt`, each a family `Nat → Nat → Type` indexed by the scope the tree
lives in: what a tree may mention besides what the tree itself describes.
`Expr.unsafeExt` and `Target.unsafeExt` are the only ways to use one, and
the printer is told how to write one, either by an `ExtPrinter` instance or
by the two functions `printExprWith` takes.

The extension used here is a *hole*: `Hole n` in an expression, written
`?n`, and `Slot name` as an assignment target, written `@name`.  Neither is
a JavaScript expression, which is the point — an extension does not have to
be one.
-/
import Spec
import LanguageJavascriptBrujin.AST
import LanguageJavascriptBrujin.ToMini
import LanguageJavascriptBrujin.Optimizer

namespace LanguageJavascriptTests.Brujin.Extensions

open Spec
open Spec.Assert
open Language.JavaScript
open Language.JavaScript.Doc
open Language.JavaScript.BrujinAST

/-- An expression extension: a numbered hole, `?n`. -/
inductive Hole : Nat → Nat → Type where
  | mk {c m : Nat} (n : Nat) : Hole c m

/-- A target extension: a named slot to assign to, `@name`. -/
inductive Slot : Nat → Nat → Type where
  | mk {c m : Nat} (name : String) : Slot c m

/-- Neither extension mentions the variables in scope, so both survive the
removal of a binding, which is what the optimizer needs of them. -/
instance : ExtInvariant Hole where castScope | .mk n => .mk n

instance : ExtInvariant Slot where castScope | .mk n => .mk n

/-- How a hole is written. -/
def printHole : {c m : Nat} → Hole c m → Doc
  | _, _, .mk n => .text s!"?{n}"

/-- How a slot is written. -/
def printSlot : {c m : Nat} → Slot c m → Doc
  | _, _, .mk name => .text s!"@{name}"

/-- Printing the two extensions is enough to print a tree that uses them,
so a single instance makes the whole printer available. -/
instance : ExtPrinter Hole Slot where
  printUnsafeExprExt := printHole
  printUnsafeTargetExt := printSlot

/-- Another way of writing a hole, to show that how an extension appears
is the printer's to decide. -/
def printHoleLoudly : {c m : Nat} → Hole c m → Doc
  | _, _, .mk n => .text s!"HOLE{n}"

/-- Another way of writing a slot: as a plain name. -/
def printSlotBare : {c m : Nat} → Slot c m → Doc
  | _, _, .mk name => .text name

/-- A tree over the two extensions. -/
abbrev HoleExpr (c m : Nat) := Expr Hole Slot c m

/-- `?0 + x`, in a scope with one mutable variable. -/
def holePlusVar : HoleExpr 0 1 := .binary (.unsafeExt (.mk 0)) .plus (.mutVar 0)

/-- `@out = ?1` -/
def assignToSlot : HoleExpr 0 0 :=
  .assign (.unsafeExt (.mk "out")) .assign (.unsafeExt (.mk 1))

/-- `f(?0, 1 + 2)`: an ordinary call, one argument of which is a hole. -/
def callWithHole : HoleExpr 1 0 :=
  .call (.constVar 0)
    (.cons (.unsafeExt (.mk 0))
      (.cons (.binary (.number (JSNumber.ofNat 1)) .plus (.number (JSNumber.ofNat 2))) .nil))

/-- `{ ?0; }`, a block whose one statement is a hole. -/
def holeBlock : Block Hole Slot 0 0 := .cons (.expr (.unsafeExt (.mk 0))) .nil

def spec : Spec := do
  describe "BrujinAST Extensions" do
    it "an expression extension is printed by the instance" do
      shouldEqual (printExpr holePlusVar) "?0 + _m0"
    it "a target extension is printed by the instance" do
      shouldEqual (printExpr assignToSlot) "@out = ?1"
    it "an extension sits inside an ordinary tree" do
      shouldEqual (printExpr callWithHole) "_c0(?0, 1 + 2)"
    it "a block of extensions prints as a program" do
      shouldEqual (printBlock holeBlock) "?0;\n"
    it "the printers can be given to the printer instead" do
      shouldEqual (printExprWith printHole printSlot holePlusVar) (printExpr holePlusVar)
    it "how an extension is written is what the printers say" do
      shouldEqual
        (printExprWith printHoleLoudly printSlotBare assignToSlot)
        "out = HOLE1"
    it "the de Bruijn names can be used with an extension too" do
      shouldEqual (printExprIndexed holePlusVar) "?0 + l#0"
    it "the optimizer folds around an extension and leaves it alone" do
      shouldEqual (printExpr (optimizeExpr callWithHole)) "_c0(?0, 3)"

end LanguageJavascriptTests.Brujin.Extensions
