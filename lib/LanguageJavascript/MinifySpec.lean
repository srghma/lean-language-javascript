/-
What the statement list pass of `LanguageJavascript.Minify` does, proved
rather than tested.

The pass used to be `partial`, so it had no equations and did not reduce:
nothing below could be stated, let alone proved.
-/
import LanguageJavascript.Minify

namespace Language.JavaScript.Process

open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

/-- A statement which disappears is dropped, whatever is pending. -/
theorem fixStmtList_cons_of_isRedundant (a : JSAnnot) (s : JSSemi)
    (pend : Option (Bool × JSCommaList1 JSExpression)) (x : JSStatement) (xs : List JSStatement)
    (h : isRedundantStmt x = true) :
    fixStmtList a s pend true (x :: xs) = fixStmtList a s pend true xs := by
  cases x
  case JSStatementBlock _ stmts _ _ =>
    cases stmts with
    | nil => simp [fixStmtList]
    | cons _ _ => simp [isRedundantStmt] at h
  all_goals simp_all [isRedundantStmt, fixStmtList]

/-- A list of statements which all disappear is minified to the empty
list. -/
theorem fixStmtList_eq_nil_of_allRedundant :
    ∀ (ss : List JSStatement) (a : JSAnnot) (s : JSSemi), allRedundant ss = true →
      fixStmtList a s none true ss = []
  | [], _, _, _ => rfl
  | x :: xs, a, s, h => by
      rw [allRedundant, Bool.and_eq_true] at h
      rw [fixStmtList_cons_of_isRedundant a s none x xs h.1]
      exact fixStmtList_eq_nil_of_allRedundant xs a s h.2

/-- The entry point, on a list of statements which all disappear. -/
theorem fixStatementList_eq_nil_of_allRedundant (s : JSSemi) (ss : List JSStatement)
    (h : allRedundant ss = true) : fixStatementList s ss = [] :=
  fixStmtList_eq_nil_of_allRedundant ss emptyAnnot s h

/-- The pass reduces in the kernel: `rfl` proves what it does to a given
list, which is what `partial` made impossible. -/
example : fixStatementList noSemi [.JSEmptyStatement emptyAnnot] = [] := rfl

example :
    fixStatementList noSemi
        [.JSStatementBlock emptyAnnot [] emptyAnnot noSemi, .JSEmptyStatement emptyAnnot] = [] :=
  rfl

end Language.JavaScript.Process
