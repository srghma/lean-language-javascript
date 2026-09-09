/-
Embedding JavaScript in Lean source, as a *scope safe* tree.

    open Language.JavaScript.BrujinAST in
    def program : Program :=
      [jsb| const greeting = "hello";
            function greet(name) {
              console.log(`${c#1} ${l#0}`);
            }
            greet("world");
      |end_js]

This is the `BrujinAST` counterpart of `[js| ... |end_js]`.  The text
between `[jsb|` and `|end_js]` is read verbatim — it is not Lean syntax —
and is parsed *and scope checked* while Lean elaborates the file, so a
JavaScript syntax error, an assignment to a `const`, a de Bruijn index that
is out of range or anything else `BrujinAST` cannot describe is reported as
an elaboration error rather than at run time.

**Naming a variable by its index.**  Besides an ordinary name, which is
resolved lexically (and becomes `unsafeGlobal` when nothing binds it), a
variable may be written with its de Bruijn index:

* `c#0`, `c#1`, … is the const scope — a `const`, a `function` or `class`
  declaration, an imported name — `c#0` being the innermost one;
* `l#0`, `l#1`, … is the mutable scope — a `let` or `var`, a parameter, a
  `catch` binder — `l#0` being the innermost one.

`printProgramIndexed` prints a tree in exactly this notation, so a program
printed that way can be pasted back into `[jsb| ... |end_js]` and gives the
same tree.

`[jsb_expr| ... |end_js]` reads a single expression in the empty scope, and
`[jsb_expr c m| ... |end_js]` one in a scope of `c` const and `m` mutable
variables, which it may name by their indices.

The elaborated term is `parseIndexed!` (respectively `parseExprIndexed!`)
applied to the source: the elaborator has already checked that this
succeeds.
-/
import Lean
import LanguageJavascriptBrujin.OfMini
import LanguageJavascriptBrujin.ToMini
import LanguageJavascriptMini.Elab

namespace Language.JavaScript.BrujinAST

open Lean
open Language.JavaScript.MiniAST.Embed

/-- A JavaScript program, written in JavaScript syntax, as a scope safe
`Program`. -/
syntax:max (name := jsbProgramTerm) "[jsb|" jsRaw : term

/-- A JavaScript expression in the empty scope, as a `BrujinAST` `Expr`. -/
syntax:max (name := jsbExprTerm) "[jsb_expr|" jsRaw : term

/-- A JavaScript expression in a scope of `c` const and `m` mutable
variables, as a `BrujinAST` `Expr`. -/
syntax:max (name := jsbExprScopedTerm) "[jsb_expr" num num "|" jsRaw : term

open Lean.Elab Lean.Elab.Term in
@[term_elab jsbProgramTerm]
def elabJsbProgram : TermElab := fun stx _ => do
  let src := stx[1].getAtomVal
  match parseIndexed src with
  | .ok _ => return mkApp (mkConst ``parseIndexed!) (toExpr src)
  | .error e => throwErrorAt stx e

/-- Elaborate an embedded expression in the scope `(c, m)`. -/
private def elabScopedExpr (stx : Syntax) (c m : Nat) (src : String) :
    Elab.Term.TermElabM Lean.Expr :=
  match parseExprIndexed c m src with
  | .ok _ =>
      return mkApp3 (mkConst ``parseExprIndexed!) (toExpr c) (toExpr m) (toExpr src)
  | .error e => throwErrorAt stx e

open Lean.Elab Lean.Elab.Term in
@[term_elab jsbExprTerm]
def elabJsbExpr : TermElab := fun stx _ =>
  elabScopedExpr stx 0 0 stx[1].getAtomVal

open Lean.Elab Lean.Elab.Term in
@[term_elab jsbExprScopedTerm]
def elabJsbExprScoped : TermElab := fun stx _ => do
  let some c := stx[1].isNatLit? | throwErrorAt stx[1] "expected a numeral"
  let some m := stx[2].isNatLit? | throwErrorAt stx[2] "expected a numeral"
  elabScopedExpr stx c m stx[4].getAtomVal

end Language.JavaScript.BrujinAST
