/-
Embedding JavaScript in Lean source.

    open Language.JavaScript.MiniAST in
    def program : MiniProgram :=
      [js| function greet(name) {
             console.log(`hello ${name}`);
           }
      |end_js]

The text between `[js|` and `|end_js]` is read verbatim — it is not Lean
syntax, so it may contain anything except the terminator — and is parsed
*while Lean elaborates the file*.  A JavaScript syntax error is reported as
an elaboration error, and the result is a `MiniProgram` value: the layout
and the comments of the embedded source are gone by construction.

`[js_expr| ... |end_js]` does the same for a single expression, giving a
`MiniExpr`.
-/
import Lean
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.Printer

namespace Language.JavaScript.MiniAST

open Lean

/-! ## Turning a `MiniProgram` into a Lean term

`ToExpr` cannot be derived for the types with a proof carrying field, since
the derived code would have to produce a term for the proof; those two are
given by hand, in terms of the total smart constructors, which recompute the
proof. -/

instance : ToExpr NEString where
  toExpr s := mkApp (mkConst ``NEString.ofString!) (toExpr s.val)
  toTypeExpr := mkConst ``NEString

deriving instance ToExpr for NEList
deriving instance ToExpr for MiniBinOp
deriving instance ToExpr for MiniUnaryOp
deriving instance ToExpr for MiniPostfixOp
deriving instance ToExpr for MiniAssignOp
deriving instance ToExpr for MiniVarKind
deriving instance ToExpr for MiniMethodKind
deriving instance ToExpr for MiniSpecifier

instance : ToExpr MiniImportClause where
  toExpr c := mkAppN (mkConst ``MiniImportClause.mk!)
    #[toExpr c.default_, toExpr c.namespace_, toExpr c.named, toExpr c.mod]
  toTypeExpr := mkConst ``MiniImportClause

deriving instance ToExpr for MiniImportDeclaration
deriving instance ToExpr for MiniExpr, MiniArrayElement, MiniArrowBody, MiniTemplatePart,
  MiniPropertyName, MiniProperty, MiniClassElement, MiniDeclarator, MiniForInit, MiniForHead,
  MiniSwitchCase, MiniCatchClause, MiniFinallyClause, MiniTryTail, MiniStatement,
  MiniExportDeclaration, MiniModuleItem
deriving instance ToExpr for MiniProgram

/-! ## The raw text parser

The embedded source is read by a parser of its own: it consumes everything
up to the terminator without tokenising it, so that JavaScript operators,
strings and comments cannot confuse the Lean lexer. -/

namespace Embed

open Lean.Parser

/-- What ends an embedded JavaScript fragment. -/
def endMarker : String := "|end_js]"

private partial def markerAt (c : ParserContext) (pos : String.Pos.Raw) : List Char → Bool
  | [] => true
  | ch :: rest => !c.atEnd pos && c.get pos == ch && markerAt c (c.next pos) rest

private partial def scanToMarker (c : ParserContext) (s : ParserState) (pos : String.Pos.Raw) :
    ParserState :=
  if markerAt c pos endMarker.toList then s.setPos pos
  else if c.atEnd pos then s.mkErrorAt "'|end_js]'" pos
  else scanToMarker c s (c.next pos)

/-- Consume the source text up to, but not including, the terminator. -/
def jsBodyFn : ParserFn := fun c s => scanToMarker c s s.pos

/-- Read the source text as one raw atom and consume the terminator. -/
def jsRawFn : ParserFn := fun c s =>
  let s := rawFn jsBodyFn (trailingWs := false) c s
  if s.hasError then s
  else whitespace c (s.setPos (s.pos + endMarker))

/-- The parser for the body of a `[js| ... |end_js]` fragment. -/
def jsRaw : Parser where
  fn := jsRawFn

@[combinator_formatter Language.JavaScript.MiniAST.Embed.jsRaw]
def jsRaw.formatter : PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer Language.JavaScript.MiniAST.Embed.jsRaw]
def jsRaw.parenthesizer : PrettyPrinter.Parenthesizer := pure ()

end Embed

open Embed in
/-- A JavaScript program, written in JavaScript syntax, as a `MiniProgram`. -/
syntax:max (name := jsProgramTerm) "[js|" jsRaw : term

open Embed in
/-- A JavaScript expression, written in JavaScript syntax, as a `MiniExpr`. -/
syntax:max (name := jsExprTerm) "[js_expr|" jsRaw : term

open Lean.Elab Lean.Elab.Term in
@[term_elab jsProgramTerm]
def elabJsProgram : TermElab := fun stx _ => do
  match parse stx[1].getAtomVal with
  | .ok p => return toExpr p
  | .error e => throwErrorAt stx e

open Lean.Elab Lean.Elab.Term in
@[term_elab jsExprTerm]
def elabJsExpr : TermElab := fun stx _ => do
  match parseExpr stx[1].getAtomVal with
  | .ok e => return toExpr e
  | .error e => throwErrorAt stx e

end Language.JavaScript.MiniAST
