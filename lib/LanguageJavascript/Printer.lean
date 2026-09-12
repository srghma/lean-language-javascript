/-
Port of `Language.JavaScript.Pretty.Printer` to Lean 4.

The Haskell version accumulates into a `blaze-builder` `Builder` while
keeping track of the current (row, column) so that the source positions
stored in the annotations can be reproduced exactly.  Here the accumulator
is a plain `String`.

The layout of the input is reproduced; the spelling of a numeric and of a
regular expression literal is not, since the tree stores the value and not
the source text — such a literal is printed canonically (`0x1f`, `0o70`,
`1.5`, `/x/gi`).  A literal which prints shorter than it was written leaves
the following token at the column it was written at, so the padding shows
up as whitespace.

The Haskell code uses one overloaded operator `(|>)`; in Lean each instance
becomes a separate function and the chains are written with the pipeline
operator, so the left to right reading order is preserved.
-/
import LanguageJavascript.AST

namespace Language.JavaScript.Pretty

open Language.JavaScript.Parser
open Language.JavaScript.Parser.AST

/-- Current position and output accumulated so far. -/
structure PosAccum where
  row : Nat
  col : Nat
  out : String
deriving Repr, Inhabited

namespace PosAccum

/-- Emit a literal string, updating the current position. -/
def s (p : PosAccum) (str : String) : PosAccum :=
  let go : (Nat × Nat) → Char → (Nat × Nat) := fun (r, c) ch =>
    if ch = '\n' then (r + 1, 1)
    else if ch = '\t' then (r, c + 8)
    else (r, c + 1)
  let (r, c) := str.foldl go (p.row, p.col)
  { row := r, col := c, out := p.out ++ str }

/-- Emit the contents of a `Substring`, updating the current position.

The characters are read out of the input where they are and pushed onto the
output one by one, so a comment or a run of whitespace costs no copy of its
text (`p.s str.toString`, which this replaced, built one). -/
def sub (p : PosAccum) (str : Substring.Raw) : PosAccum :=
  str.foldl (fun q ch =>
    if ch = '\n' then { row := q.row + 1, col := 1, out := q.out.push ch }
    else if ch = '\t' then { q with col := q.col + 8, out := q.out.push ch }
    else { q with col := q.col + 1, out := q.out.push ch }) p

/-- Pad with newlines/spaces so that the given target position is reached. -/
def posn (p : PosAccum) : TokenPosn → PosAccum
  | { offset := _, line := ltgt, column := ctgt } =>
    let (bbline, ccur) :=
      if p.row < ltgt then (String.pushn "" '\n' (ltgt - p.row), 1) else ("", p.col)
    let bbcol := if ccur < ctgt then String.pushn "" ' ' (ctgt - ccur) else ""
    let lnew := if p.row < ltgt then ltgt else p.row
    let cnew := if ccur < ctgt then ctgt else ccur
    { row := lnew, col := cnew, out := p.out ++ bbline ++ bbcol }

end PosAccum

def rComment (p : PosAccum) : CommentAnnotation → PosAccum
  | .NoComment => p
  | .CommentA pos str => (p.posn pos).sub str
  | .WhiteSpace pos str => (p.posn pos).sub str

def rComments (p : PosAccum) : List CommentAnnotation → PosAccum
  | [] => p
  | c :: cs => rComments (rComment p c) cs

def rAnnot (p : PosAccum) : JSAnnot → PosAccum
  | .JSAnnot pos cs => (rComments p cs).posn pos
  | .JSNoAnnot => p
  | .JSAnnotSpace => p.s " "

def rBinOp (p : PosAccum) : JSBinOp → PosAccum
  | .JSBinOpAnd annot => (rAnnot p annot).s "&&"
  | .JSBinOpBitAnd annot => (rAnnot p annot).s "&"
  | .JSBinOpBitOr annot => (rAnnot p annot).s "|"
  | .JSBinOpBitXor annot => (rAnnot p annot).s "^"
  | .JSBinOpDivide annot => (rAnnot p annot).s "/"
  | .JSBinOpEq annot => (rAnnot p annot).s "=="
  | .JSBinOpGe annot => (rAnnot p annot).s ">="
  | .JSBinOpGt annot => (rAnnot p annot).s ">"
  | .JSBinOpIn annot => (rAnnot p annot).s "in"
  | .JSBinOpInstanceOf annot => (rAnnot p annot).s "instanceof"
  | .JSBinOpLe annot => (rAnnot p annot).s "<="
  | .JSBinOpLsh annot => (rAnnot p annot).s "<<"
  | .JSBinOpLt annot => (rAnnot p annot).s "<"
  | .JSBinOpMinus annot => (rAnnot p annot).s "-"
  | .JSBinOpMod annot => (rAnnot p annot).s "%"
  | .JSBinOpNeq annot => (rAnnot p annot).s "!="
  | .JSBinOpNullish annot => (rAnnot p annot).s "??"
  | .JSBinOpOf annot => (rAnnot p annot).s "of"
  | .JSBinOpOr annot => (rAnnot p annot).s "||"
  | .JSBinOpPlus annot => (rAnnot p annot).s "+"
  | .JSBinOpRsh annot => (rAnnot p annot).s ">>"
  | .JSBinOpStrictEq annot => (rAnnot p annot).s "==="
  | .JSBinOpStrictNeq annot => (rAnnot p annot).s "!=="
  | .JSBinOpTimes annot => (rAnnot p annot).s "*"
  | .JSBinOpUrsh annot => (rAnnot p annot).s ">>>"

def rUnaryOp (p : PosAccum) : JSUnaryOp → PosAccum
  | .JSUnaryOpDecr annot => (rAnnot p annot).s "--"
  | .JSUnaryOpDelete annot => (rAnnot p annot).s "delete"
  | .JSUnaryOpIncr annot => (rAnnot p annot).s "++"
  | .JSUnaryOpMinus annot => (rAnnot p annot).s "-"
  | .JSUnaryOpNot annot => (rAnnot p annot).s "!"
  | .JSUnaryOpPlus annot => (rAnnot p annot).s "+"
  | .JSUnaryOpTilde annot => (rAnnot p annot).s "~"
  | .JSUnaryOpTypeof annot => (rAnnot p annot).s "typeof"
  | .JSUnaryOpVoid annot => (rAnnot p annot).s "void"

def rAssignOp (p : PosAccum) : JSAssignOp → PosAccum
  | .JSAssign annot => (rAnnot p annot).s "="
  | .JSTimesAssign annot => (rAnnot p annot).s "*="
  | .JSDivideAssign annot => (rAnnot p annot).s "/="
  | .JSModAssign annot => (rAnnot p annot).s "%="
  | .JSPlusAssign annot => (rAnnot p annot).s "+="
  | .JSMinusAssign annot => (rAnnot p annot).s "-="
  | .JSLshAssign annot => (rAnnot p annot).s "<<="
  | .JSRshAssign annot => (rAnnot p annot).s ">>="
  | .JSUrshAssign annot => (rAnnot p annot).s ">>>="
  | .JSBwAndAssign annot => (rAnnot p annot).s "&="
  | .JSBwXorAssign annot => (rAnnot p annot).s "^="
  | .JSBwOrAssign annot => (rAnnot p annot).s "|="
  | .JSLogicalAndAssign annot => (rAnnot p annot).s "&&="
  | .JSLogicalOrAssign annot => (rAnnot p annot).s "||="
  | .JSNullishAssign annot => (rAnnot p annot).s "??="

def rSemi (p : PosAccum) : JSSemi → PosAccum
  | .JSSemi annot => (rAnnot p annot).s ";"
  | .JSSemiAuto => p

def rAccessor (p : PosAccum) : JSAccessor → PosAccum
  | .JSAccessorGet annot => (rAnnot p annot).s "get"
  | .JSAccessorSet annot => (rAnnot p annot).s "set"

def rIdent (p : PosAccum) : JSIdent → PosAccum
  | .JSIdentName a str => (rAnnot p a).s str.val
  | .JSIdentNone => p

set_option maxHeartbeats 2000000 in
mutual

def rAST (p : PosAccum) : JSAST → PosAccum
  | .JSAstProgram xs a => p |> (rStatements · xs) |> (rAnnot · a)
  | .JSAstModule xs a => p |> (rModuleItems · xs) |> (rAnnot · a)
  | .JSAstStatement s a => p |> (rStatement · s) |> (rAnnot · a)
  | .JSAstExpression e a => p |> (rExpression · e) |> (rAnnot · a)
  | .JSAstLiteral x a => p |> (rExpression · x) |> (rAnnot · a)

def rExpression (p : PosAccum) : JSExpression → PosAccum
  -- Terminals
  | .JSIdentifier annot s => (rAnnot p annot).s s.val
  | .JSNumberLit annot i => (rAnnot p annot).s i.render
  | .JSLiteral annot l => (rAnnot p annot).s l.text.val
  | .JSStringLiteral annot s => (rAnnot p annot).s s.render
  | .JSRegEx annot s => (rAnnot p annot).s s.render
  -- Non terminals
  | .JSArrayLiteral als xs ars =>
      p |> (rAnnot · als) |> (·.s "[") |> (rArrayElements · xs) |> (rAnnot · ars) |> (·.s "]")
  | .JSArrowExpression xs a x =>
      p |> (rArrowParameterList · xs) |> (rAnnot · a) |> (·.s "=>") |> (rStatement · x)
  | .JSAssignExpression lhs op rhs =>
      p |> (rExpression · lhs) |> (rAssignOp · op) |> (rExpression · rhs)
  | .JSAwaitExpression a e => p |> (rAnnot · a) |> (·.s "await") |> (rExpression · e)
  | .JSCallExpression ex lb xs rb =>
      p |> (rExpression · ex) |> (rAnnot · lb) |> (·.s "(") |> (rExprCommaList · xs)
        |> (rAnnot · rb) |> (·.s ")")
  | .JSCallExpressionDot ex os xs =>
      p |> (rExpression · ex) |> (rAnnot · os) |> (·.s ".") |> (rExpression · xs)
  | .JSCallExpressionSquare ex als xs ars =>
      p |> (rExpression · ex) |> (rAnnot · als) |> (·.s "[") |> (rExpression · xs)
        |> (rAnnot · ars) |> (·.s "]")
  | .JSClassExpression ds annot n h lb xs rb =>
      p |> (rDecorators · ds) |> (rAnnot · annot) |> (·.s "class") |> (rIdent · n)
        |> (rClassHeritage · h)
        |> (rAnnot · lb) |> (·.s "{") |> (rClassElements · xs) |> (rAnnot · rb) |> (·.s "}")
  | .JSCommaExpression le c re =>
      p |> (rExpression · le) |> (rAnnot · c) |> (·.s ",") |> (rExpression · re)
  | .JSExpressionBinary lhs op rhs =>
      p |> (rExpression · lhs) |> (rBinOp · op) |> (rExpression · rhs)
  | .JSExpressionParen alp e arp =>
      p |> (rAnnot · alp) |> (·.s "(") |> (rExpression · e) |> (rAnnot · arp) |> (·.s ")")
  | .JSExpressionPostfix xs op => p |> (rExpression · xs) |> (rUnaryOp · op)
  | .JSExpressionTernary cond h v1 c v2 =>
      p |> (rExpression · cond) |> (rAnnot · h) |> (·.s "?") |> (rExpression · v1)
        |> (rAnnot · c) |> (·.s ":") |> (rExpression · v2)
  | .JSFunctionExpression annot n lb x2s rb x3 =>
      p |> (rAnnot · annot) |> (·.s "function") |> (rIdent · n) |> (rAnnot · lb) |> (·.s "(")
        |> (rExprCommaList · x2s) |> (rAnnot · rb) |> (·.s ")") |> (rBlock · x3)
  | .JSGeneratorExpression annot s n lb x2s rb x3 =>
      p |> (rAnnot · annot) |> (·.s "function") |> (rAnnot · s) |> (·.s "*") |> (rIdent · n)
        |> (rAnnot · lb) |> (·.s "(") |> (rExprCommaList · x2s) |> (rAnnot · rb) |> (·.s ")")
        |> (rBlock · x3)
  | .JSMemberDot xs dot n =>
      p |> (rExpression · xs) |> (·.s ".") |> (rAnnot · dot) |> (rExpression · n)
  | .JSMemberExpression e lb a rb =>
      p |> (rExpression · e) |> (rAnnot · lb) |> (·.s "(") |> (rExprCommaList · a)
        |> (rAnnot · rb) |> (·.s ")")
  | .JSMemberNew a lb n rb s =>
      p |> (rAnnot · a) |> (·.s "new") |> (rExpression · lb) |> (rAnnot · n) |> (·.s "(")
        |> (rExprCommaList · rb) |> (rAnnot · s) |> (·.s ")")
  | .JSMemberSquare xs als e ars =>
      p |> (rExpression · xs) |> (rAnnot · als) |> (·.s "[") |> (rExpression · e)
        |> (rAnnot · ars) |> (·.s "]")
  | .JSOptionalMemberDot xs q n =>
      p |> (rExpression · xs) |> (rAnnot · q) |> (·.s "?.") |> (rExpression · n)
  | .JSOptionalMemberSquare xs q als e ars =>
      p |> (rExpression · xs) |> (rAnnot · q) |> (·.s "?.") |> (rAnnot · als) |> (·.s "[")
        |> (rExpression · e) |> (rAnnot · ars) |> (·.s "]")
  | .JSOptionalCallExpression ex q lb xs rb =>
      p |> (rExpression · ex) |> (rAnnot · q) |> (·.s "?.") |> (rAnnot · lb) |> (·.s "(")
        |> (rExprCommaList · xs) |> (rAnnot · rb) |> (·.s ")")
  | .JSPrivateName annot s => (rAnnot p annot).s ("#" ++ s.val)
  | .JSImportMeta a d m =>
      p |> (rAnnot · a) |> (·.s "import") |> (rAnnot · d) |> (·.s ".") |> (rAnnot · m)
        |> (·.s "meta")
  | .JSNewTarget a d m =>
      p |> (rAnnot · a) |> (·.s "new") |> (rAnnot · d) |> (·.s ".") |> (rAnnot · m)
        |> (·.s "target")
  | .JSImportCall a lb xs rb =>
      p |> (rAnnot · a) |> (·.s "import") |> (rAnnot · lb) |> (·.s "(")
        |> (rExprCommaList · xs) |> (rAnnot · rb) |> (·.s ")")
  | .JSNewExpression n e => p |> (rAnnot · n) |> (·.s "new") |> (rExpression · e)
  | .JSObjectLiteral alb xs arb =>
      p |> (rAnnot · alb) |> (·.s "{") |> (rObjectPropertyList · xs) |> (rAnnot · arb)
        |> (·.s "}")
  | .JSTemplateLiteral t a h ps =>
      p |> (rMaybeExpression · t) |> (rAnnot · a) |> (·.s (templateHeadSpelling h ps))
        |> (rTemplateParts · ps)
  | .JSUnaryExpression op x => p |> (rUnaryOp · op) |> (rExpression · x)
  | .JSVarInitExpression x1 x2 => p |> (rExpression · x1) |> (rVarInitializer · x2)
  | .JSYieldExpression y x => p |> (rAnnot · y) |> (·.s "yield") |> (rMaybeExpression · x)
  | .JSYieldFromExpression y s x =>
      p |> (rAnnot · y) |> (·.s "yield") |> (rAnnot · s) |> (·.s "*") |> (rExpression · x)
  | .JSSpreadExpression a e => p |> (rAnnot · a) |> (·.s "...") |> (rExpression · e)

def rArrowParameterList (p : PosAccum) : JSArrowParameterList → PosAccum
  | .JSUnparenthesizedArrowParameter x => rIdent p x
  | .JSParenthesizedArrowParameterList lb ps rb =>
      p |> (rAnnot · lb) |> (·.s "(") |> (rExprCommaList · ps) |> (·.s ")") |> (rAnnot · rb)

def rStatement (p : PosAccum) : JSStatement → PosAccum
  | .JSStatementBlock alb blk arb s =>
      p |> (rAnnot · alb) |> (·.s "{") |> (rStatements · blk) |> (rAnnot · arb) |> (·.s "}")
        |> (rSemi · s)
  | .JSBreak annot mi s =>
      p |> (rAnnot · annot) |> (·.s "break") |> (rIdent · mi) |> (rSemi · s)
  | .JSClass ds annot n h lb xs rb s =>
      p |> (rDecorators · ds) |> (rAnnot · annot) |> (·.s "class") |> (rIdent · n)
        |> (rClassHeritage · h)
        |> (rAnnot · lb) |> (·.s "{") |> (rClassElements · xs) |> (rAnnot · rb) |> (·.s "}")
        |> (rSemi · s)
  | .JSContinue annot mi s =>
      p |> (rAnnot · annot) |> (·.s "continue") |> (rIdent · mi) |> (rSemi · s)
  | .JSConstant annot xs s =>
      p |> (rAnnot · annot) |> (·.s "const") |> (rExprCommaList1 · xs) |> (rSemi · s)
  | .JSUsing annot xs s =>
      p |> (rAnnot · annot) |> (·.s "using") |> (rExprCommaList1 · xs) |> (rSemi · s)
  | .JSAwaitUsing aw annot xs s =>
      p |> (rAnnot · aw) |> (·.s "await") |> (rAnnot · annot) |> (·.s "using")
        |> (rExprCommaList1 · xs) |> (rSemi · s)
  | .JSDoWhile ad x1 aw alb x2 arb x3 =>
      p |> (rAnnot · ad) |> (·.s "do") |> (rStatement · x1) |> (rAnnot · aw) |> (·.s "while")
        |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x2) |> (rAnnot · arb) |> (·.s ")")
        |> (rSemi · x3)
  | .JSEmptyStatement a => p |> (rAnnot · a) |> (·.s ";")
  | .JSFor af alb x1s s1 x2s s2 x3s arb x4 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (rExprCommaList · x1s)
        |> (rAnnot · s1) |> (·.s ";") |> (rExprCommaList · x2s) |> (rAnnot · s2) |> (·.s ";")
        |> (rExprCommaList · x3s) |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x4)
  | .JSForIn af alb x1s i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x1s)
        |> (rBinOp · i) |> (rExpression · x2) |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForVar af alb v x1s s1 x2s s2 x3s arb x4 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "var")
        |> (rAnnot · v) |> (rExprCommaList1 · x1s) |> (rAnnot · s1) |> (·.s ";")
        |> (rExprCommaList · x2s) |> (rAnnot · s2) |> (·.s ";") |> (rExprCommaList · x3s)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x4)
  | .JSForVarIn af alb v x1 i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "var")
        |> (rAnnot · v) |> (rExpression · x1) |> (rBinOp · i) |> (rExpression · x2)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForLet af alb v x1s s1 x2s s2 x3s arb x4 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "let")
        |> (rAnnot · v) |> (rExprCommaList1 · x1s) |> (rAnnot · s1) |> (·.s ";")
        |> (rExprCommaList · x2s) |> (rAnnot · s2) |> (·.s ";") |> (rExprCommaList · x3s)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x4)
  | .JSForLetIn af alb v x1 i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "let")
        |> (rAnnot · v) |> (rExpression · x1) |> (rBinOp · i) |> (rExpression · x2)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForLetOf af alb v x1 i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "let")
        |> (rAnnot · v) |> (rExpression · x1) |> (rBinOp · i) |> (rExpression · x2)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForConst af alb v x1s s1 x2s s2 x3s arb x4 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "const")
        |> (rAnnot · v) |> (rExprCommaList1 · x1s) |> (rAnnot · s1) |> (·.s ";")
        |> (rExprCommaList · x2s) |> (rAnnot · s2) |> (·.s ";") |> (rExprCommaList · x3s)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x4)
  | .JSForConstIn af alb v x1 i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "const")
        |> (rAnnot · v) |> (rExpression · x1) |> (rBinOp · i) |> (rExpression · x2)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForConstOf af alb v x1 i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "const")
        |> (rAnnot · v) |> (rExpression · x1) |> (rBinOp · i) |> (rExpression · x2)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForOf af alb x1s i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x1s)
        |> (rBinOp · i) |> (rExpression · x2) |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSForVarOf af alb v x1 i x2 arb x3 =>
      p |> (rAnnot · af) |> (·.s "for") |> (rAnnot · alb) |> (·.s "(") |> (·.s "var")
        |> (rAnnot · v) |> (rExpression · x1) |> (rBinOp · i) |> (rExpression · x2)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x3)
  | .JSAsyncFunction aa af n alb x2s arb x3 s =>
      p |> (rAnnot · aa) |> (·.s "async") |> (rAnnot · af) |> (·.s "function") |> (rIdent · n)
        |> (rAnnot · alb) |> (·.s "(") |> (rExprCommaList · x2s) |> (rAnnot · arb) |> (·.s ")")
        |> (rBlock · x3) |> (rSemi · s)
  | .JSFunction af n alb x2s arb x3 s =>
      p |> (rAnnot · af) |> (·.s "function") |> (rIdent · n) |> (rAnnot · alb) |> (·.s "(")
        |> (rExprCommaList · x2s) |> (rAnnot · arb) |> (·.s ")") |> (rBlock · x3) |> (rSemi · s)
  | .JSGenerator af as_ n alb x2s arb x3 s =>
      p |> (rAnnot · af) |> (·.s "function") |> (rAnnot · as_) |> (·.s "*") |> (rIdent · n)
        |> (rAnnot · alb) |> (·.s "(") |> (rExprCommaList · x2s) |> (rAnnot · arb) |> (·.s ")")
        |> (rBlock · x3) |> (rSemi · s)
  | .JSIf annot alb x1 arb x2s =>
      p |> (rAnnot · annot) |> (·.s "if") |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x1)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x2s)
  | .JSIfElse annot alb x1 arb x2s ea x3s =>
      p |> (rAnnot · annot) |> (·.s "if") |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x1)
        |> (rAnnot · arb) |> (·.s ")") |> (rStatement · x2s) |> (rAnnot · ea) |> (·.s "else")
        |> (rStatement · x3s)
  | .JSLabelled l c v => p |> (rIdent · l) |> (rAnnot · c) |> (·.s ":") |> (rStatement · v)
  | .JSLet annot xs s =>
      p |> (rAnnot · annot) |> (·.s "let") |> (rExprCommaList1 · xs) |> (rSemi · s)
  | .JSExpressionStatement l s => p |> (rExpression · l) |> (rSemi · s)
  | .JSAssignStatement lhs op rhs s =>
      p |> (rExpression · lhs) |> (rAssignOp · op) |> (rExpression · rhs) |> (rSemi · s)
  | .JSMethodCall e lp a rp s =>
      p |> (rExpression · e) |> (rAnnot · lp) |> (·.s "(") |> (rExprCommaList · a)
        |> (rAnnot · rp) |> (·.s ")") |> (rSemi · s)
  | .JSReturn annot me s =>
      p |> (rAnnot · annot) |> (·.s "return") |> (rMaybeExpression · me) |> (rSemi · s)
  | .JSSwitch annot alp x arp alb x2 arb s =>
      p |> (rAnnot · annot) |> (·.s "switch") |> (rAnnot · alp) |> (·.s "(") |> (rExpression · x)
        |> (rAnnot · arp) |> (·.s ")") |> (rAnnot · alb) |> (·.s "{") |> (rSwitchParts · x2)
        |> (rAnnot · arb) |> (·.s "}") |> (rSemi · s)
  | .JSThrow annot x s =>
      p |> (rAnnot · annot) |> (·.s "throw") |> (rExpression · x) |> (rSemi · s)
  | .JSTry annot tb tcs tf =>
      p |> (rAnnot · annot) |> (·.s "try") |> (rBlock · tb) |> (rTryCatches · tcs)
        |> (rTryFinally · tf)
  | .JSVariable annot xs s =>
      p |> (rAnnot · annot) |> (·.s "var") |> (rExprCommaList1 · xs) |> (rSemi · s)
  | .JSWhile annot alp x1 arp x2 =>
      p |> (rAnnot · annot) |> (·.s "while") |> (rAnnot · alp) |> (·.s "(")
        |> (rExpression · x1) |> (rAnnot · arp) |> (·.s ")") |> (rStatement · x2)
  | .JSWith annot alp x1 arp x s =>
      p |> (rAnnot · annot) |> (·.s "with") |> (rAnnot · alp) |> (·.s "(") |> (rExpression · x1)
        |> (rAnnot · arp) |> (·.s ")") |> (rStatement · x) |> (rSemi · s)

def rBlock (p : PosAccum) : JSBlock → PosAccum
  | .JSBlock alb ss arb =>
      p |> (rAnnot · alb) |> (·.s "{") |> (rStatements · ss) |> (rAnnot · arb) |> (·.s "}")

def rTryCatch (p : PosAccum) : JSTryCatch → PosAccum
  | .JSCatch anc alb x1 arb x3 =>
      p |> (rAnnot · anc) |> (·.s "catch") |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x1)
        |> (rAnnot · arb) |> (·.s ")") |> (rBlock · x3)
  | .JSCatchIf anc alb x1 aif ex arb x3 =>
      p |> (rAnnot · anc) |> (·.s "catch") |> (rAnnot · alb) |> (·.s "(") |> (rExpression · x1)
        |> (rAnnot · aif) |> (·.s "if") |> (rExpression · ex) |> (rAnnot · arb) |> (·.s ")")
        |> (rBlock · x3)

def rTryFinally (p : PosAccum) : JSTryFinally → PosAccum
  | .JSFinally annot x => p |> (rAnnot · annot) |> (·.s "finally") |> (rBlock · x)
  | .JSNoFinally => p

def rSwitchPart (p : PosAccum) : JSSwitchParts → PosAccum
  | .JSCase annot x1 c x2s =>
      p |> (rAnnot · annot) |> (·.s "case") |> (rExpression · x1) |> (rAnnot · c) |> (·.s ":")
        |> (rStatements · x2s)
  | .JSDefault annot c xs =>
      p |> (rAnnot · annot) |> (·.s "default") |> (rAnnot · c) |> (·.s ":") |> (rStatements · xs)

def rModuleItem (p : PosAccum) : JSModuleItem → PosAccum
  | .JSModuleImportDeclaration annot decl =>
      p |> (rAnnot · annot) |> (·.s "import") |> (rImportDeclaration · decl)
  | .JSModuleExportDeclaration annot decl =>
      p |> (rAnnot · annot) |> (·.s "export") |> (rExportDeclaration · decl)
  | .JSModuleStatementListItem s => rStatement p s

def rImportDeclaration (p : PosAccum) : JSImportDeclaration → PosAccum
  | .JSImportDeclaration imp from_ annot =>
      p |> (rImportClause · imp) |> (rFromClause · from_) |> (rSemi · annot)
  | .JSImportDeclarationBare annot m attrs s =>
      p |> (rAnnot · annot) |> (·.s m.val) |> (rImportAttributes? · attrs) |> (rSemi · s)

def rImportClause (p : PosAccum) : JSImportClause → PosAccum
  | .JSImportClauseDefault x => rIdent p x
  | .JSImportClauseNameSpace x => rImportNameSpace p x
  | .JSImportClauseNamed x => rImportsNamed p x
  | .JSImportClauseDefaultNameSpace x1 annot x2 =>
      p |> (rIdent · x1) |> (rAnnot · annot) |> (·.s ",") |> (rImportNameSpace · x2)
  | .JSImportClauseDefaultNamed x1 annot x2 =>
      p |> (rIdent · x1) |> (rAnnot · annot) |> (·.s ",") |> (rImportsNamed · x2)

def rFromClause (p : PosAccum) : JSFromClause → PosAccum
  | .JSFromClause from_ annot m attrs =>
      p |> (rAnnot · from_) |> (·.s "from") |> (rAnnot · annot) |> (·.s m.val)
        |> (rImportAttributes? · attrs)

def rImportAttribute (p : PosAccum) : JSImportAttribute → PosAccum
  | .JSImportAttribute ka k colon va v =>
      p |> (rAnnot · ka) |> (·.s k.val) |> (rAnnot · colon) |> (·.s ":") |> (rAnnot · va)
        |> (·.s v.val)

def rImportAttrCommaList (p : PosAccum) : JSCommaList JSImportAttribute → PosAccum
  | .JSLCons xs a x =>
      p |> (rImportAttrCommaList · xs) |> (rAnnot · a) |> (·.s ",") |> (rImportAttribute · x)
  | .JSLOne x => rImportAttribute p x
  | .JSLNil => p

def rImportAttributes (p : PosAccum) : JSImportAttributes → PosAccum
  | .JSImportAttributes w lb attrs rb =>
      p |> (rAnnot · w) |> (·.s "with") |> (rAnnot · lb) |> (·.s "{")
        |> (rImportAttrCommaList · attrs) |> (rAnnot · rb) |> (·.s "}")

def rImportAttributes? (p : PosAccum) : Option JSImportAttributes → PosAccum
  | none => p
  | some a => rImportAttributes p a

def rImportNameSpace (p : PosAccum) : JSImportNameSpace → PosAccum
  | .JSImportNameSpace star annot x =>
      p |> (rBinOp · star) |> (rAnnot · annot) |> (·.s "as") |> (rIdent · x)

def rImportsNamed (p : PosAccum) : JSImportsNamed → PosAccum
  | .JSImportsNamed lb xs rb =>
      p |> (rAnnot · lb) |> (·.s "{") |> (rImportSpecCommaList · xs) |> (rAnnot · rb)
        |> (·.s "}")

def rImportSpecifier (p : PosAccum) : JSImportSpecifier → PosAccum
  | .JSImportSpecifier x1 => rIdent p x1
  | .JSImportSpecifierAs x1 annot x2 =>
      p |> (rIdent · x1) |> (rAnnot · annot) |> (·.s "as") |> (rIdent · x2)

def rExportDeclaration (p : PosAccum) : JSExportDeclaration → PosAccum
  | .JSExport x1 s => p |> (rStatement · x1) |> (rSemi · s)
  | .JSExportLocals xs semi => p |> (rExportClause · xs) |> (rSemi · semi)
  | .JSExportFrom xs from_ semi =>
      p |> (rExportClause · xs) |> (rFromClause · from_) |> (rSemi · semi)
  | .JSExportAll star from_ semi =>
      p |> (rAnnot · star) |> (·.s "*") |> (rFromClause · from_) |> (rSemi · semi)
  | .JSExportAllAs star asA n from_ semi =>
      p |> (rAnnot · star) |> (·.s "*") |> (rAnnot · asA) |> (·.s "as") |> (rIdent · n)
        |> (rFromClause · from_) |> (rSemi · semi)
  | .JSExportDefault d e semi =>
      p |> (rAnnot · d) |> (·.s "default") |> (rExpression · e) |> (rSemi · semi)

def rExportClause (p : PosAccum) : JSExportClause → PosAccum
  | .JSExportClause alb s arb =>
      p |> (rAnnot · alb) |> (·.s "{") |> (rExportSpecCommaList · s) |> (rAnnot · arb)
        |> (·.s "}")

def rExportSpecifier (p : PosAccum) : JSExportSpecifier → PosAccum
  | .JSExportSpecifier i => rIdent p i
  | .JSExportSpecifierAs x1 annot x2 =>
      p |> (rIdent · x1) |> (rAnnot · annot) |> (·.s "as") |> (rIdent · x2)

def rObjectProperty (p : PosAccum) : JSObjectProperty → PosAccum
  | .JSPropertyNameandValue n c v =>
      p |> (rPropertyName · n) |> (rAnnot · c) |> (·.s ":") |> (rExpression · v)
  | .JSPropertyIdentRef a s => (rAnnot p a).s s.val
  | .JSPropertyIdentRefDefault a s eq v =>
      p |> (rAnnot · a) |> (·.s s.val) |> (rAnnot · eq) |> (·.s "=") |> (rExpression · v)
  | .JSObjectSpread a e => p |> (rAnnot · a) |> (·.s "...") |> (rExpression · e)
  | .JSObjectMethod m => rMethodDefinition p m

def rMethodDefinition (p : PosAccum) : JSMethodDefinition → PosAccum
  | .JSMethodDefinition n alp ps arp b =>
      p |> (rPropertyName · n) |> (rAnnot · alp) |> (·.s "(") |> (rExprCommaList · ps)
        |> (rAnnot · arp) |> (·.s ")") |> (rBlock · b)
  | .JSGeneratorMethodDefinition s n alp ps arp b =>
      p |> (rAnnot · s) |> (·.s "*") |> (rPropertyName · n) |> (rAnnot · alp) |> (·.s "(")
        |> (rExprCommaList · ps) |> (rAnnot · arp) |> (·.s ")") |> (rBlock · b)
  | .JSPropertyAccessor s n alp ps arp b =>
      p |> (rAccessor · s) |> (rPropertyName · n) |> (rAnnot · alp) |> (·.s "(")
        |> (rExprCommaList · ps) |> (rAnnot · arp) |> (·.s ")") |> (rBlock · b)

def rPropertyName (p : PosAccum) : JSPropertyName → PosAccum
  | .JSPropertyIdent a s => (rAnnot p a).s s.val
  | .JSPropertyPrivate a s => (rAnnot p a).s ("#" ++ s.val)
  | .JSPropertyString a s => (rAnnot p a).s s.render
  | .JSPropertyNumber a s => (rAnnot p a).s s.render
  | .JSPropertyComputed lb x rb =>
      p |> (rAnnot · lb) |> (·.s "[") |> (rExpression · x) |> (rAnnot · rb) |> (·.s "]")

def rArrayElement (p : PosAccum) : JSArrayElement → PosAccum
  | .JSArrayElement e => rExpression p e
  | .JSArrayComma a => p |> (rAnnot · a) |> (·.s ",")

/-- A part of a template literal: the substitution, then the text which
follows it, between the `}` which closes the substitution and either the
`${` of the next one or, for the last part, the closing backquote. -/
def rTemplatePart (p : PosAccum) (isLast : Bool) : JSTemplatePart → PosAccum
  | .JSTemplatePart e a s =>
      p |> (rExpression · e) |> (rAnnot · a) |> (·.s (templatePartSpelling s isLast))

def rClassHeritage (p : PosAccum) : JSClassHeritage → PosAccum
  | .JSExtends a e => p |> (rAnnot · a) |> (·.s "extends") |> (rExpression · e)
  | .JSExtendsNone => p

def rClassElement (p : PosAccum) : JSClassElement → PosAccum
  | .JSClassInstanceMethod ds m => p |> (rDecorators · ds) |> (rMethodDefinition · m)
  | .JSClassStaticMethod ds a m =>
      p |> (rDecorators · ds) |> (rAnnot · a) |> (·.s "static") |> (rMethodDefinition · m)
  | .JSClassInstanceField ds n i s =>
      p |> (rDecorators · ds) |> (rPropertyName · n) |> (rVarInitializer · i) |> (rSemi · s)
  | .JSClassStaticField ds a n i s =>
      p |> (rDecorators · ds) |> (rAnnot · a) |> (·.s "static") |> (rPropertyName · n)
        |> (rVarInitializer · i) |> (rSemi · s)
  | .JSClassStaticBlock a b => p |> (rAnnot · a) |> (·.s "static") |> (rBlock · b)
  | .JSClassSemi a => p |> (rAnnot · a) |> (·.s ";")

def rDecorator (p : PosAccum) : JSDecorator → PosAccum
  | .JSDecorator a e => p |> (rAnnot · a) |> (·.s "@") |> (rExpression · e)

def rDecorators (p : PosAccum) : List JSDecorator → PosAccum
  | [] => p
  | d :: ds => rDecorators (rDecorator p d) ds

def rVarInitializer (p : PosAccum) : JSVarInitializer → PosAccum
  | .JSVarInit a x => p |> (rAnnot · a) |> (·.s "=") |> (rExpression · x)
  | .JSVarInitNone => p

def rMaybeExpression (p : PosAccum) : Option JSExpression → PosAccum
  | some e => rExpression p e
  | none => p

-- Lists and comma lists.

def rStatements (p : PosAccum) : List JSStatement → PosAccum
  | [] => p
  | x :: xs => rStatements (rStatement p x) xs

def rExpressions (p : PosAccum) : List JSExpression → PosAccum
  | [] => p
  | x :: xs => rExpressions (rExpression p x) xs

def rModuleItems (p : PosAccum) : List JSModuleItem → PosAccum
  | [] => p
  | x :: xs => rModuleItems (rModuleItem p x) xs

def rTryCatches (p : PosAccum) : List JSTryCatch → PosAccum
  | [] => p
  | x :: xs => rTryCatches (rTryCatch p x) xs

def rSwitchParts (p : PosAccum) : List JSSwitchParts → PosAccum
  | [] => p
  | x :: xs => rSwitchParts (rSwitchPart p x) xs

def rArrayElements (p : PosAccum) : List JSArrayElement → PosAccum
  | [] => p
  | x :: xs => rArrayElements (rArrayElement p x) xs

def rClassElements (p : PosAccum) : List JSClassElement → PosAccum
  | [] => p
  | x :: xs => rClassElements (rClassElement p x) xs

def rTemplateParts (p : PosAccum) : List JSTemplatePart → PosAccum
  | [] => p
  | [x] => rTemplatePart p true x
  | x :: xs => rTemplateParts (rTemplatePart p false x) xs

def rExprCommaList (p : PosAccum) : JSCommaList JSExpression → PosAccum
  | .JSLCons pl a i =>
      p |> (rExprCommaList · pl) |> (rAnnot · a) |> (·.s ",") |> (rExpression · i)
  | .JSLOne i => rExpression p i
  | .JSLNil => p

/-- The declarators of a `var`, `let` or `const`, which are a non-empty
comma list. -/
def rExprCommaList1 (p : PosAccum) : JSCommaList1 JSExpression → PosAccum
  | .JSL1Cons pl a i =>
      p |> (rExprCommaList1 · pl) |> (rAnnot · a) |> (·.s ",") |> (rExpression · i)
  | .JSL1One i => rExpression p i

def rImportSpecCommaList (p : PosAccum) : JSCommaList JSImportSpecifier → PosAccum
  | .JSLCons pl a i =>
      p |> (rImportSpecCommaList · pl) |> (rAnnot · a) |> (·.s ",") |> (rImportSpecifier · i)
  | .JSLOne i => rImportSpecifier p i
  | .JSLNil => p

def rExportSpecCommaList (p : PosAccum) : JSCommaList JSExportSpecifier → PosAccum
  | .JSLCons pl a i =>
      p |> (rExportSpecCommaList · pl) |> (rAnnot · a) |> (·.s ",") |> (rExportSpecifier · i)
  | .JSLOne i => rExportSpecifier p i
  | .JSLNil => p

def rObjectPropertyCommaList (p : PosAccum) : JSCommaList JSObjectProperty → PosAccum
  | .JSLCons pl a i =>
      p |> (rObjectPropertyCommaList · pl) |> (rAnnot · a) |> (·.s ",") |> (rObjectProperty · i)
  | .JSLOne i => rObjectProperty p i
  | .JSLNil => p

def rObjectPropertyList (p : PosAccum) : JSCommaTrailingList JSObjectProperty → PosAccum
  | .JSCTLComma xs a => p |> (rObjectPropertyCommaList · xs) |> (rAnnot · a) |> (·.s ",")
  | .JSCTLNone xs => rObjectPropertyCommaList p xs

end

/-- Render an AST back to JavaScript source. -/
def renderJS (node : JSAST) : String :=
  (rAST { row := 1, col := 1, out := "" } node).out

/-- Render an AST back to JavaScript source. -/
def renderToString (js : JSAST) : String := renderJS js

end Language.JavaScript.Pretty
