/-
Port of `Language.JavaScript.Parser.SrcLocation` to Lean 4.

Source positions carried by the lexer tokens and, through them, by the
annotations stored in the AST.
-/

namespace Language.JavaScript.Parser

/-- A source position: byte offset, line (1 based) and column (1 based). -/
structure TokenPosn where
  offset : Nat
  line   : Nat
  column : Nat
deriving Repr, BEq, DecidableEq, Inhabited

namespace TokenPosn

/-- The position used when no real source position is available. -/
def empty : TokenPosn := ⟨0, 0, 0⟩

/-- The position a lexer starts at. -/
def start : TokenPosn := ⟨0, 1, 1⟩

instance : ToString TokenPosn where
  toString p := s!"TokenPn {p.offset} {p.line} {p.column}"

end TokenPosn

/-- Haskell-style constructor name for `TokenPosn`. -/
abbrev TokenPn (offset line column : Nat) : TokenPosn := ⟨offset, line, column⟩

/-- `tokenPosnEmpty` of the Haskell library. -/
abbrev tokenPosnEmpty : TokenPosn := TokenPosn.empty

end Language.JavaScript.Parser
