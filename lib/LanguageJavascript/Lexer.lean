/-
A JavaScript lexer producing the tokens of `Language.JavaScript.Parser.Token`.

The Haskell package generates its lexer with Alex; this is a hand written
equivalent.  As in the original, whitespace and comments occurring before a
token are attached to that token: comments are kept as `CommentAnnotation`s
and plain whitespace is recovered from the source positions when printing.

The lexer is called by the parser one token at a time, and the parser passes
the mode in which the token is to be read.  This is how the original deals
with the two context dependent parts of JavaScript's lexical grammar:

* `/` starts a regular expression where an expression is expected, and is the
  division operator where an operator is expected;
* the text following the `}` that closes a template substitution is lexed as
  a template middle/tail part.

Implementation notes (performance):

* The state is a `Substring` (`Substring.Raw`) together with a raw byte
  position into it, so no copy of the input is ever made: looking at a
  character, advancing and slicing out the text of a token are all constant
  time (the text of a token costs only the bytes of that token when it has to
  be turned into a `String`).
* Comment and whitespace annotations keep a `Substring` of the input rather
  than a fresh `String`, so a comment costs nothing to record.
* Punctuators are recognised by a direct character dispatch instead of a
  linear scan through a table of strings.
-/
import LanguageJavascript.Token

namespace Language.JavaScript.Parser.Lexer

open Language.JavaScript.Parser

/-- The state of the lexer: the input, as a `Substring`, and the current
position in it.

`pos` is a raw byte index into `input.str`; it always lies between
`input.startPos` and `input.stopPos`.  `offset`, `line` and `col` are the
character offset (from the start of the substring) and the 1-based line and
column of `pos`, as reported in `TokenPosn`s. -/
structure LexState where
  /-- The text being lexed. -/
  input : Substring.Raw
  /-- The current position, as a byte index into `input.str`. -/
  pos : String.Pos.Raw
  /-- The number of characters consumed so far. -/
  offset : Nat
  /-- The current line, 1 based. -/
  line : Nat
  /-- The current column, 1 based. -/
  col : Nat
deriving Repr, Inhabited

namespace LexState

/-- Lex a `Substring`. -/
def ofSubstring (ss : Substring.Raw) : LexState := ⟨ss, ss.startPos, 0, 1, 1⟩

/-- Lex a whole `String`. -/
def ofString (s : String) : LexState := ofSubstring s.toRawSubstring

@[inline] def atEnd (s : LexState) : Bool := s.input.stopPos.byteIdx ≤ s.pos.byteIdx

/-- The character at the current position, if any. -/
@[inline] def cur (s : LexState) : Option Char :=
  if s.atEnd then none else some (String.Pos.Raw.get s.input.str s.pos)

/-- The character `n` characters after the current position, or `'\u0000'` if
that position is past the end of the input.  A NUL character in the input is
a lexical error anyway, so it is safe to use it as the "nothing here"
marker; returning a plain `Char` avoids allocating an `Option`. -/
@[inline] def charAt (s : LexState) (n : Nat) : Char := Id.run do
  let mut p := s.pos
  for _ in [0:n] do
    if s.input.stopPos.byteIdx ≤ p.byteIdx then return '\u0000'
    p := String.Pos.Raw.next s.input.str p
  if s.input.stopPos.byteIdx ≤ p.byteIdx then '\u0000'
  else String.Pos.Raw.get s.input.str p

/-- The current position as a `TokenPosn`. -/
@[inline] def posn (s : LexState) : TokenPosn := ⟨s.offset, s.line, s.col⟩

/-- Consume one character. -/
@[inline] def next (s : LexState) : LexState :=
  if s.atEnd then s
  else
    let c := String.Pos.Raw.get s.input.str s.pos
    let p := String.Pos.Raw.next s.input.str s.pos
    if c == '\n' then
      { s with pos := p, offset := s.offset + 1, line := s.line + 1, col := 1 }
    else if c == '\t' then
      { s with pos := p, offset := s.offset + 1, col := s.col + 8 }
    else
      { s with pos := p, offset := s.offset + 1, col := s.col + 1 }

/-- Consume `n` characters. -/
def skip (s : LexState) : Nat → LexState
  | 0 => s
  | n + 1 => skip s.next n

/-- The text between a previous position and the current one, as a
`Substring` of the input: no copying takes place. -/
@[inline] def textFrom (s : LexState) (start : String.Pos.Raw) : Substring.Raw :=
  ⟨s.input.str, start, s.pos⟩

/-! ### The measure that makes the scanners total

Every scanner below advances by at least one character per step, and stops
at the end of the input; `remaining` — the number of bytes left — is
therefore a measure on which they are well founded, so none of them has to
be `partial`. -/

/-- The number of bytes of the input which are still to be read. -/
@[inline] def remaining (s : LexState) : Nat := s.input.stopPos.byteIdx - s.pos.byteIdx

/-- Consuming a character which is there reads at least one byte. -/
theorem remaining_next_lt {s : LexState} (h : ¬ s.atEnd = true) :
    s.next.remaining < s.remaining := by
  have hlt : s.pos.byteIdx < s.input.stopPos.byteIdx := by
    simp only [atEnd, decide_eq_true_eq, Nat.not_le] at h
    exact h
  have hstep := String.Pos.Raw.byteIdx_lt_byteIdx_next s.input.str s.pos
  simp only [next, h, Bool.false_eq_true, ↓reduceIte, remaining]
  repeat' split
  all_goals dsimp only; omega

/-- Consuming a character never reads past the end. -/
theorem remaining_next_le (s : LexState) : s.next.remaining ≤ s.remaining := by
  by_cases h : s.atEnd = true
  · simp [next, h]
  · exact Nat.le_of_lt (remaining_next_lt h)

/-- Consuming two characters, the first of which is there, reads at least
one byte. -/
theorem remaining_next_next_lt {s : LexState} (h : ¬ s.atEnd = true) :
    s.next.next.remaining < s.remaining :=
  Nat.lt_of_le_of_lt (remaining_next_le _) (remaining_next_lt h)

/-- There is a character at the current position exactly when the input is
not exhausted. -/
theorem not_atEnd_of_cur {s : LexState} {c : Char} (h : s.cur = some c) : ¬ s.atEnd = true := by
  intro he
  simp [cur, he] at h

/-- Does the input continue with `str` at the current position? -/
@[inline] def startsWith (s : LexState) (str : String) : Bool :=
  let n := str.utf8ByteSize
  s.pos.byteIdx + n ≤ s.input.stopPos.byteIdx &&
    String.Pos.Raw.substrEq s.input.str s.pos str ⟨0⟩ n

end LexState

/-- The mode in which the next token is to be read. -/
inductive LexMode where
  /-- An expression is expected: `/` starts a regular expression. -/
  | regex
  /-- An operator is expected: `/` is division. -/
  | div
  /-- The continuation of a template literal is expected. -/
  | template
deriving Repr, BEq, DecidableEq, Inhabited

/-- Lexical error, in the format used by the Haskell package. -/
def lexError (s : LexState) : String :=
  s!"lexical error @ line {s.line} and column {s.col}"

def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$' || c.val > 127

def isIdentPart (c : Char) : Bool := isIdentStart c || c.isDigit

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def isOctalDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'

/-- Does this substring read exactly like `s`?  No allocation takes place. -/
@[inline] def subIs (ss : Substring.Raw) (s : String) : Bool :=
  let n := s.utf8ByteSize
  ss.stopPos.byteIdx - ss.startPos.byteIdx == n &&
    String.Pos.Raw.substrEq ss.str ss.startPos s ⟨0⟩ n

/-- Keywords and reserved words, mapped to their token kind.  The identifier
is passed as a `Substring` of the input and is only compared, never copied;
the candidates are looked up by their first character. -/
def keywordKindSub (ss : Substring.Raw) : Option TokenKind :=
  let n := ss.stopPos.byteIdx - ss.startPos.byteIdx
  if n < 2 || n > 10 then none else
  match String.Pos.Raw.get ss.str ss.startPos with
  | 'a' =>
      if subIs ss "as" then some .AsToken
      else if subIs ss "async" then some .AsyncToken
      else if subIs ss "await" then some .AwaitToken else none
  | 'b' => if subIs ss "break" then some .BreakToken else none
  | 'c' =>
      if subIs ss "case" then some .CaseToken
      else if subIs ss "catch" then some .CatchToken
      else if subIs ss "class" then some .ClassToken
      else if subIs ss "const" then some .ConstToken
      else if subIs ss "continue" then some .ContinueToken else none
  | 'd' =>
      if subIs ss "debugger" then some .DebuggerToken
      else if subIs ss "default" then some .DefaultToken
      else if subIs ss "delete" then some .DeleteToken
      else if subIs ss "do" then some .DoToken else none
  | 'e' =>
      if subIs ss "else" then some .ElseToken
      else if subIs ss "enum" then some .EnumToken
      else if subIs ss "export" then some .ExportToken
      else if subIs ss "extends" then some .ExtendsToken else none
  | 'f' =>
      if subIs ss "false" then some .FalseToken
      else if subIs ss "finally" then some .FinallyToken
      else if subIs ss "for" then some .ForToken
      else if subIs ss "from" then some .FromToken
      else if subIs ss "function" then some .FunctionToken else none
  | 'g' => if subIs ss "get" then some .GetToken else none
  | 'i' =>
      if subIs ss "if" then some .IfToken
      else if subIs ss "import" then some .ImportToken
      else if subIs ss "in" then some .InToken
      else if subIs ss "instanceof" then some .InstanceofToken
      else if subIs ss "implements" || subIs ss "interface" then some .FutureToken else none
  | 'l' => if subIs ss "let" then some .LetToken else none
  | 'n' =>
      if subIs ss "new" then some .NewToken
      else if subIs ss "null" then some .NullToken else none
  | 'o' => if subIs ss "of" then some .OfToken else none
  | 'p' =>
      if subIs ss "package" || subIs ss "private" || subIs ss "protected" || subIs ss "public"
      then some .FutureToken else none
  | 'r' => if subIs ss "return" then some .ReturnToken else none
  | 's' =>
      if subIs ss "set" then some .SetToken
      else if subIs ss "static" then some .StaticToken
      else if subIs ss "super" then some .SuperToken
      else if subIs ss "switch" then some .SwitchToken else none
  | 't' =>
      if subIs ss "this" then some .ThisToken
      else if subIs ss "throw" then some .ThrowToken
      else if subIs ss "true" then some .TrueToken
      else if subIs ss "try" then some .TryToken
      else if subIs ss "typeof" then some .TypeofToken else none
  | 'v' =>
      if subIs ss "var" then some .VarToken
      else if subIs ss "void" then some .VoidToken else none
  | 'w' =>
      if subIs ss "while" then some .WhileToken
      else if subIs ss "with" then some .WithToken else none
  | 'y' => if subIs ss "yield" then some .YieldToken else none
  | _ => none

/-- Keywords and reserved words, mapped to their token kind. -/
def keywordKind (s : String) : Option TokenKind := keywordKindSub s.toRawSubstring

/-- The punctuation tokens, longest match first, recognised by dispatching on
the characters at the current position.  Returns the number of characters of
the token together with its kind. -/
def punctuatorAt (s : LexState) (c : Char) : Option (Nat × TokenKind) :=
  match c with
  | '>' =>
      let c1 := s.charAt 1
      if c1 == '>' then
        let c2 := s.charAt 2
        if c2 == '>' then
          if s.charAt 3 == '=' then some (4, .UrshAssignToken) else some (3, .UrshToken)
        else if c2 == '=' then some (3, .RshAssignToken)
        else some (2, .RshToken)
      else if c1 == '=' then some (2, .GeToken)
      else some (1, .GtToken)
  | '<' =>
      let c1 := s.charAt 1
      if c1 == '<' then
        if s.charAt 2 == '=' then some (3, .LshAssignToken) else some (2, .LshToken)
      else if c1 == '=' then some (2, .LeToken)
      else some (1, .LtToken)
  | '=' =>
      let c1 := s.charAt 1
      if c1 == '=' then
        if s.charAt 2 == '=' then some (3, .StrictEqToken) else some (2, .EqToken)
      else if c1 == '>' then some (2, .ArrowToken)
      else some (1, .SimpleAssignToken)
  | '!' =>
      if s.charAt 1 == '=' then
        if s.charAt 2 == '=' then some (3, .StrictNeToken) else some (2, .NeToken)
      else some (1, .NotToken)
  | '.' =>
      if s.charAt 1 == '.' && s.charAt 2 == '.' then some (3, .SpreadToken)
      else some (1, .DotToken)
  | '&' =>
      let c1 := s.charAt 1
      if c1 == '&' then
        if s.charAt 2 == '=' then some (3, .LogicalAndAssignToken) else some (2, .AndToken)
      else if c1 == '=' then some (2, .AndAssignToken)
      else some (1, .BitwiseAndToken)
  | '|' =>
      let c1 := s.charAt 1
      if c1 == '|' then
        if s.charAt 2 == '=' then some (3, .LogicalOrAssignToken) else some (2, .OrToken)
      else if c1 == '=' then some (2, .OrAssignToken)
      else some (1, .BitwiseOrToken)
  | '+' =>
      let c1 := s.charAt 1
      if c1 == '+' then some (2, .IncrementToken)
      else if c1 == '=' then some (2, .PlusAssignToken)
      else some (1, .PlusToken)
  | '-' =>
      let c1 := s.charAt 1
      if c1 == '-' then some (2, .DecrementToken)
      else if c1 == '=' then some (2, .MinusAssignToken)
      else some (1, .MinusToken)
  | '*' => if s.charAt 1 == '=' then some (2, .TimesAssignToken) else some (1, .MulToken)
  | '/' => if s.charAt 1 == '=' then some (2, .DivideAssignToken) else some (1, .DivToken)
  | '%' => if s.charAt 1 == '=' then some (2, .ModAssignToken) else some (1, .ModToken)
  | '^' => if s.charAt 1 == '=' then some (2, .XorAssignToken) else some (1, .BitwiseXorToken)
  | '~' => some (1, .BitwiseNotToken)
  | '@' => some (1, .AtToken)
  | '?' =>
      let c1 := s.charAt 1
      if c1 == '?' then
        if s.charAt 2 == '=' then some (3, .NullishAssignToken) else some (2, .NullishToken)
      -- `?.` is the optional chaining operator, but `x?.5:y` is a
      -- conditional whose branch is `.5`, so a digit after the dot wins
      else if c1 == '.' && !(s.charAt 2).isDigit then some (2, .OptionalChainToken)
      else some (1, .HookToken)
  | ':' => some (1, .ColonToken)
  | ';' => some (1, .SemiColonToken)
  | ',' => some (1, .CommaToken)
  | '[' => some (1, .LeftBracketToken)
  | ']' => some (1, .RightBracketToken)
  | '{' => some (1, .LeftCurlyToken)
  | '}' => some (1, .RightCurlyToken)
  | '(' => some (1, .LeftParenToken)
  | ')' => some (1, .RightParenToken)
  | _ => none

/-- Consume characters while the predicate holds. -/
def scanWhile (p : Char → Bool) (t : LexState) : LexState :=
  match _h : t.cur with
  | none => t
  | some ch => if p ch then scanWhile p t.next else t
termination_by t.remaining
decreasing_by exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)

/-- Is this character a line terminator? -/
def isLineTerminator (c : Char) : Bool :=
  c == '\n' || c == '\r' || c == '\u2028' || c == '\u2029'

/-- Is this character whitespace? -/
def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\u000b' || c == '\u000c' || c == '\u00a0'
    || c == '\u1680' || c == '\u180e' || ('\u2000' ≤ c && c ≤ '\u200a')
    || c == '\u202f' || c == '\u205f' || c == '\u3000' || c == '\ufeff'
    || isLineTerminator c

/-- Consume the rest of a line comment. -/
def scanLineComment (t : LexState) : LexState :=
  match _h : t.cur with
  | none => t
  | some ch => if isLineTerminator ch then t else scanLineComment t.next
termination_by t.remaining
decreasing_by exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)

/-- Consume the rest of a block comment, including the closing `*/`. -/
def scanBlockComment (t : LexState) : Except String LexState :=
  if _h : t.atEnd then .error (lexError t)
  else if t.startsWith "*/" then .ok (t.skip 2)
  else scanBlockComment t.next
termination_by t.remaining
decreasing_by exact LexState.remaining_next_lt _h

/-- Scanning a line comment never reads past the end of the input. -/
theorem scanLineComment_remaining_le (t : LexState) :
    (scanLineComment t).remaining ≤ t.remaining := by
  induction t using scanLineComment.induct with
  | case1 t h => rw [scanLineComment]; split <;> simp_all
  | case2 t ch h hterm => rw [scanLineComment]; split <;> simp_all
  | case3 t ch h hterm ih =>
      rw [scanLineComment]
      split
      · exact Nat.le_refl _
      · rename_i ch' hc'
        have hch : ch = ch' := Option.some.inj (h.symm.trans hc')
        subst hch
        simp only [hterm, Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_trans ih (LexState.remaining_next_le t)

/-- Scanning a block comment never reads past the end of the input. -/
theorem scanBlockComment_remaining_le {t u : LexState} (h : scanBlockComment t = .ok u) :
    u.remaining ≤ t.remaining := by
  induction t using scanBlockComment.induct generalizing u with
  | case1 t ht => rw [scanBlockComment] at h; simp [ht] at h
  | case2 t ht hstar =>
      rw [scanBlockComment] at h
      simp only [ht, Bool.false_eq_true, ↓reduceDIte, hstar, ↓reduceIte, Except.ok.injEq] at h
      subst h
      show (t.next.next).remaining ≤ t.remaining
      exact Nat.le_trans (LexState.remaining_next_le _) (LexState.remaining_next_le t)
  | case3 t ht hstar ih =>
      rw [scanBlockComment] at h
      simp only [ht, Bool.false_eq_true, ↓reduceDIte, hstar, ↓reduceIte] at h
      exact Nat.le_trans (ih h) (LexState.remaining_next_le t)

/-- Skip whitespace and comments, collecting the comments (in reverse).

The loop is well founded on `LexState.remaining`, the number of bytes left:
a step either consumes a whitespace character or scans a comment, and a
comment starts with two characters which are there, so every step reads at
least one byte.  There is no step counter, so the scan is driven by the
input alone. -/
def skipTriviaAux (s : LexState) (acc : List CommentAnnotation) :
    Except String (List CommentAnnotation × LexState) :=
  match _hc : s.cur with
  | none => .ok (acc, s)
  | some c =>
    if isWhitespace c then
      skipTriviaAux s.next acc
    else if c == '/' && s.charAt 1 == '/' then
      let start := s.pos
      let p := s.posn
      let t := scanLineComment s.next
      skipTriviaAux t (.CommentA p (t.textFrom start) :: acc)
    else if c == '/' && s.charAt 1 == '*' then
      let start := s.pos
      let p := s.posn
      match _ht : scanBlockComment (s.skip 2) with
      | .error e => .error e
      | .ok t => skipTriviaAux t (.CommentA p (t.textFrom start) :: acc)
    else
      .ok (acc, s)
termination_by s.remaining
decreasing_by
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _hc)
  · exact Nat.lt_of_le_of_lt (scanLineComment_remaining_le s.next)
      (LexState.remaining_next_lt (LexState.not_atEnd_of_cur _hc))
  · exact Nat.lt_of_le_of_lt (scanBlockComment_remaining_le _ht)
      (LexState.remaining_next_next_lt (LexState.not_atEnd_of_cur _hc))

/-- Skip whitespace and comments, collecting the comments in source order. -/
@[inline] def skipTrivia (s : LexState) :
    Except String (List CommentAnnotation × LexState) := do
  let (acc, t) ← skipTriviaAux s []
  return (acc.reverse, t)

/-- Read a string literal, including its quotes. -/
def scanString (quote : Char) (t : LexState) : Except String LexState :=
  match _h : t.cur with
  | none => .error (lexError t)
  | some c =>
    if c == quote then .ok t.next
    else if c == '\n' then .error (lexError t)
    else if c == '\\' then
      match t.next.cur with
      | none => .error (lexError t.next)
      | some _ => scanString quote t.next.next
    else scanString quote t.next
termination_by t.remaining
decreasing_by
  · exact LexState.remaining_next_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)

def lexString (s : LexState) (quote : Char) : Except String LexState :=
  scanString quote s.next

/-- Read the body of a regular expression literal.

As in the Alex lexer of the Haskell package, a character class runs up to the
first `]`; a backslash inside a class does not escape it. -/
def scanRegex (inClass : Bool) (t : LexState) : Except String LexState :=
  match _h : t.cur with
  | none => .error (lexError t)
  | some c =>
    if c == '\n' then .error (lexError t)
    else if inClass then
      if c == ']' then scanRegex false t.next else scanRegex true t.next
    else if c == '\\' then
      match t.next.cur with
      | none => .error (lexError t.next)
      | some _ => scanRegex false t.next.next
    else if c == '[' then scanRegex true t.next
    else if c == '/' then .ok (scanWhile isIdentPart t.next)
    else scanRegex false t.next
termination_by t.remaining
decreasing_by
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)

/-- Read a regular expression literal, including the delimiters and flags. -/
def lexRegex (s : LexState) : Except String LexState := scanRegex false s.next

/-- Read a numeric literal, returning its token kind. -/
def lexNumber (s : LexState) : Except String (TokenKind × LexState) :=
  if s.cur == some '0' && (s.charAt 1 == 'x' || s.charAt 1 == 'X') then
    let s2 := s.skip 2
    let t := scanWhile isHexDigit s2
    if t.pos.byteIdx == s2.pos.byteIdx then .error (lexError t) else .ok (.HexIntegerToken, t)
  else if s.cur == some '0' && isOctalDigit (s.charAt 1) then
    .ok (.OctalToken, scanWhile isOctalDigit s.next)
  else
    let t := scanWhile Char.isDigit s
    let t := if t.cur == some '.' then scanWhile Char.isDigit t.next else t
    let t :=
      if t.cur == some 'e' || t.cur == some 'E' then
        let u := t.next
        let u := if u.cur == some '+' || u.cur == some '-' then u.next else u
        scanWhile Char.isDigit u
      else t
    .ok (.DecimalToken, t)

/-- Read a template literal head (or a template with no substitution). -/
def scanTemplateStart (t : LexState) : Except String (TokenKind × LexState) :=
  match _h : t.cur with
  | none => .error (lexError t)
  | some c =>
    if c == '\\' then
      match t.next.cur with
      | none => .error (lexError t.next)
      | some _ => scanTemplateStart t.next.next
    else if c == '`' then .ok (.NoSubstitutionTemplateToken, t.next)
    else if c == '$' && t.charAt 1 == '{' then .ok (.TemplateHeadToken, t.skip 2)
    else scanTemplateStart t.next
termination_by t.remaining
decreasing_by
  · exact LexState.remaining_next_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)

def lexTemplateStart (s : LexState) : Except String (TokenKind × LexState) :=
  scanTemplateStart s.next

/-- Read the continuation of a template literal, after the `}` that closes a
substitution. -/
def lexTemplateContinue (t : LexState) : Except String (TokenKind × LexState) :=
  match _h : t.cur with
  | none => .error (lexError t)
  | some c =>
    if c == '\\' then
      match t.next.cur with
      | none => .error (lexError t.next)
      | some _ => lexTemplateContinue t.next.next
    else if c == '`' then .ok (.TemplateTailToken, t.next)
    else if c == '$' && t.charAt 1 == '{' then .ok (.TemplateMiddleToken, t.skip 2)
    else lexTemplateContinue t.next
termination_by t.remaining
decreasing_by
  · exact LexState.remaining_next_next_lt (LexState.not_atEnd_of_cur _h)
  · exact LexState.remaining_next_lt (LexState.not_atEnd_of_cur _h)

/-- Read the next token. -/
def lexToken (mode : LexMode) (s0 : LexState) : Except String (Token × LexState) := do
  if mode == .template then
    -- No trivia handling inside a template literal.
    let start := s0.pos
    let p := s0.posn
    let (kind, t) ← lexTemplateContinue s0
    return ({ kind := kind, span := p, literal := t.textFrom start, comment := [] }, t)
  let (comments, s) ← skipTrivia s0
  let start := s.pos
  let p := s.posn
  let mk (kind : TokenKind) (t : LexState) : Token × LexState :=
    ({ kind := kind, span := p, literal := t.textFrom start, comment := comments }, t)
  match s.cur with
  | none => return ({ kind := .TailToken, span := p, literal := s.textFrom s.pos,
                      comment := comments }, s)
  | some c =>
    if isIdentStart c then
      let t := scanWhile isIdentPart s.next
      match keywordKindSub (t.textFrom start) with
      | some k => return mk k t
      | none => return mk .IdentifierToken t
    else if c == '#' && isIdentStart (s.charAt 1) then
      -- a private class name, `#x`; its text includes the `#`
      let t := scanWhile isIdentPart (s.skip 2)
      return mk .PrivateNameToken t
    else if c.isDigit || (c == '.' && (s.charAt 1).isDigit) then
      let (kind, t) ← lexNumber s
      return mk kind t
    else if c == '"' || c == '\'' then
      let t ← lexString s c
      return mk .StringToken t
    else if c == '`' then
      let (kind, t) ← lexTemplateStart s
      return mk kind t
    else if c == '/' && mode == .regex then
      let t ← lexRegex s
      return mk .RegExToken t
    else
      match punctuatorAt s c with
      | some (n, kind) => return mk kind (s.skip n)
      | none => .error (lexError s)

end Language.JavaScript.Parser.Lexer
