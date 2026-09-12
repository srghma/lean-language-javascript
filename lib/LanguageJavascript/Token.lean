/-
Port of `Language.JavaScript.Parser.Token` to Lean 4.

In the Haskell original, `Token` is a large sum type where every constructor
carries a source span, (sometimes) a literal and a list of comment
annotations.  In Lean we split this into a plain enumeration of token
*kinds* plus a record holding the payload; this keeps the token type easy to
build and to pattern match on, while carrying exactly the same information.
-/
import LanguageJavascript.SrcLocation

namespace Language.JavaScript.Parser

-- Structural decidable equality for the raw substrings carried by comment
-- annotations.  (Content equality is what `==` below uses; propositional
-- equality of a `Substring` is equality of the underlying string and of the
-- two offsets.)
deriving instance DecidableEq for String.Pos.Raw, Substring.Raw

/-- Comments and whitespace attached to a token.

The text is a `Substring`: an annotation is a slice of the source being
parsed, not a part of the resulting AST proper, so there is no reason to
copy it out of the input. -/
inductive CommentAnnotation where
  | CommentA (pos : TokenPosn) (text : Substring.Raw)
  | WhiteSpace (pos : TokenPosn) (text : Substring.Raw)
  | NoComment
-- `BEq` compares the *contents* of the texts (that is what `BEq Substring`
-- does), so annotations coming from different source strings compare equal
-- when they read the same.  Propositional equality, and hence the derived
-- `DecidableEq`, is the structural one.
deriving Repr, BEq, DecidableEq, Inhabited

namespace CommentAnnotation

/-- The text of a comment or whitespace annotation. -/
def text? : CommentAnnotation → Option Substring.Raw
  | .CommentA _ t => some t
  | .WhiteSpace _ t => some t
  | .NoComment => none

end CommentAnnotation

/-- The lexical class of a token. -/
inductive TokenKind where
  -- Comment
  | CommentToken
  | WsToken
  -- Identifiers
  | IdentifierToken
  /-- A private class name, `#x`; the text includes the `#`. -/
  | PrivateNameToken
  -- Javascript literals
  | DecimalToken
  | HexIntegerToken
  | OctalToken
  | StringToken
  | RegExToken
  -- Keywords
  | AsyncToken
  | AwaitToken
  | BreakToken
  | CaseToken
  | CatchToken
  | ClassToken
  | ConstToken
  | LetToken
  | ContinueToken
  | DebuggerToken
  | DefaultToken
  | DeleteToken
  | DoToken
  | ElseToken
  | EnumToken
  | ExtendsToken
  | FalseToken
  | FinallyToken
  | ForToken
  | FunctionToken
  | FromToken
  | IfToken
  | InToken
  | InstanceofToken
  | NewToken
  | NullToken
  | OfToken
  | ReturnToken
  | StaticToken
  | SuperToken
  | SwitchToken
  | ThisToken
  | ThrowToken
  | TrueToken
  | TryToken
  | TypeofToken
  | VarToken
  | VoidToken
  | WhileToken
  | YieldToken
  | ImportToken
  | WithToken
  | ExportToken
  -- Future reserved words
  | FutureToken
  -- Accessors
  | GetToken
  | SetToken
  -- Delimiters and operators
  | AutoSemiToken
  | SemiColonToken
  | CommaToken
  | HookToken
  | ColonToken
  | OrToken
  | AndToken
  | BitwiseOrToken
  | BitwiseXorToken
  | BitwiseAndToken
  | StrictEqToken
  | EqToken
  | TimesAssignToken
  | DivideAssignToken
  | ModAssignToken
  | PlusAssignToken
  | MinusAssignToken
  | LshAssignToken
  | RshAssignToken
  | UrshAssignToken
  | AndAssignToken
  | XorAssignToken
  | OrAssignToken
  /-- `&&=` -/
  | LogicalAndAssignToken
  /-- `||=` -/
  | LogicalOrAssignToken
  /-- `??=` -/
  | NullishAssignToken
  | SimpleAssignToken
  | StrictNeToken
  | NeToken
  | LshToken
  | LeToken
  | LtToken
  | UrshToken
  | RshToken
  | GeToken
  | GtToken
  | IncrementToken
  | DecrementToken
  | PlusToken
  | MinusToken
  | MulToken
  | DivToken
  | ModToken
  | NotToken
  | BitwiseNotToken
  | ArrowToken
  | SpreadToken
  | DotToken
  /-- `??` -/
  | NullishToken
  /-- `?.` -/
  | OptionalChainToken
  /-- `@`, which introduces a decorator. -/
  | AtToken
  | LeftBracketToken
  | RightBracketToken
  | LeftCurlyToken
  | RightCurlyToken
  | LeftParenToken
  | RightParenToken
  | CondcommentEndToken
  -- Template literal lexical components
  | NoSubstitutionTemplateToken
  | TemplateHeadToken
  | TemplateMiddleToken
  | TemplateTailToken
  -- Special cases
  | AsToken
  | TailToken
  | EOFToken
deriving Repr, BEq, DecidableEq, Inhabited

namespace TokenKind

/-- The name of the token kind, as the Haskell `Show` instance would print it. -/
def name : TokenKind → String
  | CommentToken => "CommentToken"
  | WsToken => "WsToken"
  | IdentifierToken => "IdentifierToken"
  | PrivateNameToken => "PrivateNameToken"
  | DecimalToken => "DecimalToken"
  | HexIntegerToken => "HexIntegerToken"
  | OctalToken => "OctalToken"
  | StringToken => "StringToken"
  | RegExToken => "RegExToken"
  | AsyncToken => "AsyncToken"
  | AwaitToken => "AwaitToken"
  | BreakToken => "BreakToken"
  | CaseToken => "CaseToken"
  | CatchToken => "CatchToken"
  | ClassToken => "ClassToken"
  | ConstToken => "ConstToken"
  | LetToken => "LetToken"
  | ContinueToken => "ContinueToken"
  | DebuggerToken => "DebuggerToken"
  | DefaultToken => "DefaultToken"
  | DeleteToken => "DeleteToken"
  | DoToken => "DoToken"
  | ElseToken => "ElseToken"
  | EnumToken => "EnumToken"
  | ExtendsToken => "ExtendsToken"
  | FalseToken => "FalseToken"
  | FinallyToken => "FinallyToken"
  | ForToken => "ForToken"
  | FunctionToken => "FunctionToken"
  | FromToken => "FromToken"
  | IfToken => "IfToken"
  | InToken => "InToken"
  | InstanceofToken => "InstanceofToken"
  | NewToken => "NewToken"
  | NullToken => "NullToken"
  | OfToken => "OfToken"
  | ReturnToken => "ReturnToken"
  | StaticToken => "StaticToken"
  | SuperToken => "SuperToken"
  | SwitchToken => "SwitchToken"
  | ThisToken => "ThisToken"
  | ThrowToken => "ThrowToken"
  | TrueToken => "TrueToken"
  | TryToken => "TryToken"
  | TypeofToken => "TypeofToken"
  | VarToken => "VarToken"
  | VoidToken => "VoidToken"
  | WhileToken => "WhileToken"
  | YieldToken => "YieldToken"
  | ImportToken => "ImportToken"
  | WithToken => "WithToken"
  | ExportToken => "ExportToken"
  | FutureToken => "FutureToken"
  | GetToken => "GetToken"
  | SetToken => "SetToken"
  | AutoSemiToken => "AutoSemiToken"
  | SemiColonToken => "SemiColonToken"
  | CommaToken => "CommaToken"
  | HookToken => "HookToken"
  | ColonToken => "ColonToken"
  | OrToken => "OrToken"
  | AndToken => "AndToken"
  | BitwiseOrToken => "BitwiseOrToken"
  | BitwiseXorToken => "BitwiseXorToken"
  | BitwiseAndToken => "BitwiseAndToken"
  | StrictEqToken => "StrictEqToken"
  | EqToken => "EqToken"
  | TimesAssignToken => "TimesAssignToken"
  | DivideAssignToken => "DivideAssignToken"
  | ModAssignToken => "ModAssignToken"
  | PlusAssignToken => "PlusAssignToken"
  | MinusAssignToken => "MinusAssignToken"
  | LshAssignToken => "LshAssignToken"
  | RshAssignToken => "RshAssignToken"
  | UrshAssignToken => "UrshAssignToken"
  | AndAssignToken => "AndAssignToken"
  | XorAssignToken => "XorAssignToken"
  | OrAssignToken => "OrAssignToken"
  | LogicalAndAssignToken => "LogicalAndAssignToken"
  | LogicalOrAssignToken => "LogicalOrAssignToken"
  | NullishAssignToken => "NullishAssignToken"
  | SimpleAssignToken => "SimpleAssignToken"
  | StrictNeToken => "StrictNeToken"
  | NeToken => "NeToken"
  | LshToken => "LshToken"
  | LeToken => "LeToken"
  | LtToken => "LtToken"
  | UrshToken => "UrshToken"
  | RshToken => "RshToken"
  | GeToken => "GeToken"
  | GtToken => "GtToken"
  | IncrementToken => "IncrementToken"
  | DecrementToken => "DecrementToken"
  | PlusToken => "PlusToken"
  | MinusToken => "MinusToken"
  | MulToken => "MulToken"
  | DivToken => "DivToken"
  | ModToken => "ModToken"
  | NotToken => "NotToken"
  | BitwiseNotToken => "BitwiseNotToken"
  | ArrowToken => "ArrowToken"
  | SpreadToken => "SpreadToken"
  | DotToken => "DotToken"
  | NullishToken => "NullishToken"
  | OptionalChainToken => "OptionalChainToken"
  | AtToken => "AtToken"
  | LeftBracketToken => "LeftBracketToken"
  | RightBracketToken => "RightBracketToken"
  | LeftCurlyToken => "LeftCurlyToken"
  | RightCurlyToken => "RightCurlyToken"
  | LeftParenToken => "LeftParenToken"
  | RightParenToken => "RightParenToken"
  | CondcommentEndToken => "CondcommentEndToken"
  | NoSubstitutionTemplateToken => "NoSubstitutionTemplateToken"
  | TemplateHeadToken => "TemplateHeadToken"
  | TemplateMiddleToken => "TemplateMiddleToken"
  | TemplateTailToken => "TemplateTailToken"
  | AsToken => "AsToken"
  | TailToken => "TailToken"
  | EOFToken => "EOFToken"

end TokenKind

/-- A lexical token: its kind, source span, literal text and the comments
and whitespace occurring between the previous token and this one. -/
structure Token where
  kind     : TokenKind
  span     : TokenPosn := TokenPosn.empty
  /-- The text of the token, as a `Substring` of the input: the lexer never
  copies it out of the source.  Use `Token.text` where a `String` is needed,
  which is only when the text goes into the AST. -/
  literal  : Substring.Raw := "".toRawSubstring
  comment  : List CommentAnnotation := []
deriving Repr, BEq, DecidableEq, Inhabited

namespace Token

/-- The text of the token, as a `String`. -/
def text (t : Token) : String := t.literal.toString

/-- Detailed string for a token; mainly intended for debugging. -/
def debugTokenString (t : Token) : String := t.kind.name

end Token

end Language.JavaScript.Parser
