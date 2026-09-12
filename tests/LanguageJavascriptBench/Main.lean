/-
A small benchmark for the lexer, the parser, the printer and the minifier.

Usage: `lake exe bench [chunks] [lex] [parse] [render] [minify] [regex]`.  It builds a
synthetic JavaScript source by repeating a fixed chunk (see
`LanguageJavascriptSampleSource.lean`), then reports the wall clock time of each
of the requested phases; with no phase given, all of them are run.
-/
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascript.Minify
import LanguageJavascript.RegExpLitSpec
import LanguageJavascriptBench.SampleSource

open Language.JavaScript.Parser
open Language.JavaScript.Parser.Lexer
open LanguageJavascriptBench.Sample (source)

/-- After these token kinds a `/` is the division operator; after anything
else it starts a regular expression.  (The parser knows which of the two it
expects; the benchmark, which only tokenises, uses this approximation.) -/
def divFollows : TokenKind → Bool
  | .IdentifierToken | .DecimalToken | .HexIntegerToken | .OctalToken
  | .StringToken | .RegExToken | .RightParenToken | .RightBracketToken
  | .ThisToken | .TrueToken | .FalseToken | .NullToken
  | .IncrementToken | .DecrementToken => true
  | _ => false

/-- Tokenise the whole input, counting the tokens.  `fuel` bounds the number
of tokens: every one but the last reads at least one byte, so the number of
bytes left is enough, and the count is a total definition. -/
def countTokensAux (fuel : Nat) (mode : LexMode) (s : LexState) (acc : Nat) :
    Except String Nat :=
  match fuel with
  | 0 => .ok acc
  | fuel + 1 => do
    let (t, s') ← lexToken mode s
    if t.kind == .TailToken then return acc + 1
    else countTokensAux fuel (if divFollows t.kind then .div else .regex) s' (acc + 1)

/-- Tokenise the whole input, counting the tokens. -/
def countTokens (mode : LexMode) (s : LexState) (acc : Nat) : Except String Nat :=
  countTokensAux (s.remaining + 1) mode s acc

/-- Time a pure computation.  `IO.lazyPure` keeps the compiler from floating
the (pure) work out of the timed region. -/
def timePure {α : Type} (name : String) (f : Unit → α) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoMsNow
  IO.println s!"  {name}: {t1 - t0} ms"
  (← IO.getStdout).flush
  return a

/-- A regular expression literal, long enough for the cost of reading it to
be visible: a pattern with a character class and an escaped slash, and all
the flags which can be combined. -/
def regexLiteral (i : Nat) : String :=
  "/" ++ String.ofList (List.replicate 400 'a') ++ "[^/]\\/" ++
    String.ofList (List.replicate 400 'b') ++ toString i ++ "/gimsu"

def main (args : List String) : IO Unit := do
  let known := ["lex", "parse", "render", "minify", "regex"]
  let phases := args.filter (fun a => known.contains a)
  let doLex := phases.isEmpty || phases.contains "lex"
  let doParse := phases.isEmpty || phases.contains "parse"
  let doRender := phases.isEmpty || phases.contains "render"
  let doMinify := phases.isEmpty || phases.contains "minify"
  let doRegex := phases.isEmpty || phases.contains "regex"
  let n := (args.filterMap String.toNat?).head?.getD 200
  let src ← timePure "build input" (fun _ => source n)
  IO.println s!"input: {src.utf8ByteSize} bytes ({n} chunks)"
  (← IO.getStdout).flush
  if doLex then
    match ← timePure "lex" (fun _ => countTokens .regex (LexState.ofString src) 0) with
    | .ok k => IO.println s!"    {k} tokens"
    | .error e => throw (IO.userError e)
  if doParse || doRender || doMinify then
    match ← timePure "parse" (fun _ => parseProgram src) with
    | .ok ast =>
        match ast with
        | .JSAstProgram ss _ => IO.println s!"    {ss.length} statements"
        | _ => pure ()
        if doRender then
          let out ← timePure "render" (fun _ => Language.JavaScript.Pretty.renderToString ast)
          IO.println s!"    {out.utf8ByteSize} bytes"
        if doMinify then
          let out ← timePure "minify"
            (fun _ => Language.JavaScript.Pretty.renderToString
              (Language.JavaScript.Process.minifyJS ast))
          IO.println s!"    {out.utf8ByteSize} bytes"
    | .error e => throw (IO.userError e)
  if doRegex then
    -- the in-place reader of a regular expression literal against the list
    -- based one it replaced (`RegExpLit.parse?_eq_parseAcc?` proves that the
    -- two read the same literal)
    let lits := (List.range (10 * n)).map regexLiteral
    IO.println s!"regular expression literals: {lits.length}"
    let sumLengths (f : String → Option Language.JavaScript.RegExpLit) : Nat :=
      lits.foldl (fun acc s => acc + (f s).elim 0 (fun r => r.source.val.utf8ByteSize)) 0
    let a ← timePure "read (list of characters)"
      (fun _ => sumLengths Language.JavaScript.RegExpLit.parseAcc?)
    let b ← timePure "read (in place)"
      (fun _ => sumLengths Language.JavaScript.RegExpLit.parse?)
    IO.println s!"    {a} = {b} bytes of pattern"
  return ()
