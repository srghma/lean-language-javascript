/-
A small benchmark for the lexer, the parser, the printer and the minifier.

Usage: `lake exe bench [chunks] [lex] [parse] [render] [minify]`.  It builds a
synthetic JavaScript source by repeating a fixed chunk (see
`LanguageJavascriptSampleSource.lean`), then reports the wall clock time of each
of the requested phases; with no phase given, all of them are run.
-/
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascript.Minify
import LanguageJavascriptBench.SampleSource

open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.Lexer
open LanguageJavaScriptBench.Sample (source)

/-- After these token kinds a `/` is the division operator; after anything
else it starts a regular expression.  (The parser knows which of the two it
expects; the benchmark, which only tokenises, uses this approximation.) -/
def divFollows : TokenKind → Bool
  | .IdentifierToken | .DecimalToken | .HexIntegerToken | .OctalToken
  | .StringToken | .RegExToken | .RightParenToken | .RightBracketToken
  | .ThisToken | .TrueToken | .FalseToken | .NullToken
  | .IncrementToken | .DecrementToken => true
  | _ => false

/-- Tokenise the whole input, counting the tokens. -/
partial def countTokens (mode : LexMode) (s : LexState) (acc : Nat) : Except String Nat := do
  let (t, s') ← lexToken mode s
  if t.kind == .TailToken then return acc + 1
  else countTokens (if divFollows t.kind then .div else .regex) s' (acc + 1)

/-- Time a pure computation.  `IO.lazyPure` keeps the compiler from floating
the (pure) work out of the timed region. -/
def timePure {α : Type} (name : String) (f : Unit → α) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoMsNow
  IO.println s!"  {name}: {t1 - t0} ms"
  (← IO.getStdout).flush
  return a

def main (args : List String) : IO Unit := do
  let known := ["lex", "parse", "render", "minify"]
  let phases := args.filter (fun a => known.contains a)
  let doLex := phases.isEmpty || phases.contains "lex"
  let doParse := phases.isEmpty || phases.contains "parse"
  let doRender := phases.isEmpty || phases.contains "render"
  let doMinify := phases.isEmpty || phases.contains "minify"
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
          let out ← timePure "render" (fun _ => LanguageJavaScript.Pretty.renderToString ast)
          IO.println s!"    {out.utf8ByteSize} bytes"
        if doMinify then
          let out ← timePure "minify"
            (fun _ => LanguageJavaScript.Pretty.renderToString
              (LanguageJavaScript.Process.minifyJS ast))
          IO.println s!"    {out.utf8ByteSize} bytes"
    | .error e => throw (IO.userError e)
  return ()
