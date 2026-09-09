/-
A large input test.  There is no such test in the Haskell suite; it is here
to check that the lexer and the parser stay usable on realistically sized
sources: everything below runs on a source of a few hundred kilobytes, which
only completes quickly if the lexer's cost is proportional to the size of the
input (and not, say, to its square).

The test is a correctness test, not a timing one: it checks that a large
generated program parses, that printing the parse tree reproduces the source
character for character, and that minifying it produces the expected number
of statements.
-/
import LanguageJavascriptTests.Utils
import LanguageJavascriptBench.SampleSource

namespace Test.Language.Javascript

open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.AST
open LanguageJavaScript.Pretty
open LanguageJavaScript.Process

/-- The number of chunks of the generated source; about 340 kB. -/
def scalingChunks : Nat := 1000

/-- Parse a large generated source, print it back and minify it, and report
what happened in one line. -/
def scalingReport : String :=
  let src := LanguageJavaScriptBench.Sample.source scalingChunks
  match parseProgram src with
  | .error e => s!"parse error: {e}"
  | .ok ast =>
    let stmts := match ast with
      | .JSAstProgram ss _ => ss.length
      | _ => 0
    let printed := renderToString ast
    let minified := renderToString (minifyJS ast)
    let roundTrip := if printed == src then "round trip ok" else "round trip DIFFERS"
    let smaller := if minified.utf8ByteSize < src.utf8ByteSize then "minified smaller"
      else "minified NOT smaller"
    s!"{stmts} statements, {roundTrip}, {smaller}"

/-- The expected outcome: one function declaration per chunk, an exact round
trip, and a minified program that is shorter than the source. -/
def scalingExpected : String :=
  s!"{scalingChunks} statements, round trip ok, minified smaller"

end Test.Language.Javascript
