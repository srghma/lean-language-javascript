/-
A large input test.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascript.Minify
import LanguageJavascriptBench.SampleSource

namespace LanguageJavascriptTests.Scaling

open Spec
open Spec.Assert
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

def spec : Spec := do
  describe "Large input" do
    it "1000 chunks" do
      shouldEqual scalingReport scalingExpected

end LanguageJavascriptTests.Scaling
