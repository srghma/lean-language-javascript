/-
A large input test.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascript.Minify
import LanguageJavascriptBench.SampleSource
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.Printer
import LanguageJavascriptMini.ToFull
import LanguageJavascriptBrujin.AST
import LanguageJavascriptBrujin.OfMini
import LanguageJavascriptBrujin.ToMini
import LanguageJavascriptBrujin.Optimizer

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
  let src := LanguageJavascriptBench.Sample.source scalingChunks
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

def scalingExpected : String :=
  s!"{scalingChunks} statements, round trip ok, minified smaller"

def miniScalingReport : String :=
  let src := LanguageJavascriptBench.Sample.source scalingChunks
  match Language.JavaScript.MiniAST.parse src with
  | .error e => s!"parse error: {e}"
  | .ok p =>
    let printed := Language.JavaScript.MiniAST.printProgram p
    let stable := match Language.JavaScript.MiniAST.parse printed with
      | .ok q => q == p
      | .error _ => false
    let viaAST :=
      match Language.JavaScript.MiniAST.ofAST (Language.JavaScript.MiniAST.toAST p) with
      | .ok q => q == p
      | .error _ => false
    let stableText := if stable then "printing stable" else "printing UNSTABLE"
    let viaText := if viaAST then "AST round trip ok" else "AST round trip FAILED"
    s!"{p.items.length} items, {stableText}, {viaText}"

def miniScalingExpected : String :=
  s!"{scalingChunks} items, printing stable, AST round trip ok"

def brujinScalingReport : String :=
  let src := LanguageJavascriptBench.Sample.source scalingChunks
  match Language.JavaScript.BrujinAST.parse src with
  | .error e => s!"conversion error: {e}"
  | .ok p =>
    let printed := Language.JavaScript.BrujinAST.printProgram p
    let stable := match Language.JavaScript.BrujinAST.parse printed with
      | .ok q => q == p
      | .error _ => false
    let items := (Language.JavaScript.BrujinAST.toMiniProgram p).items.length
    s!"{items} items, {if stable then "printing stable" else "printing UNSTABLE"}"

def brujinScalingExpected : String :=
  s!"{scalingChunks} items, printing stable"

def brujinOptScalingReport : String :=
  let src := LanguageJavascriptBench.Sample.source scalingChunks
  match Language.JavaScript.BrujinAST.parse src with
  | .error e => s!"conversion error: {e}"
  | .ok p =>
    let q := Language.JavaScript.BrujinAST.optimizeProgram p
    let stable :=
      match Language.JavaScript.BrujinAST.parseIndexed
          (Language.JavaScript.BrujinAST.printProgramIndexed q) with
      | .ok r => r == q
      | .error _ => false
    let idempotent := Language.JavaScript.BrujinAST.optimizeProgram q == q
    let items := (Language.JavaScript.BrujinAST.toMiniProgram q).items.length
    let stableText := if stable then "indexed rendering stable" else "indexed rendering UNSTABLE"
    let idemText := if idempotent then "idempotent" else "NOT idempotent"
    s!"{items} items, {stableText}, {idemText}"

def brujinOptScalingExpected : String :=
  s!"{scalingChunks} items, indexed rendering stable, idempotent"

def spec : Spec := do
  describe "Large input" do
    it "Annotated AST (1000 chunks)" do
      shouldEqual scalingReport scalingExpected
    it "MiniAST (1000 chunks)" do
      shouldEqual miniScalingReport miniScalingExpected
    it "BrujinAST (1000 chunks)" do
      shouldEqual brujinScalingReport brujinScalingExpected
    it "BrujinAST Optimizer (1000 chunks)" do
      shouldEqual brujinOptScalingReport brujinOptScalingExpected

end LanguageJavascriptTests.Scaling
