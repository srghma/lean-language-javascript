import Spec.RunSpec
import LanguageJavascriptTests.Types
import LanguageJavascriptTests.RegExpEngine
import LanguageJavascriptTests.LiteralParser
import LanguageJavascriptTests.ExpressionParser
import LanguageJavascriptTests.StatementParser
import LanguageJavascriptTests.ProgramParser
import LanguageJavascriptTests.ModuleParser
import LanguageJavascriptTests.RoundTrip
import LanguageJavascriptTests.Modern
import LanguageJavascriptTests.Minify
import LanguageJavascriptTests.Scaling
import LanguageJavascriptTests.Mini.AST
import LanguageJavascriptTests.Brujin.AST
import LanguageJavascriptTests.Brujin.Optimizer
import LanguageJavascriptTests.Brujin.Extensions
import LanguageJavascriptTests.Elab

open Spec

def spec : Spec := do
  LanguageJavascriptTests.Types.spec
  LanguageJavascriptTests.RegExpEngine.spec
  LanguageJavascriptTests.LiteralParser.spec
  LanguageJavascriptTests.ExpressionParser.spec
  LanguageJavascriptTests.StatementParser.spec
  LanguageJavascriptTests.ProgramParser.spec
  LanguageJavascriptTests.ModuleParser.spec
  LanguageJavascriptTests.RoundTrip.spec
  LanguageJavascriptTests.Modern.spec
  LanguageJavascriptTests.Minify.spec
  LanguageJavascriptTests.Scaling.spec
  LanguageJavascriptTests.Mini.AST.spec
  LanguageJavascriptTests.Brujin.AST.spec
  LanguageJavascriptTests.Brujin.Optimizer.spec
  LanguageJavascriptTests.Brujin.Extensions.spec
  LanguageJavascriptTests.Elab.spec

def main (args : List String) : IO UInt32 := do
  runSpecFromArgsAndReturnExitCode args spec
