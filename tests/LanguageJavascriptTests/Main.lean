import Spec.RunSpec
import LanguageJavascriptTests.LiteralParser
import LanguageJavascriptTests.ExpressionParser
import LanguageJavascriptTests.StatementParser
import LanguageJavascriptTests.ProgramParser
import LanguageJavascriptTests.ModuleParser
import LanguageJavascriptTests.RoundTrip
import LanguageJavascriptTests.Minify
import LanguageJavascriptTests.Scaling
import LanguageJavascriptTests.Mini.AST
import LanguageJavascriptTests.Brujin.AST

open Spec

def spec : Spec := do
  LanguageJavascriptTests.LiteralParser.spec
  LanguageJavascriptTests.ExpressionParser.spec
  LanguageJavascriptTests.StatementParser.spec
  LanguageJavascriptTests.ProgramParser.spec
  LanguageJavascriptTests.ModuleParser.spec
  LanguageJavascriptTests.RoundTrip.spec
  LanguageJavascriptTests.Minify.spec
  LanguageJavascriptTests.Scaling.spec
  , ("Deterministic AST (MiniAST)", testMiniAST)
  , ("Scope safe AST (BrujinAST)", testBrujinAST)

def main (args : List String) : IO UInt32 := do
  runSpecFromArgsAndReturnExitCode args spec
