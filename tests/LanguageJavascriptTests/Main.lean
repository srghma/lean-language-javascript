/-
Runs every ported test suite and reports the result, in the spirit of the
Haskell `hspec` driver.  The same tests are also checked at compile time by
the `#guard` in each test module, so `lake build` already verifies them;
this executable makes the outcome visible (`lake exe tests`).
-/
import LanguageJavascriptTests.LiteralParser
import LanguageJavascriptTests.ExpressionParser
import LanguageJavascriptTests.StatementParser
import LanguageJavascriptTests.ProgramParser
import LanguageJavascriptTests.ModuleParser
import LanguageJavascriptTests.RoundTrip
import LanguageJavascriptTests.Minify
import LanguageJavascriptTests.Scaling

open Test.Language.Javascript

def suites : List (String × List Test) :=
  [ ("Parse literals", testLiteralParser)
  , ("Parse expressions", testExpressionParser)
  , ("Parse statements", testStatementParser)
  , ("Program parser", testProgramParser)
  , ("Module parser", testModuleParser)
  , ("Roundtrip", testRoundTrip)
  , ("Minify", testMinify)
  ]

def main : IO UInt32 := do
  IO.println "JavaScript AST, parser, printer and minifier:"
  let mut ok := true
  let mut total := 0
  for (name, ts) in suites do
    total := total + ts.length
    let good ← runTests name ts
    ok := ok && good
  -- The one file-based test of the Haskell `ProgramParser` suite; it reads
  -- `test/Unicode.js` so it cannot be checked at compile time.
  total := total + 1
  let unicodePath : System.FilePath ← do
    let candidates : List System.FilePath := [
      "./LanguageJavascriptTests/test/Unicode.js",
      "./test/Unicode.js",
      "tests/LanguageJavascriptTests/test/Unicode.js"
    ]
    let mut found : System.FilePath := "./LanguageJavascriptTests/test/Unicode.js"
    for c in candidates do
      if (← c.pathExists) then
        found := c
        break
    pure found
  let good ← runIOTest "Program parser (utf8 file)"
      (testFileUtf8 unicodePath)
      "JSAstProgram [JSOpAssign ('=',JSIdentifier 'àáâãäå',JSDecimal '1'),JSSemicolon]"
  ok := ok && good
  -- A large generated source, run at run time only: it is far too big to be
  -- checked by the compile time `#guard`s.
  total := total + 1
  let good ← runIOTest "Large input" (pure scalingReport) scalingExpected
  ok := ok && good
  if ok then
    IO.println s!"All {total} tests passed."
    return 0
  else
    IO.println "Some tests FAILED."
    return 1
