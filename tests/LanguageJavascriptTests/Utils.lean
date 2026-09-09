/-
Test helpers, corresponding to the helper functions of the Haskell test
suite (which uses hspec).

A test is a labelled pair of an actual and an expected string, exactly as the
Haskell tests compare `showStripped` output (or the re-rendered source) with
a literal string.  Each test module checks its own tests at compile time with
`#guard`; `LanguageJavascriptTests.Main` runs them all and reports failures.
-/
import LanguageJavascript.Parser
import LanguageJavascript.Printer
import LanguageJavascript.Minify

namespace Test.Language.Javascript

open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.AST
open LanguageJavaScript.Pretty
open LanguageJavaScript.Process

/-- A single test case. -/
structure Test where
  label : String
  actual : String
  expected : String
deriving Repr, Inhabited

/-- Build a test case; mirrors hspec's `shouldBe`. -/
def shouldBe (label actual expected : String) : Test := ⟨label, actual, expected⟩

def Test.passed (t : Test) : Bool := t.actual == t.expected

def allPass (ts : List Test) : Bool := ts.all Test.passed

def failures (ts : List Test) : List Test := ts.filter (fun t => !t.passed)

/-- `showStrippedMaybe` of the Haskell test suite. -/
def showStrippedMaybe : Except String JSAST → String
  | .ok ast => "Right (" ++ showStripped ast ++ ")"
  | .error e => "Left (\"" ++ e ++ "\")"

def testExpr (str : String) : String := showStrippedMaybe (parseExpressionAST str)

def testProg (str : String) : String := showStrippedMaybe (parseProgram str)

def testStmt (str : String) : String := showStrippedMaybe (parseStatementAST str)

def testLiteral (str : String) : String := showStrippedMaybe (parseLiteralAST str)

def testModule (str : String) : String := showStrippedMaybe (parseModule str)

/-- Parse a program and print it again; the result must be the input. -/
def testRT (str : String) : Test := shouldBe str (renderToString (readJs str)) str

/-- Parse a module and print it again; the result must be the input. -/
def testRTModule (str : String) : Test :=
  shouldBe str (renderToString (readJsModule str)) str

/-- Minify a program and print it. -/
def minifyProg (str : String) : String := renderToString (minifyJS (readJs str))

/-- Minify a module and print it. -/
def minifyModule (str : String) : String := renderToString (minifyJS (readJsModule str))

/-- Minify a single expression and print it. -/
def minifyExpr (str : String) : String :=
  match parseExpressionAST str with
  | .ok ast => renderToString (minifyJS ast)
  | .error e => e

/-- `testFileUtf8` of the Haskell test suite: parse a UTF-8 encoded source
file and show the stripped AST. -/
def testFileUtf8 (fileName : System.FilePath) : IO String := do
  return showStripped (← parseFileUtf8 fileName)

/-- Run a single `IO`-valued test (used for the file-based tests, which
cannot be checked at compile time). -/
def runIOTest (name : String) (actual : IO String) (expected : String) : IO Bool := do
  let got ← actual
  if got == expected then
    IO.println s!"  {name}: 1 test passed"
    return true
  else
    IO.println s!"  {name}: 1 test FAILED"
    IO.println s!"    expected: {expected}"
    IO.println s!"    actual:   {got}"
    return false

/-- Run a group of tests, printing any failures. -/
def runTests (name : String) (ts : List Test) : IO Bool := do
  let bad := failures ts
  if bad.isEmpty then
    IO.println s!"  {name}: {ts.length} tests passed"
    return true
  else
    IO.println s!"  {name}: {bad.length} of {ts.length} tests FAILED"
    for t in bad do
      IO.println s!"    input:    {t.label}"
      IO.println s!"    expected: {t.expected}"
      IO.println s!"    actual:   {t.actual}"
    return false

end Test.Language.Javascript
