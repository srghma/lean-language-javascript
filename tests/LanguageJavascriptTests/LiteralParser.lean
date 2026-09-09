/-
Port of the Haskell test module `LiteralParser`.
-/
import Spec
import LanguageJavascript.Parser
import LanguageJavascript.AST

namespace LanguageJavascriptTests.LiteralParser

open Spec
open Spec.Assert
open LanguageJavaScript.Parser
open LanguageJavaScript.Parser.AST

def escapeLabel (s : String) : String :=
  s.replace "\n" "\\n" |>.replace "\r" "\\r"

def showStrippedMaybe : Except String JSAST → String
  | .ok ast => "Right (" ++ showStripped ast ++ ")"
  | .error e => "Left (\"" ++ e ++ "\")"

def testLiteral (str : String) : String := showStrippedMaybe (parseLiteralAST str)

/-- The quote character used by the generated string tests. -/
inductive Quote where
  | SingleQuote
  | DoubleQuote
deriving BEq, DecidableEq, Inhabited

open Quote

/-- Printable ASCII, as Haskell's `isPrint` on characters below 127. -/
def isPrintAscii (ch : Nat) : Bool := 32 ≤ ch && ch < 127

/-- The three digit decimal escape used for non printable characters. -/
def threeDigits (ch : Nat) : String :=
  let str := ("000" ++ toString ch).toList
  String.ofList (str.drop (str.length - 3))

def showCh (quote : Quote) (ch : Nat) : String :=
  if ch == 34 then (if quote == DoubleQuote then "\\\"" else "\"")
  else if ch == 39 then (if quote == SingleQuote then "\\'" else "'")
  else if ch == 92 then "\\\\"
  else if isPrintAscii ch then String.singleton (Char.ofNat ch)
  else "\\" ++ threeDigits ch

def quoteString (quote : Quote) (s : String) : String :=
  if quote == SingleQuote then "'" ++ s ++ "'" else "\"" ++ s ++ "\""

def mkString (quote : Quote) (i : Nat) : String :=
  quoteString quote ("char #" ++ toString i ++ " " ++ showCh quote i)

def mkTestStrings (quote : Quote) : List String :=
  (List.range 256).map (mkString quote)

def literalCases : List (String × String) :=
  [ ("null", "Right (JSAstLiteral (JSLiteral 'null'))")
  , ("false", "Right (JSAstLiteral (JSLiteral 'false'))")
  , ("true", "Right (JSAstLiteral (JSLiteral 'true'))")
  -- hex numbers
  , ("0x1234fF", "Right (JSAstLiteral (JSHexInteger '0x1234fF'))")
  , ("0X1234fF", "Right (JSAstLiteral (JSHexInteger '0X1234fF'))")
  -- decimal numbers
  , ("1.0e4", "Right (JSAstLiteral (JSDecimal '1.0e4'))")
  , ("2.3E6", "Right (JSAstLiteral (JSDecimal '2.3E6'))")
  , ("4.5", "Right (JSAstLiteral (JSDecimal '4.5'))")
  , ("0.7e8", "Right (JSAstLiteral (JSDecimal '0.7e8'))")
  , ("0.7E8", "Right (JSAstLiteral (JSDecimal '0.7E8'))")
  , ("10", "Right (JSAstLiteral (JSDecimal '10'))")
  , ("0", "Right (JSAstLiteral (JSDecimal '0'))")
  , ("0.03", "Right (JSAstLiteral (JSDecimal '0.03'))")
  , ("0.7e+8", "Right (JSAstLiteral (JSDecimal '0.7e+8'))")
  , ("0.7e-18", "Right (JSAstLiteral (JSDecimal '0.7e-18'))")
  , ("1.0e+4", "Right (JSAstLiteral (JSDecimal '1.0e+4'))")
  , ("1.0e-4", "Right (JSAstLiteral (JSDecimal '1.0e-4'))")
  , ("1e18", "Right (JSAstLiteral (JSDecimal '1e18'))")
  , ("1e+18", "Right (JSAstLiteral (JSDecimal '1e+18'))")
  , ("1e-18", "Right (JSAstLiteral (JSDecimal '1e-18'))")
  , ("1E-01", "Right (JSAstLiteral (JSDecimal '1E-01'))")
  -- octal numbers
  , ("070", "Right (JSAstLiteral (JSOctal '070'))")
  , ("010234567", "Right (JSAstLiteral (JSOctal '010234567'))")
  -- strings
  , ("'cat'", "Right (JSAstLiteral (JSStringLiteral 'cat'))")
  , ("\"cat\"", "Right (JSAstLiteral (JSStringLiteral \"cat\"))")
  , ("'\\u1234'", "Right (JSAstLiteral (JSStringLiteral '\\u1234'))")
  , ("'\\uabcd'", "Right (JSAstLiteral (JSStringLiteral '\\uabcd'))")
  , ("\"\\r\\n\"", "Right (JSAstLiteral (JSStringLiteral \"\\r\\n\"))")
  , ("\"\\b\"", "Right (JSAstLiteral (JSStringLiteral \"\\b\"))")
  , ("\"\\f\"", "Right (JSAstLiteral (JSStringLiteral \"\\f\"))")
  , ("\"\\t\"", "Right (JSAstLiteral (JSStringLiteral \"\\t\"))")
  , ("\"\\v\"", "Right (JSAstLiteral (JSStringLiteral \"\\v\"))")
  , ("\"\\0\"", "Right (JSAstLiteral (JSStringLiteral \"\\0\"))")
  , ("\"hello\\nworld\"", "Right (JSAstLiteral (JSStringLiteral \"hello\\nworld\"))")
  , ("'hello\\nworld'", "Right (JSAstLiteral (JSStringLiteral 'hello\\nworld'))")
  , ("'char \u000a'", "Left (\"lexical error @ line 1 and column 7\")")
  -- strings with escaped quotes
  , ("'\"'", "Right (JSAstLiteral (JSStringLiteral '\"'))")
  , ("\"\\\"\"", "Right (JSAstLiteral (JSStringLiteral \"\\\"\"))")
  ]

def spec : Spec := do
  describe "Parse literals" do
    for (input, expected) in literalCases do
      it (escapeLabel input) do
        shouldEqual (testLiteral input) expected
    for str in mkTestStrings SingleQuote ++ mkTestStrings DoubleQuote do
      it (escapeLabel str) do
        shouldEqual (testLiteral str) ("Right (JSAstLiteral (JSStringLiteral " ++ str ++ "))")

end LanguageJavascriptTests.LiteralParser
