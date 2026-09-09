/-
Port of the Haskell test module `LiteralParser`.
-/
import LanguageJavascriptTests.Utils

namespace Test.Language.Javascript

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

/-- Every generated string literal must be parsed back verbatim. -/
def generatedStringTests : List Test :=
  (mkTestStrings SingleQuote ++ mkTestStrings DoubleQuote).map fun str =>
    shouldBe str (testLiteral str) ("Right (JSAstLiteral (JSStringLiteral " ++ str ++ "))")

def testLiteralParser : List Test :=
  -- null/true/false
  [ shouldBe "null" (testLiteral "null") "Right (JSAstLiteral (JSLiteral 'null'))"
  , shouldBe "false" (testLiteral "false") "Right (JSAstLiteral (JSLiteral 'false'))"
  , shouldBe "true" (testLiteral "true") "Right (JSAstLiteral (JSLiteral 'true'))"
  -- hex numbers
  , shouldBe "0x1234fF" (testLiteral "0x1234fF") "Right (JSAstLiteral (JSHexInteger '0x1234fF'))"
  , shouldBe "0X1234fF" (testLiteral "0X1234fF") "Right (JSAstLiteral (JSHexInteger '0X1234fF'))"
  -- decimal numbers
  , shouldBe "1.0e4" (testLiteral "1.0e4") "Right (JSAstLiteral (JSDecimal '1.0e4'))"
  , shouldBe "2.3E6" (testLiteral "2.3E6") "Right (JSAstLiteral (JSDecimal '2.3E6'))"
  , shouldBe "4.5" (testLiteral "4.5") "Right (JSAstLiteral (JSDecimal '4.5'))"
  , shouldBe "0.7e8" (testLiteral "0.7e8") "Right (JSAstLiteral (JSDecimal '0.7e8'))"
  , shouldBe "0.7E8" (testLiteral "0.7E8") "Right (JSAstLiteral (JSDecimal '0.7E8'))"
  , shouldBe "10" (testLiteral "10") "Right (JSAstLiteral (JSDecimal '10'))"
  , shouldBe "0" (testLiteral "0") "Right (JSAstLiteral (JSDecimal '0'))"
  , shouldBe "0.03" (testLiteral "0.03") "Right (JSAstLiteral (JSDecimal '0.03'))"
  , shouldBe "0.7e+8" (testLiteral "0.7e+8") "Right (JSAstLiteral (JSDecimal '0.7e+8'))"
  , shouldBe "0.7e-18" (testLiteral "0.7e-18") "Right (JSAstLiteral (JSDecimal '0.7e-18'))"
  , shouldBe "1.0e+4" (testLiteral "1.0e+4") "Right (JSAstLiteral (JSDecimal '1.0e+4'))"
  , shouldBe "1.0e-4" (testLiteral "1.0e-4") "Right (JSAstLiteral (JSDecimal '1.0e-4'))"
  , shouldBe "1e18" (testLiteral "1e18") "Right (JSAstLiteral (JSDecimal '1e18'))"
  , shouldBe "1e+18" (testLiteral "1e+18") "Right (JSAstLiteral (JSDecimal '1e+18'))"
  , shouldBe "1e-18" (testLiteral "1e-18") "Right (JSAstLiteral (JSDecimal '1e-18'))"
  , shouldBe "1E-01" (testLiteral "1E-01") "Right (JSAstLiteral (JSDecimal '1E-01'))"
  -- octal numbers
  , shouldBe "070" (testLiteral "070") "Right (JSAstLiteral (JSOctal '070'))"
  , shouldBe "010234567" (testLiteral "010234567") "Right (JSAstLiteral (JSOctal '010234567'))"
  -- strings
  , shouldBe "'cat'" (testLiteral "'cat'") "Right (JSAstLiteral (JSStringLiteral 'cat'))"
  , shouldBe "\"cat\"" (testLiteral "\"cat\"") "Right (JSAstLiteral (JSStringLiteral \"cat\"))"
  , shouldBe "'\\u1234'" (testLiteral "'\\u1234'")
      "Right (JSAstLiteral (JSStringLiteral '\\u1234'))"
  , shouldBe "'\\uabcd'" (testLiteral "'\\uabcd'")
      "Right (JSAstLiteral (JSStringLiteral '\\uabcd'))"
  , shouldBe "\"\\r\\n\"" (testLiteral "\"\\r\\n\"")
      "Right (JSAstLiteral (JSStringLiteral \"\\r\\n\"))"
  , shouldBe "\"\\b\"" (testLiteral "\"\\b\"") "Right (JSAstLiteral (JSStringLiteral \"\\b\"))"
  , shouldBe "\"\\f\"" (testLiteral "\"\\f\"") "Right (JSAstLiteral (JSStringLiteral \"\\f\"))"
  , shouldBe "\"\\t\"" (testLiteral "\"\\t\"") "Right (JSAstLiteral (JSStringLiteral \"\\t\"))"
  , shouldBe "\"\\v\"" (testLiteral "\"\\v\"") "Right (JSAstLiteral (JSStringLiteral \"\\v\"))"
  , shouldBe "\"\\0\"" (testLiteral "\"\\0\"") "Right (JSAstLiteral (JSStringLiteral \"\\0\"))"
  , shouldBe "\"hello\\nworld\"" (testLiteral "\"hello\\nworld\"")
      "Right (JSAstLiteral (JSStringLiteral \"hello\\nworld\"))"
  , shouldBe "'hello\\nworld'" (testLiteral "'hello\\nworld'")
      "Right (JSAstLiteral (JSStringLiteral 'hello\\nworld'))"
  , shouldBe "'char \u000a'" (testLiteral "'char \u000a'")
      "Left (\"lexical error @ line 1 and column 7\")"
  -- strings with escaped quotes
  , shouldBe "'\"'" (testLiteral "'\"'") "Right (JSAstLiteral (JSStringLiteral '\"'))"
  , shouldBe "\"\\\"\"" (testLiteral "\"\\\"\"")
      "Right (JSAstLiteral (JSStringLiteral \"\\\"\"))"
  ] ++ generatedStringTests

#guard allPass testLiteralParser

end Test.Language.Javascript
