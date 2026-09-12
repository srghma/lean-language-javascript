/-
Tests for the refined component types the three ASTs share: a numeric and a
regular expression literal are read as their value and printed canonically,
a spelling which is not a literal is refused, and a string literal keeps its
quote and the escapes the source wrote.
-/
import Spec
import LanguageJavascript.Types
import LanguageJavascript.AST

namespace LanguageJavascriptTests.Types

open Spec
open Spec.Assert
open Language.JavaScript

/-- The canonical spelling of the number a spelling denotes, or
`REJECTED`. -/
def numValue (raw : String) : String :=
  match JSNumber.parse? raw with
  | some n => n.render
  | none => "REJECTED"

/-- The quote, the body and the spelling of a string literal, or
`REJECTED`. -/
def strParts (raw : String) : String :=
  match JSStringSrc.ofString? raw with
  | some s => s.quote.text ++ "|" ++ s.body ++ "|" ++ s.render
  | none => "REJECTED"

/-- The pattern, the flags and the canonical spelling of a regular
expression literal, or `REJECTED`. -/
def regexParts (raw : String) : String :=
  match RegExpLit.parse? raw with
  | some r => r.source.val ++ "|" ++ r.flags.render ++ "|" ++ r.render
  | none => "REJECTED"

def numberCases : List (String × String × String) :=
  [ ("a hexadecimal literal is printed canonically, not as it was written",
      numValue "0X1234fF", "0x1234ff")
  , ("a trailing zero of the mantissa is dropped", numValue "1.50", "1.5")
  , ("an exponent", numValue "1.0e4", "10000")
  , ("a legacy octal literal", numValue "070", "0o70")
  , ("a negative exponent", numValue "1E-01", "0.1")
  , ("a numeric separator", numValue "1_000", "1000")
  , ("a BigInt", numValue "123n", "123n")
  , ("a spelling which is not a number is refused", numValue "potato", "REJECTED")
  , ("and so is the empty spelling", numValue "", "REJECTED")
  -- the reader scans the spelling in place, skipping the separators where
  -- they are written rather than removing them first
  , ("separators anywhere in a hexadecimal literal", numValue "0x_f_f", "0xff")
  , ("a separator before the BigInt suffix", numValue "1_2_n", "12n")
  , ("a separator is not a digit of its own", numValue "_", "REJECTED")
  , ("an `n` which is not the suffix", numValue "0xnf", "REJECTED")
  , ("a BigInt written in binary", numValue "0b1_01n", "0b101n")
  , ("a fractional BigInt is refused", numValue "1.5n", "REJECTED")
  , ("a fractional part of zero digits", numValue "1.", "1")
  , ("a fractional part alone", numValue ".5", "0.5")
  , ("an exponent of no digits is the literal it is written after",
      numValue "1e", "1")
  , ("a sign with no exponent digits is refused", numValue "1e+", "REJECTED")
  , ("a second decimal point is refused", numValue "1.2.3", "REJECTED")
  , ("a decimal point is not a digit", numValue ".", "REJECTED")
  , ("a legacy octal with a digit which is not octal is base ten",
      numValue "089", "89")
  , ("the digits of a hexadecimal literal are not those of a decimal one",
      numValue "1f", "REJECTED")
  , ("a spelling of characters which take several bytes is refused",
      numValue "1é", "REJECTED")
  ]

def stringCases : List (String × String × String) :=
  [ ("a single quoted literal", strParts "'a\\n'", "'|a\\n|'a\\n'")
  , ("a double quoted literal", strParts "\"a\"", "\"|a|\"a\"")
  , ("the empty literal", strParts "''", "'||''")
  , ("an unterminated literal is refused", strParts "'abc", "REJECTED")
  , ("and so is one closed by the other quote", strParts "\"abc'", "REJECTED")
  , ("and so is something which is not a literal", strParts "abc", "REJECTED")
  , ("a body of characters which take several bytes",
      strParts "'éà'", "'|éà|'éà'")
  , ("a quote alone is not a literal", strParts "'", "REJECTED")
  , ("and neither is a character which takes several bytes",
      strParts "é", "REJECTED")
  ]

def regexCases : List (String × String × String) :=
  [ ("a pattern with flags", regexParts "/a[/]b/gi", "a[/]b|gi|/a[/]b/gi")
  , ("the flags are printed in the canonical order",
      regexParts "/x/ig", "x|gi|/x/gi")
  , ("a class closes at the first unescaped bracket, as in the lexer",
      regexParts "/[/\\]/", "[/\\]||/[/\\]/")
  , ("something which is not a literal is refused", regexParts "notregex", "REJECTED")
  , ("and so is an unterminated one", regexParts "/abc", "REJECTED")
  , ("a pattern of characters which take several bytes",
      regexParts "/é∀[/]/u", "é∀[/]|u|/é∀[/]/u")
  , ("an escaped slash does not close the literal",
      regexParts "/a\\/b/", "a\\/b||/a\\/b/")
  , ("a repeated flag is refused", regexParts "/a/gg", "REJECTED")
  , ("an unknown flag is refused", regexParts "/a/z", "REJECTED")
  , ("an empty pattern is refused", regexParts "//", "REJECTED")
  ]

/-! ## The non-empty comma list

`JSCommaList1` is the type of the declarators of a `var`, a `let` or a
`const`: the empty list cannot be written down. -/

open Language.JavaScript.Parser.AST in
/-- `1, 2, 3` as a non-empty comma list. -/
def oneTwoThree : JSCommaList1 Nat :=
  .JSL1Cons (.JSL1Cons (.JSL1One 1) .JSNoAnnot 2) .JSNoAnnot 3

open Language.JavaScript.Parser.AST in
/-- The elements of a comma list, if it has any. -/
def elems1? (l : JSCommaList Nat) : String :=
  match toCommaList1? l with
  | some l1 => toString l1.toList
  | none => "EMPTY"

open Language.JavaScript.Parser.AST in
def commaList1Cases : List (String × String × String) :=
  [ ("the elements are in order", toString oneTwoThree.toList, "[1, 2, 3]")
  , ("flattening gives the elements of the comma list it is",
      toString (fromCommaList oneTwoThree.toCommaList), "[1, 2, 3]")
  , ("a single element", toString (JSCommaList1.JSL1One 7).toList, "[7]")
  , ("the last element and the ones before it",
      toString (fromCommaList oneTwoThree.unsnoc.1) ++ "|" ++ toString oneTwoThree.unsnoc.2,
      "[1, 2]|3")
  , ("appending", toString ((oneTwoThree.append .JSNoAnnot (.JSL1One 4)).toList), "[1, 2, 3, 4]")
  , ("mapping", toString ((oneTwoThree.map (· * 10)).toList), "[10, 20, 30]")
  , ("a comma list with elements becomes a non-empty one",
      elems1? (.JSLCons (.JSLOne 1) .JSNoAnnot 2), "[1, 2]")
  , ("the empty comma list does not", elems1? .JSLNil, "EMPTY")
  ]

def spec : Spec := do
  describe "Numeric literals of the annotated AST" do
    for (label, actual, expected) in numberCases do
      it label do
        shouldEqual actual expected

  describe "String literals of the annotated AST" do
    for (label, actual, expected) in stringCases do
      it label do
        shouldEqual actual expected

  describe "Regular expression literals of the annotated AST" do
    for (label, actual, expected) in regexCases do
      it label do
        shouldEqual actual expected

  describe "The non-empty comma list of the annotated AST" do
    for (label, actual, expected) in commaList1Cases do
      it label do
        shouldEqual actual expected

end LanguageJavascriptTests.Types
