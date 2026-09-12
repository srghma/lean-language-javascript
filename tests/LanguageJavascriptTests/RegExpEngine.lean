/-
Tests for the bridge between the regular expression literals of the three
trees and the `lean-regex` library: what the library reads, what the flags
do, and what a match gives.
-/
import Spec
import LanguageJavascript.RegExpEngine

namespace LanguageJavascriptTests.RegExpEngine

open Spec
open Spec.Assert
open Language.JavaScript

/-- The literal written `raw`. -/
def lit (raw : String) : RegExpLit := RegExpLit.parse! raw

/-- `raw` matched against `haystack`: `yes`, `no`, or `UNSUPPORTED` when the
library does not read the literal. -/
def testOf (raw haystack : String) : String :=
  match (lit raw).test? haystack with
  | some true => "yes"
  | some false => "no"
  | none => "UNSUPPORTED"

/-- Every match of `raw` in `haystack`, separated by `|`. -/
def matchesOf (raw haystack : String) : String :=
  match (lit raw).extractAll? haystack with
  | some ms => String.intercalate "|" ms.toList
  | none => "UNSUPPORTED"

/-- `String.prototype.replace` with `raw`. -/
def replaceOf (raw haystack replacement : String) : String :=
  ((lit raw).replaceJS? haystack replacement).getD "UNSUPPORTED"

/-- The capture groups of the first match, separated by `|`; a group which
did not match is `-`. -/
def captureOf (raw haystack : String) : String :=
  match (lit raw).compiled? with
  | none => "UNSUPPORTED"
  | some c =>
      match c.capture haystack with
      | none => "NO MATCH"
      | some gs => String.intercalate "|" (gs.toList.map (·.getD "-"))

def patternCases : List (String × String × String) :=
  [ ("the pattern of the literal is read by the library",
      toString (lit "/a+b/").patternSupported, "true")
  , ("an escaped delimiter is a plain slash for the library",
      (lit "/a\\/b/").librarySource, "a/b")
  , ("and an escaped backslash before one is kept",
      (lit "/a\\\\/").librarySource, "a\\\\")
  , ("a literal whose pattern the library does not read is refused",
      toString (lit "/(?=a)b/").patternSupported, "false")
  , ("a character class, a repetition and an alternation",
      testOf "/^(ab|c[de]{2})$/" "cdd", "yes")
  , ("a Perl class",
      matchesOf "/\\d+/" "a12b345", "12|345")
  , ("an escaped delimiter matches a slash",
      testOf "/a\\/b/" "xa/by", "yes")
  ]

def flagCases : List (String × String × String) :=
  [ ("i case folds the pattern", testOf "/AbC/i" "xabcx", "yes")
  , ("and without it the case matters", testOf "/AbC/" "xabcx", "no")
  , ("s makes a dot match a line break", testOf "/a.c/s" "a\nc", "yes")
  , ("and without it it does not", testOf "/a.c/" "a\nc", "no")
  , ("^ and $ are the anchors of the whole subject", testOf "/^b/" "a\nb", "no")
  , ("d and u change nothing here", testOf "/a+/du" "xaay", "yes")
  , ("m is not modelled, so nothing is answered for it",
      testOf "/^b/m" "a\nb", "UNSUPPORTED")
  , ("and neither is y", testOf "/a/y" "a", "UNSUPPORTED")
  , ("g does not change a test", testOf "/a/g" "xax", "yes")
  , ("g replaces every match", replaceOf "/a/g" "a1a2" "X", "X1X2")
  , ("and without it only the first one", replaceOf "/a/" "a1a2" "X", "X1a2")
  ]

def matchCases : List (String × String × String) :=
  [ ("every match, left to right", matchesOf "/a+/" "a1aa2aaa3", "a|aa|aaa")
  , ("no match at all", matchesOf "/z/" "abc", "")
  , ("the capture groups of the first match, group 0 being the whole one",
      captureOf "/(a+)(b*)/" "xaaabb", "aaabb|aaa|bb")
  , ("a group which did not take part in the match",
      captureOf "/(a)|(z)/" "a", "a|a|-")
  , ("a subject with no match has no capture groups",
      captureOf "/(a)/" "zzz", "NO MATCH")
  , ("a literal the library does not read matches nothing",
      matchesOf "/(?<n>a)/" "a", "UNSUPPORTED")
  ]

def spec : Spec := do
  describe "RegExp patterns through lean-regex" do
    for (label, actual, expected) in patternCases do
      it label do
        shouldEqual actual expected

  describe "RegExp flags through lean-regex" do
    for (label, actual, expected) in flagCases do
      it label do
        shouldEqual actual expected

  describe "RegExp matching through lean-regex" do
    for (label, actual, expected) in matchCases do
      it label do
        shouldEqual actual expected

end LanguageJavascriptTests.RegExpEngine
