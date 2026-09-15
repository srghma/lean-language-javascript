import Tests.Corpus12

/-!
# Samples of property names, of literals and of the width of a character

Prettier writes a quoted property name without its quotes when it is an
ECMAScript 5 `IdentifierName`, whose characters are those of the Unicode
properties `ID_Start` and `ID_Continue`, and it writes a quoted name that
is a plain decimal number as that number.  It also counts the columns a
line takes the way a terminal does: an East Asian wide character, and a
pictograph, take two of them.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- An object literal of one property, whose key is a quoted name. -/
def stringKeyObj (key : String) : MiniExpr := .object [.keyValue (.string key) (num 1)]

/-- An object literal of one property, whose key is a numeric literal. -/
def numberKeyObj (n : JSNumber) : MiniExpr := .object [.keyValue (.number n) (num 1)]

/-- A string of `n` copies of `s`. -/
def repeatStr (s : String) : Nat → String
  | 0 => ""
  | n + 1 => s ++ repeatStr s n

/-- A call of `f` on one string argument. -/
def callOfString (f : String) (s : String) : MiniExpr := .call (v f) [.string s]

/-- The samples. -/
def samples13 : List Sample :=
  -- the quotes of a name that is an identifier are dropped
  [ { name := "key-identifier", prog := ⟨[es (stringKeyObj "ok")]⟩ }
  , { name := "key-dollar", prog := ⟨[es (stringKeyObj "$a_1")]⟩ }
  , { name := "key-underscore", prog := ⟨[es (stringKeyObj "_a_b_")]⟩ }
  , { name := "key-dashed", prog := ⟨[es (stringKeyObj "a-b")]⟩ }
  , { name := "key-empty", prog := ⟨[es (stringKeyObj "")]⟩ }
  , { name := "key-space", prog := ⟨[es (stringKeyObj "a b")]⟩ }
  , { name := "key-keyword", prog := ⟨[es (stringKeyObj "class")]⟩ }
  , { name := "key-proto", prog := ⟨[es (stringKeyObj "__proto__")]⟩ }
  -- and so are the quotes of a name that is a plain decimal number
  , { name := "key-digits", prog := ⟨[es (stringKeyObj "1")]⟩ }
  , { name := "key-digits-zero", prog := ⟨[es (stringKeyObj "0")]⟩ }
  , { name := "key-leading-zero", prog := ⟨[es (stringKeyObj "01")]⟩ }
  , { name := "key-decimal", prog := ⟨[es (stringKeyObj "1.5")]⟩ }
  , { name := "key-hex", prog := ⟨[es (stringKeyObj "0x10")]⟩ }
  , { name := "key-big", prog := ⟨[es (stringKeyObj "999999999999999999999")]⟩ }
  -- a name of characters outside ASCII is an identifier exactly when the
  -- Unicode properties say it is
  , { name := "key-latin-accent", prog := ⟨[es (stringKeyObj "café")]⟩ }
  , { name := "key-ordinal", prog := ⟨[es (stringKeyObj "ª")]⟩ }
  , { name := "key-micro", prog := ⟨[es (stringKeyObj "µ")]⟩ }
  , { name := "key-hebrew", prog := ⟨[es (stringKeyObj "א")]⟩ }
  , { name := "key-han", prog := ⟨[es (stringKeyObj "中")]⟩ }
  , { name := "key-arabic-digit", prog := ⟨[es (stringKeyObj "a٣")]⟩ }
  , { name := "key-undertie", prog := ⟨[es (stringKeyObj "a‿b")]⟩ }
  , { name := "key-snowman", prog := ⟨[es (stringKeyObj "☃")]⟩ }
  , { name := "key-vulgar-fraction", prog := ⟨[es (stringKeyObj "½")]⟩ }
  , { name := "key-inverted-bang", prog := ⟨[es (stringKeyObj "¡a")]⟩ }
  , { name := "key-middle-dot", prog := ⟨[es (stringKeyObj "a·b")]⟩ }
  , { name := "key-emoji", prog := ⟨[es (stringKeyObj "😀")]⟩ }
  , { name := "key-mixed"
      prog := ⟨[es (.object [.keyValue (.string "ok") (num 1),
                  .keyValue (.string "a-b") (num 2)])]⟩ }
  , { name := "key-number", prog := ⟨[es (numberKeyObj (JSNumber.ofNat 1))]⟩ }
  , { name := "key-number-decimal", prog := ⟨[es (numberKeyObj (.decimal 15 (-1)))]⟩ }
  , { name := "key-number-hex", prog := ⟨[es (numberKeyObj (.radix .hexadecimal 255))]⟩ }
  , { name := "key-number-bigint", prog := ⟨[es (numberKeyObj (.bigint .decimal 12))]⟩ }
  , { name := "key-computed-string"
      prog := ⟨[es (.object [.keyValue (.computed (.string "ok")) (num 1)])]⟩ }
  , { name := "class-key-string"
      prog := ⟨[st (.classDecl [] (nes "A") none
                  [.field [] false false (.string "ok") (some (num 1)),
                   .method [] false .normal (.string "a-b") [] []])]⟩ }
  -- the literals themselves
  , { name := "string-quotes-double", prog := ⟨[es (.string "say \"hi\"")]⟩ }
  , { name := "string-quotes-single", prog := ⟨[es (.string "it's")]⟩ }
  , { name := "string-quotes-both", prog := ⟨[es (.string "it's \"hi\"")]⟩ }
  , { name := "string-backslash", prog := ⟨[es (.string "a\\b")]⟩ }
  , { name := "string-controls", prog := ⟨[es (.string "a\u0001b\u007fc")]⟩ }
  , { name := "string-unicode", prog := ⟨[es (.string "héllo ☃")]⟩ }
  , { name := "directive", prog := ⟨[es (.string "use strict"), es (v "a")]⟩ }
  -- a wide character takes two columns, so these lines just fit or just
  -- overflow, though they hold the same number of characters
  , { name := "wide-string-35", prog := ⟨[es (callOfString "f" (repeatStr "あ" 35))]⟩ }
  , { name := "wide-string-36", prog := ⟨[es (callOfString "f" (repeatStr "あ" 36))]⟩ }
  , { name := "wide-string-37", prog := ⟨[es (callOfString "f" (repeatStr "あ" 37))]⟩ }
  , { name := "narrow-string-75", prog := ⟨[es (callOfString "f" (repeatStr "a" 75))]⟩ }
  , { name := "narrow-string-76", prog := ⟨[es (callOfString "f" (repeatStr "a" 76))]⟩ }
  , { name := "narrow-string-77", prog := ⟨[es (callOfString "f" (repeatStr "a" 77))]⟩ }
  , { name := "emoji-string-36", prog := ⟨[es (callOfString "f" (repeatStr "😀" 36))]⟩ }
  , { name := "emoji-string-38", prog := ⟨[es (callOfString "f" (repeatStr "😀" 38))]⟩ }
  , { name := "combining-string", prog := ⟨[es (callOfString "f" (repeatStr "é" 74))]⟩ }
  , { name := "wide-key"
      prog := ⟨[st (constDecl (longName 0)
                  (.object [.keyValue (.string (repeatStr "あ" 20))
                    (.string (repeatStr "b" 40))]))]⟩ }
  , { name := "wide-ident-key"
      prog := ⟨[st (constDecl (longName 0)
                  (.object [.keyValue (.ident (nes (repeatStr "あ" 20)))
                    (.string (repeatStr "b" 40))]))]⟩ }
  -- the pictographs prettier counts as wide, and one it does not
  , { name := "watch-string-37", prog := ⟨[es (callOfString "f" (repeatStr "⌚" 37))]⟩ }
  , { name := "watch-string-38", prog := ⟨[es (callOfString "f" (repeatStr "⌚" 38))]⟩ }
  , { name := "umbrella-string-38", prog := ⟨[es (callOfString "f" (repeatStr "☔" 38))]⟩ }
  , { name := "pointing-string-38", prog := ⟨[es (callOfString "f" (repeatStr "☝" 38))]⟩ }
  , { name := "narrow-pictograph-74"
      prog := ⟨[es (callOfString "f" (repeatStr "🫽" 74))]⟩ }
  , { name := "narrow-pictograph-75"
      prog := ⟨[es (callOfString "f" (repeatStr "🫽" 75))]⟩ }
  , { name := "wide-template"
      prog := ⟨[es (.template none (repeatStr "あ" 36) [⟨v "a", ""⟩])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
