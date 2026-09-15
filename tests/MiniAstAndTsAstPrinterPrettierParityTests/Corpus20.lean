import Tests.Corpus19

/-!
# Samples of the corners of the lexical syntax

The samples here exercise the spelling of what a syntax tree holds as the
characters it denotes: the quotes and the escapes of a string literal, the
escapes of the text of a template literal, the quotes a property name
keeps or loses, the shape of a numeric literal and of a regular expression
literal, and the places where a statement has to be parenthesised so that
its first token does not start a declaration.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A property whose name is written as a string literal. -/
def keyS (k : String) (e : MiniExpr) : MiniProperty := .keyValue (.string k) e

/-- The samples. -/
def samples20 : List Sample :=
  [ -- the quotes of a property name
    { name := "reserved-word-keys"
      prog := ⟨[es (.object [keyS "class" (num 1), keyS "default" (num 2),
                  keyS "if" (num 3), keyS "true" (num 4), keyS "null" (num 5),
                  keyS "undefined" (num 6), keyS "async" (num 7), keyS "let" (num 8)])]⟩ }
  , { name := "reserved-word-members"
      prog := ⟨[es (.dot (v "a") (nes "class")), es (.dot (v "a") (nes "default")),
                es (.dot (v "a") (nes "new")), es (.dot (v "a") (nes "function"))]⟩ }
  , { name := "keys-not-identifiers"
      prog := ⟨[es (.object [keyS "" (num 1), keyS "1a" (num 2), keyS "a b" (num 3),
                  keyS "$dollar" (num 4), keyS "_under" (num 5), keyS "é" (num 6),
                  keyS "a-b" (num 7)])]⟩ }
  , { name := "keys-unicode-identifier"
      prog := ⟨[es (.object [keyS "café" (num 1), keyS "日本語" (num 2),
                  keyS "π" (num 3), keyS "a\u200Cb" (num 4)])]⟩ }
  , { name := "identifier-unicode"
      prog := ⟨[st (constDecl "café" (num 1)), es (.dot (v "a") (nes "日本語"))]⟩ }
  , { name := "class-computed-and-string-keys"
      prog := ⟨[st (.classDecl [] (nes "A") none
                  [.method [] false .normal (.string "a-method") [] [],
                   .method [] false .normal (.number (JSNumber.ofNat 2)) [] [],
                   .field [] false false (.string "a field") (some (num 1))])]⟩ }
    -- the quotes and the escapes of a string literal
  , { name := "string-quote-choice"
      prog := ⟨[es (.string "one ' quote"), es (.string "one \" quote"),
                es (.string "two '' quotes and one \""),
                es (.string "one ' quote and two \"\""),
                es (.string "equal ' and \"")]⟩ }
  , { name := "string-control-characters"
      prog := ⟨[es (.string "bell \u0007 here"), es (.string "esc \u001B here"),
                es (.string "del \u007F here"), es (.string "nul \u0000 here"),
                es (.string "\u000B vertical tab"), es (.string "form \u000C feed")]⟩ }
  , { name := "string-backslashes"
      prog := ⟨[es (.string "a\\b"), es (.string "\\"), es (.string "\\\\"),
                es (.string "a\\'b"), es (.string "path\\to\\file")]⟩ }
  , { name := "string-escapes-and-unicode"
      prog := ⟨[es (.string "a\u0000b"), es (.string "\u001f"), es (.string "e\u0301"),
                es (.string "\u2028 and \u2029"), es (.string "emoji 😀 here")]⟩ }
    -- the escapes of the text of a template literal
  , { name := "template-with-backtick-and-dollar"
      prog := ⟨[es (.template none "a ` and $ and ${} here" []),
                es (.template none "" [⟨v "a", ""⟩]),
                es (.template none "" [⟨v "a", ""⟩, ⟨v "bb", ""⟩])]⟩ }
  , { name := "template-with-backslash"
      prog := ⟨[es (.template none "a \\ and \\n here" []),
                es (.template (some (v "tag")) "raw \\d+" []),
                es (.template none "" [⟨v "a", " ` "⟩, ⟨v "bb", "${"⟩])]⟩ }
  , { name := "template-with-carriage-return"
      prog := ⟨[es (.template none "first\r\nsecond" [])]⟩ }
  , { name := "template-multiline"
      prog := ⟨[st (constDecl "text" (.template none "first line\nsecond line" []))]⟩ }
  , { name := "template-tag-chain"
      prog := ⟨[es (.template (some (.call (.dot (v "styled") (nes "div")) [])) "color: red" [])]⟩ }
    -- regular expression literals
  , { name := "regex-flags"
      prog := ⟨[es (.regex ⟨nes "a+b",
        { hasIndices := true, global := true, ignoreCase := true, multiline := true,
          dotAll := true, unicode := true, sticky := true }⟩)]⟩ }
  , { name := "regex-slash-and-class"
      prog := ⟨[es (.regex ⟨nes "a\\/b", {}⟩), es (.regex ⟨nes "[/]", {}⟩),
                es (.regex ⟨nes "\\d{2,3}", {}⟩)]⟩ }
  , { name := "regex-divide-ambiguity"
      prog := ⟨[es (.binary (.regex ⟨nes "ab", {}⟩) .divide (v "a")),
                es (.binary (v "a") .divide (v "bb"))]⟩ }
    -- numeric literals
  , { name := "number-exponents"
      prog := ⟨[es (.number (.decimal 1 100)), es (.number (.decimal 123 (-25))),
                es (.number (.decimal 1 (-1))), es (.number (.decimal 1234567890123 0)),
                es (.number (.decimal 0 5)), es (.number (.radix .hexadecimal 0)),
                es (.number (.bigint .binary 6))]⟩ }
  , { name := "number-member-access"
      prog := ⟨[es (.dot (num 1) (nes "toString")),
                es (.dot (.number (.decimal 15 (-1))) (nes "toFixed")),
                es (.dot (.number (.radix .hexadecimal 255)) (nes "toString"))]⟩ }
  , { name := "negative-number-operands"
      prog := ⟨[es (.binary (num 1) .minus (.unary .minus (num 2))),
                es (.binary (num 1) .plus (.unary .plus (num 2))),
                es (.unary .minus (.unary .minus (num 1)))]⟩ }
    -- the first token of a statement
  , { name := "statement-starts-with-object"
      prog := ⟨[es (.object [kv "a" (num 1)]),
                es (.assignPattern (.object [⟨.ident (nes "a"), p "a"⟩] none) (v "bb"))]⟩ }
  , { name := "statement-starts-with-function"
      prog := ⟨[es (.call (.func false false none [] [.expr (v "a")]) []),
                es (.call (.classExpr [] none none []) []),
                es (.dot (.func false false none [] []) (nes "name"))]⟩ }
  , { name := "statement-starts-with-array"
      prog := ⟨[es (.dot (.array [.elem (num 1)]) (nes "length")),
                es (.assignPattern (.array [.elem (p "a")]) (v "xs"))]⟩ }
  , { name := "statement-starts-with-let"
      prog := ⟨[es (.index (v "let") (num 0)), es (.dot (v "let") (nes "x"))]⟩ }
  , { name := "dangling-else"
      prog := ⟨[st (.if_ (v "a") (.if_ (v "bb") (.expr (call "first" [])) none)
                  (some (.expr (call "second" []))))]⟩ }
  , { name := "empty-statement-bodies"
      prog := ⟨[st (.if_ (v "a") .empty (some .empty)),
                st (.while_ (v "a") .empty), st (.labelled (nes "l") .empty)]⟩ }
    -- parenthesisation the precedence calls for
  , { name := "coalesce-mixed"
      prog := ⟨[es (.binary (.binary (v "a") .coalesce (v "bb")) .or (v "value")),
                es (.binary (v "a") .and (.binary (v "bb") .coalesce (v "value")))]⟩ }
  , { name := "arrow-in-conditional"
      prog := ⟨[es (.ternary (v "a") (.arrow false [par "x"] (.expr (v "x")))
                  (.arrow false [] (.expr .null)))]⟩ }
  , { name := "assign-in-condition"
      prog := ⟨[st (.if_ (.assign (v "a") .assign (call "next" [])) (.block []) none),
                st (.while_ (.assign (v "a") .assign (call "next" [])) (.block []))]⟩ }
  , { name := "await-of-ternary"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.expr (.await (.ternary (v "a") (v "bb") (v "value"))),
                   .expr (.await (.binary (v "a") .plus (v "bb"))),
                   .return_ (some (.unary .minus (.await (v "a"))))])]⟩ }
  , { name := "new-of-call-result"
      prog := ⟨[es (.new (.call (.dot (v "a") (nes "getClass")) []) []),
                es (.call (.new (v "Foo") []) []),
                es (.new (.ternary (v "a") (v "B") (v "C")) [])]⟩ }
  , { name := "typeof-of-typeof"
      prog := ⟨[es (.unary .typeof (.unary .typeof (v "a"))),
                es (.unary .not (.unary .delete (.dot (v "a") (nes "bb"))))]⟩ }
  , { name := "sequence-in-index"
      prog := ⟨[es (.index (v "a") (.seq (v "bb") (v "value"))),
                es (.array [.elem (.seq (v "a") (v "bb"))])]⟩ }
  , { name := "object-in-arrow-body-nested"
      prog := ⟨[es (.arrow false [] (.expr (.arrow false [] (.expr (.object [kv "a" (num 1)])))))]⟩ }
    -- functions of unusual parameters
  , { name := "generator-and-async-functions"
      prog := ⟨[st (.funcDecl true true (nes "both") [] []),
                es (.func true true none [] []),
                es (.func true false (some (nes "named")) [] [])]⟩ }
  , { name := "param-defaults-and-rest"
      prog := ⟨[st (.funcDecl false false (nes "f")
                  [.plain (.withDefault (p "a") (num 1)),
                   .plain (.object [⟨.ident (nes "bb"), .withDefault (p "bb") (num 2)⟩]
                     (some (p "others"))),
                   .rest (p "rest")] [])]⟩ }
  , { name := "getter-with-long-body"
      prog := ⟨[st (.classDecl [] (nes "A") none
                  [.method [] false .get (.ident (nes (longName 0))) []
                    [.return_ (some (.binary (v (longName 1)) .plus (v (longName 2))))]])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
