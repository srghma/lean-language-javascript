import Tests.Corpus23

/-!
# Samples of the corners of the syntax tree

The samples of this file walk over the parts of the language the earlier
ones touch only in passing: the parentheses of `await`, of `yield` and of
an optional chain, the shapes a numeric literal and a property name may
take, the members of a class which have a private name, and the places
where a sequence expression, a spread or a label may stand.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples. -/
def samples24 : List Sample :=
  [ -- mixing `??` with `||` and `&&`, which needs parentheses
    { name := "corner-coalesce-mix"
      prog := ⟨[es (.binary (.binary (v "a") .coalesce (v "bb")) .or (v "f")),
                es (.binary (v "a") .and (.binary (v "bb") .coalesce (v "f")))]⟩ }
  , -- repeated prefix operators
    { name := "corner-unary-repeat"
      prog := ⟨[es (.unary .not (.unary .not (v "a"))),
                es (.unary .minus (.unary .minus (v "a"))),
                es (.unary .plus (.unary .plus (v "a"))),
                es (.unary .minus (.unary .preDecr (v "a"))),
                es (.unary .typeof (.unary .typeof (v "a"))),
                es (.binary (.unary .minus (v "a")) .minus (.unary .minus (v "bb")))]⟩ }
  , -- numbers of many shapes
    { name := "corner-numbers"
      prog := ⟨[es (.array [.elem (.number (.decimal 5 (-1))),
                  .elem (.number (.decimal 1 100)),
                  .elem (.number (.decimal 0 0)),
                  .elem (.number (.decimal 123456789012345678901234567890 0)),
                  .elem (.number (.radix .hexadecimal 3735928559)),
                  .elem (.number (.bigint .binary 5)),
                  .elem (.number (.decimal 1 (-21))),
                  .elem (.number (.decimal 25 (-2))),
                  .elem (.number (.decimal 1 6)),
                  .elem (.number (.decimal 1 (-6)))])]⟩ }
  , -- strings with characters that have to be escaped
    { name := "corner-strings"
      prog := ⟨[es (.array [.elem (.string "\u0001"),
                  .elem (.string "del\u007f"),
                  .elem (.string "e\u00e9\u4e2d"),
                  .elem (.string "quote\"and'both")])]⟩ }
  , -- sparse arrays
    { name := "corner-holes"
      prog := ⟨[es (.array [.hole]),
                es (.array [.hole, .hole]),
                es (.array [.elem (num 1), .hole]),
                es (.array [.hole, .elem (num 1)])]⟩ }
  , -- object keys of unusual shapes
    { name := "corner-keys"
      prog := ⟨[es (.object [.keyValue (.number (.decimal 1 3)) (num 1),
                  .keyValue (.number (.decimal 5 (-1))) (num 2),
                  .keyValue (.string "1a") (num 3),
                  .keyValue (.string "0") (num 4),
                  .keyValue (.string "00") (num 5),
                  .keyValue (.string "class") (num 6)])]⟩ }
  , -- `new` of a callee which itself is a call, and of a chain
    { name := "corner-new"
      prog := ⟨[es (.new (.call (v "f") []) []),
                es (.new (.dot (.call (v "f") []) (nes "g")) [num 1]),
                es (.new (.chain (v "a") ⟨.dot true (nes "bb"), []⟩) []),
                es (.dot (.new (v "f") []) (nes "value"))]⟩ }
  , -- `for` heads of unusual shapes
    { name := "corner-for"
      prog := ⟨[st (.for_ .none none none (.block [])),
                st (.for_ .none none (some (.seq (.postfix (v "a") .incr)
                    (.postfix (v "bb") .decr))) (.block [])),
                st (.for_ (.expr (.seq (.assign (v "a") .assign (num 0))
                    (.assign (v "bb") .assign (num 1)))) (some (v "a")) none .empty)]⟩ }
  , -- `delete` and `void` of a sequence, and a bare `return`
    { name := "corner-seq"
      prog := ⟨[es (.unary .delete (.seq (v "a") (v "bb"))),
                es (.unary .void (.seq (v "a") (v "bb"))),
                st (.return_ none)]⟩ }
  , -- a long chain of curried arrow functions
    { name := "corner-arrow-chain"
      prog := ⟨[st (constDecl (longName 0)
                  (.arrow false [par (longName 1)]
                    (.expr (.arrow false [par (longName 2)]
                      (.expr (.arrow false [par (longName 3)]
                        (.expr (call "computeTheValue" [v (longName 1), v (longName 2)]))))))))]⟩ }
  , -- a long member chain with computed accesses
    { name := "corner-member-computed"
      prog := ⟨[es (.call (.dot (.index (.call (.dot (v "theCollection") (nes "filter"))
                    [v "handler"]) (num 0)) (nes "theRatherLongPropertyName"))
                  [v "aLongIdentifierNameNumberZero"])]⟩ }
  , -- an assignment whose right hand side is a long binary expression
    { name := "corner-assign-binary"
      prog := ⟨[st (constDecl (longName 0)
                  (.binary (.binary (v (longName 1)) .plus (v (longName 2))) .plus
                    (v (longName 3))))]⟩ }
  , -- a `do ... while` whose body is not a block, and a labelled `;`
    { name := "corner-do-while"
      prog := ⟨[st (.doWhile (.expr (.call (v "f") [])) (v "a")),
                st (.doWhile .empty (v "a")),
                st (.labelled (nes "lbl") .empty)]⟩ }
  , -- a class whose heritage is a long call
    { name := "corner-class-heritage"
      prog := ⟨[st (.classDecl [] (nes "TheClassWithAVeryLongNameIndeed")
                  (some (.call (v "theVeryLongNameForAVariableHere")
                    [v "aLongIdentifierNameNumberOne"]))
                  [.method [] false .normal (.ident (nes "m")) [] []])]⟩ }
  , -- template literals in a member chain and as a tag of a chain
    { name := "corner-template-chain"
      prog := ⟨[es (.dot (.template none "text" [⟨v "a", ""⟩]) (nes "length")),
                es (.template (some (.dot (v "theCollection") (nes "tag"))) "x" [⟨v "a", "y"⟩])]⟩ }
  , -- `await` of a conditional, of a binary, and of another `await`
    { name := "corner-await"
      prog := ⟨[st (.funcDecl true false (nes "helper") []
                  [.expr (.await (.ternary (v "a") (v "bb") (v "f"))),
                   .expr (.binary (.await (v "a")) .plus (v "bb")),
                   .expr (.unary .not (.await (v "a"))),
                   .expr (.await (.await (v "a")))])]⟩ }
  , -- a `yield` in the places which need parentheses
    { name := "corner-yield"
      prog := ⟨[st (.funcDecl false true (nes "helper") []
                  [.expr (.binary (.yield (some (v "a"))) .plus (v "bb")),
                   .expr (.ternary (.yield none) (v "a") (v "bb")),
                   .expr (.call (v "f") [.yield (some (v "a"))])])]⟩ }
  , -- an arrow whose body needs parentheses
    { name := "corner-arrow-body"
      prog := ⟨[es (.arrow false [] (.expr (.assign (v "a") .assign (num 1)))),
                es (.arrow false [] (.expr (.arrow false [] (.expr (.object []))))),
                es (.arrow false [par "a"] (.expr (.ternary (v "a") (v "bb") (v "f"))))]⟩ }
  , -- a class with decorators on the class itself
    { name := "corner-decorators"
      prog := ⟨[st (.classDecl [v "logged", .call (v "inject") [.string "svc"]]
                  (nes "TheClass") none
                  [.field [v "observable"] false false (.ident (nes "x")) (some (num 1))])]⟩ }
  , -- a getter and a setter with computed keys
    { name := "corner-accessors"
      prog := ⟨[es (.object [.method .get (.computed (.string "key")) [] [],
                  .method .set (.computed (v "k")) [par "value"] [],
                  .method .generator (.computed (v "k")) [] []])]⟩ }
  , -- parenthesised optional chains
    { name := "corner-chain-parens"
      prog := ⟨[es (.dot (.chain (v "a") ⟨.dot true (nes "bb"), []⟩) (nes "f")),
                es (.new (.chain (v "a") ⟨.dot true (nes "bb"), []⟩) [num 1]),
                es (.chain (.chain (v "a") ⟨.dot true (nes "bb"), []⟩)
                    ⟨.call false [], []⟩)]⟩ }
  , -- a long optional chain
    { name := "corner-chain-long"
      prog := ⟨[st (constDecl (longName 0)
                  (.chain (v "theConfigurationObject")
                    ⟨.dot true (nes "theRatherLongPropertyName"),
                     [.call false [v "handler"], .dot true (nes "theHandlerName"),
                      .call true [v "item"]]⟩))]⟩ }
  , -- chains of conditional expressions
    { name := "corner-ternary-chain"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (v "aLongIdentifierNameNumberOne") (v "theCollection")
                    (.ternary (v "aLongIdentifierNameNumberTwo") (v "computeTheValue")
                      (.ternary (v "theHandlerName") (num 1) (num 2)))))]⟩ }
  , -- assignment chains
    { name := "corner-assign-chain"
      prog := ⟨[es (.assign (v "aLongIdentifierNameNumberZero") .assign
                  (.assign (v "aLongIdentifierNameNumberOne") .assign
                    (.assign (v "aLongIdentifierNameNumberTwo") .assign
                      (call "computeTheValue" [v "item"]))))]⟩ }
  , -- `export default` of a function, and an exported class
    { name := "corner-export-default"
      prog := ⟨[.exportDecl (.defaultExpr (.func false false none [] [])),
                .exportDecl (.decl (.classDecl [] (nes "TheClass") none []))]⟩ }
  , -- a long list of named imports and exports
    { name := "corner-import-long"
      prog := ⟨[.importDecl (.clause (MiniImportClause.mk! none none
                  (some [⟨nes "aLongIdentifierNameNumberZero", none⟩,
                         ⟨nes "aLongIdentifierNameNumberOne", none⟩,
                         ⟨nes "aLongIdentifierNameNumberTwo", some (nes "theShortOne")⟩])
                  (nes "a-module-with-a-long-name"))),
                .exportDecl (.locals [⟨nes "aLongIdentifierNameNumberZero", none⟩,
                         ⟨nes "aLongIdentifierNameNumberOne", none⟩,
                         ⟨nes "aLongIdentifierNameNumberTwo", some (nes "theShortOne")⟩])]⟩ }
  , -- private members of a class
    { name := "corner-private"
      prog := ⟨[st (.classDecl [] (nes "TheClass") none
                  [.field [] false false (.private_ (nes "x")) none,
                   .method [] false .normal (.private_ (nes "m")) [] [],
                   .method [] true .normal (.private_ (nes "n")) [] [],
                   .method [] false .get (.private_ (nes "y")) [] [],
                   .method [] false .set (.private_ (nes "y")) [par "value"] [],
                   .method [] false .generator (.private_ (nes "g")) [] []])]⟩ }
  , -- an empty object literal in the places where it matters
    { name := "corner-empty-object"
      prog := ⟨[es (.call (.dot (.object []) (nes "toString")) []),
                es (.arrow false [] (.expr (.object []))),
                es (.call (.arrow false [] (.block [])) []),
                es (.call (.func false false none [] []) [])]⟩ }
  , -- `let` used as a name
    { name := "corner-let-name"
      prog := ⟨[es (.index (v "let") (num 0)),
                es (.dot (v "let") (nes "value")),
                st (.decl .var ⟨⟨p "let", some (num 1)⟩, []⟩)]⟩ }
  , -- a `switch` whose discriminant and tests are long
    { name := "corner-switch-long"
      prog := ⟨[st (.switch (.binary (v "theVeryLongNameForAVariableHere") .plus
                    (v "aLongIdentifierNameNumberOne"))
                  [.case (.binary (v "aVeryVeryLongIdentifierNameHere") .plus
                      (v "theIteratorOfTheList")) [.break_ none]])]⟩ }
  , -- a `throw` and a `return` of a long logical expression
    { name := "corner-throw-long"
      prog := ⟨[st (.throw (.binary (v "aVeryVeryLongIdentifierNameHere") .or
                    (.binary (v "theIteratorOfTheList") .or (v "theHandlerName")))),
                st (.funcDecl false false (nes "helper") []
                  [.return_ (some (.binary (v "aVeryVeryLongIdentifierNameHere") .and
                    (.binary (v "theIteratorOfTheList") .and (v "theHandlerName"))))])]⟩ }
  , -- an arrow whose single parameter destructures
    { name := "corner-arrow-destructure"
      prog := ⟨[es (.arrow false [.plain (.object [⟨.ident (nes "aLongIdentifierNameNumberZero"),
                      .ident (nes "aLongIdentifierNameNumberZero")⟩,
                    ⟨.ident (nes "aLongIdentifierNameNumberOne"),
                      .ident (nes "aLongIdentifierNameNumberOne")⟩] none)]
                  (.expr (num 1)))]⟩ }
  , -- a template literal with a long substitution
    { name := "corner-template-long"
      prog := ⟨[st (constDecl "value"
                  (.template none "the text before "
                    [⟨.binary (v "aVeryVeryLongIdentifierNameHere") .plus
                        (v "theIteratorOfTheList"), " and after"⟩]))]⟩ }
  , -- a `new` of long arguments
    { name := "corner-new-long"
      prog := ⟨[es (.new (.dot (v "theConfigurationObject") (nes "TheBuilder"))
                  [v "aVeryVeryLongIdentifierNameHere", v "theIteratorOfTheList",
                   v "theHandlerName"])]⟩ }
  , -- a property named `__proto__`
    { name := "corner-proto"
      prog := ⟨[es (.object [.keyValue (.string "__proto__") .null]),
                es (.object [.keyValue (.ident (nes "__proto__")) .null,
                  .shorthand (nes "undefined")])]⟩ }
  , -- a class whose heritage needs parentheses
    { name := "corner-heritage-ternary"
      prog := ⟨[st (.classDecl [] (nes "TheClass")
                  (some (.ternary (v "a") (v "bb") (v "f"))) []),
                st (.classDecl [] (nes "TheOtherClass")
                  (some (.await (v "a"))) [])]⟩ }
  , -- a call whose callee needs parentheses
    { name := "corner-callee-parens"
      prog := ⟨[es (.call (.arrow false [] (.expr (num 1))) []),
                es (.call (.ternary (v "a") (v "f") (v "g")) []),
                es (.call (.assign (v "a") .assign (v "f")) []),
                es (.call (.seq (v "a") (v "f")) [])]⟩ }
  , -- a spread of several shapes
    { name := "corner-spread"
      prog := ⟨[es (.call (v "f") [.spread (.ternary (v "a") (v "bb") (v "f"))]),
                es (.array [.elem (.spread (.assign (v "a") .assign (v "bb")))]),
                es (.object [.spread (.binary (v "a") .or (v "bb"))])]⟩ }
  , -- a sequence expression as a statement, long enough to break
    { name := "corner-seq-long"
      prog := ⟨[es (.seq (call "computeTheValue" [v "aLongIdentifierNameNumberZero"])
                  (call "computeTheValue" [v "aLongIdentifierNameNumberOne"]))]⟩ }
  , -- labelled statements around loops and blocks
    { name := "corner-labels"
      prog := ⟨[st (.labelled (nes "outer") (.labelled (nes "inner")
                  (.while_ (v "a") (.block [.break_ (some (nes "outer"))])))),
                st (.labelled (nes "lbl") (.block []))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
