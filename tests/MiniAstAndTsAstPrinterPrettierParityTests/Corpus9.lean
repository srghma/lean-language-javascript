import Tests.Corpus8

/-!
# Samples of the corners of the language

Programs which exercise the parts of the syntax tree the other samples
leave out: the operators stacked on each other, the shapes of the numeric
literals, the head of a `for (;;)`, and so on.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A call of a method on an object. -/
def dotCallOn (obj : MiniExpr) (name : String) (args : List MiniExpr) : MiniExpr :=
  .call (.dot obj (nes name)) args

/-- The samples. -/
def samples9 : List Sample :=
  -- unary operators stacked on each other
  [ { name := "unary-stack"
      prog := ⟨[es (.unary .minus (.unary .minus (v "a"))),
                es (.unary .plus (.unary .plus (v "a"))),
                es (.unary .not (.unary .not (v "a"))),
                es (.unary .typeof (.unary .typeof (v "a"))),
                es (.unary .minus (.unary .preDecr (v "a"))),
                es (.unary .tilde (.unary .tilde (v "a"))),
                es (.binary (v "a") .minus (.unary .minus (v "b"))),
                es (.binary (v "a") .plus (.unary .plus (v "b"))),
                es (.postfix (v "a") .incr),
                es (.unary .delete (.dot (v "a") (nes "b")))]⟩ }
  -- nested ternaries
  , { name := "ternary-chain"
      prog := ⟨[st (constDecl (longName 0)
                  (.ternary (v (longName 1)) (num 1)
                    (.ternary (v (longName 2)) (num 2)
                      (.ternary (v (longName 3)) (num 3) (num 4)))))]⟩ }
  , { name := "ternary-nested-cond"
      prog := ⟨[es (.ternary (.ternary (v "a") (v "b") (v "c")) (v "d") (v "e"))]⟩ }
  , { name := "ternary-in-call"
      prog := ⟨[es (call (longName 0)
                  [.ternary (v (longName 1)) (v (longName 2)) (v (longName 3))])]⟩ }
  -- an arrow chain that has to break
  , { name := "arrow-chain-long"
      prog := ⟨[st (constDecl (longName 0)
                  (.arrow false [par (longName 1)]
                    (.expr (.arrow false [par (longName 2)]
                      (.expr (.arrow false [par (longName 3)]
                        (.expr (.binary (v (longName 1)) .plus (v (longName 2))))))))))]⟩ }
  -- a long chain of `+`
  , { name := "binary-plus-chain"
      prog := ⟨[st (constDecl "value"
                  (.binary (.binary (.binary (.binary (v (longName 0)) .plus (v (longName 1)))
                    .plus (v (longName 2))) .plus (v (longName 3))) .plus (v (longName 4))))]⟩ }
  -- mixed logical operators in an `if`
  , { name := "if-long-condition"
      prog := ⟨[st (.if_ (.binary (.binary (v (longName 0)) .and (v (longName 1))) .or
                    (.binary (v (longName 2)) .and (v (longName 3))))
                  (.block [.expr (v "a")]) none)]⟩ }
  -- empty things
  , { name := "empty-things"
      prog := ⟨[st (constDecl "a" (.object [])),
                st (constDecl "b" (.array [])),
                st (.funcDecl false false (nes "f") [] []),
                st (.classDecl [] (nes "C") none []),
                st (.block []),
                st .empty,
                es (.new (v "Foo") []),
                es (.call (.arrow false [] (.block [])) [])]⟩ }
  -- template literals
  , { name := "templates"
      prog := ⟨[es (.template none "a" [⟨v "b", "c"⟩, ⟨num 1, ""⟩]),
                es (.template none "" []),
                es (.template (some (v "tag")) "x" [⟨.binary (v "a") .plus (v "b"), "y"⟩]),
                st (constDecl "s" (.template none "start "
                  [⟨call (longName 0) [v (longName 1), v (longName 2)], " end"⟩]))]⟩ }
  -- decorators
  , { name := "decorators"
      prog := ⟨[st (.classDecl [v "dec"] (nes "C") none
                  [.method [v "bound"] false .normal (.ident (nes "m")) [] [],
                   .field [call "inject" [v "Service"]] true false (.ident (nes "x")) (some (num 1))])]⟩ }
  -- numeric literal shapes
  , { name := "numbers-edge"
      prog := ⟨[es (.array [.elem (.number (.decimal 1 21)), .elem (.number (.decimal 1 20)),
                  .elem (.number (.decimal 1 (-6))), .elem (.number (.decimal 1 (-7))),
                  .elem (.number (.radix .hexadecimal 0)), .elem (.number (.bigint .hexadecimal 255)),
                  .elem (.number (.decimal 5 (-1))), .elem (.number (.decimal 123 (-5))),
                  .elem (.number (.decimal 1234567890123456789 0))])]⟩ }
  -- member access off a literal
  , { name := "member-off-literal"
      prog := ⟨[es (.dot (num 1) (nes "toString")),
                es (.dot (.number (.decimal 15 (-1))) (nes "toFixed")),
                es (.dot (.string "s") (nes "length")),
                es (.dot (.object []) (nes "a")),
                es (.dot (.func false false none [] []) (nes "call")),
                es (.dot (.arrow false [] (.expr (num 1))) (nes "call")),
                es (.dot (.new (v "Foo") []) (nes "a")),
                es (.dot (.unary .minus (num 1)) (nes "a"))]⟩ }
  -- `in` inside the head of a `for`
  , { name := "for-head-in"
      prog := ⟨[st (.for_ (.expr (.binary (.string "a") .inOp (v "o"))) none none .empty),
                st (.for_ (.decl .let_ ⟨⟨p "x", some (.binary (.string "a") .inOp (v "o"))⟩, []⟩)
                  none none .empty),
                st (.for_ (.expr (call "f" [.binary (v "a") .inOp (v "b")])) none none .empty),
                st (.for_ (.expr (.array [.elem (.binary (v "a") .inOp (v "b"))])) none none .empty),
                st (.for_ (.expr (.binary (v "c") .plus (.binary (v "a") .inOp (v "b"))))
                  none none .empty),
                st (.for_ (.expr (.ternary (.binary (v "a") .inOp (v "b")) (num 1) (num 2)))
                  none none .empty),
                st (.for_ (.expr (.arrow false [] (.expr (.binary (v "a") .inOp (v "b")))))
                  none none .empty),
                st (.for_ (.expr (.dot (.binary (v "a") .inOp (v "b")) (nes "c")))
                  none none .empty),
                st (.for_ (.expr (.unary .typeof (.binary (v "a") .inOp (v "b"))))
                  none none .empty),
                st (.for_ .none (some (.binary (v "a") .inOp (v "b")))
                  (some (.binary (v "a") .inOp (v "b"))) .empty),
                st (.for_ (.expr (.func false false none [] [.expr (.binary (v "a") .inOp (v "b"))]))
                  none none .empty),
                st (.forIn (.decl .const (p "k")) (v "o") .empty)]⟩ }
  , { name := "for-head-plain"
      prog := ⟨[st (.for_ .none none none (.block [])),
                st (.for_ (.expr (.seq (v "a") (v "b"))) (some (v "c"))
                  (some (.seq (v "d") (v "e"))) .empty)]⟩ }
  -- mixed numeric arrays
  , { name := "array-numbers-signed"
      prog := ⟨[es (.array [.elem (.unary .minus (num 1)), .elem (num 2), .elem (num 3),
                  .elem (.unary .plus (num 4)), .elem (num 5), .elem (num 6), .elem (num 7),
                  .elem (num 8), .elem (num 9), .elem (num 10), .elem (num 11), .elem (num 12),
                  .elem (num 13), .elem (num 14), .elem (num 15), .elem (num 16),
                  .elem (num 17), .elem (num 18), .elem (num 19), .elem (num 20)]),
                es (.array [.elem (num 1), .hole, .elem (num 2), .elem (num 3), .elem (num 4),
                  .elem (num 5), .elem (num 6), .elem (num 7), .elem (num 8), .elem (num 9),
                  .elem (num 10), .elem (num 11), .elem (num 12), .elem (num 13),
                  .elem (num 14), .elem (num 15), .elem (num 16), .elem (num 17)])]⟩ }
  -- getters, setters and computed keys of an object literal
  , { name := "object-methods"
      prog := ⟨[st (constDecl "o" (.object
                  [.method .normal (.computed (v "k")) [par "a"] [],
                   .method .get (.string "s") [] [.return_ (some (num 1))],
                   .method .set (.number (JSNumber.ofNat 3)) [par "v"] [],
                   .keyValue (.number (.decimal 15 (-1))) (num 1),
                   .keyValue (.string "valid_name") (num 2),
                   .keyValue (.string "not a name") (num 3)]))]⟩ }
  -- an assignment whose right hand side is a long chain of `&&`
  , { name := "assign-logical-chain"
      prog := ⟨[st (constDecl (longName 0)
                  (.binary (.binary (v (longName 1)) .and (v (longName 2))) .and
                    (v (longName 3))))]⟩ }
  -- `await` and `yield` in argument and operand positions
  , { name := "await-yield-positions"
      prog := ⟨[st (.funcDecl true false (nes "f") []
                  [.expr (.binary (.await (v "a")) .plus (.await (v "b"))),
                   .expr (.dot (.await (v "a")) (nes "b")),
                   .expr (.unary .not (.await (v "a"))),
                   .return_ (some (.await (call "g" [])))]),
                st (.funcDecl false true (nes "g") []
                  [.expr (.yield none), .expr (.yieldFrom (v "a")),
                   .expr (.binary (.yield (some (v "a"))) .plus (num 1)),
                   .expr (.array [.elem (.yield (some (v "a")))])])]⟩ }
  -- long member chains and computed access
  , { name := "chain-computed"
      prog := ⟨[es (dotCallOn (.index (dotCallOn (v (longName 0)) (longName 1) [])
                    (.string "key")) (longName 2) [v "a"])]⟩ }
  -- a `switch` with a long discriminant and fall through cases
  , { name := "switch-shapes"
      prog := ⟨[st (.switch (v "a") []),
                st (.switch (.binary (v (longName 0)) .plus (v (longName 1)))
                  [.case (num 1) [], .case (num 2) [.block [.expr (v "a")]],
                   .default [.break_ none]])]⟩ }
  -- `try` with several `catch` clauses and a `finally`
  , { name := "try-shapes"
      prog := ⟨[st (.try_ [] (.finallyOnly [])),
                st (.try_ [.expr (v "a")]
                  (.catches ⟨⟨.array [.elem (p "a"), .rest (p "b")], none, []⟩, []⟩
                    (.some [.expr (v "b")])))]⟩ }
  -- a `with` statement and a labelled block
  , { name := "with-and-label"
      prog := ⟨[st (.with_ (v "o") (.block [.expr (v "a")])),
                st (.labelled (nes "lbl") (.block [.break_ (some (nes "lbl"))])),
                st (.labelled (nes "lbl2") .empty)]⟩ }
  -- long parameter lists and destructured parameters
  , { name := "params-long"
      prog := ⟨[st (.funcDecl false false (nes "f")
                  [par (longName 0), par (longName 1), par (longName 2), par (longName 3)]
                  [.return_ none]),
                st (.funcDecl true true (nes "g")
                  [.plain (.object [⟨.ident (nes (longName 0)), .ident (nes (longName 0))⟩,
                    ⟨.ident (nes (longName 1)), .ident (nes (longName 1))⟩] none)]
                  [])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
