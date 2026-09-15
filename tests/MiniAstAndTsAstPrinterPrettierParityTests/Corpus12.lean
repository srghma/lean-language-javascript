import Tests.Corpus11

/-!
# Samples of the `with` statement and of the decorators of an exported class

The object of a `with` statement stands between parentheses, as the
condition of a `while` does, but prettier does not lay it out as a
condition: a binary expression written there is grouped and its operands
after the first are indented, exactly as they are anywhere else.  The
samples here exercise that at several widths.

The decorators of a class which is exported stand each on a line of its
own, below the `export` keyword.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A `with` statement whose body is a single call. -/
def withStmt (obj : MiniExpr) : MiniStatement :=
  .with_ obj (.block [.expr (call "handle" [v "item"])])

/-- A class expression of one decorator and of one method. -/
def loggedClass : MiniExpr :=
  .classExpr [v "logged"] none none [.method [] false .normal (.ident (nes "a")) [] []]

/-- A class expression of two decorators, of a name and of a parent. -/
def loggedNamedClass : MiniExpr :=
  .classExpr [v "logged", call "inject" [v "service"]] (some (nes "TheClass"))
    (some (v "Base")) []

/-- The samples. -/
def samples12 : List Sample :=
  [ { name := "with-short"
      prog := ⟨[st (withStmt (v "theConfigurationObject"))]⟩ }
  , { name := "with-non-block-body"
      prog := ⟨[st (.with_ (v "theConfigurationObject") (.expr (call "handle" [v "item"])))]⟩ }
  , { name := "with-empty-body"
      prog := ⟨[st (.with_ (v "theConfigurationObject") .empty)]⟩ }
  -- the operands after the first of a chain that breaks are indented,
  -- which the condition of a `while` does not do
  , { name := "with-logical-chain"
      prog := ⟨[st (withStmt (.binary (.binary (v (longName 0)) .or (v (longName 1)))
                  .or (v (longName 2))))]⟩ }
  , { name := "while-logical-chain"
      prog := ⟨[st (.while_ (.binary (.binary (v (longName 0)) .or (v (longName 1)))
                  .or (v (longName 2))) (.block [.expr (call "handle" [v "item"])]))]⟩ }
  -- a chain which fits once it stands on a line of its own is kept there,
  -- since it is a group of its own
  , { name := "with-chain-fits-indented"
      prog := ⟨[st (.block [.block [withStmt
                  (.binary (v "theConfigurationObject") .and
                    (.binary (.null) .or (v "theVeryLongNameForAVariableHere")))]])]⟩ }
  , { name := "with-mixed-operators"
      prog := ⟨[st (withStmt (.binary
                  (.binary (v (longName 0)) .and (v (longName 1))) .or
                  (.binary (v (longName 2)) .times (v "g"))))]⟩ }
  -- `with (!(a || b))` is kept on the line of the keyword, as a condition is
  , { name := "with-negated-logical"
      prog := ⟨[st (withStmt (.unary .not (.binary (v (longName 0)) .or (v (longName 1)))))]⟩ }
  , { name := "with-ternary"
      prog := ⟨[st (withStmt (.ternary (v (longName 0)) (v (longName 1)) (v (longName 2))))]⟩ }
  , { name := "with-sequence"
      prog := ⟨[st (withStmt (.seq (v "a") (v "bb")))]⟩ }
  , { name := "with-call"
      prog := ⟨[st (withStmt (call (longName 0) [v (longName 1), v (longName 2)]))]⟩ }
  , { name := "with-object"
      prog := ⟨[st (withStmt (.object [.keyValue (.ident (nes (longName 0))) (num 1),
                  .keyValue (.ident (nes (longName 1))) (num 2),
                  .keyValue (.ident (nes (longName 2))) (num 3)]))]⟩ }
  , { name := "with-assignment"
      prog := ⟨[st (withStmt (.assign (v "item") .assign (v "theConfigurationObject")))]⟩ }
  , { name := "with-nested"
      prog := ⟨[st (.with_ (v "a") (.with_ (v "bb") (.block [.expr (v "item")])))]⟩ }
  -- the decorators of an exported class
  , { name := "export-default-decorated"
      prog := ⟨[.exportDecl (.defaultExpr loggedClass)]⟩ }
  , { name := "export-default-decorated-named"
      prog := ⟨[.exportDecl (.defaultExpr loggedNamedClass)]⟩ }
  , { name := "export-default-plain-class"
      prog := ⟨[.exportDecl (.defaultExpr (.classExpr [] none none []))]⟩ }
  , { name := "export-decorated-declaration"
      prog := ⟨[.exportDecl (.decl (.classDecl [v "logged"] (nes "TheClass") none []))]⟩ }
  , { name := "export-plain-declaration"
      prog := ⟨[.exportDecl (.decl (.classDecl [] (nes "TheClass") none []))]⟩ }
  , { name := "decorated-class-statement"
      prog := ⟨[st (.classDecl [v "logged"] (nes "TheClass") none [])]⟩ }
  , { name := "decorated-class-in-const"
      prog := ⟨[st (constDecl "x" loggedClass)]⟩ }
  , { name := "decorated-class-argument"
      prog := ⟨[es (.call (v "f") [loggedClass])]⟩ }
  , { name := "decorated-class-member"
      prog := ⟨[es (.dot loggedClass (nes "x"))]⟩ }
  , { name := "decorated-class-callee"
      prog := ⟨[es (.call loggedClass [])]⟩ }
  , { name := "decorated-class-expression-statement"
      prog := ⟨[es loggedClass]⟩ }
  , { name := "decorated-class-return"
      prog := ⟨[st (.funcDecl false false (nes "f") [] [.return_ (some loggedClass)])]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
