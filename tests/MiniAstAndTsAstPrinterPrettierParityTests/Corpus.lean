import MiniAST

/-!
# A corpus of sample programs

The programs in this file exercise the printer over the whole `MiniAST`
syntax tree.  They are used by the prettier conformance tests.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- A non-empty string, for building samples. -/
def nes (x : String) : NEString := NEString.ofString! x

/-- An identifier expression. -/
def v (x : String) : MiniExpr := .ident (nes x)

/-- An identifier pattern. -/
def p (x : String) : MiniPattern := .ident (nes x)

/-- A plain parameter. -/
def par (x : String) : MiniParam := .plain (p x)

/-- A numeric literal. -/
def num (k : Nat) : MiniExpr := .number (JSNumber.ofNat k)

/-- A statement item of a program. -/
def st (x : MiniStatement) : MiniModuleItem := .stmt x

/-- An expression statement. -/
def es (e : MiniExpr) : MiniModuleItem := .stmt (.expr e)

/-- A `const x = e;` statement. -/
def constDecl (x : String) (e : MiniExpr) : MiniStatement :=
  .decl .const ⟨⟨p x, some e⟩, []⟩

/-- A call of `f` on `args`. -/
def call (f : String) (args : List MiniExpr) : MiniExpr := .call (v f) args

/-- A long identifier, to force lines to break. -/
def longName (k : Nat) : String :=
  match k with
  | 0 => "aLongIdentifierNameNumberZero"
  | 1 => "aLongIdentifierNameNumberOne"
  | 2 => "aLongIdentifierNameNumberTwo"
  | 3 => "aLongIdentifierNameNumberThree"
  | _ => "aLongIdentifierNameNumberFour"

/-- One named sample. -/
structure Sample where
  /-- The name of the sample. -/
  name : String
  /-- The program. -/
  prog : MiniProgram
  /-- The interpreter directive the file starts with, if it has one. -/
  interpreter : Option String := none

/-- The samples. -/
def samples : List Sample :=
  [ { name := "decl-simple"
      prog := ⟨[st (constDecl "x" (num 1)),
                st (.decl .let_ ⟨⟨p "y", some (.string "hi")⟩, []⟩),
                st (.decl .var ⟨⟨p "z", none⟩, []⟩)]⟩ }
  , { name := "decl-multi"
      prog := ⟨[st (.decl .const
                  ⟨⟨p (longName 0), some (num 1)⟩,
                   [⟨p (longName 1), some (num 2)⟩, ⟨p (longName 2), some (num 3)⟩]⟩)]⟩ }
  , { name := "decl-multi-short"
      prog := ⟨[st (.decl .let_ ⟨⟨p "a", some (num 1)⟩, [⟨p "b", some (num 2)⟩]⟩)]⟩ }
  , { name := "numbers"
      prog := ⟨[es (.array [.elem (num 0), .elem (num 1000),
                  .elem (.number (.decimal 15 (-1))),
                  .elem (.number (.decimal 1 21)),
                  .elem (.number (.decimal 1 (-7))),
                  .elem (.number (.radix .hexadecimal 255)),
                  .elem (.number (.radix .binary 10)),
                  .elem (.number (.radix .octal 15)),
                  .elem (.number (.bigint .decimal 12)),
                  .elem (.number (.decimal 123456 (-3)))])]⟩ }
  , { name := "strings"
      prog := ⟨[es (.array [.elem (.string "abc"), .elem (.string "it's"),
                  .elem (.string "say \"hi\""), .elem (.string "tab\there"),
                  .elem (.string "nl\nhere")])]⟩ }
  , { name := "object-short"
      prog := ⟨[st (constDecl "o" (.object [.keyValue (.ident (nes "a")) (num 1),
                  .shorthand (nes "b"), .spread (v "c")]))]⟩ }
  , { name := "object-long"
      prog := ⟨[st (constDecl "o" (.object
                  [.keyValue (.ident (nes (longName 0))) (num 1),
                   .keyValue (.string "b-key") (num 2),
                   .keyValue (.computed (v (longName 1))) (num 3),
                   .method .normal (.ident (nes "m")) [par "x"] [.return_ (some (v "x"))]]))]⟩ }
  , { name := "object-accessors"
      prog := ⟨[st (constDecl "o" (.object
                  [.method .get (.ident (nes "a")) [] [.return_ (some (num 1))],
                   .method .set (.ident (nes "a")) [par "v"] [],
                   .method .generator (.ident (nes "g")) [] [.expr (.yield (some (num 1)))]]))]⟩ }
  , { name := "array-holes"
      prog := ⟨[st (constDecl "a" (.array [.elem (num 1), .hole, .elem (num 2)])),
                st (constDecl "b" (.array [])),
                st (constDecl "c" (.array [.elem (num 1), .hole]))]⟩ }
  , { name := "array-long"
      prog := ⟨[st (constDecl "a" (.array
                  [.elem (v (longName 0)), .elem (v (longName 1)),
                   .elem (v (longName 2)), .elem (v (longName 3))]))]⟩ }
  , { name := "binary-short"
      prog := ⟨[es (.binary (v "a") .plus (.binary (v "b") .times (v "c"))),
                es (.binary (.binary (v "a") .plus (v "b")) .times (v "c")),
                es (.binary (.binary (v "a") .and (v "b")) .or (v "c"))]⟩ }
  , { name := "binary-long"
      prog := ⟨[st (constDecl "x"
                  (.binary (.binary (.binary (v (longName 0)) .plus (v (longName 1)))
                    .plus (v (longName 2))) .plus (v (longName 3))))]⟩ }
  , { name := "logical-long"
      prog := ⟨[st (.if_ (.binary (.binary (v (longName 0)) .and (v (longName 1)))
                    .and (v (longName 2)))
                  (.block [.return_ (some (v "a"))]) none)]⟩ }
  , { name := "ternary-short"
      prog := ⟨[es (.ternary (v "a") (v "b") (v "c"))]⟩ }
  , { name := "ternary-long"
      prog := ⟨[st (constDecl "x" (.ternary (v (longName 0)) (v (longName 1)) (v (longName 2))))]⟩ }
  , { name := "call-long"
      prog := ⟨[es (call (longName 0) [v (longName 1), v (longName 2), v (longName 3)])]⟩ }
  , { name := "member-chain"
      prog := ⟨[es (.dot (.call (.dot (.call (.dot (v "a") (nes "b")) []) (nes "c")) []) (nes "d"))]⟩ }
  , { name := "optional-chain"
      prog := ⟨[es (.chain (v "a") ⟨.dot true (nes "b"), [.call false [], .index true (num 0)]⟩)]⟩ }
  , { name := "new-and-spread"
      prog := ⟨[es (.new (v "Foo") [v "a", .spread (v "rest")]),
                es (.new (.dot (v "a") (nes "B")) []),
                es (.new (.call (v "f") []) [])]⟩ }
  , { name := "unary"
      prog := ⟨[es (.unary .not (v "a")), es (.unary .minus (.unary .minus (v "a"))),
                es (.unary .typeof (v "a")), es (.unary .void (num 0)),
                es (.unary .delete (.dot (v "a") (nes "b"))),
                es (.postfix (v "a") .incr), es (.unary .preDecr (v "a"))]⟩ }
  , { name := "assignment"
      prog := ⟨[es (.assign (v "a") .assign (num 1)),
                es (.assign (v "a") .plus (num 1)),
                es (.assign (v "a") .logicalOr (num 1)),
                es (.assignPattern (.array [.elem (p "a"), .elem (p "b")]) (v "xs")),
                es (.assignPattern (.object [⟨.ident (nes "a"), p "a"⟩] none) (v "o"))]⟩ }
  , { name := "arrow"
      prog := ⟨[st (constDecl "f" (.arrow false [par "x"] (.expr (.binary (v "x") .plus (num 1))))),
                st (constDecl "g" (.arrow false [] (.block [.return_ (some (num 1))]))),
                st (constDecl "h" (.arrow false [par "x"]
                  (.expr (.object [.keyValue (.ident (nes "a")) (v "x")]))))]⟩ }
  , { name := "function"
      prog := ⟨[st (.funcDecl false false (nes "f") [par "a", .rest (p "rest")]
                  [.return_ (some (v "a"))]),
                st (.funcDecl true true (nes "g") [] [.expr (.await (v "x"))])]⟩ }
  , { name := "class"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [.field [] false false (.ident (nes "x")) (some (num 1)),
                   .field [] true false (.private_ (nes "y")) none,
                   .method [] false .normal (.ident (nes "m")) [par "a"] [.return_ (some (v "a"))],
                   .method [] true .get (.ident (nes "g")) [] [.return_ (some (num 1))],
                   .staticBlock [.expr (call "init" [])]])]⟩ }
  , { name := "class-expr"
      prog := ⟨[st (constDecl "C" (.classExpr [] none (some (v "B"))
                  [.method [] false .normal (.ident (nes "constructor")) []
                    [.expr (.superCall [])]]))]⟩ }
  , { name := "control-flow"
      prog := ⟨[st (.if_ (v "a") (.block [.expr (call "f" [])])
                  (some (.if_ (v "b") (.block []) (some (.block [.expr (call "g" [])]))))),
                st (.while_ (v "a") (.block [.break_ none])),
                st (.doWhile (.block [.continue_ none]) (v "a")),
                st (.for_ (.decl .let_ ⟨⟨p "i", some (num 0)⟩, []⟩)
                  (some (.binary (v "i") .lt (num 10))) (some (.postfix (v "i") .incr))
                  (.block [.expr (call "f" [v "i"])])),
                st (.forOf false (.decl .const (p "x")) (v "xs") (.block [])),
                st (.forIn (.decl .const (p "k")) (v "o") (.block [])),
                st (.labelled (nes "loop") (.while_ (.true_) (.block [.break_ (some (nes "loop"))])))]⟩ }
  , { name := "if-no-block"
      prog := ⟨[st (.if_ (v "a") (.return_ none) none),
                st (.if_ (v "a") (.expr (call "f" [])) (some (.expr (call "g" []))))]⟩ }
  , { name := "switch"
      prog := ⟨[st (.switch (v "x")
                  [.case (num 1) [.expr (call "f" []), .break_ none],
                   .case (num 2) [],
                   .default [.return_ none]])]⟩ }
  , { name := "try"
      prog := ⟨[st (.try_ [.expr (call "f" [])]
                  (.catches ⟨⟨p "e", none, [.expr (call "g" [v "e"])]⟩, []⟩
                    (.some [.expr (call "h" [])]))),
                st (.try_ [] (.finallyOnly [.expr (call "h" [])]))]⟩ }
  , { name := "throw-return"
      prog := ⟨[st (.throw (.new (v "Error") [.string "bad"])),
                st (.funcDecl false false (nes "f") [] [.return_ (some (num 1))])]⟩ }
  , { name := "template"
      prog := ⟨[st (constDecl "s" (.template none "a" [⟨v "x", "b"⟩, ⟨num 1, ""⟩])),
                st (constDecl "u" (.template (some (v "tag")) "q" []))]⟩ }
  , { name := "patterns"
      prog := ⟨[st (.decl .const ⟨⟨.array [.elem (p "a"), .hole,
                    .elem (.withDefault (p "b") (num 1)), .rest (p "r")], some (v "xs")⟩, []⟩),
                st (.decl .const ⟨⟨.object [⟨.ident (nes "a"), p "a"⟩,
                    ⟨.ident (nes "b"), p "c"⟩,
                    ⟨.ident (nes "d"), .withDefault (p "d") (num 2)⟩]
                    (some (p "rest")), some (v "o")⟩, []⟩)]⟩ }
  , { name := "regex"
      prog := ⟨[es (.regex ⟨nes "a+b", { global := true, ignoreCase := true }⟩)]⟩ }
  , { name := "sequence"
      prog := ⟨[st (.for_ (.expr (.seq (.assign (v "i") .assign (num 0))
                    (.assign (v "j") .assign (num 1)))) none none (.block []))]⟩ }
  , { name := "imports"
      prog := ⟨[.importDecl (.bare (nes "./side-effect.js") []),
                .importDecl (.clause (MiniImportClause.mk! (some (nes "def")) none none
                  (nes "./a.js"))),
                .importDecl (.clause (MiniImportClause.mk! none (some (nes "ns")) none
                  (nes "./b.js"))),
                .importDecl (.clause (MiniImportClause.mk! (some (nes "def")) none
                  (some [⟨nes "a", none⟩, ⟨nes "b", some (nes "c")⟩]) (nes "./c.js")))]⟩ }
  , { name := "exports"
      prog := ⟨[.exportDecl (.locals [⟨nes "a", none⟩, ⟨nes "b", some (nes "c")⟩]),
                .exportDecl (.fromClause [⟨nes "a", none⟩] (nes "./d.js") []),
                .exportDecl (.all none (nes "./e.js") []),
                .exportDecl (.all (some (nes "ns")) (nes "./f.js") []),
                .exportDecl (.defaultExpr (v "x")),
                .exportDecl (.decl (constDecl "y" (num 1)))]⟩ }
  , { name := "this-super"
      prog := ⟨[st (.classDecl [] (nes "A") (some (v "B"))
                  [.method [] false .normal (.ident (nes "m")) []
                    [.expr (.call (.superDot (nes "m")) []),
                     .expr (.superIndex (.string "k")),
                     .expr (.dot (.this) (nes "x"))]])]⟩ }
  , { name := "await-async-arrow"
      prog := ⟨[st (.funcDecl true false (nes "main") []
                  [constDecl "x" (.await (call "f" [])),
                   .expr (.importCall (.string "./m.js") none)])]⟩ }
  , { name := "empty-and-block"
      prog := ⟨[st (.block [.expr (call "f" [])]),
                st (.while_ (v "a") .empty)]⟩ }
  , { name := "nested-long-call"
      prog := ⟨[es (call (longName 0)
                  [call (longName 1) [v (longName 2), v (longName 3)], v (longName 4)])]⟩ }
  , { name := "statement-parens"
      prog := ⟨[es (.object [.keyValue (.ident (nes "a")) (num 1)]),
                es (.func false false none [] []),
                es (.call (.func false false none [] []) []),
                es (.assignPattern (.object [⟨.ident (nes "a"), p "a"⟩] none) (v "o"))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
