import Tests.Corpus17

/-!
# Samples of long lists

Prettier fills a line with as many elements of an array of short numbers
as fit, rather than writing one element per line, and it breaks a long
list of parameters, of arguments, of properties or of declarators one
element per line.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The multiples of 37 below `37 * n`, as elements of an array literal. -/
def numberElems (n : Nat) : List MiniArrayElement :=
  (List.range n).map fun k => .elem (num (k * 37))

/-- `n` copies of the string `s`, as elements of an array literal. -/
def stringElems (n : Nat) (s : String) : List MiniArrayElement :=
  (List.range n).map fun _ => .elem (.string s)

/-- `n` parameters of long names. -/
def longParams (n : Nat) : List MiniParam :=
  (List.range n).map fun k => par (longName k ++ toString k)

/-- The halves `0`, `1.5`, `3`, ... below `1.5 * n`, as elements of an
array literal. -/
def halfElems (n : Nat) : List MiniArrayElement :=
  (List.range n).map fun k => .elem (.number (.decimal (k * 15) (-1)))

/-- A call whose only argument is an array of `n` halves, wrapped in `k`
nested blocks, which shifts it right by `2 * k` columns.  The trailing
comma of the last element counts towards the width of the line it stands
on, so the element it belongs to moves to a line of its own sooner. -/
def fillAtDepth (k n : Nat) : MiniStatement :=
  nestBlocks k (.expr (call "f" [.array (halfElems n)]))

/-- The samples. -/
def samples18 : List Sample :=
  [ { name := "array-of-numbers-short", prog := ⟨[es (.array (numberElems 5))]⟩ }
  , { name := "array-of-numbers-long", prog := ⟨[es (.array (numberElems 40))]⟩ }
  , { name := "array-of-numbers-nested"
      prog := ⟨[st (constDecl (longName 0) (.array (numberElems 40)))]⟩ }
  , { name := "array-of-numbers-with-hole"
      prog := ⟨[es (.array (numberElems 20 ++ [.hole] ++ numberElems 20))]⟩ }
  , { name := "array-of-strings", prog := ⟨[es (.array (stringElems 20 "value"))]⟩ }
  , { name := "array-of-arrays"
      prog := ⟨[es (.array ((List.range 8).map fun _ => .elem (.array (numberElems 4))))]⟩ }
  , { name := "array-of-objects"
      prog := ⟨[es (.array ((List.range 4).map fun _ =>
                  .elem (.object [.keyValue (.ident (nes "a")) (num 1)])))]⟩ }
  , { name := "array-of-mixed"
      prog := ⟨[es (.array (numberElems 10 ++ [.elem (v "handler")] ++ numberElems 10))]⟩ }
  , { name := "array-of-negative-numbers"
      prog := ⟨[es (.array ((List.range 30).map fun k => .elem (.unary .minus (num k))))]⟩ }
  , { name := "array-of-bigints"
      prog := ⟨[es (.array ((List.range 20).map fun k =>
                  .elem (.number (.bigint .decimal k))))]⟩ }
  , { name := "many-parameters"
      prog := ⟨[st (.funcDecl false false (nes "f") (longParams 6) [])]⟩ }
  , { name := "many-arguments"
      prog := ⟨[es (call "f" ((List.range 6).map fun k => v (longName k ++ toString k)))]⟩ }
  , { name := "many-properties"
      prog := ⟨[st (constDecl (longName 0) (.object ((List.range 8).map fun k =>
                  .keyValue (.ident (nes (longName k ++ toString k))) (num k))))]⟩ }
  , { name := "many-switch-cases"
      prog := ⟨[st (.switch (v "value") ((List.range 6).map fun k =>
                  .case (num k) [.expr (call "handle" [num k]), .break_ none]))]⟩ }
  , { name := "many-declarators"
      prog := ⟨[st (.decl .const ⟨⟨p (longName 0), some (num 1)⟩,
                  [⟨p (longName 1), some (num 2)⟩, ⟨p (longName 2), some (num 3)⟩]⟩)]⟩ }
  , { name := "array-fill-trailing-comma-0", prog := ⟨[st (fillAtDepth 0 29)]⟩ }
  , { name := "array-fill-trailing-comma-1", prog := ⟨[st (fillAtDepth 1 29)]⟩ }
  , { name := "array-fill-trailing-comma-2", prog := ⟨[st (fillAtDepth 2 29)]⟩ }
  , { name := "array-fill-trailing-comma-3", prog := ⟨[st (fillAtDepth 3 29)]⟩ }
  , { name := "array-fill-trailing-comma-4", prog := ⟨[st (fillAtDepth 4 29)]⟩ }
  , { name := "array-fill-trailing-comma-5", prog := ⟨[st (fillAtDepth 5 29)]⟩ }
  , { name := "array-fill-trailing-comma-6", prog := ⟨[st (fillAtDepth 6 29)]⟩ }
  , { name := "array-fill-short-0", prog := ⟨[st (fillAtDepth 0 12)]⟩ }
  , { name := "array-fill-short-3", prog := ⟨[st (fillAtDepth 3 12)]⟩ }
  , { name := "deep-object"
      prog := ⟨[st (constDecl (longName 0)
                  (.object [.keyValue (.ident (nes (longName 1)))
                    (.object [.keyValue (.ident (nes (longName 2)))
                      (.object [.keyValue (.ident (nes (longName 3))) (num 1)])])]))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus
