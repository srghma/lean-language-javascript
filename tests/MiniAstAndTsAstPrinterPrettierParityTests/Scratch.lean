import Tests.Corpus39

/-!
# A scratch pad for investigating single samples

The samples here are the ones under investigation at the moment; they are
printed by `lake build scratch` and compared with prettier by
`sh scripts/scratch.sh`.  A sample that turns up a difference belongs in
one of the corpus files once it is fixed.
-/

namespace Language.JavaScript.MiniAST.Corpus

open Language.JavaScript

/-- The samples under investigation. -/
def scratchSamples : List Sample :=
  [ { name := "probe-element"
      prog := ⟨[st (constDecl "element" (el "div" [sattr "className" "a-wrapper"]
                  (some [.text "hello ", elc "b" [] (some [.text "world"])])))]⟩ }
  ]

end Language.JavaScript.MiniAST.Corpus

open Language.JavaScript.MiniAST

def main : IO Unit := do
  for sample in Corpus.scratchSamples do
    IO.print s!"===CASE {sample.name}\n"
    IO.print (printFile sample.interpreter sample.prog)
