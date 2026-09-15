import Tests.Ts.Prelude

/-!
# A scratch pad for investigating single TypeScript samples

The samples here are the ones under investigation at the moment; they are
printed by `lake build scratchts` and compared with prettier by
`sh scripts/scratch-ts.sh`.  A sample that turns up a difference belongs in
one of the `Tests/Ts/Corpus*.lean` files once it is fixed.
-/

namespace Language.TypeScript.MiniTsAST.Corpus

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- The samples under investigation. -/
def scratchSamples : List Sample :=
  [ { name := "a-sample"
      prog := ⟨[st (constDecl "aValueName" (some (ty "number")) (num 1))]⟩ }
  ]

end Language.TypeScript.MiniTsAST.Corpus

open Language.TypeScript.MiniTsAST

def main (args : List String) : IO Unit := do
  let width := (args[0]?.bind String.toNat?).getD Printer.defaultWidth
  for sample in Corpus.scratchSamples do
    IO.print s!"===CASE {sample.name}\n"
    IO.print (printFileWidth sample.interpreter width sample.prog)
