import Tests.Ts.Corpus
import Tests.Ts.Corpus2
import Tests.Ts.Corpus3
import Tests.Ts.Corpus4
import Tests.Ts.Corpus5
import Tests.Ts.Corpus6
import Tests.Ts.Corpus7
import Tests.Ts.Corpus8
import Tests.Ts.Corpus9
import Tests.Ts.Corpus10
import Tests.Ts.Corpus11
import Tests.Ts.Corpus12
import Tests.Ts.Corpus13
import Tests.Ts.Corpus14
import Tests.Ts.Corpus15
import Tests.Ts.Corpus16

/-!
# Dump the TypeScript printer's output for the corpus

Prints every sample of the `Tests/Ts/Corpus*.lean` files, each preceded by a marker
line, so that an external tool can compare the output with prettier's.

Usage: `dumpts [width] [guard] [option=value ...]`.  The first positional
argument sets the width the printer lays the samples out for; it defaults
to prettier's eighty columns.  A positional argument of `guard` asks for
the samples printed with parentheses around every instantiation
expression, `f<T>`, which TypeScript would otherwise read back as a pair
of comparisons; that text is the one `scripts/check-guard-ts.mjs` hands
to prettier.  Any argument of the shape `name=value`, spelled the way
prettier's own configuration spells it (`semi=false`,
`trailingComma=es5`, `tabWidth=4`, ...), sets that option; the comparison
scripts hand prettier the same configuration.
-/

open Language.JavaScript (Options defaultOptions)
open Language.TypeScript.MiniTsAST

def main (args : List String) : IO Unit := do
  let (opts, args) := Options.ofArgs defaultOptions args
  let opts := match args[0]?.bind String.toNat? with
    | some w => { opts with printWidth := w }
    | none => opts
  let guard := args.contains "guard"
  for sample in Corpus.samples ++ Corpus.samples2 ++ Corpus.samples3 ++ Corpus.samples4 ++ Corpus.samples5 ++ Corpus.samples6 ++ Corpus.samples7 ++ Corpus.samples8 ++ Corpus.samples9 ++ Corpus.samples10 ++ Corpus.samples11 ++ Corpus.samples12 ++ Corpus.samples13 ++ Corpus.samples14 ++ Corpus.samples15 ++ Corpus.samples16 do
    IO.print s!"===CASE {sample.name}\n"
    IO.print (if guard then printProgramGuardedWith opts sample.interpreter sample.prog
              else printFileWith opts sample.interpreter sample.prog)
