import Tests.Corpus
import Tests.Corpus2
import Tests.Corpus3
import Tests.Corpus4
import Tests.Corpus5
import Tests.Corpus6
import Tests.Corpus7
import Tests.Corpus8
import Tests.Corpus9
import Tests.Corpus10
import Tests.Corpus11
import Tests.Corpus12
import Tests.Corpus13
import Tests.Corpus14
import Tests.Corpus15
import Tests.Corpus16
import Tests.Corpus17
import Tests.Corpus18
import Tests.Corpus19
import Tests.Corpus20
import Tests.Corpus21
import Tests.Corpus22
import Tests.Corpus23
import Tests.Corpus24
import Tests.Corpus25
import Tests.Corpus26
import Tests.Corpus27
import Tests.Corpus28
import Tests.Corpus29
import Tests.Corpus30
import Tests.Corpus31
import Tests.Corpus32
import Tests.Corpus33
import Tests.Corpus34
import Tests.Corpus35
import Tests.Corpus36
import Tests.Corpus37
import Tests.Corpus38
import Tests.Corpus41
import Tests.Corpus42
import MiniTsAST

/-!
# The JavaScript corpus, printed by the TypeScript printer

Every JavaScript program is a TypeScript program: `MiniTsAST.OfJS`
embeds the tree of `MiniAST` into the TypeScript one, and this program
prints every sample of the JavaScript corpus through the TypeScript
printer.  The text has to be the one `dump` prints, and prettier has to
return it unchanged when it reads it as TypeScript.

Usage: `dumpjsts [width] [option=value ...]`.
-/

open Language.JavaScript.MiniAST
open Language.TypeScript.MiniTsAST

def main (args : List String) : IO Unit := do
  let (opts, args) := Language.JavaScript.Options.ofArgs Language.JavaScript.defaultOptions args
  let opts := match args[0]?.bind String.toNat? with
    | some w => { opts with printWidth := w }
    | none => opts
  for sample in Corpus.samples ++ Corpus.samples2 ++ Corpus.samples3 ++ Corpus.samples4 ++ Corpus.samples5 ++ Corpus.samples6 ++ Corpus.samples7 ++ Corpus.samples8 ++ Corpus.samples9 ++ Corpus.samples10 ++ Corpus.samples11 ++ Corpus.samples12 ++ Corpus.samples13 ++ Corpus.samples14 ++ Corpus.samples15 ++ Corpus.samples16 ++ Corpus.samples17 ++ Corpus.samples18 ++ Corpus.samples19 ++ Corpus.samples20 ++ Corpus.samples21 ++ Corpus.samples22 ++ Corpus.samples23 ++ Corpus.samples24 ++ Corpus.samples25 ++ Corpus.samples26 ++ Corpus.samples27 ++ Corpus.samples28 ++ Corpus.samples29 ++ Corpus.samples30 ++ Corpus.samples31 ++ Corpus.samples32 ++ Corpus.samples33 ++ Corpus.samples34 ++ Corpus.samples35 ++ Corpus.samples36 ++ Corpus.samples37 ++ Corpus.samples38 ++ Corpus.samples39 ++ Corpus.samples40 ++ Corpus.samples41 ++ Corpus.samples42 do
    IO.print s!"===CASE {sample.name}\n"
    IO.print (Language.TypeScript.MiniTsAST.printFileWith opts sample.interpreter
      (OfJS.ofProgram sample.prog))
