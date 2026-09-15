import Tests.Ts.Fuzz

/-!
# Dump the TypeScript printer's output for random TypeScript programs

Prints the random programs of `Tests.Ts.Fuzz`, each preceded by a marker
line, in the format `scripts/check-prettier-ts.mjs` reads.

Usage: `fuzztsgen [count] [seed] [depth] [items] [nesting] [width] [guard]`.

A seventh argument of `guard` asks for the programs printed with
parentheses around every instantiation expression, `f<T>`, which
TypeScript would otherwise read back as a pair of comparisons; that text
is the one `scripts/check-guard-ts.mjs` hands to prettier.

`nesting` wraps the statements of every program in that many nested
namespaces, which shifts them right by two columns each: a layout decision
depends on the width that is left on the line, so printing the same
programs at several indentations exercises the decisions at several
widths.  A program which holds an import or an export is left alone, since
those may not stand inside a namespace.
-/

open Language.JavaScript
open Language.TypeScript.MiniTsAST

/-- Whether every item of the program is a statement, and so may be moved
inside a namespace. -/
def allStatements (prog : MiniProgram) : Bool :=
  prog.items.all fun item => match item with | .stmt _ => true | _ => false

/-- The program with its items wrapped in `n` nested namespaces. -/
def nestProgram (n : Nat) (prog : MiniProgram) : MiniProgram :=
  if n == 0 || !allStatements prog then prog
  else
    let rec wrap : Nat → List MiniModuleItem → List MiniModuleItem
      | 0, items => items
      | k + 1, items =>
          wrap k [.stmt (.namespaceDecl false
            (.qualified ⟨NEString.ofString! ("Wrapper" ++ toString k), []⟩) (some items))]
    ⟨wrap n prog.items⟩

def main (args : List String) : IO Unit := do
  let (opts, args) := Options.ofArgs defaultOptions args
  let count := (args[0]?.bind String.toNat?).getD 200
  let seed := (args[1]?.bind String.toNat?).getD 1
  let depth := (args[2]?.bind String.toNat?).getD 3
  let items := (args[3]?.bind String.toNat?).getD 3
  let nesting := (args[4]?.bind String.toNat?).getD 0
  let opts := match args[5]?.bind String.toNat? with
    | some w => { opts with printWidth := w }
    | none => opts
  let guard := args.contains "guard"
  let mut i := 0
  for prog in Fuzz.programs count depth items (UInt64.ofNat seed) do
    IO.print s!"===CASE tsfuzz-{seed}-{nesting}-{i}\n"
    let p := nestProgram nesting prog
    IO.print (if guard then printProgramGuardedWith opts none p else printProgramWith opts p)
    i := i + 1
