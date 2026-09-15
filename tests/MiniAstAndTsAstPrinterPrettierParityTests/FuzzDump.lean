import Tests.Fuzz

/-!
# Dump the printer's output for random programs

Usage: `fuzz [count] [seed] [depth] [statements] [nesting] [jsx] [width]
[option=value ...]`.  Prints `count`
random programs, each preceded by a marker line, in the format
`scripts/check-prettier.mjs` reads.

`nesting` wraps the statements of every program in that many nested blocks,
which shifts them right by two columns each.  A layout decision depends on
the width that is left on the line, so printing the same programs at
several indentations exercises the decisions at several widths.  A program
which holds an import or an export is left alone, since those may not stand
inside a block.

A sixth argument of `jsx` asks for programs every statement of which is
built around a JSX element, rather than the general random programs.  A
seventh argument sets the width the printer lays the programs out for; it
defaults to prettier's eighty columns.  Any argument of the shape
`name=value`, spelled the way prettier's own configuration spells it
(`semi=false`, `arrowParens=avoid`, …), sets that option.
-/

open Language.JavaScript.MiniAST
open Language.JavaScript

/-- Whether every item of the program is a statement, and so may be moved
inside a block. -/
def allStatements (prog : MiniProgram) : Bool :=
  prog.items.all fun item => match item with | .stmt _ => true | _ => false

/-- The statements of a program, which must all be statements. -/
def statementsOf (prog : MiniProgram) : List MiniStatement :=
  prog.items.filterMap fun item => match item with | .stmt s => some s | _ => none

/-- The program with its statements wrapped in `n` nested blocks. -/
def nestProgram (n : Nat) (prog : MiniProgram) : MiniProgram :=
  if n == 0 || !allStatements prog then prog
  else
    let rec wrap : Nat → List MiniStatement → List MiniStatement
      | 0, stmts => stmts
      | k + 1, stmts => wrap k [.block stmts]
    ⟨(wrap n (statementsOf prog)).map .stmt⟩

def main (args : List String) : IO Unit := do
  let (opts, args) := Options.ofArgs defaultOptions args
  let count := (args[0]?.bind String.toNat?).getD 200
  let seed := (args[1]?.bind String.toNat?).getD 1
  let depth := (args[2]?.bind String.toNat?).getD 4
  let stmts := (args[3]?.bind String.toNat?).getD 3
  let nesting := (args[4]?.bind String.toNat?).getD 0
  -- `jsx` as a sixth argument asks for the programs built around JSX
  -- elements instead of the general ones.
  let jsxOnly := args[5]? == some "jsx"
  let opts := match args[6]?.bind String.toNat? with
    | some w => { opts with printWidth := w }
    | none => opts
  let progs :=
    if jsxOnly then Fuzz.jsxPrograms count depth stmts (UInt64.ofNat seed)
    else Fuzz.programs count depth stmts (UInt64.ofNat seed)
  let mut i := 0
  for prog in progs do
    IO.print s!"===CASE fuzz-{seed}-{nesting}-{i}\n"
    IO.print (printProgramWith opts (nestProgram nesting prog))
    i := i + 1
