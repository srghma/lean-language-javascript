import MiniTsAST.Syntax
import MiniTsAST.JSX
import MiniTsAST.Printer
import MiniTsAST.OfJS

/-!
# TypeScript MiniTsAST and Pretty Printer

A deterministic TypeScript syntax tree — the JavaScript tree of `MiniAST`
together with the TypeScript syntax — and a printer for it whose output
matches the one the `prettier` code formatter produces for TypeScript
with its default options (two space indentation, eighty column lines).

* `MiniTsAST.Syntax` holds the syntax tree: expressions, statements,
  the type expressions, and the TypeScript declarations.
* `MiniTsAST.JSX` holds the parts of the JSX layout that work on
  documents alone.
* `MiniTsAST.OfJS` embeds the JavaScript tree of `MiniAST` into this
  one, which is what lets the JavaScript corpus be printed by this
  printer as well.
* `MiniTsAST.Printer` holds the printer and the entry points
  `printProgram`, `printStatement` and `printExpr`.

The layout engine (`MiniAST.Doc`) and the identifier tables
(`MiniAST.Unicode`) are shared with the JavaScript printer.
-/
