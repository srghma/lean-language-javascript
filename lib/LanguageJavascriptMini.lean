import MiniAST.Doc
import MiniAST.Unicode
import MiniAST.Syntax
import MiniAST.JSX
import MiniAST.Printer

/-!
# JavaScript MiniAST and Pretty Printer

A deterministic JavaScript syntax tree, JSX included, and a printer for it
whose output matches the one the `prettier` code formatter produces with
its default options (two space indentation, eighty column lines).

* `MiniAST.Doc` is the layout engine.
* `MiniAST.Unicode` holds the identifier character tables.
* `MiniAST.Syntax` holds the syntax tree and its component types,
  among them the JSX elements, attributes and children.
* `MiniAST.JSX` holds the parts of the JSX layout that work on documents
  alone: the children of an element laid out as a `fill`, the runs of
  whitespace written `{" "}`, and the tags an element is assembled from.
* `MiniAST.Printer` holds the printer and the entry points
  `printProgram`, `printStatement` and `printExpr`.
-/
