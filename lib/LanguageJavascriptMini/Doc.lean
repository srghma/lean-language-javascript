/-
A small Wadler style pretty printing engine, used by `MiniASTPrinter`.

A `Doc` describes a document with optional line breaks.  A `group` is
printed on one line if it fits in the remaining width, and broken otherwise;
`ifBreak` lets a document depend on that choice (this is how trailing commas
appear only in the broken layout).
-/

namespace Language.JavaScript.Doc

/-- A document. -/
inductive Doc where
  /-- The empty document. -/
  | nil
  /-- Literal text.  It may contain newlines, in which case the current
  column is recomputed from the text. -/
  | text (s : String)
  /-- A space if the enclosing group is flat, a newline otherwise. -/
  | line
  /-- Nothing if the enclosing group is flat, a newline otherwise. -/
  | softline
  /-- Always a newline; it also forces every enclosing group to break. -/
  | hardline
  | cat (a b : Doc)
  /-- Increase the indentation of the newlines inside. -/
  | nest (n : Nat) (d : Doc)
  /-- Print flat if it fits, broken otherwise. -/
  | group (d : Doc)
  /-- Choose according to whether the enclosing group is broken. -/
  | ifBreak (whenBroken whenFlat : Doc)
deriving Inhabited

namespace Doc

instance : Append Doc := ⟨Doc.cat⟩

/-- Concatenate a list of documents. -/
def concat (ds : List Doc) : Doc := ds.foldl (init := .nil) (· ++ ·)

/-- Concatenate a list of documents, separated by `sep`. -/
def joinWith (sep : Doc) : List Doc → Doc
  | [] => .nil
  | [d] => d
  | d :: ds => d ++ sep ++ joinWith sep ds

/-- Whether the group being laid out is flat or broken. -/
inductive Mode where
  | flat | broken
deriving Inhabited, BEq

/-- Would the pending documents fit into `width` more columns, up to the
first line break of a broken group? -/
partial def fits (width : Int) (items : List (Nat × Mode × Doc)) : Bool :=
  if width < 0 then false else
  match items with
  | [] => true
  | (i, m, d) :: rest =>
    match d with
    | .nil => fits width rest
    | .text s =>
        if s.contains '\n' then true else fits (width - s.length) rest
    | .line => match m with
      | .flat => fits (width - 1) rest
      | .broken => true
    | .softline => match m with
      | .flat => fits width rest
      | .broken => true
    | .hardline => match m with
      | .flat => false
      | .broken => true
    | .cat a b => fits width ((i, m, a) :: (i, m, b) :: rest)
    | .nest n d => fits width ((i + n, m, d) :: rest)
    | .group d => fits width ((i, .flat, d) :: rest)
    | .ifBreak b f => match m with
      | .flat => fits width ((i, m, f) :: rest)
      | .broken => fits width ((i, m, b) :: rest)

/-- The column reached after emitting `s` starting at column `col`. -/
private def columnAfter (col : Nat) (s : String) : Nat :=
  s.foldl (fun c ch => if ch == '\n' then 0 else c + 1) col

private def newlineWith (indent : Nat) : String :=
  "\n" ++ String.ofList (List.replicate indent ' ')

private partial def go (width : Nat) (out : String) (col : Nat) :
    List (Nat × Mode × Doc) → String
  | [] => out
  | (i, m, d) :: rest =>
    match d with
    | .nil => go width out col rest
    | .text s => go width (out ++ s) (columnAfter col s) rest
    | .line => match m with
      | .flat => go width (out ++ " ") (col + 1) rest
      | .broken => go width (out ++ newlineWith i) i rest
    | .softline => match m with
      | .flat => go width out col rest
      | .broken => go width (out ++ newlineWith i) i rest
    | .hardline => go width (out ++ newlineWith i) i rest
    | .cat a b => go width out col ((i, m, a) :: (i, m, b) :: rest)
    | .nest n d => go width out col ((i + n, m, d) :: rest)
    | .group d =>
        let flat := fits ((width : Int) - col) ((i, .flat, d) :: rest)
        go width out col ((i, if flat then .flat else .broken, d) :: rest)
    | .ifBreak b f => match m with
      | .flat => go width out col ((i, m, f) :: rest)
      | .broken => go width out col ((i, m, b) :: rest)

/-- Lay out a document, breaking groups that do not fit into `width`
columns. -/
def render (width : Nat) (d : Doc) : String := go width "" 0 [(0, .broken, d)]

end Doc

end Language.JavaScript.Doc
