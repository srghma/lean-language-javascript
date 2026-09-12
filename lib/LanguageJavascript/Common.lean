/-
Component types shared by the JavaScript trees.

The deterministic tree (`MiniAST`) and the scope safe tree (`BrujinAST`)
describe the *same* language, so they agree on the small leaf types that
carry no syntax tree inside them: the operators, the keyword of a variable
declaration, the kind of a method, one `name as alias` of an import or
export clause, and one import attribute.  Those types live here, in the
`Language.JavaScript` namespace — the parent of the namespace of each tree,
so they are visible from all of them without an `open` — instead of in one
tree, so that neither tree has to depend on another only to name them.

`NEString`, the non empty string they are phrased in terms of, comes from
`Language.JavaScript.Types`, which is where the *refined* component types
(non empty strings and lists, numbers, regular expression literals) live.
-/
import LanguageJavascript.Types

namespace Language.JavaScript

/-! ## Operators -/

/-- Binary operators. -/
inductive BinOp where
  | and | or
  /-- `??`, the nullish coalescing operator. -/
  | coalesce
  | bitAnd | bitOr | bitXor
  | eq | neq | strictEq | strictNeq
  | lt | le | gt | ge
  | lsh | rsh | ursh
  | plus | minus | times | divide | mod
  | inOp | instanceOf
deriving Repr, BEq, DecidableEq, Inhabited

/-- Prefix operators. -/
inductive UnaryOp where
  | not | tilde | plus | minus
  | typeof | void | delete
  | preIncr | preDecr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Postfix operators. -/
inductive PostfixOp where
  | incr | decr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Assignment operators. -/
inductive AssignOp where
  | assign
  | plus | minus | times | divide | mod
  | lsh | rsh | ursh
  | bitAnd | bitXor | bitOr
  /-- `&&=` -/
  | logicalAnd
  /-- `||=` -/
  | logicalOr
  /-- `??=` -/
  | coalesce
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword introducing a variable declaration. -/
inductive VarKind where
  | var | let_ | const
deriving Repr, BEq, DecidableEq, Inhabited

/-- What kind of method a member of an object or class literal is. -/
inductive MethodKind where
  | normal | generator | get | set
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Import and export clauses -/

/-- One `name` or `name as alias` of an import or export clause. -/
structure Specifier where
  /-- The exported name. -/
  name : NEString
  /-- The local name, when it differs. -/
  alias_ : Option NEString
deriving Repr, BEq, DecidableEq, Inhabited

/-- One import attribute, `type: "json"`, of an `import` or of an
`export ... from` declaration.  Both the key — an identifier or a string
literal in source — and the value hold the characters they denote, so the
two ways of writing a key give the same value. -/
structure ImportAttr where
  /-- The key. -/
  key : String
  /-- The value. -/
  value : String
deriving Repr, BEq, DecidableEq, Inhabited

end Language.JavaScript
