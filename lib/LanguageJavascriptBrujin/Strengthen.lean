/-
Removing a binding from the scope of a `BrujinAST` tree.

This is what an optimizer needs in order to delete a binding: a tree that
lives in a scope with one more const (respectively mutable) variable can be
moved into the smaller scope exactly when it does not mention that
variable, and the variables above it have to be renumbered.  Both halves
are what the following functions do, and the *type* records the result:

    strengthenConstExpr (k : Nat) : Expr (c + 1) m → Option (Expr c m)

gives `none` precisely when the variable of index `k` is mentioned, and
otherwise a tree in the smaller scope, with every index above `k` lowered
by one.  There is nothing to prove about the renumbering afterwards: a
wrong index would not typecheck.

`k` is the index of the variable to remove *at the root of the tree*.
Under a binder it grows: the body of a function of arity `a` sees `a` more
mutable variables, so the mutable variable that was `k` outside is `k + a`
inside; the same happens with the const scope inside a named function or
class, and inside the rest of a block, after a statement that binds `dc`
const and `dm` mutable variables.
-/
import LanguageJavascriptBrujin.AST

namespace Language.JavaScript.BrujinAST

/-! ## Moving between equal scopes

A scope such as `c + 1 + dc` and the scope `c + dc + 1` the recursion wants
are equal but not definitionally so; `Expr.castScope` and its siblings (in
`BrujinAST`) move a tree between them.  Only the body of an arrow function
is missing there. -/

/-- Move the body of an arrow function to an equal scope. -/
def ArrowBody.castScope {c c' m m' : Nat} (hc : c = c') (hm : m = m') (b : ArrowBody c m) :
    ArrowBody c' m' := hc ▸ hm ▸ b

/-! ## Removing a const variable -/

mutual

/-- Remove the const variable of index `k` from the scope of an
expression; `none` if it is mentioned. -/
partial def strengthenConstExpr {c m : Nat} (k : Nat) : Expr (c + 1) m → Option (Expr c m)
  | .mutVar i => some (.mutVar i)
  | .constVar i =>
      if i.val = k then none
      else if h : k < i.val then some (.constVar ⟨i.val - 1, by omega⟩)
      else if h' : i.val < c then some (.constVar ⟨i.val, h'⟩)
      else none
  | .unsafeGlobal n => some (.unsafeGlobal n)
  | .number raw => some (.number raw)
  | .string v => some (.string v)
  | .regex raw => some (.regex raw)
  | .null => some .null
  | .true_ => some .true_
  | .false_ => some .false_
  | .this => some .this
  | .array els => (strengthenConstArrayElems k els).map .array
  | .object ps => (strengthenConstProperties k ps).map .object
  | .assign t op rhs => do
      pure (.assign (← strengthenConstTarget k t) op (← strengthenConstExpr k rhs))
  | .update t op isPrefix => do pure (.update (← strengthenConstTarget k t) op isPrefix)
  | .await x => do pure (.await (← strengthenConstExpr k x))
  | .call f args => do pure (.call (← strengthenConstExpr k f) (← strengthenConstExprs k args))
  | .new f args => do pure (.new (← strengthenConstExpr k f) (← strengthenConstExprs k args))
  | .dot o n => do pure (.dot (← strengthenConstExpr k o) n)
  | .index o i => do pure (.index (← strengthenConstExpr k o) (← strengthenConstExpr k i))
  | .classAnon her body => do
      pure (.classAnon (← strengthenConstOptExpr k her) (← strengthenConstClassElems k body))
  | .classSelf her body => do
      pure (.classSelf (← strengthenConstOptExpr k her)
        (← strengthenConstClassElems (c := c + 1) (k + 1) body))
  | .seq a b => do pure (.seq (← strengthenConstExpr k a) (← strengthenConstExpr k b))
  | .binary a op b => do
      pure (.binary (← strengthenConstExpr k a) op (← strengthenConstExpr k b))
  | .ternary a b d => do
      pure (.ternary (← strengthenConstExpr k a) (← strengthenConstExpr k b)
        (← strengthenConstExpr k d))
  | .arrow arity body => do pure (.arrow arity (← strengthenConstArrowBody k body))
  | .func isAsync isGen arity body => do
      pure (.func isAsync isGen arity (← strengthenConstBlock k body))
  | .funcSelf isAsync isGen arity body => do
      pure (.funcSelf isAsync isGen arity (← strengthenConstBlock (c := c + 1) (k + 1) body))
  | .spread x => do pure (.spread (← strengthenConstExpr k x))
  | .template tag head parts => do
      pure (.template (← strengthenConstOptExpr k tag) head
        (← strengthenConstTemplateParts k parts))
  | .unary op x => do pure (.unary op (← strengthenConstExpr k x))
  | .yield x => do pure (.yield (← strengthenConstOptExpr k x))
  | .yieldFrom x => do pure (.yieldFrom (← strengthenConstExpr k x))

/-- Remove the const variable of index `k` from an assignment target. -/
partial def strengthenConstTarget {c m : Nat} (k : Nat) : Target (c + 1) m → Option (Target c m)
  | .mut i => some (.mut i)
  | .unsafeGlobal n => some (.unsafeGlobal n)
  | .dot o n => do pure (.dot (← strengthenConstExpr k o) n)
  | .index o i => do pure (.index (← strengthenConstExpr k o) (← strengthenConstExpr k i))

/-- Remove the const variable of index `k` from a list of expressions. -/
partial def strengthenConstExprs {c m : Nat} (k : Nat) : Exprs (c + 1) m → Option (Exprs c m)
  | .nil => some .nil
  | .cons e r => do pure (.cons (← strengthenConstExpr k e) (← strengthenConstExprs k r))

/-- Remove the const variable of index `k` from an optional expression. -/
partial def strengthenConstOptExpr {c m : Nat} (k : Nat) : OptExpr (c + 1) m → Option (OptExpr c m)
  | .none => some .none
  | .some e => do pure (.some (← strengthenConstExpr k e))

/-- Remove the const variable of index `k` from the elements of an array. -/
partial def strengthenConstArrayElems {c m : Nat} (k : Nat) :
    ArrayElems (c + 1) m → Option (ArrayElems c m)
  | .nil => some .nil
  | .cons .hole r => do pure (.cons .hole (← strengthenConstArrayElems k r))
  | .cons (.elem e) r => do
      pure (.cons (.elem (← strengthenConstExpr k e)) (← strengthenConstArrayElems k r))

/-- Remove the const variable of index `k` from a template literal. -/
partial def strengthenConstTemplateParts {c m : Nat} (k : Nat) :
    TemplateParts (c + 1) m → Option (TemplateParts c m)
  | .nil => some .nil
  | .cons (.mk e s) r => do
      pure (.cons (.mk (← strengthenConstExpr k e) s) (← strengthenConstTemplateParts k r))

/-- Remove the const variable of index `k` from the name of a property. -/
partial def strengthenConstPropName {c m : Nat} (k : Nat) :
    PropName (c + 1) m → Option (PropName c m)
  | .ident n => some (.ident n)
  | .string v => some (.string v)
  | .number raw => some (.number raw)
  | .computed e => do pure (.computed (← strengthenConstExpr k e))

/-- Remove the const variable of index `k` from an object literal. -/
partial def strengthenConstProperties {c m : Nat} (k : Nat) :
    Properties (c + 1) m → Option (Properties c m)
  | .nil => some .nil
  | .cons (.keyValue key v) r => do
      pure (.cons (.keyValue (← strengthenConstPropName k key) (← strengthenConstExpr k v))
        (← strengthenConstProperties k r))
  | .cons (.method kind key arity body) r => do
      pure (.cons (.method kind (← strengthenConstPropName k key) arity
        (← strengthenConstBlock k body)) (← strengthenConstProperties k r))

/-- Remove the const variable of index `k` from a class body. -/
partial def strengthenConstClassElems {c m : Nat} (k : Nat) :
    ClassElems (c + 1) m → Option (ClassElems c m)
  | .nil => some .nil
  | .cons (.mk isStatic kind key arity body) r => do
      pure (.cons (.mk isStatic kind (← strengthenConstPropName k key) arity
        (← strengthenConstBlock k body)) (← strengthenConstClassElems k r))

/-- Remove the const variable of index `k` from the body of an arrow. -/
partial def strengthenConstArrowBody {c m : Nat} (k : Nat) :
    ArrowBody (c + 1) m → Option (ArrowBody c m)
  | .expr e => do pure (.expr (← strengthenConstExpr k e))
  | .block b => do pure (.block (← strengthenConstBlock k b))

/-- Remove the const variable of index `k` from the first clause of a
`for (;;)`. -/
partial def strengthenConstForInit {c m dc dm : Nat} (k : Nat) :
    ForInit (c + 1) m dc dm → Option (ForInit c m dc dm)
  | .none => some .none
  | .expr e => do pure (.expr (← strengthenConstExpr k e))
  | .constDecl init => do pure (.constDecl (← strengthenConstExpr k init))
  | .letDecl init => do pure (.letDecl (← strengthenConstOptExpr k init))

/-- Remove the const variable of index `k` from the binder of a
`for (... of ...)`. -/
partial def strengthenConstForHead {c m dc dm : Nat} (k : Nat) :
    ForHead (c + 1) m dc dm → Option (ForHead c m dc dm)
  | .target t => do pure (.target (← strengthenConstTarget k t))
  | .constBind => some .constBind
  | .letBind => some .letBind

/-- Remove the const variable of index `k` from the cases of a `switch`. -/
partial def strengthenConstSwitchCases {c m : Nat} (k : Nat) :
    SwitchCases (c + 1) m → Option (SwitchCases c m)
  | .nil => some .nil
  | .cons (.case t b) r => do
      pure (.cons (.case (← strengthenConstExpr k t) (← strengthenConstBlock k b))
        (← strengthenConstSwitchCases k r))
  | .cons (.default b) r => do
      pure (.cons (.default (← strengthenConstBlock k b)) (← strengthenConstSwitchCases k r))

/-- Remove the const variable of index `k` from an optional block. -/
partial def strengthenConstOptBlock {c m : Nat} (k : Nat) :
    OptBlock (c + 1) m → Option (OptBlock c m)
  | .none => some .none
  | .some b => do pure (.some (← strengthenConstBlock k b))

/-- Remove the const variable of index `k` from what follows a `try`. -/
partial def strengthenConstTryTail {c m : Nat} (k : Nat) :
    TryTail (c + 1) m → Option (TryTail c m)
  | .catch_ body fin => do
      pure (.catch_ (← strengthenConstBlock k body) (← strengthenConstOptBlock k fin))
  | .finallyOnly b => do pure (.finallyOnly (← strengthenConstBlock k b))

/-- Remove the const variable of index `k` from a statement. -/
partial def strengthenConstStmt {c m dc dm : Nat} (k : Nat) :
    Stmt (c + 1) m dc dm → Option (Stmt c m dc dm)
  | .expr e => do pure (.expr (← strengthenConstExpr k e))
  | .constDecl init => do pure (.constDecl (← strengthenConstExpr k init))
  | .letDecl init => do pure (.letDecl (← strengthenConstOptExpr k init))
  | .block b => do pure (.block (← strengthenConstBlock k b))
  | .if_ cond t e => do
      pure (.if_ (← strengthenConstExpr k cond) (← strengthenConstBlock k t)
        (← strengthenConstOptBlock k e))
  | .while_ cond b => do
      pure (.while_ (← strengthenConstExpr k cond) (← strengthenConstBlock k b))
  | .doWhile b cond => do
      pure (.doWhile (← strengthenConstBlock k b) (← strengthenConstExpr k cond))
  | .for_ (dc := dc') init cond step body => do
      let init ← strengthenConstForInit k init
      let cond ← strengthenConstOptExpr (c := c + dc') (k + dc')
        (cond.castScope (by omega) rfl)
      let step ← strengthenConstOptExpr (c := c + dc') (k + dc')
        (step.castScope (by omega) rfl)
      let body ← strengthenConstBlock (c := c + dc') (k + dc')
        (body.castScope (by omega) rfl)
      pure (.for_ init cond step body)
  | .forIn (dc := dc') head obj body => do
      let head ← strengthenConstForHead k head
      let obj ← strengthenConstExpr k obj
      let body ← strengthenConstBlock (c := c + dc') (k + dc')
        (body.castScope (by omega) rfl)
      pure (.forIn head obj body)
  | .forOf (dc := dc') head obj body => do
      let head ← strengthenConstForHead k head
      let obj ← strengthenConstExpr k obj
      let body ← strengthenConstBlock (c := c + dc') (k + dc')
        (body.castScope (by omega) rfl)
      pure (.forOf head obj body)
  | .funcDecl isAsync isGen arity body => do
      pure (.funcDecl isAsync isGen arity (← strengthenConstBlock (c := c + 1) (k + 1) body))
  | .classDecl her body => do
      pure (.classDecl (← strengthenConstOptExpr k her)
        (← strengthenConstClassElems (c := c + 1) (k + 1) body))
  | .return_ e => do pure (.return_ (← strengthenConstOptExpr k e))
  | .throw e => do pure (.throw (← strengthenConstExpr k e))
  | .break_ l => some (.break_ l)
  | .continue_ l => some (.continue_ l)
  | .labelled l s => do pure (.labelled l (← strengthenConstStmt k s))
  | .switch disc cases => do
      pure (.switch (← strengthenConstExpr k disc) (← strengthenConstSwitchCases k cases))
  | .try_ b tail => do
      pure (.try_ (← strengthenConstBlock k b) (← strengthenConstTryTail k tail))

/-- Remove the const variable of index `k` from a block. -/
partial def strengthenConstBlock {c m : Nat} (k : Nat) : Block (c + 1) m → Option (Block c m)
  | .nil => some .nil
  | .cons (dc := dc) (dm := dm) hd tl => do
      let hd ← strengthenConstStmt k hd
      let tl ← strengthenConstBlock (c := c + dc) (k + dc) (tl.castScope (by omega) rfl)
      pure (.cons hd tl)

end

/-! ## Removing a mutable variable -/

mutual

/-- Remove the mutable variable of index `k` from the scope of an
expression; `none` if it is mentioned. -/
partial def strengthenMutExpr {c m : Nat} (k : Nat) : Expr c (m + 1) → Option (Expr c m)
  | .constVar i => some (.constVar i)
  | .mutVar i =>
      if i.val = k then none
      else if h : k < i.val then some (.mutVar ⟨i.val - 1, by omega⟩)
      else if h' : i.val < m then some (.mutVar ⟨i.val, h'⟩)
      else none
  | .unsafeGlobal n => some (.unsafeGlobal n)
  | .number raw => some (.number raw)
  | .string v => some (.string v)
  | .regex raw => some (.regex raw)
  | .null => some .null
  | .true_ => some .true_
  | .false_ => some .false_
  | .this => some .this
  | .array els => (strengthenMutArrayElems k els).map .array
  | .object ps => (strengthenMutProperties k ps).map .object
  | .assign t op rhs => do
      pure (.assign (← strengthenMutTarget k t) op (← strengthenMutExpr k rhs))
  | .update t op isPrefix => do pure (.update (← strengthenMutTarget k t) op isPrefix)
  | .await x => do pure (.await (← strengthenMutExpr k x))
  | .call f args => do pure (.call (← strengthenMutExpr k f) (← strengthenMutExprs k args))
  | .new f args => do pure (.new (← strengthenMutExpr k f) (← strengthenMutExprs k args))
  | .dot o n => do pure (.dot (← strengthenMutExpr k o) n)
  | .index o i => do pure (.index (← strengthenMutExpr k o) (← strengthenMutExpr k i))
  | .classAnon her body => do
      pure (.classAnon (← strengthenMutOptExpr k her) (← strengthenMutClassElems k body))
  | .classSelf her body => do
      pure (.classSelf (← strengthenMutOptExpr k her) (← strengthenMutClassElems k body))
  | .seq a b => do pure (.seq (← strengthenMutExpr k a) (← strengthenMutExpr k b))
  | .binary a op b => do pure (.binary (← strengthenMutExpr k a) op (← strengthenMutExpr k b))
  | .ternary a b d => do
      pure (.ternary (← strengthenMutExpr k a) (← strengthenMutExpr k b)
        (← strengthenMutExpr k d))
  | .arrow arity body => do
      pure (.arrow arity (← strengthenMutArrowBody (m := m + arity) (k + arity)
        (body.castScope rfl (by omega))))
  | .func isAsync isGen arity body => do
      pure (.func isAsync isGen arity (← strengthenMutBlock (m := m + arity) (k + arity)
        (body.castScope rfl (by omega))))
  | .funcSelf isAsync isGen arity body => do
      pure (.funcSelf isAsync isGen arity (← strengthenMutBlock (m := m + arity) (k + arity)
        (body.castScope rfl (by omega))))
  | .spread x => do pure (.spread (← strengthenMutExpr k x))
  | .template tag head parts => do
      pure (.template (← strengthenMutOptExpr k tag) head (← strengthenMutTemplateParts k parts))
  | .unary op x => do pure (.unary op (← strengthenMutExpr k x))
  | .yield x => do pure (.yield (← strengthenMutOptExpr k x))
  | .yieldFrom x => do pure (.yieldFrom (← strengthenMutExpr k x))

/-- Remove the mutable variable of index `k` from an assignment target. -/
partial def strengthenMutTarget {c m : Nat} (k : Nat) : Target c (m + 1) → Option (Target c m)
  | .mut i =>
      if i.val = k then none
      else if h : k < i.val then some (.mut ⟨i.val - 1, by omega⟩)
      else if h' : i.val < m then some (.mut ⟨i.val, h'⟩)
      else none
  | .unsafeGlobal n => some (.unsafeGlobal n)
  | .dot o n => do pure (.dot (← strengthenMutExpr k o) n)
  | .index o i => do pure (.index (← strengthenMutExpr k o) (← strengthenMutExpr k i))

/-- Remove the mutable variable of index `k` from a list of expressions. -/
partial def strengthenMutExprs {c m : Nat} (k : Nat) : Exprs c (m + 1) → Option (Exprs c m)
  | .nil => some .nil
  | .cons e r => do pure (.cons (← strengthenMutExpr k e) (← strengthenMutExprs k r))

/-- Remove the mutable variable of index `k` from an optional expression. -/
partial def strengthenMutOptExpr {c m : Nat} (k : Nat) : OptExpr c (m + 1) → Option (OptExpr c m)
  | .none => some .none
  | .some e => do pure (.some (← strengthenMutExpr k e))

/-- Remove the mutable variable of index `k` from the elements of an
array. -/
partial def strengthenMutArrayElems {c m : Nat} (k : Nat) :
    ArrayElems c (m + 1) → Option (ArrayElems c m)
  | .nil => some .nil
  | .cons .hole r => do pure (.cons .hole (← strengthenMutArrayElems k r))
  | .cons (.elem e) r => do
      pure (.cons (.elem (← strengthenMutExpr k e)) (← strengthenMutArrayElems k r))

/-- Remove the mutable variable of index `k` from a template literal. -/
partial def strengthenMutTemplateParts {c m : Nat} (k : Nat) :
    TemplateParts c (m + 1) → Option (TemplateParts c m)
  | .nil => some .nil
  | .cons (.mk e s) r => do
      pure (.cons (.mk (← strengthenMutExpr k e) s) (← strengthenMutTemplateParts k r))

/-- Remove the mutable variable of index `k` from the name of a
property. -/
partial def strengthenMutPropName {c m : Nat} (k : Nat) :
    PropName c (m + 1) → Option (PropName c m)
  | .ident n => some (.ident n)
  | .string v => some (.string v)
  | .number raw => some (.number raw)
  | .computed e => do pure (.computed (← strengthenMutExpr k e))

/-- Remove the mutable variable of index `k` from an object literal. -/
partial def strengthenMutProperties {c m : Nat} (k : Nat) :
    Properties c (m + 1) → Option (Properties c m)
  | .nil => some .nil
  | .cons (.keyValue key v) r => do
      pure (.cons (.keyValue (← strengthenMutPropName k key) (← strengthenMutExpr k v))
        (← strengthenMutProperties k r))
  | .cons (.method kind key arity body) r => do
      pure (.cons (.method kind (← strengthenMutPropName k key) arity
          (← strengthenMutBlock (m := m + arity) (k + arity) (body.castScope rfl (by omega))))
        (← strengthenMutProperties k r))

/-- Remove the mutable variable of index `k` from a class body. -/
partial def strengthenMutClassElems {c m : Nat} (k : Nat) :
    ClassElems c (m + 1) → Option (ClassElems c m)
  | .nil => some .nil
  | .cons (.mk isStatic kind key arity body) r => do
      pure (.cons (.mk isStatic kind (← strengthenMutPropName k key) arity
          (← strengthenMutBlock (m := m + arity) (k + arity) (body.castScope rfl (by omega))))
        (← strengthenMutClassElems k r))

/-- Remove the mutable variable of index `k` from the body of an arrow. -/
partial def strengthenMutArrowBody {c m : Nat} (k : Nat) :
    ArrowBody c (m + 1) → Option (ArrowBody c m)
  | .expr e => do pure (.expr (← strengthenMutExpr k e))
  | .block b => do pure (.block (← strengthenMutBlock k b))

/-- Remove the mutable variable of index `k` from the first clause of a
`for (;;)`. -/
partial def strengthenMutForInit {c m dc dm : Nat} (k : Nat) :
    ForInit c (m + 1) dc dm → Option (ForInit c m dc dm)
  | .none => some .none
  | .expr e => do pure (.expr (← strengthenMutExpr k e))
  | .constDecl init => do pure (.constDecl (← strengthenMutExpr k init))
  | .letDecl init => do pure (.letDecl (← strengthenMutOptExpr k init))

/-- Remove the mutable variable of index `k` from the binder of a
`for (... of ...)`. -/
partial def strengthenMutForHead {c m dc dm : Nat} (k : Nat) :
    ForHead c (m + 1) dc dm → Option (ForHead c m dc dm)
  | .target t => do pure (.target (← strengthenMutTarget k t))
  | .constBind => some .constBind
  | .letBind => some .letBind

/-- Remove the mutable variable of index `k` from the cases of a
`switch`. -/
partial def strengthenMutSwitchCases {c m : Nat} (k : Nat) :
    SwitchCases c (m + 1) → Option (SwitchCases c m)
  | .nil => some .nil
  | .cons (.case t b) r => do
      pure (.cons (.case (← strengthenMutExpr k t) (← strengthenMutBlock k b))
        (← strengthenMutSwitchCases k r))
  | .cons (.default b) r => do
      pure (.cons (.default (← strengthenMutBlock k b)) (← strengthenMutSwitchCases k r))

/-- Remove the mutable variable of index `k` from an optional block. -/
partial def strengthenMutOptBlock {c m : Nat} (k : Nat) :
    OptBlock c (m + 1) → Option (OptBlock c m)
  | .none => some .none
  | .some b => do pure (.some (← strengthenMutBlock k b))

/-- Remove the mutable variable of index `k` from what follows a `try`. -/
partial def strengthenMutTryTail {c m : Nat} (k : Nat) : TryTail c (m + 1) → Option (TryTail c m)
  | .catch_ body fin => do
      pure (.catch_ (← strengthenMutBlock (m := m + 1) (k + 1) body)
        (← strengthenMutOptBlock k fin))
  | .finallyOnly b => do pure (.finallyOnly (← strengthenMutBlock k b))

/-- Remove the mutable variable of index `k` from a statement. -/
partial def strengthenMutStmt {c m dc dm : Nat} (k : Nat) :
    Stmt c (m + 1) dc dm → Option (Stmt c m dc dm)
  | .expr e => do pure (.expr (← strengthenMutExpr k e))
  | .constDecl init => do pure (.constDecl (← strengthenMutExpr k init))
  | .letDecl init => do pure (.letDecl (← strengthenMutOptExpr k init))
  | .block b => do pure (.block (← strengthenMutBlock k b))
  | .if_ cond t e => do
      pure (.if_ (← strengthenMutExpr k cond) (← strengthenMutBlock k t)
        (← strengthenMutOptBlock k e))
  | .while_ cond b => do
      pure (.while_ (← strengthenMutExpr k cond) (← strengthenMutBlock k b))
  | .doWhile b cond => do
      pure (.doWhile (← strengthenMutBlock k b) (← strengthenMutExpr k cond))
  | .for_ (dm := dm') init cond step body => do
      let init ← strengthenMutForInit k init
      let cond ← strengthenMutOptExpr (m := m + dm') (k + dm')
        (cond.castScope rfl (by omega))
      let step ← strengthenMutOptExpr (m := m + dm') (k + dm')
        (step.castScope rfl (by omega))
      let body ← strengthenMutBlock (m := m + dm') (k + dm')
        (body.castScope rfl (by omega))
      pure (.for_ init cond step body)
  | .forIn (dm := dm') head obj body => do
      let head ← strengthenMutForHead k head
      let obj ← strengthenMutExpr k obj
      let body ← strengthenMutBlock (m := m + dm') (k + dm') (body.castScope rfl (by omega))
      pure (.forIn head obj body)
  | .forOf (dm := dm') head obj body => do
      let head ← strengthenMutForHead k head
      let obj ← strengthenMutExpr k obj
      let body ← strengthenMutBlock (m := m + dm') (k + dm') (body.castScope rfl (by omega))
      pure (.forOf head obj body)
  | .funcDecl isAsync isGen arity body => do
      pure (.funcDecl isAsync isGen arity
        (← strengthenMutBlock (m := m + arity) (k + arity) (body.castScope rfl (by omega))))
  | .classDecl her body => do
      pure (.classDecl (← strengthenMutOptExpr k her) (← strengthenMutClassElems k body))
  | .return_ e => do pure (.return_ (← strengthenMutOptExpr k e))
  | .throw e => do pure (.throw (← strengthenMutExpr k e))
  | .break_ l => some (.break_ l)
  | .continue_ l => some (.continue_ l)
  | .labelled l s => do pure (.labelled l (← strengthenMutStmt k s))
  | .switch disc cases => do
      pure (.switch (← strengthenMutExpr k disc) (← strengthenMutSwitchCases k cases))
  | .try_ b tail => do
      pure (.try_ (← strengthenMutBlock k b) (← strengthenMutTryTail k tail))

/-- Remove the mutable variable of index `k` from a block. -/
partial def strengthenMutBlock {c m : Nat} (k : Nat) : Block c (m + 1) → Option (Block c m)
  | .nil => some .nil
  | .cons (dc := dc) (dm := dm) hd tl => do
      let hd ← strengthenMutStmt k hd
      let tl ← strengthenMutBlock (m := m + dm) (k + dm) (tl.castScope rfl (by omega))
      pure (.cons hd tl)

end

/-! ## The top level

An `export { x }` mentions a variable, so a binding that is exported is
never removable — which is exactly what these give. -/

/-- Remove the const variable of index `k` from an `export { ... }`
clause. -/
def strengthenConstExportLocals {c m : Nat} (k : Nat) :
    ExportLocals (c + 1) m → Option (ExportLocals c m)
  | .nil => some .nil
  | .cons (.const i exported) r => do
      let hd ←
        if i.val = k then none
        else if h : k < i.val then some (ExportLocal.const ⟨i.val - 1, by omega⟩ exported)
        else if h' : i.val < c then some (ExportLocal.const ⟨i.val, h'⟩ exported)
        else none
      pure (.cons hd (← strengthenConstExportLocals k r))
  | .cons (.mut i exported) r => do
      pure (.cons (.mut i exported) (← strengthenConstExportLocals k r))

/-- Remove the mutable variable of index `k` from an `export { ... }`
clause. -/
def strengthenMutExportLocals {c m : Nat} (k : Nat) :
    ExportLocals c (m + 1) → Option (ExportLocals c m)
  | .nil => some .nil
  | .cons (.mut i exported) r => do
      let hd ←
        if i.val = k then none
        else if h : k < i.val then some (ExportLocal.mut ⟨i.val - 1, by omega⟩ exported)
        else if h' : i.val < m then some (ExportLocal.mut ⟨i.val, h'⟩ exported)
        else none
      pure (.cons hd (← strengthenMutExportLocals k r))
  | .cons (.const i exported) r => do
      pure (.cons (.const i exported) (← strengthenMutExportLocals k r))

/-- Remove the const variable of index `k` from a top level item. -/
def strengthenConstModuleItem {c m dc dm : Nat} (k : Nat) :
    ModuleItem (c + 1) m dc dm → Option (ModuleItem c m dc dm)
  | .stmt s => do pure (.stmt (← strengthenConstStmt k s))
  | .importBare mod => some (.importBare mod)
  | .importClause clause => some (.importClause clause)
  | .exportFrom specs mod => some (.exportFrom specs mod)
  | .exportLocals specs => do pure (.exportLocals (← strengthenConstExportLocals k specs))
  | .exportDecl s => do pure (.exportDecl (← strengthenConstStmt k s))

/-- Remove the mutable variable of index `k` from a top level item. -/
def strengthenMutModuleItem {c m dc dm : Nat} (k : Nat) :
    ModuleItem c (m + 1) dc dm → Option (ModuleItem c m dc dm)
  | .stmt s => do pure (.stmt (← strengthenMutStmt k s))
  | .importBare mod => some (.importBare mod)
  | .importClause clause => some (.importClause clause)
  | .exportFrom specs mod => some (.exportFrom specs mod)
  | .exportLocals specs => do pure (.exportLocals (← strengthenMutExportLocals k specs))
  | .exportDecl s => do pure (.exportDecl (← strengthenMutStmt k s))

/-- Remove the const variable of index `k` from the top level items. -/
partial def strengthenConstModuleItems {c m : Nat} (k : Nat) :
    ModuleItems (c + 1) m → Option (ModuleItems c m)
  | .nil => some .nil
  | .cons (dc := dc) hd tl => do
      let hd ← strengthenConstModuleItem k hd
      let tl ← strengthenConstModuleItems (c := c + dc) (k + dc) (tl.castScope (by omega) rfl)
      pure (.cons hd tl)

/-- Remove the mutable variable of index `k` from the top level items. -/
partial def strengthenMutModuleItems {c m : Nat} (k : Nat) :
    ModuleItems c (m + 1) → Option (ModuleItems c m)
  | .nil => some .nil
  | .cons (dm := dm) hd tl => do
      let hd ← strengthenMutModuleItem k hd
      let tl ← strengthenMutModuleItems (m := m + dm) (k + dm) (tl.castScope rfl (by omega))
      pure (.cons hd tl)

end Language.JavaScript.BrujinAST
