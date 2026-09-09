/-
Conversion of the deterministic `MiniAST` into the scope safe `BrujinAST`.

This is the interesting direction: `MiniAST` talks about variables by name,
`BrujinAST` by de Bruijn index into one of its two scopes, so the
conversion is a scope check.  It keeps an environment of the bindings that
are in scope, remembering for each of them its name, whether it is a const
or a mutable binding, and its *level* — the number of bindings of its kind
that were in scope where it was bound.  The index of a variable at a given
depth is then computed from its level (`constIndex?`, `mutIndex?`).

A name that the environment does not know is not an error: it becomes
`Expr.unsafeGlobal`, the escape hatch.  That covers the globals
(`console`, `Math`, …) and also a function of the same file that is used
before the statement which declares it — `BrujinAST` has no hoisting.

What *is* an error is a program the target cannot describe: a destructuring
pattern or a default value in a binder, `with`, an assignment to a `const`
variable, a `catch` with a guard or with several clauses, and a `for` whose
first clause declares more than one variable.  A `var`/`let`/`const`
statement with several declarators is not an error: it is split into one
statement per declarator first, and empty statements are dropped.
-/
import RequestProject.JavaScript.BrujinAST
import RequestProject.JavaScript.MiniASTOfAST

namespace Language.JavaScript.BrujinAST

open Language.JavaScript.MiniAST

/-! ## The environment -/

/-- One binding that is in scope. -/
structure Binding where
  /-- The name it was written with in the `MiniAST` tree. -/
  name : NEString
  /-- Whether it is a const binding (as opposed to a mutable one). -/
  isConst : Bool
  /-- Its level: the number of bindings of its kind that were already in
  scope where it was bound. -/
  level : Nat
deriving Repr, Inhabited

/-- The bindings in scope, most recently bound first. -/
abbrev Env := List Binding

namespace Env

/-- The innermost binding of `n`, if there is one. -/
def lookup (env : Env) (n : NEString) : Option Binding :=
  env.find? fun b => b.name.val == n.val

/-- Add `names`, bound left to right as const bindings, to a scope that had
`c` const bindings. -/
def pushConsts (env : Env) (c : Nat) (names : List NEString) : Env :=
  (names.zipIdx.map fun (n, j) => ⟨n, true, c + j⟩).reverse ++ env

/-- Add `names`, bound left to right as mutable bindings, to a scope that
had `m` mutable bindings. -/
def pushMuts (env : Env) (m : Nat) (names : List NEString) : Env :=
  (names.zipIdx.map fun (n, j) => ⟨n, false, m + j⟩).reverse ++ env

end Env

/-- The result of a conversion: the node, or a message. -/
abbrev ConvM := Except String

/-- Report a program that `BrujinAST` cannot describe. -/
def fail (msg : String) : ConvM α := .error ("BrujinAST: " ++ msg)

/-! ## Resolving a name -/

/-- The expression a name denotes: the variable it is bound to, or
`unsafeGlobal` if it is not bound. -/
def resolveVar (env : Env) (c m : Nat) (n : NEString) : Expr c m :=
  match env.lookup n with
  | none => .unsafeGlobal n
  | some b =>
      if b.isConst then
        match constIndex? c b.level with
        | some i => .constVar i
        | none => .unsafeGlobal n
      else
        match mutIndex? m b.level with
        | some i => .mutVar i
        | none => .unsafeGlobal n

/-- The assignment target a name denotes.  Assigning to a const binding is
an error — that is what `const` means. -/
def resolveTarget (env : Env) (c m : Nat) (n : NEString) : ConvM (Target c m) :=
  match env.lookup n with
  | none => pure (.unsafeGlobal n)
  | some b =>
      if b.isConst then
        fail s!"assignment to the const variable {n.val}"
      else
        match mutIndex? m b.level with
        | some i => pure (.mut i)
        | none => pure (.unsafeGlobal n)

/-- The name a binder is written with; a destructuring pattern or a default
value is not supported. -/
def binderName : MiniExpr → ConvM NEString
  | .ident n => pure n
  | .array _ | .object _ => fail "a destructuring pattern in a binder"
  | .assign _ _ _ => fail "a default value in a binder"
  | _ => fail "a binder that is not a name"

/-- The names of a parameter list. -/
def paramNamesOf (params : List MiniExpr) : ConvM (List NEString) :=
  params.mapM binderName

/-! ## Splitting declarations

A statement of `BrujinAST` binds at most one variable, so a declaration
with several declarators is split first; an empty statement is dropped. -/

/-- Split a `var`/`let`/`const` statement into one statement per
declarator, and drop an empty statement. -/
def splitDecl : MiniStatement → List MiniStatement
  | .empty => []
  | .decl kind decls => decls.toList.map fun d => .decl kind ⟨d, []⟩
  | s => [s]

/-- Split every declaration of a list of statements. -/
def expandStmts (l : List MiniStatement) : List MiniStatement := l.flatMap splitDecl

/-- Split every declaration of a list of top level items. -/
def expandItems (items : List MiniModuleItem) : List MiniModuleItem :=
  items.flatMap fun
    | .stmt s => (splitDecl s).map .stmt
    | .exportDecl (.decl s) => (splitDecl s).map fun s => .exportDecl (.decl s)
    | it => [it]

/-! ## The conversion -/

/-- A converted statement: how many const and mutable bindings it adds, the
statement itself, and the bindings it adds, in binding order. -/
structure StmtRes (c m : Nat) where
  /-- The number of const bindings the statement adds. -/
  dc : Nat
  /-- The number of mutable bindings the statement adds. -/
  dm : Nat
  /-- The statement. -/
  stmt : Stmt c m dc dm
  /-- The bindings it adds, in binding order. -/
  binds : List Binding

/-- A converted top level item. -/
structure ItemRes (c m : Nat) where
  /-- The number of const bindings the item adds. -/
  dc : Nat
  /-- The number of mutable bindings the item adds. -/
  dm : Nat
  /-- The item. -/
  item : ModuleItem c m dc dm
  /-- The bindings it adds, in binding order. -/
  binds : List Binding

mutual

/-- Convert an expression. -/
partial def ofExpr (env : Env) (c m : Nat) (e : MiniExpr) : ConvM (Expr c m) := do
  match e with
  | .ident n => pure (resolveVar env c m n)
  | .number raw => pure (.number raw)
  | .string v => pure (.string v)
  | .regex raw => pure (.regex raw)
  | .null => pure .null
  | .true_ => pure .true_
  | .false_ => pure .false_
  | .this => pure .this
  | .array els => pure (.array (ArrayElems.ofList (← els.mapM (ofArrayElem env c m))))
  | .object ps => pure (.object (Properties.ofList (← ps.mapM (ofProperty env c m))))
  | .assign lhs op rhs =>
      pure (.assign (← ofTarget env c m lhs) op (← ofExpr env c m rhs))
  | .postfix x op => pure (.update (← ofTarget env c m x) op false)
  | .unary op x =>
      match op with
      | .preIncr => pure (.update (← ofTarget env c m x) .incr true)
      | .preDecr => pure (.update (← ofTarget env c m x) .decr true)
      | _ => pure (.unary op (← ofExpr env c m x))
  | .await x => pure (.await (← ofExpr env c m x))
  | .call f args => pure (.call (← ofExpr env c m f) (Exprs.ofList (← args.mapM (ofExpr env c m))))
  | .new f args => pure (.new (← ofExpr env c m f) (Exprs.ofList (← args.mapM (ofExpr env c m))))
  | .dot o n => pure (.dot (← ofExpr env c m o) n)
  | .index o i => pure (.index (← ofExpr env c m o) (← ofExpr env c m i))
  | .classExpr name heritage body =>
      let her ← ofOptExpr env c m heritage
      match name with
      | none => pure (.classAnon her (← ofClassElems env c m body))
      | some n =>
          pure (.classSelf her (← ofClassElems (env.pushConsts c [n]) (c + 1) m body))
  | .seq a b => pure (.seq (← ofExpr env c m a) (← ofExpr env c m b))
  | .binary a op b => pure (.binary (← ofExpr env c m a) op (← ofExpr env c m b))
  | .ternary a b d =>
      pure (.ternary (← ofExpr env c m a) (← ofExpr env c m b) (← ofExpr env c m d))
  | .arrow params body =>
      let ps ← paramNamesOf params
      let inner := env.pushMuts m ps
      match body with
      | .expr x => pure (.arrow ps.length (.expr (← ofExpr inner c (m + ps.length) x)))
      | .block b => pure (.arrow ps.length (.block (← ofBlock inner c (m + ps.length) b)))
  | .func isAsync isGen name params body =>
      let ps ← paramNamesOf params
      match name with
      | none =>
          let inner := env.pushMuts m ps
          pure (.func isAsync isGen ps.length (← ofBlock inner c (m + ps.length) body))
      | some n =>
          let inner := (env.pushConsts c [n]).pushMuts m ps
          pure (.funcSelf isAsync isGen ps.length (← ofBlock inner (c + 1) (m + ps.length) body))
  | .spread x => pure (.spread (← ofExpr env c m x))
  | .template tag head parts =>
      pure (.template (← ofOptExpr env c m tag) head
        (TemplateParts.ofList (← parts.mapM fun p => do
          pure (TemplatePart.mk (← ofExpr env c m p.expr) p.suffix))))
  | .yield x => pure (.yield (← ofOptExpr env c m x))
  | .yieldFrom x => pure (.yieldFrom (← ofExpr env c m x))

/-- Convert an optional expression. -/
partial def ofOptExpr (env : Env) (c m : Nat) : Option MiniExpr → ConvM (OptExpr c m)
  | none => pure .none
  | some e => do pure (.some (← ofExpr env c m e))

/-- Convert the left hand side of an assignment or of an increment. -/
partial def ofTarget (env : Env) (c m : Nat) (e : MiniExpr) : ConvM (Target c m) := do
  match e with
  | .ident n => resolveTarget env c m n
  | .dot o n => pure (.dot (← ofExpr env c m o) n)
  | .index o i => pure (.index (← ofExpr env c m o) (← ofExpr env c m i))
  | _ => fail "an assignment target that is not a variable or a member"

/-- Convert an element of an array literal. -/
partial def ofArrayElem (env : Env) (c m : Nat) : MiniArrayElement → ConvM (ArrayElem c m)
  | .hole => pure .hole
  | .elem e => do pure (.elem (← ofExpr env c m e))

/-- Convert the name of a property. -/
partial def ofPropName (env : Env) (c m : Nat) : MiniPropertyName → ConvM (PropName c m)
  | .ident n => pure (.ident n)
  | .string v => pure (.string v)
  | .number raw => pure (.number raw)
  | .computed e => do pure (.computed (← ofExpr env c m e))

/-- Convert a member of an object literal.  Shorthand `{x}` becomes the
key/value pair `{x: x}`, with the variable resolved. -/
partial def ofProperty (env : Env) (c m : Nat) : MiniProperty → ConvM (Property c m)
  | .keyValue k v => do pure (.keyValue (← ofPropName env c m k) (← ofExpr env c m v))
  | .shorthand n => pure (.keyValue (.ident n) (resolveVar env c m n))
  | .method kind k params body => do
      let ps ← paramNamesOf params
      pure (.method kind (← ofPropName env c m k) ps.length
        (← ofBlock (env.pushMuts m ps) c (m + ps.length) body))

/-- Convert a member of a class body. -/
partial def ofClassElem (env : Env) (c m : Nat) (el : MiniClassElement) :
    ConvM (ClassElem c m) := do
  let ps ← paramNamesOf el.params
  pure (.mk el.isStatic el.kind (← ofPropName env c m el.key) ps.length
    (← ofBlock (env.pushMuts m ps) c (m + ps.length) el.body))

/-- Convert the members of a class body. -/
partial def ofClassElems (env : Env) (c m : Nat) (els : List MiniClassElement) :
    ConvM (ClassElems c m) := do
  pure (ClassElems.ofList (← els.mapM (ofClassElem env c m)))

/-- Convert one case of a `switch`. -/
partial def ofSwitchCase (env : Env) (c m : Nat) : MiniSwitchCase → ConvM (SwitchCase c m)
  | .case t b => do pure (.case (← ofExpr env c m t) (← ofBlock env c m b))
  | .default b => do pure (.default (← ofBlock env c m b))

/-- Convert the body of a statement, which is a block if it is written as
one and a one statement block otherwise. -/
partial def ofBody (env : Env) (c m : Nat) : MiniStatement → ConvM (Block c m)
  | .block b => ofBlock env c m b
  | .empty => pure .nil
  | s => ofBlock env c m [s]

/-- Convert an optional body. -/
partial def ofOptBody (env : Env) (c m : Nat) : Option MiniStatement → ConvM (OptBlock c m)
  | none => pure .none
  | some s => do pure (.some (← ofBody env c m s))

/-- Convert a list of statements into a block. -/
partial def ofBlock (env : Env) (c m : Nat) (stmts : List MiniStatement) :
    ConvM (Block c m) :=
  ofStmts env c m (expandStmts stmts)

/-- Convert a list of statements in which the declarations have already
been split. -/
partial def ofStmts (env : Env) (c m : Nat) : List MiniStatement → ConvM (Block c m)
  | [] => pure .nil
  | s :: rest => do
      let r ← ofStmt env c m s
      let tl ← ofStmts (r.binds.reverse ++ env) (c + r.dc) (m + r.dm) rest
      pure (.cons r.stmt tl)

/-- Convert a `for (... in ...)` or `for (... of ...)` statement. -/
partial def ofForInOf (env : Env) (c m : Nat) (isOf : Bool) (head : MiniForHead)
    (obj : MiniExpr) (body : MiniStatement) : ConvM (StmtRes c m) := do
  let obj' ← ofExpr env c m obj
  match head with
  | .pattern lhs =>
      let t ← ofTarget env c m lhs
      let b ← ofBody env c m body
      return ⟨0, 0, if isOf then .forOf (.target t) obj' b else .forIn (.target t) obj' b, []⟩
  | .decl kind lhs =>
      let n ← binderName lhs
      match kind with
      | .const =>
          let b ← ofBody (env.pushConsts c [n]) (c + 1) m body
          return ⟨0, 0, if isOf then .forOf .constBind obj' b else .forIn .constBind obj' b, []⟩
      | _ =>
          let b ← ofBody (env.pushMuts m [n]) c (m + 1) body
          return ⟨0, 0, if isOf then .forOf .letBind obj' b else .forIn .letBind obj' b, []⟩

/-- Convert a `for (;;)` statement. -/
partial def ofForC (env : Env) (c m : Nat) (init : MiniForInit) (cond step : Option MiniExpr)
    (body : MiniStatement) : ConvM (StmtRes c m) := do
  match init with
  | .none =>
      return ⟨0, 0, .for_ .none (← ofOptExpr env c m cond) (← ofOptExpr env c m step)
        (← ofBody env c m body), []⟩
  | .expr e =>
      let e' ← ofExpr env c m e
      return ⟨0, 0, .for_ (.expr e') (← ofOptExpr env c m cond) (← ofOptExpr env c m step)
        (← ofBody env c m body), []⟩
  | .decl kind decls =>
      match decls.tl with
      | _ :: _ => fail "a `for` clause that declares several variables"
      | [] =>
        let d := decls.hd
        let n ← binderName d.lhs
        match kind with
        | .const =>
            match d.init with
            | none => fail "a const declaration without an initialiser"
            | some i =>
                let i' ← ofExpr env c m i
                let inner := env.pushConsts c [n]
                return ⟨0, 0, .for_ (.constDecl i') (← ofOptExpr inner (c + 1) m cond)
                  (← ofOptExpr inner (c + 1) m step) (← ofBody inner (c + 1) m body), []⟩
        | _ =>
            let i' ← ofOptExpr env c m d.init
            let inner := env.pushMuts m [n]
            return ⟨0, 0, .for_ (.letDecl i') (← ofOptExpr inner c (m + 1) cond)
              (← ofOptExpr inner c (m + 1) step) (← ofBody inner c (m + 1) body), []⟩

/-- Convert a statement. -/
partial def ofStmt (env : Env) (c m : Nat) (s : MiniStatement) : ConvM (StmtRes c m) := do
  match s with
  | .expr e => return ⟨0, 0, .expr (← ofExpr env c m e), []⟩
  | .empty => return ⟨0, 0, .block .nil, []⟩
  | .decl kind decls =>
      match decls.tl with
      | _ :: _ => fail "a declaration of several variables (it should have been split)"
      | [] =>
        let d := decls.hd
        let n ← binderName d.lhs
        match kind with
        | .const =>
            match d.init with
            | none => fail "a const declaration without an initialiser"
            | some i => return ⟨1, 0, .constDecl (← ofExpr env c m i), [⟨n, true, c⟩]⟩
        | _ => return ⟨0, 1, .letDecl (← ofOptExpr env c m d.init), [⟨n, false, m⟩]⟩
  | .block b => return ⟨0, 0, .block (← ofBlock env c m b), []⟩
  | .if_ cond t e =>
      return ⟨0, 0, .if_ (← ofExpr env c m cond) (← ofBody env c m t)
        (← ofOptBody env c m e), []⟩
  | .while_ cond b => return ⟨0, 0, .while_ (← ofExpr env c m cond) (← ofBody env c m b), []⟩
  | .doWhile b cond => return ⟨0, 0, .doWhile (← ofBody env c m b) (← ofExpr env c m cond), []⟩
  | .for_ init cond step body => ofForC env c m init cond step body
  | .forIn head obj body => ofForInOf env c m false head obj body
  | .forOf head obj body => ofForInOf env c m true head obj body
  | .funcDecl isAsync isGen name params body =>
      let ps ← paramNamesOf params
      let inner := (env.pushConsts c [name]).pushMuts m ps
      let b ← ofBlock inner (c + 1) (m + ps.length) body
      return ⟨1, 0, .funcDecl isAsync isGen ps.length b, [⟨name, true, c⟩]⟩
  | .classDecl name heritage body =>
      let her ← ofOptExpr env c m heritage
      let els ← ofClassElems (env.pushConsts c [name]) (c + 1) m body
      return ⟨1, 0, .classDecl her els, [⟨name, true, c⟩]⟩
  | .return_ e => return ⟨0, 0, .return_ (← ofOptExpr env c m e), []⟩
  | .throw e => return ⟨0, 0, .throw (← ofExpr env c m e), []⟩
  | .break_ l => return ⟨0, 0, .break_ l, []⟩
  | .continue_ l => return ⟨0, 0, .continue_ l, []⟩
  | .labelled l s' =>
      let ⟨dc, dm, st, _⟩ ← ofStmt env c m s'
      match dc, dm, st with
      | 0, 0, st' => return ⟨0, 0, .labelled l st', []⟩
      | _, _, _ => fail "a labelled statement that declares a variable"
  | .switch d cases =>
      return ⟨0, 0, .switch (← ofExpr env c m d)
        (SwitchCases.ofList (← cases.mapM (ofSwitchCase env c m))), []⟩
  | .try_ body tail =>
      let b ← ofBlock env c m body
      match tail with
      | .finallyOnly fb => return ⟨0, 0, .try_ b (.finallyOnly (← ofBlock env c m fb)), []⟩
      | .catches cs fin =>
          match cs.tl with
          | _ :: _ => fail "a `try` with several catch clauses"
          | [] =>
            let cat := cs.hd
            match cat.guard with
            | some _ => fail "a catch clause with a guard"
            | none =>
                let n ← binderName cat.param
                let cb ← ofBlock (env.pushMuts m [n]) c (m + 1) cat.body
                let f : OptBlock c m ←
                  match fin with
                  | .none => pure .none
                  | .some fb => do pure (.some (← ofBlock env c m fb))
                return ⟨0, 0, .try_ b (.catch_ cb f), []⟩
  | .with_ _ _ => fail "a `with` statement (its scope is dynamic)"

end

/-! ## Modules -/

/-- Convert a top level item. -/
def ofModuleItem (env : Env) (c m : Nat) : MiniModuleItem → ConvM (ItemRes c m)
  | .stmt s => do
      let r ← ofStmt env c m s
      return ⟨r.dc, r.dm, .stmt r.stmt, r.binds⟩
  | .importDecl (.bare mod) => pure ⟨0, 0, .importBare mod, []⟩
  | .importDecl (.clause cl) => do
      let specs := cl.named.getD []
      let names := specs.map (·.name)
      let locals :=
        cl.default_.toList ++ cl.namespace_.toList ++ specs.map fun s => s.alias_.getD s.name
      match ImportClause.mk? cl.mod cl.default_.isSome cl.namespace_.isSome names with
      | none => fail "an import that binds nothing"
      | some clause =>
          return ⟨clause.count, 0, .importClause clause,
            locals.zipIdx.map fun (n, j) => ⟨n, true, c + j⟩⟩
  | .exportDecl (.fromClause specs mod) => pure ⟨0, 0, .exportFrom specs mod, []⟩
  | .exportDecl (.locals specs) => do
      let entries ← specs.mapM fun sp => do
        let exported := sp.alias_.getD sp.name
        match env.lookup sp.name with
        | none => fail s!"export of the unbound name {sp.name.val}"
        | some b =>
            if b.isConst then
              match constIndex? c b.level with
              | some i => pure (ExportLocal.const i exported)
              | none => fail s!"export of the out of scope name {sp.name.val}"
            else
              match mutIndex? m b.level with
              | some i => pure (ExportLocal.mut i exported)
              | none => fail s!"export of the out of scope name {sp.name.val}"
      return ⟨0, 0, .exportLocals (ExportLocals.ofList entries), []⟩
  | .exportDecl (.decl s) => do
      let r ← ofStmt env c m s
      return ⟨r.dc, r.dm, .exportDecl r.stmt, r.binds⟩

/-- Convert a list of top level items in which the declarations have
already been split. -/
partial def ofItems (env : Env) (c m : Nat) : List MiniModuleItem → ConvM (ModuleItems c m)
  | [] => pure .nil
  | it :: rest => do
      let r ← ofModuleItem env c m it
      let tl ← ofItems (r.binds.reverse ++ env) (c + r.dc) (m + r.dm) rest
      pure (.cons r.item tl)

/-- Convert a whole `MiniAST` program into a scope safe one. -/
def ofMiniProgram (p : MiniProgram) : ConvM Program := do
  pure ⟨← ofItems [] 0 0 (expandItems p.items)⟩

/-- Read JavaScript source into a `BrujinAST` program. -/
def parse (input : String) : ConvM Program := do
  ofMiniProgram (← MiniAST.parse input)

end Language.JavaScript.BrujinAST
